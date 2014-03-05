{-
    Breadth-first searching for DLvalidity program
    Author: Abdul Rahim Nizamani
    Created: 2013-10-02
    Updated: 2013-10-17
-}

module Bfs where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (on)
import Expr.TRS
import Data.List
import Niz
import Control.Monad
import Types
import Proof
import Control.Exception
import Control.Concurrent
import Control.Concurrent.MVar
import System.IO
import System.IO.Unsafe
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Time.Clock
import Data.Maybe

-- | Run proof search in concurrent threads
search :: Int -> Int -> [Fi] -> [Fi] -> [RuleD] -> FiSet -> FiSet -> IO (Maybe StateD,Int)
search width depth gamma axioms' rules wm goal = do
    -- create mvars to hold values shared between threads
        -- MVar to hold visited nodes
    let startwm = (Nothing,getSet wm)
    visited <- newMVar (Set.singleton (0,startwm))
        -- MVar to hold threads collection
    threads <- newMVar ([] :: [MVar Int]) -- threadsvalue)
        -- MVar to hold currently minimum proof
    proofmvar <- newMVar (Nothing :: Maybe StateD, 0 :: Int)

    let axioms = gamma ++ axioms'
    let gamma' = Set.fromList $ map Fi $ concatMap getValues gamma
    let rem = head . filter (\r -> ruleName r == "RemoveAxiom") $ rules
    let rules' = filter (\r -> ruleName r /= "RemoveAxiom") $ rules
    let rem' = (rem,getMatches axioms (condition rem))
    let matches = [(rule,getMatches axioms (condition rule)) | rule <- rules']
    nodes <- applyRules width depth gamma' rem' matches 1 $ Start startwm
    let result = filter (isGoal (getSet goal)) nodes
    --U.appendFile "temp.txt" ("\n" ++ (unlines $ map show result))
    
    if (not . null) result
    then do
        let (PStep a b c d) = head result
        return (Just . PStep a b c . reverse $ drop 1 d, length nodes)
    else do
    
    -- Run parallel threads for proof search, one thread for each of the top branch
    prev <- takeMVar visited
    putMVar visited $ Set.union prev (Set.fromList $ zip (repeat 1) $ map getWM nodes)
    
    let processes = map (\(id,x) -> runSearch visited proofmvar (applyRules width depth gamma' rem' matches) depth 2 [x] (getSet goal) id)
                    $ zip [1..] nodes
    putStrLn $ "Starting " ++ show (length processes) ++ " threads."

    threadids <- mapM (forkChild threads) processes
    waitForChildren threads
    (result,lev) <- takeMVar proofmvar
    putMVar proofmvar (result,lev)
    v <- takeMVar visited
    putMVar visited v
    if isNothing result
    then return (result,Set.size v)
    else do
        let (PStep a b c d) = fromJust result
        return (Just . PStep a b c . reverse $ drop 1 d, Set.size v)

waitForChildren :: MVar [MVar Int] -> IO ()
waitForChildren threads = do
      cs <- takeMVar threads
      case cs of
        []   -> do
            putMVar threads cs
            return ()
        m:ms -> do
            list  <- mapM (\x -> do result <- tryTakeMVar x
                                    case result of
                                      Nothing -> return (Left x)
                                      Just i  -> return (Right i))   (m:ms)
            let ms' = [x | (Left x) <- list]
            if (length ms' < length (m:ms))
            then do
                putMVar threads ms'
                putStrLn $ "Remaining threads: " ++ show (length ms')
                waitForChildren threads
            else do
                putMVar threads (m:ms)
                waitForChildren threads

forkChild :: MVar [MVar Int] -> IO () -> IO ThreadId
forkChild threads io = do
        mvar <- newEmptyMVar        
        childs <- takeMVar threads
        putMVar threads (mvar:childs)
        
        forkFinally' io (endIO mvar)
    where endIO m (Left e) = do putMVar m (-1)
          endIO m (Right _) = putMVar m 1
forkFinally' :: IO a -> (Either SomeException a -> IO ()) -> IO ThreadId
forkFinally' action and_then =
  mask $ \restore ->
    forkIO $ try (restore action) >>= and_then


getAllSteps :: Map StateD StateD -> Int -> StateD -> IO [StateD]
getAllSteps m level s = do
    let x = Map.lookup s m
    if isJust x && level > 0
    then do
        xs <- getAllSteps m (level-1) (fromJust x)
        return $ (fromJust x):xs
    else
        return []

runSearch :: MVar (Set (Int,WM))
             -> MVar (Maybe StateD, Int)
             -> (Int -> StateD -> IO [StateD])
             -> Int -- Max depth to explore
             -> Int -- depth level in the tree
             -> [StateD]
             -> Set Fi
             -> Int -- thread number
             -> IO () -- (Maybe (Int,StateD))
runSearch _ _ _ maxlength level _ _ _ | level > maxlength = return ()
runSearch visited proofmvar expand maxlength level nodes goal tid = do
  (state,lev) <- takeMVar proofmvar
  putMVar proofmvar (state,lev)
  if (isJust state && level >= lev)
  then return ()
  else do
    start <- getCurrentTime
    states <- mapM (expand' proofmvar expand level) nodes
    let newstates = concatMap fst states
    
    let result = filter (isGoal goal) newstates
    if notnull result
    then do
      putStrLn $ "Goal found at level " ++ show level
      (state,lev) <- takeMVar proofmvar
      putStrLn $ "Previous goal: " ++ (isNothing state ? "Nothing" $ show (length (getPrevious (fromJust state))))
      let res = minimumBy (compare `on` proofSize) result -- (head (sortBy (compare `on` proofSize) result))
      (isNothing state)
          ? putMVar proofmvar (Just res,level)
          $ (level < lev) 
            ? putMVar proofmvar (Just res,level)
            $ (level == lev && proofSize res < proofSize (fromJust state))
                ? putMVar proofmvar (Just res,level)
                $ putMVar proofmvar (state,lev)
    else do
      prev' <- takeMVar visited
      putMVar visited prev'
      
      --let new' = filter (not . isVisited prev' level) $ nubBy ((==) `on` (getWM)) newstates
      let new' = filter (\x -> and [(i,getWM x) `Set.notMember` prev' | i <- [0..level]])
                   $ nubBy ((==) `on` (getWM)) newstates
      let newset' = Set.fromList $ zip (repeat level) $ map getWM new'
      putStr $ "   nodes: " ++ show (Set.size newset') ++ ", thread " ++ show tid ++ " at level " ++ show level
      end <- getCurrentTime
      putStr $ " time: " ++ show (diffUTCTime end start)
      
      -- Update set of visited nodes
      prev <- takeMVar visited
      let prevnew = Set.union prev newset'
      putMVar visited prevnew
      putStrLn $ "  Total: " ++ show (Set.size prevnew)
      --let new = filter (not . isVisited prev level) new'
      --let new = filter (\x -> and [(i,getWM x) `Set.notMember` prev | i <- [0..level]]) new'
      if notnull new'
        then runSearch visited proofmvar expand maxlength (level+1) new' goal tid
        else return ()

expand' proofmvar expand level node = do
    (proof,lev) <- takeMVar proofmvar
    putMVar proofmvar (proof,lev)
    if (isJust proof && level >= lev)
    then return ([],node)
    else do
        n' <- expand level node
        return (n', node)

isGoal :: Set Fi -> StateD -> Bool
isGoal goal s = isGoal' goal (getWM s)
isGoal' goal (Nothing,set) | Set.size set /= Set.size goal = False
isGoal' goal (Nothing,set) | set == goal = True
isGoal' goal ((Just x),set) | (Set.insert x set) == goal = True
isGoal' _ _ = False

isVisited prev lev state =
    let result = Set.lookupLE (lev,getWM state) prev
    in case result of
    Just (lev',wm') -> if lev' < lev then False else wm' == getWM state
    _ -> False
    -- and [(i,getWM state) `Set.notMember` prev | i <- [0..lev]]