{-
    Iterative deepening depth-first search, concurrent threads
    Author: Abdul Rahim Nizamani
    Created: 2013-10-02
    Updated: 2013-10-02
-}

module Iddfs where

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

children :: MVar ([StateD], [MVar Int])
children = unsafePerformIO (newMVar ([], []))

waitForChildren :: IO ()
waitForChildren = do
      (proof,cs) <- takeMVar children
      case cs of
        []   -> do
            putMVar children (proof,cs)
            return ()
        m:ms -> do
            list  <- mapM (\x -> do result <- tryTakeMVar x
                                    case result of
                                      Nothing -> return (Left x)
                                      Just i  -> return (Right i))   (m:ms)
            let ms' = [x | (Left x) <- list]
            if (length ms' < length (m:ms))
            then do
                putMVar children (proof,ms')
                putStrLn $ "Remaining threads: " ++ show (length ms')
                waitForChildren
            else do
                putMVar children (proof,(m:ms))
                waitForChildren

forkChild :: IO () -> IO ThreadId
forkChild io = do
        mvar <- newEmptyMVar
        (proof,childs) <- takeMVar children
        putMVar children (proof,(mvar:childs))
        forkFinally' io (endIO mvar)
    where endIO m (Left e) = do putMVar m (-1)
          endIO m (Right _) = putMVar m 1
forkFinally' :: IO a -> (Either SomeException a -> IO ()) -> IO ThreadId
forkFinally' action and_then =
  mask $ \restore ->
    forkIO $ try (restore action) >>= and_then

-- | Run proof search in concurrent threads
search :: Int -> Int -> [Fi] -> [Fi] -> [RuleD] -> FiSet -> Int -> IO [StateD]
search width depth gamma axioms' rules wm mxlength = do
    let axioms = gamma ++ axioms'
    let gamma' = Set.fromList $ concatMap getValues gamma
    let rem = head . filter (\r -> ruleName r == "RemoveAxiom") $ rules
    let rules' = filter (\r -> ruleName r /= "RemoveAxiom") $ rules
    let rem' = (rem,getMatches axioms (condition rem))
    let matches = [(rule,getMatches axioms (condition rule)) | rule <- rules']
    nodes' <- applyRules width depth gamma' rem' matches 1 (Start wm)
    let nodes = nubBy ((==) `on` (getWM)) $ nodes'
    let result = dropWhile ((> 0) . size) nodes
    if notnull result
      then return $ (head result):[]
      else do
        let processes = map (\(n,id) ->
                                iddfsPar (applyRules width depth gamma' rem' matches) (n:[]) id mxlength 2)
                            $ zip nodes [1..]
        putStrLn $ "Starting " ++ show (length processes) ++ " threads."
        threadids <- mapM forkChild processes
        waitForChildren
        (result,cs) <- takeMVar children
        putMVar children (result,cs)
        return result

iddfsPar :: (Int -> StateD -> IO [StateD])
             -> [StateD]
             -> Int -- Thread number
             -> Int -- max length of proof
             -> Int -- current max level
             -> IO ()
iddfsPar expand start _ maxlength maxlevel | maxlevel > maxlength = return ()
iddfsPar expand start threadid maxlength maxlevel = do
    --(result,cs) <- takeMVar children
    --putMVar children (result,cs)
    --if notnull result
    --then return ()
    --else do
    putStrLn $ "Thread no: " ++ show threadid ++ " searching up to level " ++ show maxlevel
    dfsInThread expand [start] maxlevel
    iddfsPar expand start threadid maxlength (maxlevel + 1)

dfsInThread :: (Int -> StateD -> IO [StateD])
             -> [[StateD]]
             -> Int -- max level
             -> IO ()
dfsInThread expand [] maxlength = return ()
dfsInThread expand tree maxlength = do
    (result,cs) <- takeMVar children
    putMVar children (result,cs)
    if notnull result
    then return ()
    else do
    let path = head tree -- path from start to current node
    if length path >= maxlength
    then dfsInThread expand (tail tree) maxlength
    else do
    let node = head path
    nodes <- expand maxlength node
    -- let nodes = Set.toList nodes'
    if null nodes
    then dfsInThread expand (tail tree) maxlength
    else do
      let result = dropWhile (not . Set.null . getSet . getWM) nodes
      if notnull result
      then do  -- found the goal
        putStrLn $ "Goal found."
        let newproof = (head result) : path
        (proof,cs) <- takeMVar children
        (null proof || length proof > length newproof)
           ? do putMVar children (reverse newproof,cs)
           $ do putMVar children (proof   ,cs)
        return ()
      else do
        let newpaths = map (\n -> n:path) nodes
        dfsInThread expand (newpaths ++ tail tree) maxlength

