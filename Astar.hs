

module Astar where
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Function (on)
import Expr.TRS
import Data.List
import Niz
import Control.Monad
import Types
import Proof
import Control.Parallel.Strategies
import Control.Exception
import Control.Concurrent
import Control.Concurrent.MVar
import System.IO
import System.IO.Unsafe
import qualified Data.Map as Map
import Data.Map (Map)
import Data.Time.Clock
import Data.Maybe (fromJust)
import Graph.Astar

children :: MVar ([StateD], [MVar Int])
children = unsafePerformIO (newMVar ([], []))

search = aStarM (ruleApplication axioms rules) stateDist (hDist (getSet axioms)) isGoal (return (Start wm))

-- | Check if a state is a goal state. If so, end the search.
isGoal :: StateD -> IO Bool
isGoal s = return (size (getSet $ getWM s) == 0)
--isGoal s = return $ (length . Set.toList . getSet $ getWM s) > 1
--                    && (head . Set.toList . getSet $ getWM s) == (read "C1⊑C9" :: Fi)

-- | Heuristic distance to the goal.
hDist :: Set Fi -> StateD -> IO Int
hDist _ _ = return 1 -- return . size . getWM $ x
    --let wm = Set.toList . getSet . getWM $ x
    --let wmsize = size wm
    --return $ if any (`Set.member` axioms) wm then wmsize else 2*wmsize

-- | Distance between two neighboring states.
stateDist :: StateD -> StateD -> IO Int
stateDist a _ =
    return 1           -- minimum length of proofs
    -- return $ size a    -- minimum size of proofs

    
-- | Main function that applies all rules to the given state and generates branching states.
-- Used by the Astar search to compute next set of nodes to explore.
ruleApplication :: Int -> Int -> FiSet -> Set RuleD -> Int -> StateD -> IO (Set StateD)
ruleApplication _ _ _ _ _ (PStep wm  _ _ _)  | Set.null (getSet wm)
        = return Set.empty -- don't apply if WM is empty
ruleApplication _ maxlength _ _ _ (PStep _ _ _ pwm)  | size pwm >= maxlength
        = return Set.empty -- don't apply max length reached
ruleApplication maxwm _ axioms rules' level s = do
    (proof,cs) <- takeMVar children
    putMVar children (proof,cs)
    if (notnull proof && level >= length proof)
    then do
        --io . putStrLn $ "Closeing thread. Proof already exists. " ++ show (length proof)
        id <- myThreadId
        killThread id
        return Set.empty
    else do
        let rules = Set.toList rules'
        rset <- applyRule axioms s (head . filter (\r -> ruleName r == "RemoveAxiom") $ rules)
        if size rset > 0 && size (head $ Set.toList rset) < size s
        then return rset
        else do
            sets <- sequence . parMap rpar (applyRule axioms s) $ rules
            let states = Set.toList . Set.unions $ sets
            --smap <- takeMVar previous
            result <- filterM (prune maxwm (getPrevious s)) states
            --mapM (\s -> Map.insert s 1 smap) $ (map getWM states)
            --putMVar previous smap
            -- let newmap = Map.fromList $ zip (map getWM states) (repeat 1)
            --putMVar previous (Map.union smap newmap)
            return $ Set.fromList result
