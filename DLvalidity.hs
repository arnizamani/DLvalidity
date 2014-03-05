-- author: Abdul Rahim Nizamani (c) 2013
-- ITIT, GU, Gothenburg, Sweden
-- Last update: 2013-09-04

{-# LANGUAGE GADTs, MultiParamTypeClasses, TypeSynonymInstances, FlexibleInstances, OverlappingInstances  #-}
 
-- Description Logic, validity prover
module Main where
import Expr.Ident
import Expr.Element
import Expr.Equation as E
import Expr.Expr
import Expr.TRS
import Data.Char
import Data.List
import Data.Set (Set)
import System.Environment (getArgs,getProgName)
import qualified Data.Set as Set
import Data.Function (on)
import Control.Arrow ((&&&),(***))
import qualified System.IO.UTF8 as U
import Data.Graph.AStar
import Data.Maybe
import Control.Parallel
import Control.Parallel.Strategies
import Control.Concurrent
import Control.Monad
import Control.Monad.Trans.Class
import Control.Monad.Trans.State.Strict as ST
import Data.Tree
import Data.Map (Map)
import qualified Data.Map as Map
import Control.Exception
import qualified Control.Monad.Parallel as P
import System.IO.Unsafe (unsafePerformIO)
import Debug.Trace
import Niz
import Types
import Proof
--import Iddfs
import Bfs
import Data.Time.Clock
-- Main goal
test  = read "{[C1]⊑[C2]}" :: FiSet
empty = read "{}" :: FiSet
-------------------------------------------------------------------------------
-- Parameters -----------------------------------------------------------------
-------------------------------------------------------------------------------

axiomFile = "DL.axioms"
ruleFile = "DL.rules"

-------------------------------------------------------------------------------
-- Proof Search ---------------------------------------------------------------
-------------------------------------------------------------------------------

main :: IO ()
main = do
    args <- getArgs
    pname <- getProgName
    case args of
      (a:b:c:d:x:y:_) -> do
        let fiset = (reads x :: [(FiSet,String)])
        if null fiset
        then do
        putStrLn $ "Cannot read the start."
        return ()
        else do
        let goal = (reads y :: [(FiSet,String)])
        if null goal
        then do
        putStrLn $ "Cannot read the goal."
        return ()
        else do
        solve a b (read c :: Int) (read d :: Int) (fst . head $ fiset) (fst . head $ goal)
      (a:b:c:d:x:_) -> do
        let fiset = (reads x :: [(FiSet,String)])
        if null fiset
        then do
        putStrLn $ "Cannot read the start."
        return ()
        else do
        solve a b (read c :: Int) (read d :: Int) (fst . head $ fiset) empty
      (a:b:c:d:_) -> solve a b (read c :: Int) (read d :: Int) test empty
      _ -> do
            putStrLn $ "Wrong arguments."
            putStrLn $ pname ++ " problem-file output-file Width Depth [{start} {goal}]"
            putStrLn $ " where, {start} can be e.g. {C1<=C2}"
            putStrLn $ "    and {goal} can be e.g. {}"
-- | Main function to solve a problem in DL validity prover.
-- Takes a set of formulas and a filename for printing the result.
solve :: FilePath -> FilePath -> Int -> Int -> FiSet -> FiSet -> IO ()
solve gammafile file maxwm maxlength wm goal = do
    start <- getCurrentTime
    (axioms,gamma) <- readAxioms gammafile axiomFile
    if null gamma || null axioms
    then return ()
    else do
    rules <- readRules ruleFile
    (result,visited) <- search maxwm maxlength gamma axioms rules wm goal
    let solution = if isJust result
                      then printProof (Start (Nothing,getSet wm)) (fromJust result)
                      else ["No proof found."]
    end <- getCurrentTime
    let duration = show (diffUTCTime end start)
    let printed =  (("Problem: " ++ show wm):"":[])
                   -- ++ ("Given: ":(map show (Set.toList $ getSet gamma))) ++ [""]
                   ++ ["WM: " ++ show maxwm]
                   ++ ["MaxLength: " ++ show maxlength]
                   ++ ["Search time: " ++ duration]
                   ++ ["Nodes explored: " ++ show visited]
                   ++ ( "\nSolution: ":solution )
                   ++ ( (""):("List of rules: "):(map show rules) )
                   ++ ( (""):("List of axioms: "):(map show (sort (gamma++axioms))) )
    U.writeFile file $ unlines printed
    if isJust result then putStrLn "Solved." else putStrLn "No solution found."

-- | Read rules from the rule file.
readRules :: FilePath -> IO [RuleD]
readRules file = do
    text <- U.readFile file
    let lines' = filter (\x -> notnull x && take 1 x /= "#") . map strip . lines $ text
    let rules = map fst . map head . filter notnull $ map (\x -> reads x :: [(RuleD,String)]) lines'
    if length rules /= length lines'
    then do
        putStrLn $ "Could not parse file " ++ file
        return $ []
    else do
    putStrLn $ "Rules: " ++ show (length rules)
    return $ rules -- Set.fromList rules

-- | Read axioms and return the set of all axioms.
readAxioms :: FilePath -> FilePath -> IO ([Fi],[Fi])
readAxioms gammaFile axiomFile = do
    axiomText <- U.readFile axiomFile
    gammaText <- U.readFile gammaFile
    
    let axiomLines = filter (\x -> notnull x && take 1 x /= "#") . map (filter (not . isSpace)) . lines $ axiomText
    let gammaLines = filter (\x -> notnull x && take 1 x /= "#") . map (filter (not . isSpace)) . lines $ gammaText
    
    let axioms1' = map (\x -> reads x :: [(Fi,String)]) axiomLines
    let axioms1 = map fst . map head . filter notnull $ axioms1'
    
    if length axioms1 /= length axiomLines
    then do
        putStrLn $ "Could not parse file " ++ axiomFile
        let x = map snd . filter (null . fst) $ zip axioms1' axiomLines
        putStrLn $ show x
        return ([],[])
    else do
    let axioms2' = map (\x -> reads x :: [(Fi,String)]) gammaLines
    let axiomsGamma = map fst . map head . filter notnull $ axioms2'
    if length axiomsGamma /= length gammaLines
    then do
        putStrLn $ "Could not parse file " ++ gammaFile
        let x = map snd . filter (null . fst) $ zip axioms2' gammaLines
        putStrLn $ show x
        return ([],[])
    else do
    let newConcepts = map (\(Fi t) -> t)
                      . concatMap Set.toList . map getSet
                      . map (\x -> (read ("{A" ++ show x ++ "}") :: FiSet))
                      $ [1..]
    let gammaSubset    = [eq | e@(Subset eq)    <- axiomsGamma, isAtomic (root (lhs eq))]
    let gammaIdentical = [eq | e@(Identical eq) <- axiomsGamma, isAtomic (root (lhs eq))]
    
    let newgamma = map (\(e,a) ->
                           Identical
                             (equ
                                (lhs e)
                                (makeExpr (Composite And)
                                          [a,
                                           (isAtomic (root (rhs e))) ? rhs e $ makeBox (rhs e)])))
                       (zip gammaSubset newConcepts)
    -- make boxed version of axioms in Gamma
    let gammaBoxed = [Identical (equ (lhs eq) (makeBox (rhs eq)))
                            | e@(Identical eq) <- axiomsGamma,
                              not (isAtomic (root (rhs eq)))]
                     ++
                     [Subset (equ (lhs eq) (makeBox (rhs eq)))
                            | e@(Subset eq) <- axiomsGamma,
                              not (isAtomic (root (rhs eq)))]
                     
    let new1 = concat [ [
                         Subset eq,
                         Subset (equ (rhs eq) (lhs eq)),
                         Identical (equ (rhs eq) (lhs eq))]
                             | e@(Identical eq)  <- axioms1,
                               not (isBox . root $ lhs eq),
                               not (isBox . root $ rhs eq)]
                
    
    let new2 = concat [ [
                         Subset eq,
                         Subset (equ (rhs eq) (lhs eq)),
                         Identical (equ (rhs eq) (lhs eq))]
                             | e@(Identical eq)  <- axiomsGamma,
                               not (isBox . root $ lhs eq),
                               not (isBox . root $ rhs eq)]
    
    
    let resultAxioms = nub $ (axioms1 ++ new1 ++ newgamma)
    let resultGamma = nub $ (axiomsGamma ++ new2)
    putStrLn $ "Axioms: " ++ show (length resultAxioms)
    putStrLn $ "Gamma:  " ++ show (length resultGamma)
    return $ (resultAxioms,resultGamma)

-------------------------------------------------------------------------------
-- Helper functions -----------------------------------------------------------
-------------------------------------------------------------------------------


mapFi :: Fi -> (Concept -> Concept) -> Fi
mapFi (Fi c) func = Fi (func c)
mapFi (Subset c) func = Subset $ equ (func (lhs c)) (func (rhs c))
mapFi (Identical c) func = Identical $ equ (func (lhs c)) (func (rhs c))

isConcept :: Fi -> Bool
isConcept (Fi _) = True
isConcept _ = False

isIdentical :: Fi -> Bool
isIdentical (Identical _) = True
isIdentical _ = False

isSubset :: Fi -> Bool
isSubset (Subset _) = True
isSubset _ = False

filength :: Fi -> Int
filength (Fi c) = size c
filength (Identical e) = size e
filength (Subset e) = size e

-- | Only used for testing the parsing of rule and axiom files
readwrite :: FilePath -> FilePath -> IO ()
readwrite file newfile = do
    text1 <- U.readFile file
    let lines1 = filter (\x -> head x /= '#') . filter (not . null) . map strip . lines $ text1
    let result1 = map (\x -> read x :: Fi) $ lines1
    text2 <- U.readFile newfile
    let lines2 = filter (\x -> head x /= '#') . filter (not . null) . map strip . lines $ text2
    let result2 = map (\x -> read x :: Fi) $ lines2    
    putStrLn $show $ result1 == result2

getLeft (Fi c) = c
getLeft (Identical eq) = lhs eq
getLeft (Subset eq) = lhs eq
getRight (Fi c) = c
getRight (Identical eq) = rhs eq
getRight (Subset eq) = rhs eq

-- pretty printing of proof steps
printProof :: StateD -> StateD -> [String]
--printProof _ state | null (getPrevious state) = []
printProof (Start x) (PStep a b c xs)
            = line:heading:line:(" " ++ showWM x):(concatMap printStep nodes)
                    ++ [space ln, "Proof Length: " ++ show plength, "Proof size: " ++ show psize,line]
  where
    wm = max (max (maxWm nodes) 5) (size (Set.toList (snd x)))
    dm = max (maxDm nodes) 4
    pm = max (maxPm nodes) 6
    ln = wm + dm + pm + 8
    line = take ln $ repeat '='
    space i = take i $ repeat ' '
    heading = " WM " ++ space (wm-3) ++ " |  DM " ++ space (dm-4) ++ " |  Rule " ++ space (pm-5)
    printStep (a,(b,c)) =  [space wm ++ "  | "
                                 ++ (maybe "" show c) ++ space (dm - (length (maybe "" show c))) ++ " | "
                                 ++ ruleName b ++ space (pm - length (show $ ruleName b))]
                          
                          ++ [" " ++ showWM a]
    plength = length nodes -- proof length
    psize = sum $ map (\((x,wm),_) -> (sum . map size . Set.toList $ wm) + (maybe 0 size x)) nodes
    nodes = xs ++ [(a,(b,c))]

showWM :: WM -> String
showWM (Nothing,x) = show (FiSet x)
showWM (Just y,x) = show . FiSet $ Set.insert y x
    
maxWm :: [(WM,(RuleD,Maybe Fi))] -> Int
maxWm [] = 0
maxWm states = maximum $ map (\(wm,_) -> length . showWM $ wm) states

maxDm :: [(WM,(RuleD,Maybe Fi))] -> Int
maxDm [] = 0
maxDm states = maximum $ map (\(a,(b,c)) -> maybe 0 (length . show) $ c) states

maxPm :: [(WM,(RuleD,Maybe Fi))] -> Int
maxPm [] = 0
maxPm states = maximum $ map (\(_,(rule,_)) -> length . ruleName $ rule) states

-- convert strings for output on the screen (convert logic characters into ascii symbols)
-- helpful for printing out intermediate results using trace function
output :: String -> String
output "" = ""
output ('⊑':xs) = " <= " ++ output xs
output ('≡':xs) = " == " ++ output xs
output ('∃':xs) = "<" ++ output xs
output ('∀':xs) = ">" ++ output xs
output ('∧':xs) = "&" ++ output xs
output ('∨':xs) = "|" ++ output xs
output ('¬':xs) = "-" ++ output xs
output ('⊤':xs) = "T" ++ output xs
output ('⊥':xs) = "F" ++ output xs
output (x:xs) = x:output xs

