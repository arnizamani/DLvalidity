{-
    Proof functions for DLvalidity program
    Author: Abdul Rahim Nizamani
    Created: 2013-10-02
    Updated: 2013-10-02
-}


module Proof where

import Data.Set (Set)
import qualified Data.Set as Set
import Expr.TRS
import Expr.Ident
import Expr.Expr
import Expr.Element
import Expr.Equation
import Niz
import Data.List
import Types
import Data.Function (on)
import Control.Monad (filterM)
import qualified System.IO.UTF8 as U
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
--import Debug.Trace
--import Control.Concurrent.MVar

unitConcepts = getSet (read "{C1,C2,C3,C4,C5,C6,C7,C8,C9,C10,C11,C12,C13,C14,C15,C16,C17,C18,C19,C20}" :: FiSet)

getValues :: Formula a -> [a]
getValues (Fi x) = [x]
getValues (Subset eq) = [lhs eq, rhs eq]
getValues (Identical eq) = [lhs eq, rhs eq]

unionFiSet :: Ord a => FormulaSet a -> FormulaSet a -> FormulaSet a
unionFiSet (FiSet set1) (FiSet set2) = FiSet (Set.union set1 set2)

intersectFiSet :: Ord a => FormulaSet a -> FormulaSet a -> FormulaSet a
intersectFiSet (FiSet set1) (FiSet set2) = FiSet (Set.intersection set1 set2)

diffFiSet :: Ord a => FormulaSet a -> FormulaSet a -> FormulaSet a
diffFiSet (FiSet set1) (FiSet set2) = FiSet (Set.difference set1 set2)

singleFiSet = FiSet . Set.singleton

ruleName InspectBox = "InspectBox"
ruleName Recall = "Recall"
ruleName Remove = "Remove"
ruleName r@(Rewrite _ _ _ _) = ruleName' r

-- search tree pruning
prune :: Int -> Set WM -> StateD -> IO Bool
prune maxwm smap s = do
    let wm' = fst $ getWM s
    if isNothing wm'
    then return False
    else do
      let wm = fromJust wm'
      return $
        -- size must be within wm limit
        size s <= maxwm
        -- wm must not contain any concept which has double boxes [[ ]]
        && not (any hasDoubleBox . getValues $ wm)
        -- wm must not be among the previously computed nodes
        && not (Set.member (getWM s) smap)
        -- wm must not contain any variable
        && (not . isPattern $ wm)

type MyRule = (RuleD,[([(Ident,Fi)],Maybe Fi)])

-- | a general function for applying patterns to a single Formula in WM
applyRuleOnFi :: Set Fi -> WM -> [(WM,(RuleD,Maybe Fi))] -> MyRule -> IO [StateD]
applyRuleOnFi _ (Nothing,_) _ _ = return []
applyRuleOnFi gamma (Just wm,set) pwm (rule,matches) = do
    let applied = [(r,axiom)
                            | (x,axiom) <- matches,
                              r         <- applyMatch gamma x (matching rule) (rewrite rule) wm,
                              Set.singleton wm /= r]
    -- let newwm = [(e',axiom) | (e,e',axiom) <- applied, e /= e']
    let rewritten = [PStep (Just newwm,newset) rule axiom (((Just newwm,newset),(rule,axiom)):pwm)
                      | (wm',axiom) <- applied,
                        newwm <- Set.toList wm',
                        let newset = Set.union set (Set.delete newwm wm'),
                        isNothing ((Just newwm,newset) `lookup` pwm)
                    ]
    let r2 = [PStep (Nothing,set) rule axiom (((Nothing,set),(rule,axiom)):pwm)
                      | (wm',axiom) <- applied,
                        Set.null wm']
    return $ rewritten ++ r2

{-
-- | a general function for applying patterns to the WM
applyRule :: Set Fi -> FiSet -> [(FiSet,(RuleD,Maybe Fi))] -> MyRule -> IO [StateD]
applyRule _    wm _ _    | Set.null (getSet wm) = return []
applyRule gamma wm pwm (rule,matches) = do
    let result = [(singleFiSet fi,r,axiom)
                            | (x,axiom) <- matches,
                              fi        <- Set.toList (getSet wm),
                              r         <- applyMatch gamma x (matching rule) (rewrite rule) fi]
    let newwm = [((unionFiSet e' (diffFiSet wm e)),axiom) | (e,e',axiom) <- result, e /= e']
    
    let rewritten = [PStep wm' rule axiom ((wm',(rule,axiom)):pwm)
                      | (wm',axiom) <- newwm, isNothing (wm' `lookup` pwm)]
    return rewritten
-}
-- | matches a condition with the axioms and returns variable bindings
-- E.g., for condition c==d, returns bindings of c and d from axioms which match
-- it, i.e, which are of the form c==d
getMatches :: [Fi] -> Maybe Fi -> [ ([(Ident,Fi)],Maybe Fi) ]
getMatches _ Nothing = [([], Nothing)]
getMatches axioms (Just condition) = [(getVarBinding a condition, Just a)
                                        | a <- axioms,
                                          match a condition]

applyMatch :: Set Fi -> [(Ident,Fi)] -> Fi -> (FormulaSet Substitute) -> Fi -> [Set Fi]
-- Remove rule, new fiset is empty
applyMatch gamma bind' fi (FiSet newfi) wm | match wm fi && (Set.null newfi) = 
    let bind = nub $ bind' ++ (getVarBinding wm fi)
        matches = [(match x1 x2 || match x2 x1) | (id1,x1) <- bind, (id2,x2) <- bind, id1==id2]
    in  if notnull matches && and matches
            then [Set.empty]
            else [Set.singleton wm]
applyMatch gamma [] fi newfi wm | match wm fi =
    let bind = getVarBinding wm fi
        result = map (Set.unions . map getSet)
                . transpose
                $ [substitution gamma x bind wm | x <- (Set.toList . getSet $ newfi) ]
    in  if null result then [Set.singleton wm] else result
applyMatch gamma bind' fi newfi wm | match wm fi =
    let bind = nub $ bind' ++ (getVarBinding wm fi)
        clb = clearBinding bind
        b' = [b | b <- bind, not (b `elem` clb)]
        matches = [(match x1 x2 || match x2 x1) | (id1,x1) <- bind, (id2,x2) <- bind, id1==id2]
        result = map (Set.unions . map getSet)
                 . transpose
                 $ [substitution gamma x bind wm | x <- (Set.toList . getSet $ newfi) ]
    in if notnull matches && and matches && notnull result
         then result --trace (output $ " bind: " ++ show bind ++ ", result: " ++ show result) $ result
         else if (notnull b' && sort bind /= sort b')
                then [Set.singleton wm]
                else result
applyMatch _ _ _ _ wm = [Set.singleton wm]

-- | apply substitute, for Substitution and Strengthening rules
-- if the second part is Nothing, then apply normal 'apply' function
-- otherwise, first apply then substitute
substitution :: Set Fi -> Formula Substitute -> [(Ident,Fi)] -> Fi -> [FiSet]
substitution _ f@(Fi (Sub (a,Nothing))) xs wm = [singleFiSet $ apply (Fi a) xs]
substitution _ f@(Subset eq) xs wm | snd (getSub (lhs eq)) == Nothing && snd (getSub (rhs eq)) == Nothing
            =  [singleFiSet $ apply (Subset    (equ (fst (getSub (lhs eq))) (fst (getSub (rhs eq))))) xs]
substitution _ f@(Identical eq) xs wm | snd (getSub (lhs eq)) == Nothing && snd (getSub (rhs eq)) == Nothing
            = [singleFiSet $ apply (Identical (equ (fst (getSub (lhs eq))) (fst (getSub (rhs eq))))) xs]
-- WM is of format (Subset _) or (Identical _)
substitution gamma f@(Fi (Sub (a,Just ((c,d),plus)))) xs wm =
    let substFunc = plus ? substituteFi' Neg $ substitute
        boxed c   = not (c `Set.member` unitConcepts)
                    &&  (c `Set.member` gamma)
                        ? fiBoxed c
                        $ c
        c' = not (isVar (root c)) ? (Fi c) $ lookup' (getIdent (root c)) xs (Fi c)
        d' = not (isVar (root d)) ? (Fi d) $ lookup' (getIdent (root d)) xs (Fi d)
        a' = apply (Fi a) xs
    in not (isPattern c' || isPattern d')
        ?  (let result' = substFunc a' (d',boxed c')
                result = map (singleFiSet) result'
            in result) -- trace (output ("c': " ++ show c' ++ " c:" ++ show c ++ " a:" ++ show a ++ " b:" ++ show b ++ " result: " ++ show result)) result)
        $ let  p = (\(Fi i) -> i) c'
               q = (\(Fi i) -> i) d'
               xs' = [(x,y) | (x, Fi y) <- xs]
               subexp = nub $ subConcepts True wm
               bindings = filter notnull
                            [(nub $ xs' ++ getVarBinding subc q) | subc <- subexp]
               subst' = [((Fi $ apply p bind), (Fi $ apply q bind)) | bind <- bindings]
               subst  = concatMap (\(c,d) -> substFunc a' (d, boxed c)) subst'
               result = map singleFiSet subst
           in result

substitution g f@(Subset eq) xs wm =
    map (singleFiSet) [Subset (equ l' r')
                         | (FiSet l) <- lh,
                           (FiSet r) <- rh,
                           not (Set.null l),
                           not (Set.null r),
                           (Fi l') <- (Set.toList l),
                           (Fi r') <- (Set.toList r)]
    where
        lh = substitution g (Fi (lhs eq)) xs wm
        rh = substitution g (Fi (rhs eq)) xs wm
substitution g f@(Identical eq) xs wm = 
    map (singleFiSet) [Identical (equ l' r')
                         | (FiSet l) <- lh,
                           (FiSet r) <- rh,
                           not (Set.null l),
                           not (Set.null r),
                           (Fi l') <- (Set.toList l),
                           (Fi r') <- (Set.toList r)]
    where
        lh = substitution g (Fi (lhs eq)) xs wm 
        rh = substitution g (Fi (rhs eq)) xs wm

isFiBoxed (Fi c) = isBox (root c)
isFiBoxed (Subset eq) = isBox (root $ lhs eq) || isBox (root $ rhs eq)
isFiBoxed (Identical eq) = isBox (root $ lhs eq) || isBox (root $ rhs eq)

lookup' :: Eq a => a -> [(a,b)] -> b -> b
lookup' a xs b = case lookup a xs of
    Nothing -> b
    Just  x -> x
substituteFi' b (Fi c) (Fi x, Fi y) = map Fi (substitute' c (x,y) b)

-- | Checks if the given formula contains a constant Concept, e.g., C1 or C2
containsConstant :: Fi -> Bool
containsConstant x = any con' (getValues x)
    where
        con' c | isAtomic (root c) = isAtom (getAtomic (root c))
        con' c | isComposite (root c) = any con' (forest c)
        con' c = False
        isAtom (Atom _) = True
        isAtom _ = False
subConcepts :: Bool -> Fi -> [Concept]
subConcepts t exp = nub $ case exp of
            (Fi c) -> subConcepts' t c
            Identical a -> subConcepts' t (lhs a) ++ subConcepts' t (rhs a)
            Subset a -> subConcepts' t (lhs a) ++ subConcepts' t (rhs a)

subConcepts' :: Bool -> Concept -> [Concept]
subConcepts' t c | isComposite (root c) && getComposite (root c) == Forall 
        = c : concatMap (subConcepts' t) (tail $ forest c)
subConcepts' t c | isComposite (root c) && getComposite (root c) == Exists
        = c : concatMap (subConcepts' t) (tail $ forest c)
subConcepts' t c | isComposite (root c) = c : concatMap (subConcepts' t) (forest c)
subConcepts' t c | isBox (root c) = c : subConcepts' t (head (forest c))
subConcepts' t c | t = [c]
subConcepts' _ _ = []

fiBoxed :: Fi -> Fi
fiBoxed (Fi c) = Fi (makeBox c)
fiBoxed (Subset eq) = Subset $ fmap makeBox eq
fiBoxed (Identical eq) = Identical $ fmap makeBox eq

containsBox :: Fi -> Bool
containsBox (Fi c) = hasBox c
containsBox (Subset c) = hasBox (lhs c) || hasBox (rhs c)
containsBox (Identical c) = hasBox (lhs c) || hasBox (rhs c)

isFiAtomic (Fi c) = isAtomic (root c) && null (forest c)
isFiAtomic _ = False

applyRules :: Int
              -> Int
              -> Set Fi
              -> MyRule
              -> [MyRule]
              -> Int
              -> StateD
              -> IO [StateD]
applyRules _ depth _ _ _ _ (PStep _ _ _ pwm)  | size pwm >= depth
        = return [] -- don't apply if max depth reached
applyRules width _ gamma rem matches level s | isNothing (fst $ getWM s) && Set.null (snd $ getWM s)
        = return [] -- nothing to apply on, WM is empty
applyRules width _ gamma rem matches level s | isNothing (fst $ getWM s) = do
        let ((_,set),pwm) = (getWM s, getPrevious s)
        let newwm = [(Just w,Set.delete w set) | w <- Set.toList set]
        states' <- sequence [applyRuleOnFi gamma wm pwm r | r <- (rem:matches),wm <- newwm]
        let states = nubBy ((==) `on` (getWM)) $ concat states'
        let result1 = [PStep (Just wm',set') a b c
                             | s'@(PStep w@(Just wm',set') a b c) <- states,
                               (not . isPattern $ wm'),
                               wmSize w <= width,
                               not (any hasDoubleBox . getValues $ wm')
                         ]
        let result2 = [PStep (Nothing,set') a b c | (PStep (Nothing,set') a b c) <- states]
            --let print = "\nLevel: " ++ show level ++ ", " ++ show s
            --               ++ ("\n" ++ (unlines $ map show result))
            --U.appendFile "temp.txt" print
        return $ result1 ++ result2

applyRules width _ gamma rem matches level s = do
        let (wm,pwm) = (getWM s, getPrevious s)
        rset <- applyRuleOnFi gamma wm pwm rem
        if size rset > 0 && size (head rset) < size s
          then return rset
          else do
            states' <- mapM (applyRuleOnFi gamma wm pwm) $ (rem:matches)
            let states = nubBy ((==) `on` (getWM)) $ concat states'
            let result1 = [PStep (Just wm',set') a b c
                             | s'@(PStep w@(Just wm',set') a b c) <- states,
                               (not . isPattern $ wm'),
                               wmSize w <= width,
                               not (any hasDoubleBox . getValues $ wm')
                         ]
            let result2 = [PStep (Nothing,set') a b c | (PStep (Nothing,set') a b c) <- states]
            --let print = "\nLevel: " ++ show level ++ ", " ++ show s
            --               ++ ("\n" ++ (unlines $ map show result))
            --U.appendFile "temp.txt" print
            return $ result1 ++ result2
--applyRules _ _ _ _ _ _ _ = return []


{-
applyRules width depth gamma axioms rules rem matches search level s = do
    let (wmm,pwm) = (getWM s, getPrevious s)
    if Set.null (getSet wmm)
    then return []
    else do
    if Set.size (getSet wmm) == 1
    then do
        let wm = head . Set.toList $ getSet wmm
        rset <- applyRuleOnFi gamma wm pwm rem
        if size rset > 0 && size (head rset) < size s
        then return rset
        else do
        states' <- mapM (applyRuleOnFi gamma wm pwm) $ (rem:matches)
        let states = nubBy ((==) `on` (getWM)) $ concat states'
        let result = [s' | s' <- states,
                           let wm' = Set.toList (getSet (getWM s')),
                           (not . any isPattern $ wm'),
                           size s' <= width,
                           isNothing (lookup (getWM s') pwm),
                           not (any hasDoubleBox . concatMap getValues $ wm')
                     ]
        return result
    else do
        let wm = Set.toList $ getSet wmm
        
        let gamma' = Set.toList gamma
        let newdepth = (depth - size pwm)
        proofs <- sequence [do
                               result <- search newwidth newdepth gamma' axioms rules (singleFiSet w)
                               if isNothing result
                               then return Nothing
                               else return $ Just (fromJust result,w)
                                    | w <- wm,
                                      let newwidth = (width - size (wm \\ [w]))]
        if any isNothing proofs
        then return []
        else do
        let states = [(getSet wm,r,d,pwm,wmstart) | (Just ((PStep wm r d pwm),wmstart)) <- proofs]
        let wms = [wm | (wm,_,_,_,_) <- states]
        let result = foldl (\(wm1,pwm1) (w,r,d,pwm2,wm2) ->
                              (wm1 \\ [wm2], [(FiSet (Set.fromList ((wm1 \\ [wm2]) ++ Set.toList w)),(r,d))] ++ pwm1 ++ pwm2)
                           )
                           (wm,pwm)
                           states
        let removeaxiom = head $ filter (\r -> ruleName r == "RemoveAxiom") rules
        return $ [PStep (FiSet Set.empty) removeaxiom Nothing (snd result)]
-}


{-
applyRules width _ gamma _ _ rem matches _ level s = do
        let (wm,pwm) = (getWM s, getPrevious s)
        rset <- applyRule gamma wm pwm rem
        if size rset > 0 && size (head rset) < size s
          then return rset
          else do
            states' <- mapM (applyRule gamma wm pwm) $ (rem:matches)
            let states = nubBy ((==) `on` (getWM)) $ concat states'
            let result = [s' | s' <- states,
                               let wm' = Set.toList (getSet (getWM s')),
                               (not . any isPattern $ wm'),
                               size s' <= width,
                               -- isNothing (lookup (getWM s') pwm),
                               not (any hasDoubleBox . concatMap getValues $ wm')
                         ]
            --let print = "\nLevel: " ++ show level ++ ", " ++ show s
            --               ++ ("\n" ++ (unlines $ map show result))
            --U.appendFile "temp.txt" print
            return result
-}

 