{-
    Types and Instance Declarations for DLvalidity program
    Author: Abdul Rahim Nizamani
    Created: 2013-10-02
    Updated: 2013-10-02
-}

{-# LANGUAGE MultiParamTypeClasses, FlexibleInstances, OverlappingInstances  #-}

module Types where

import Text.ParserCombinators.ReadP

import Expr.TRS
import Expr.Element
import Expr.Expr
import Expr.Equation
import Data.Char
import Data.Set (Set)
import qualified Data.Set as Set
import Data.List
import Niz

-------------------------------------------------------------------------------
-- Special symbols ------------------------------------------------------------
-------------------------------------------------------------------------------
eq' = "≡"
or' = "∨"
and' = "∧"
gamma' = "Γ"
delta' = "Δ"
fi' = "φ"
not' = "¬"
subset' = "⊑"
forall' = "∀"
exists' = "∃"
top' = "⊤"
bot' = "⊥"

-------------------------------------------------------------------------------
-- Types ----------------------------------------------------------------------
-------------------------------------------------------------------------------

-- | an Atom is the atomic unit of an expression: either a name, or top or bottom
data Atom = Atom String | Top | Bot
            deriving (Eq, Ord) -- Show, Read, Size

-- | operators and quantifiers for Description Logic
data Oper = Neg | And | Or | Forall | Exists
            deriving (Eq, Ord) -- Show, Read, Operator, Size

-- | A concept in Description Logic
type Concept = Expr (Element Oper Atom)

data Substitute = Sub {getSub :: (Concept,Maybe ((Concept,Concept),Bool))}
    deriving (Eq, Ord)

-- | A formula in DL
data Formula a = Fi a | Identical (Equation a) | Subset (Equation a) -- | FBox (Formula a)
        deriving (Eq) -- Show, Read, Size

type Fi = Formula Concept

data FormulaSet a = FiSet {getSet :: Set (Formula a)}
    deriving (Eq, Ord)

type FiSet = FormulaSet Concept
 
-- | Rules for DL contain a condition, a matching formula and a set of rewrite formulas
data RuleD =
    InspectBox |
    Recall |
    Remove |
    Rewrite {ruleName' :: String, condition :: Maybe Fi, matching :: Fi, rewrite :: (FormulaSet Substitute)}
    deriving (Eq, Ord) -- Show, Read

type WM = (Maybe Fi, Set Fi)
type StateD = ProofStep WM RuleD (Maybe Fi)
        -- Eq, Ord, Show, Pattern, Size

proofSize :: StateD -> Int
proofSize (Start wm) = wmSize wm
proofSize (PStep wm _ _ []) = wmSize wm
proofSize (PStep wm _ _ (_:pwm)) = wmSize wm + (sum $ map (wmSize . fst) $ pwm)

wmSize (y,x) = (sum . map size . Set.toList $ x) + (maybe 0 size y)

getFiSet :: FormulaSet Substitute -> FormulaSet Concept
getFiSet (FiSet set) = FiSet $ Set.mapMonotonic (fmap (fst . getSub)) set

-------------------------------------------------------------------------------
-- Instance declarations ------------------------------------------------------
-------------------------------------------------------------------------------

instance Rule RuleD where
    showRule (Rewrite a Nothing c d) = a ++ "= :: " ++ show c ++ " -> " ++ show d
    showRule (Rewrite a b c d) = a ++ "= " ++ show b ++ " :: " ++ show c ++ " -> " ++ show d
    showRule x = show x
    showName = show

instance Size (FormulaSet a) where
    size = size . getSet
    
instance Functor Formula where
    fmap f (Fi a) = Fi (f a)
    fmap f (Identical eq) = Identical $ fmap f eq
    fmap f (Subset eq) = Subset $ fmap f eq
    -- fmap f (FBox fi) = FBox (fmap f fi)

-- Atom -----------------------------------------------------------------------
instance Size Atom where
    size _ = 1

instance Show Atom where
    show (Atom x) = x
    show (Top) = top'
    show (Bot) = bot'

instance Read Atom where
    readsPrec _ s = readP_to_S readAtom (filter (not . isSpace) s)

-- Oper ---------------------------------------------------------------------
instance Size Oper where
    size (Forall) = 1
    size (Exists) = 1
    size _ = 1

instance Show Oper where
    show Neg = not'
    show And = and'
    show Or  = or'
    show (Forall) = forall'
    show (Exists) = exists'

instance Operator Oper Atom where
    arity Neg = 1
    arity And = 2
    arity Or  = 2
    arity (Forall) = 2
    arity (Exists) = 2
    domain (Forall) = []
    domain (Exists) = []
    domain _ = []
instance Show Concept where
    --show e | isBox (root e) && null (forest e) = "[]"
    show e | isBox (root e) = show ((forest e))
    show e | isVar (root e) = show (root e)
    show e | isAtomic (root e) = show (root e)
    show e | isComposite (root e) && notnull (forest e)
        = let op = (\(Composite c) -> c) $ root e
          in case op of
                Neg -> show op ++ show (head (forest e))
                And -> "(" ++ show (head (forest e)) ++ show op ++ show (head (tail (forest e))) ++ ")"
                Or  -> "(" ++ show (head (forest e)) ++ show op ++ show (head (tail (forest e))) ++ ")"
                Forall -> show op ++ show (head (forest e)) ++ "."  ++ show (head (tail (forest e)))
                Exists -> show op ++ show (head (forest e)) ++ "."  ++ show (head (tail (forest e)))
instance Size Concept where
    size e |isBox (root e) = 1
    size e = size (root e) + (sum . map size $ forest e)
-- Fi -------------------------------------------------------------------------
instance Show a => Show (Formula a) where
    show (Fi c) = show c
    show (Identical eq) = show (lhs eq) ++ eq' ++ show (rhs eq)
    show (Subset eq)    = show (lhs eq) ++ subset' ++ show (rhs eq)

--instance Hashable a => Hashable (Formula a) where
--    hashWithSalt = hashUsing getValues

instance Read Fi where
    readsPrec _ s = readP_to_S (readFi) (filter (not . isSpace) s)

instance Ord a => Ord (Formula a) where
    compare (Fi c) (Fi d) = compare c d
    compare (Fi _) _ = LT
    compare _ (Fi _) = GT
    compare (Subset c) (Subset d) = compare c d
    compare (Subset _) _ = LT
    compare _ (Subset _) = GT
    compare (Identical c) (Identical d) = compare c d

instance Size Fi where
    size (Fi c) = size c
    size (Identical a) = size (lhs a) + size (rhs a)
    size (Subset a) = size (lhs a) + size (rhs a)

instance Pattern Fi where
    isPattern (Fi c) = isPattern c
    isPattern (Subset a) = isPattern (lhs a) || isPattern (rhs a)
    isPattern (Identical a) = isPattern (lhs a) || isPattern (rhs a)
    match c d | c == d = True
    match (Fi c) (Fi d) = match c d
    match (Subset a) (Subset b) | a == b = True
    match (Subset a) (Subset b) = match (lhs a) (lhs b) && match (rhs a) (rhs b) && (length (clearBinding bind) == length bind)
        where   bind = nub $ getVarBinding (lhs a) (lhs b) ++ getVarBinding (rhs a) (rhs b)
    match (Identical a) (Identical b) | a == b = True
    match (Identical a) (Identical b) = match (lhs a) (lhs b) && match (rhs a) (rhs b) && (length (clearBinding bind) == length bind)
        where   bind = nub $ getVarBinding (lhs a) (lhs b) ++ getVarBinding (rhs a) (rhs b)
    match _ (Fi a) = isVar (root a)
    match _ _ = False
    getVarBinding (Fi c) (Fi d) = map (\(a,b) -> (a, Fi b)) $ getVarBinding c d
    getVarBinding (Subset a) (Subset b) = map (\(a,b) -> (a, Fi b))
                                          . clearBinding
                                          . nub $ getVarBinding (lhs a) (lhs b) ++ getVarBinding (rhs a) (rhs b)
    getVarBinding (Identical a) (Identical b) = map (\(a,b) -> (a, Fi b))
                                                . clearBinding
                                                . nub $ getVarBinding (lhs a) (lhs b) ++ getVarBinding (rhs a) (rhs b)
    getVarBinding fi (Fi a) | isVar (root a) = [(getIdent (root a), fi)]
    getVarBinding _ _ = []
    substitute (Fi c) (Fi x, Fi y) = null result ? [Fi c] $ result
        where result = map Fi (substitute c (x,y))
    substitute (Subset a) (Fi x, Fi y) = null result ? [Subset a] $ result
        where lh' = substitute (lhs a) (x,y)
              rh' = substitute (rhs a) (x,y)
              lh = null lh' ? [lhs a] $ lh'
              rh = null rh' ? [rhs a] $ rh'
              result = [Subset (equ l r) | l <- lh, r <- rh]
    substitute (Identical a) (Fi x, Fi y) = null result ? [Identical a] $ result
        where lh' = substitute (lhs a) (x,y)
              rh' = substitute (rhs a) (x,y)
              lh = null lh' ? [lhs a] $ lh'
              rh = null rh' ? [rhs a] $ rh'
              result = [Identical (equ l r) | l <- lh, r <- rh ]
    substitute x _ = [x]
    substAll (Fi c) (Fi x, Fi y) = Fi $ substAll c (x,y)
    substAll (Subset a) (Fi x, Fi y) = Subset $ equ (substAll (lhs a) (x,y)) (substAll (rhs a) (x,y))
    substAll (Identical a) (Fi x, Fi y) = Identical $ equ (substAll (lhs a) (x,y)) (substAll (rhs a) (x,y))
    substAll x _ = x
    apply (Fi a) xs | isVar (root a) = case lookup (getIdent (root a)) xs of
        Nothing -> (Fi a)
        Just x  -> (x)
    apply (Fi c) xs = Fi $ apply c [(x,y) | (x,Fi y) <- xs]
    apply (Subset c) xs = Subset $ equ (apply (lhs c) d) (apply (rhs c) d)
                            where d = [(x,y) | (x,Fi y) <- xs]
    apply (Identical c) xs = Identical $ equ (apply (lhs c) d) (apply (rhs c) d)
                            where d = [(x,y) | (x,Fi y) <- xs]

-- FiSet ----------------------------------------------------------------------
instance Show a => Show (FormulaSet a) where
    show (FiSet set) | Set.null set = "{}"
    show (FiSet set) = "{" ++ (concat . intersperse "," . map show $ (Set.toList set)) ++ "}"

instance Read FiSet where
    readsPrec _ s = readP_to_S (readFiSet) (filter (not . isSpace) s)
 
-- Rule -----------------------------------------------------------------------
instance Show RuleD where
    show InspectBox = "InspectBox"
    show Recall = "Recall"
    show Remove = "Remove"
    show (Rewrite name Nothing b c) = name ++ " ::Δ," ++ show b ++ " -> Δ," ++ show c
    show (Rewrite name (Just a) b c) = name ++ show a ++ " ::Δ," ++ show b ++ " -> Δ," ++ show c

instance Read RuleD where
    readsPrec _ s = readP_to_S (readRule) s

-- StateD ---------------------------------------------------------------------
instance Ord StateD where
    compare (Start _) (Start _) = EQ
    compare (Start _) _ = LT
    compare _ (Start _) = GT
    compare x y | getWM x /= getWM y = compare (getWM $ x) (getWM $ y)
    compare x y = compare (getRule x) (getRule y)
                    -- compare (getReward . getRule $ x) (getReward . getRule $ y)
instance Size StateD where
    size x = size' $ getWM x
      where
        size' (Nothing,x) = sum . map size . Set.toList $ x
        size' (Just y,x) = (sum . map size . Set.toList $ x)
                          + size y

instance Show Substitute where
    show (Sub (c,Nothing)) = show c
    show (Sub (c, Just ((a,b),plus))) = show c ++ "[" ++ show a ++ "/" ++ show b ++ "]" ++ (plus ? "+" $ "")

-------------------------------------------------------------------------------
-- Parsers --------------------------------------------------------------------
-------------------------------------------------------------------------------

readTop    = (string top'    <++ string "T") >> return Top
readBot    = (string bot'    <++ string "F") >> return Bot
readNeg    = (string not'    <++ string "~") >> return Neg
readAnd    = (string and'    <++ string "&") >> return And
readOr     = (string or'     <++ string "|") >> return Or
readForall = (string forall' <++ string ">") >> return Forall
readExists = (string exists' <++ string "<") >> return Exists

readAtom, readAtom' :: ReadP Atom
readAtom' = do
    first <- satisfy (\x -> isAlpha x && isUpper x)
    rest <- munch isAlphaNum
    return (Atom (first:rest))
readAtom = (readTop <++ readBot <++ readAtom') >>= return

readConcept :: ReadP (Expr (Element Oper Atom))
readConcept = do
    e <- (readBoxed readConcept' >>= return . makeBox)
         <++ readConcept'
    return e
  where
    readConcept' = readBinary <++ readUnary <++ readAtomic <++ readVar

readBoxed :: ReadP a -> ReadP a
readBoxed p = do
    char '['
    r <-  p
    char ']'
    return $ r
readUnary :: ReadP (Expr (Element Oper Atom))
readUnary = do
    op <- readNeg
    c <- tryQuantified
    return $ makeExpr (Composite op) [c]
readBinary = do
    skipSpaces
    char '('
    c <- tryQuantified
    skipSpaces
    op <- (readAnd +++ readOr)
    skipSpaces
    d <- tryQuantified
    char ')'
    skipSpaces
    return $ makeExpr (Composite op) [c,d]
readAtomic = do
    skipSpaces
    a <- readAtom
    skipSpaces
    return $ makeExpr (Atomic a) []

tryQuantified :: ReadP Concept
tryQuantified = do
    c <- (readBoxed readQConcept >>= return . makeBox)
         <++ readQConcept
         <++ readConcept
    return c

readQConcept :: ReadP Concept
readQConcept = do
    q <- readForall <++ readExists
    r <- readRole
    char '.'
    c <- readConcept
    return (makeExpr (Composite q) [r,c])
readRole :: ReadP Concept
readRole = do
    r <- (((readAtom >>= (\a -> return $ makeExpr (Atomic a) []))) <++ readVar)
    return r
readFi :: ReadP Fi
readFi = do
    f <- readFormula
    return $ fmap (fst . getSub) f
readFormula :: ReadP (Formula Substitute)
readFormula = do
        c <- readSubset <++ readIdentical <++ readFi'             
        return c
readFiSet :: ReadP FiSet
readFiSet = do
    set <- readForSet
    return $ getFiSet set
readForSet :: ReadP (FormulaSet Substitute)
readForSet = do
    skipSpaces
    char '{'
    skipSpaces
    fi <- sepBy (readFormula) (char ',')
    char '}'
    skipSpaces
    return $ FiSet . Set.fromList $ fi
readFi' :: ReadP (Formula Substitute)
readFi' = (readWithSubstitute <++ readWithoutSubstitute) >>= (return . Fi)

readSubset :: ReadP (Formula Substitute)
readSubset = do
    skipSpaces
    x <- (readWithSubstitute <++ readWithoutSubstitute)
    skipSpaces
    string subset' <++ string "<="
    skipSpaces
    y <- (readWithSubstitute <++ readWithoutSubstitute)
    skipSpaces
    return $ Subset (equ x y)
readIdentical :: ReadP (Formula Substitute)
readIdentical = do
    skipSpaces
    x <- (readWithSubstitute <++ readWithoutSubstitute)
    skipSpaces
    string eq' <++ string "=="
    skipSpaces
    y <- (readWithSubstitute <++ readWithoutSubstitute)
    skipSpaces
    return $ Identical (equ x y)


readWithSubstitute, readWithoutSubstitute :: ReadP Substitute
readWithoutSubstitute = tryQuantified >>= (\c -> return (Sub (c, Nothing)))
readWithSubstitute = do
    skipSpaces
    x <- tryQuantified
    skipSpaces
    char '['
    skipSpaces
    y <- tryQuantified
    char '/'
    z <- tryQuantified
    skipSpaces
    b <- readPositive <++ readNeutral
    skipSpaces
    return (Sub (x,Just ((y,z),b)))

readPositive = char ']' >> char '+' >> return True
readNeutral  = char ']' >> return False

readRule :: ReadP RuleD
readRule = do
    skipSpaces
    x <- satisfy (\x -> isAlpha x)
    rest <- munch isAlphaNum
    skipSpaces
    char '='
    skipSpaces
    condition <- readCondition
    skipSpaces
    char 'Δ'
    skipSpaces
    char ','
    skipSpaces
    first <- readFi
    skipSpaces
    string "->"
    skipSpaces
    char 'Δ'
    skipSpaces
    char ','
    skipSpaces
    second <- readForSet
    skipSpaces
    return $ Rewrite (x:rest) condition (first) (second)
--readSubSet :: ReadP Atom -> ReadP Oper -> ReadP (FormulaSet Substitute)
--readSubSet a b = undefined

readCondition :: ReadP (Maybe Fi)
readCondition = 
    (do string "::"
        return Nothing) <++ (do f <- readFi
                                skipSpaces
                                string "::"
                                return (Just f))


