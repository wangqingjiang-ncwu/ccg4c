-- Copyright (c) 2019-2023 China University of Water Resources and Electric Power.
-- All rights reserved.

-- This module includes types and functions about Combinatory Logic.
module CL (
    Term(..),    -- Term and its all Constructors
    nilTerm,     -- Nil term
    TermType,    -- Term type
    isNilTerm,   -- Term -> Bool
    isPrimTerm,  -- Term -> Bool
    isCompoundTerm,   -- Term -> Bool
    isConstTerm,      -- Term -> Bool
    isVarTerm,        -- Term -> Bool
    isJuxTerm,        -- Term -> Bool
    fstTerm,     -- Term -> Maybe Term
    sndTerm,     -- Term -> Maybe Term
    subTermOfTerm,    -- Term -> [Term]
    fvOfTerm,    -- Term -> [Term]
    app,         -- Term -> Term -> Term
    CombAxiom,   -- Term -> Term
    combAxiom,   -- [CombAxiom]
    aAxiom,      -- Term -> Term
    sAxiom,      -- Term -> Term
    kAxiom,      -- Term -> Term
    iAxiom,      -- Term -> Term
    bAxiom,      -- Term -> Term
    tAxiom,      -- Term -> Term
    cAxiom,      -- Term -> Term
    wAxiom,      -- Term -> Term
    mAxiom,      -- Term -> Term
    yAxiom,      -- Term -> Term
    jAxiom,      -- Term -> Term
    b'Axiom,     -- Term -> Term
    vAxiom,      -- Term -> Term
    s'Axiom,     -- Term -> Term
    rAxiom,      -- Term -> Term
    termSeq2Term,     -- [Term] -> Term
    getTermFromStr,   -- String -> Term
    sortTerms,   -- [Term] -> [Term]
    subTermReduct,    -- Term -> Term
    reduct,      -- Int - > Term -> Term
  ) where

import Utils

{- Terms are divided into const, variable and juxtapositioned ones.
 -}
data Term = ConstTerm String | VarTerm String | JuxTerm Term Term deriving (Eq)

{- Nil term is needed sometimes, and let it be ConstTerm "".
 -}
nilTerm :: Term
nilTerm = ConstTerm ""

{- Term type may be primitive or compound.
 -}
data TermType = PrimTerm | CompoundTerm deriving (Eq, Show)

{- A term is represented by tree structure.
 - Terms with type PrimTerm and not being nil term are leaves.
 - Terms with type CompoundTerm are intermediate nodes.
 - A nilTerm denotes a nil tree.
 -}

isNilTerm :: Term -> Bool
isNilTerm (ConstTerm "") = True
isNilTerm _ = False

isPrimTerm :: Term -> Bool
isPrimTerm (ConstTerm _) = True
isPrimTerm (VarTerm _) = True
isPrimTerm _ = False

isCompoundTerm :: Term -> Bool
isCompoundTerm (ConstTerm _) = False
isCompoundTerm (VarTerm _) = False
isCompoundTerm _ = True

isConstTerm :: Term -> Bool
isConstTerm (ConstTerm _) = True
isConstTerm (VarTerm _) = False
isConstTerm (JuxTerm _ _) = False

isVarTerm :: Term -> Bool
isVarTerm (ConstTerm _) = False
isVarTerm (VarTerm _) = True
isVarTerm (JuxTerm _ _) = False

isJuxTerm :: Term -> Bool
isJuxTerm (ConstTerm _) = False
isJuxTerm (VarTerm _) = False
isJuxTerm (JuxTerm _ _) = True

-- For juxtapositioned terms, fstTerm return the first term, namely, functional term.
fstTerm :: Term -> Maybe Term
fstTerm (ConstTerm _) = Nothing
fstTerm (VarTerm _) = Nothing
fstTerm (JuxTerm a _) = Just a

-- For juxtapositioned terms, sndTerm return the second term, namely, parameter term.
sndTerm :: Term -> Maybe Term
sndTerm (ConstTerm _) = Nothing
sndTerm (VarTerm _) = Nothing
sndTerm (JuxTerm _ a) = Just a

{- Subterms of a term are recursively defined as follows.
 - (s1) M is a subterm of M;
 - (s2)	if M is a subterm of N or of P, then M is a subterm of NP.
 -}
subTermOfTerm :: Term -> [Term]
subTermOfTerm (ConstTerm t) = [ConstTerm t]
subTermOfTerm (VarTerm t) = [VarTerm t]
subTermOfTerm (JuxTerm a b) = [JuxTerm a b] ++ (subTermOfTerm a) ++ (subTermOfTerm b)

{- x is a free variable of M iff x is a subterm of M.
 -}
fvOfTerm :: Term -> [Term]
fvOfTerm t = [x| x <- subTermOfTerm t, isVarTerm x]

-- Define relation Ord between two Terms such that two categories can be compared.
instance Ord Term where
    ConstTerm a < ConstTerm b = a < b
    ConstTerm _ < VarTerm _ = True
    ConstTerm _ < JuxTerm _ _ = True
    VarTerm _ < ConstTerm _ = False
    VarTerm a < VarTerm b = a < b
    VarTerm _ < JuxTerm _ _ = True
    JuxTerm _ _ < ConstTerm _ = False
    JuxTerm _ _ < VarTerm _ = False
    JuxTerm a b < JuxTerm c d =  a < c || a == c && b < d
    ConstTerm a <= ConstTerm b = a <= b
    ConstTerm _ <= VarTerm _ = True
    ConstTerm _ <= JuxTerm _ _ = True
    VarTerm _ <= ConstTerm _ = False
    VarTerm a <= VarTerm b = a <= b
    VarTerm _ <= JuxTerm _ _ = True
    JuxTerm _ _ <= ConstTerm _ = False
    JuxTerm _ _ <= VarTerm _ = False
    JuxTerm a b <= JuxTerm c d =  a < c || a == c && b <= d

-- Define how a term shows.
instance Show Term where
    show (ConstTerm a) = a
    show (VarTerm a) = a
    show (JuxTerm a b) = "(" ++ show a ++ " " ++ show b ++ ")"

{- The above definition conceals the binary operation that conjoins the two terms M and N.
 - This operation is called application, and it is often denoted by juxtaposition, that is,
 - by placing its two arguments next to each other as in (M N).
 -}
app :: Term -> Term -> Term
app a b = JuxTerm a b

type CombAxiom = Term -> Term
combAxiom :: [CombAxiom]
combAxiom = [aAxiom, sAxiom, kAxiom, iAxiom, bAxiom, tAxiom, cAxiom, wAxiom, mAxiom, yAxiom, jAxiom, b'Axiom, vAxiom, s'Axiom, rAxiom]

{- The basic and usual combinators
 - Axy => xy
 - Sxyz => xz(yz)      Kxy => x         Ix => x
 - Bxyz => x(yz)       Txy => yx        Cxyz => xzy
 - Wxy => xyy          Mx => xx         Yx => x(Yx)
 - Jxyzv => xy(xvz)    B'xyz => y(xz)   Vxyz => zxy
 - S'xyz => yz(xz)     Rxyz => yzx
 -}

{- Axioms of some well-known combinators
 -}
aAxiom :: Term -> Term
aAxiom (JuxTerm (JuxTerm (ConstTerm "A") x) y) = app x y
aAxiom _ = nilTerm

sAxiom :: Term -> Term
sAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") x) y) z) = JuxTerm (JuxTerm x z) (JuxTerm y z)
sAxiom _ = nilTerm

kAxiom :: Term -> Term
kAxiom (JuxTerm (JuxTerm (ConstTerm "K") x) _) = x
kAxiom _ = nilTerm

iAxiom :: Term -> Term
iAxiom (JuxTerm (ConstTerm "I") x) = x
iAxiom _ = nilTerm

bAxiom :: Term -> Term
bAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B") x) y) z) = JuxTerm x (JuxTerm y z)
bAxiom _ = nilTerm

tAxiom :: Term -> Term
tAxiom (JuxTerm (JuxTerm (ConstTerm "T") x) y) = JuxTerm y x
tAxiom _ = nilTerm

cAxiom :: Term -> Term
cAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "C") x) y) z) = JuxTerm x (JuxTerm z y)
cAxiom _ = nilTerm

wAxiom :: Term -> Term
wAxiom (JuxTerm (JuxTerm (ConstTerm "W") x) y) = JuxTerm (JuxTerm x y) y
wAxiom _ = nilTerm

mAxiom :: Term -> Term
mAxiom (JuxTerm (ConstTerm "M") x) = JuxTerm x x
mAxiom _ = nilTerm

yAxiom :: Term -> Term
yAxiom (JuxTerm (ConstTerm "Y") x) = JuxTerm x (JuxTerm (ConstTerm "Y") x)
yAxiom _ = nilTerm

jAxiom :: Term -> Term
jAxiom (JuxTerm (JuxTerm (JuxTerm (JuxTerm (ConstTerm "J") x) y) z) v)
    = JuxTerm (JuxTerm x y) (JuxTerm (JuxTerm x v) z)
jAxiom _ = nilTerm

b'Axiom :: Term -> Term
b'Axiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B'") x) y) z) = JuxTerm y (JuxTerm x z)
b'Axiom _ = nilTerm

vAxiom :: Term -> Term
vAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "V") x) y) z) = JuxTerm z (JuxTerm x y)
vAxiom _ = nilTerm

s'Axiom :: Term -> Term
s'Axiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S'") x) y) z) = JuxTerm (JuxTerm y z) (JuxTerm x z)
s'Axiom _ = nilTerm

rAxiom :: Term -> Term
rAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "R") x) y) z) = JuxTerm y (JuxTerm z x)
rAxiom _ = nilTerm

-- Get a term from a sequence of terms. The sequence is considered as left combination priority.
termSeq2Term :: [Term] -> Term
termSeq2Term [] = nilTerm
termSeq2Term [x] = x
termSeq2Term xs = app (termSeq2Term (init xs)) (last xs)

{- Suppose the well-formated string of a term is strict, namely not including any redundant space character.
 - A null string is well-formatted;
 - A string satisfies the following conditions is well-formatted: Starts with not '('
 - and contain no space character.
 - A string satisfies the following conditions is well-formatted: Starts with '(', ends with ')',
 - and contains two juxtapositioned string which are well-formatted and seperated by one space character;
 - Other strings except the above are not well-formatted.
 -}
getTermFromStr :: String -> Term
getTermFromStr "" = nilTerm
getTermFromStr [x] = ConstTerm [x]
getTermFromStr str
    | head str /= '(' && spaceIdx == -1 = ConstTerm str
    | head str == '(' && last str == ')' && spaceIdx > 0 && spaceIdx < length str - 1 = JuxTerm (getTermFromStr mStr) (getTermFromStr nStr)
    | otherwise = error $ "getTermFromStr: Format error at '" ++ str ++ "'"
    where
    str' = init (tail str)
    spaceIdx = indexOfDelimiter 0 0 0 ' ' str'
    mStr = take spaceIdx str'
    nStr = drop (spaceIdx + 1) str'

-- Sort terms according to non-descending order.
sortTerms :: [Term] -> [Term]
sortTerms [] = []
sortTerms [x] = [x]
sortTerms (x:xs) = (sortTerms [y | y <- xs, y <= x]) ++ [x] ++ (sortTerms [y | y <- xs, x < y])

{- Do one-step reduction for every subterm of a term. One-step reduction is one times of application of a certain combination axiom.
 -}
subTermReduct :: Term -> Term
subTermReduct (JuxTerm (JuxTerm (ConstTerm "A") x) y) = subTermReduct $ aAxiom ((JuxTerm (JuxTerm (ConstTerm "A") x) y))
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") x) y) z) = sAxiom ((JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") x) y) z))
subTermReduct (JuxTerm (JuxTerm (ConstTerm "K") x) y) = kAxiom ((JuxTerm (JuxTerm (ConstTerm "K") x) y)
subTermReduct (JuxTerm (ConstTerm "I") x) = iAxiom (JuxTerm (ConstTerm "I") x)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B") x) y) z) = bAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B") x) y) z)
subTermReduct (JuxTerm (JuxTerm (ConstTerm "T") x) y) = tAxiom (JuxTerm (JuxTerm (ConstTerm "T") x) y)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "C") x) y) z) = cAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "C") x) y) z)
subTermReduct (JuxTerm (JuxTerm (ConstTerm "W") x) y) = wAxiom (JuxTerm (JuxTerm (ConstTerm "W") x) y)
subTermReduct (JuxTerm (ConstTerm "M") x) = mAxiom (JuxTerm (ConstTerm "M") x)
subTermReduct (JuxTerm (ConstTerm "Y") x) = yAxiom (JuxTerm (ConstTerm "Y") x)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (JuxTerm (ConstTerm "J") x) y) z) v) = jAxiom (JuxTerm (JuxTerm (JuxTerm (JuxTerm (ConstTerm "J") x) y) z) v)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B'") x) y) z) = b'Axiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B'") x) y) z)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "V") x) y) z) = vAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "V") x) y) z)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S'") x) y) z) = s'Axiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S'") x) y) z)
subTermReduct (JuxTerm (JuxTerm (JuxTerm (ConstTerm "R") x) y) z) = rAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "R") x) y) z)
subTermReduct t = t

{- If a term has a normal form, namely, transitive closure of relation subTermOfTerm exists.
 - idxMax is the maximal transitive times.
 - If idxMax = 1, reduct completes one times of subTermReduct, which is not one-step reduction.
 -}
reduct :: Int -> Term -> Term
reduct idxMax term
    | term == term' = term
    | idxMax > 0 = reduct (idxMax - 1) term'
    | otherwise = term
    where
    term' = subTermReduct term
