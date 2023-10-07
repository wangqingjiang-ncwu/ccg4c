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
    oneStepReduct,    -- Term -> Term
    sortTerms,        -- [Term] -> [Term]
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
combAxiom = [sAxiom, kAxiom, iAxiom, bAxiom, tAxiom, cAxiom, wAxiom, mAxiom, yAxiom, jAxiom, b'Axiom, vAxiom, s'Axiom, rAxiom]

{- The basic and usual combinators
 - Sxyz => xz(yz)      Kxy => x         Ix => x
 - Bxyz => x(yz)       Txy => yx        Cxyz => xzy
 - Wxy => xyy          Mx => xx         Yx => x(Yx)
 - Jxyzv => xy(xvz)    B'xyz => y(xz)   Vxyz => zxy
 - S'xyz => yz(xz)     Rxyz => yzx
 -}

{- Axioms of some well-known combinators
 -}
sAxiom :: Term -> Term
sAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S") x) y) z) = JuxTerm (JuxTerm x z) (JuxTerm y z)
sAxiom t = t

kAxiom :: Term -> Term
kAxiom (JuxTerm (JuxTerm (ConstTerm "K") x) _) = x
kAxiom t = t

iAxiom :: Term -> Term
iAxiom (JuxTerm (ConstTerm "I") x) = x
iAxiom t = t

bAxiom :: Term -> Term
bAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B") x) y) z) = JuxTerm x (JuxTerm y z)
bAxiom t = t

tAxiom :: Term -> Term
tAxiom (JuxTerm (JuxTerm (ConstTerm "T") x) y) = JuxTerm y x
tAxiom t = t

cAxiom :: Term -> Term
cAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "C") x) y) z) = JuxTerm x (JuxTerm z y)
cAxiom t = t

wAxiom :: Term -> Term
wAxiom (JuxTerm (JuxTerm (ConstTerm "W") x) y) = JuxTerm (JuxTerm x y) y
wAxiom t = t

mAxiom :: Term -> Term
mAxiom (JuxTerm (ConstTerm "M") x) = JuxTerm x x
mAxiom t = t

yAxiom :: Term -> Term
yAxiom (JuxTerm (ConstTerm "Y") x) = JuxTerm x (JuxTerm (ConstTerm "Y") x)
yAxiom t = t

jAxiom :: Term -> Term
jAxiom (JuxTerm (JuxTerm (JuxTerm (JuxTerm (ConstTerm "J") x) y) z) v)
    = JuxTerm (JuxTerm x y) (JuxTerm (JuxTerm x v) z)
jAxiom t = t

b'Axiom :: Term -> Term
b'Axiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "B'") x) y) z) = JuxTerm y (JuxTerm x z)
b'Axiom t = t

vAxiom :: Term -> Term
vAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "V") x) y) z) = JuxTerm z (JuxTerm x y)
vAxiom t = t

s'Axiom :: Term -> Term
s'Axiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "S'") x) y) z) = JuxTerm (JuxTerm y z) (JuxTerm x z)
s'Axiom t = t

rAxiom :: Term -> Term
rAxiom (JuxTerm (JuxTerm (JuxTerm (ConstTerm "R") x) y) z) = JuxTerm y (JuxTerm z x)
rAxiom t = t

-- Get a term from a sequence of terms. The sequence is considered as left combination priority.
termSeq2Term :: [Term] -> Term
termSeq2Term [] = nilTerm
termSeq2Term [x] = x
termSeq2Term xs = JuxTerm (termSeq2Term (init xs)) (last xs)

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

{- One-step reduction is one times of application of a certain combination axiom.
 - The application happens on a certain subterm of the input term.
 - If no subterm can reduct, namely there is no redexes, then the term is a normal form.
 -}
oneStepReduct :: Term -> Term
oneStepReduct a = a
