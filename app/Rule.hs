{- Copyright (c) 2019-2023 China University of Water Resources and Electric Power, all rights reserved.
 - This module descibe a Combinatory Categorial Grammar. The grammar is distinctly different with CCG of Mark Steedman,
 - which is the combination of Ajdukiewicz's Categorial Grammar and Schonfinkel's Combinatory Logic and its type system.
 - Syntactic rules are from Combinatory Logic and its type system. Lexical rules are left for Chinese usage.
 -}

module Rule (
    rules,    -- [(Category,Seman,PhraStru) -> (Category,Seman,PhraStru) -> (Category, Tag, Seman, PhraStru, Act)]
    ruleTags, -- [Tag], List of CCG rule tags
    semComb,  -- Term -> Seman -> Seman -> Seman
    Rule(..),         -- Enumerated type for the tags of category-converted rules
    comA,     --  (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comS,     --(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comK,     --(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comB,     --(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comT,     --(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comC,     --(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comW,     --(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comB',    -- (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comV,     -- (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comS',    -- (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    comR,     -- (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
    ccTags,           -- [String], List of category type-conversional tags
    lexRule,          -- [Rule]
    OnOff,            -- [Rule], Rule used is the one in this module
    ruleOn,           -- Rule -> OnOff -> OnOff
    ruleOff,          -- Rule -> OnOff -> OnOff
    updateOnOff,      -- [Rule] -> [String] -> [Rule]
    showOnOff         -- [Rule] -> IO ()
    ) where

import Data.Tuple.Utils
import Category
import CL
import Phrase

-- CCG rules constitute a functional list.
rules :: [(Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)]

rules = [comA, comS, comK, comB, comT, comC, comW, comB', comV, comS', comR]

{- In parsing trees, every combination should print its corresponding rule tag.
 - To now, the rules used for combining two phrases are not limited in the following.
 -}
ruleTags :: [Tag]
ruleTags = ["A","S","K","B","T","C","W","B'","V","S'","R"]

-- The combination of two semantic components is defined by a certain combinator.
semComb :: Term -> Seman -> Seman -> Seman
semComb comb se1 se2
    | comb == ConstTerm "A" = show $ aAxiom t
    | comb == ConstTerm "S" = show $ sAxiom t
    | comb == ConstTerm "K" = show $ aAxiom t     -- Same as "A"
    | comb == ConstTerm "B" = show $ bAxiom t
    | comb == ConstTerm "T" = show $ tAxiom t
    | comb == ConstTerm "C" = show $ cAxiom t
    | comb == ConstTerm "W" = show $ wAxiom t
    | comb == ConstTerm "B'" = show $ b'Axiom t
    | comb == ConstTerm "V" = show $ vAxiom t
    | comb == ConstTerm "S'" = show $ s'Axiom t
    | comb == ConstTerm "R" = show $ rAxiom t
    | otherwise = error "semComb: Combinator does not exist."
    where
    t1 = getTermFromStr se1
    t2 = getTermFromStr se2
    t = termSeq2Term [comb, t1, t2]

{- Syntactic rules corresponding to various combinators.
 - The basic and usual combinators are as following.
 - Axy = xy
 - Sxyz => xz(yz)      Kxy => x         Bxyz => x(yz)       Txy => yx           Cxyz => xzy
 - Wxy => xyy          B'xyz => y(xz)   Vxyz => zxy         S'xyz => yz(xz)     Rxyz => yzx
 -}

{- Basic systactic rule is application of one category onto the next category, which is equivalent with
 - forward application in Category Grammar.
 - Combinator A: B/A: P  A:Q  ->  B: PQ
 -}
comA :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comA cate1 cate2
    | isPrimCate ca1 = (nilCate, "A", "", "", False)
    | isAvail && isDeriCate ca2 && isDeriCate (leftCate ca2) && leftCate ca1 == xCate && leftCate (leftCate ca2) == xCate = (leftCate (leftCate ca2), "A", semComb (ConstTerm "A") se1 se2, "NR", True)    -- For X/((X/B)/A) (C/B)/A
    | otherwise = (nilCate, "A", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    isAvail = rightCate ca1 == ca2

-- Combinator S: (C/B)/A: P  B/A: Q → C/A: SPQ
comS :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comS cate1 cate2
    | isAvail = (derivate (leftCate lca1) "/" rca2, "S", semComb (ConstTerm "S") se1 se2, "NR", True)
    | otherwise = (nilCate, "S", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca1 = leftCate ca1
    rca2 = rightCate ca2
    isAvail = rightCate ca1 == rightCate ca2 && rightCate lca1 == leftCate ca2

-- Combinator K: A: P  B: Q  → A: P
comK :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comK cate1 cate2 = (ca1, "K", semComb (ConstTerm "K") se1 se2, "NR", True)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    se2 = snd3 cate2

-- Combinator B: C/B: P  B/A: Q → C/A: BPQ
comB :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comB cate1 cate2
    | isAvail = (derivate lca1 "/" rca2, "B", semComb (ConstTerm "B") se1 se2, "NR", True)
    | otherwise = (nilCate, "B", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca1 = leftCate ca1
    rca2 = rightCate ca2
    isAvail = rightCate ca1 == leftCate ca2

--- Combinator T: A: P  B/A: Q  →  B: QP
comT :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comT cate1 cate2
    | isAvail = (lca2, "T", semComb (ConstTerm "T") se1 se2, "NR", True)
    | otherwise = (nilCate, "T", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca2 = leftCate ca2
    isAvail = ca1 == rightCate ca2

-- Combinator C: (C/B)/A: P  B: Q  ->  C/A: CPQ
comC :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comC cate1 cate2
    | isAvail = (derivate llca1 "/" rca1, "C", semComb (ConstTerm "C") se1 se2, "NR", True)
    | otherwise = (nilCate, "C", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca1 = leftCate ca1
    llca1 = leftCate lca1
    rca1 = rightCate ca1
    isAvail = rightCate lca1 == ca2

-- Combinator W: (B/A)/A: P  A: Q → B: PQQ
comW :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comW cate1 cate2
    | isAvail = (llca1, "W", semComb (ConstTerm "W") se1 se2, "NR", True)
    | otherwise = (nilCate, "W", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca1 = leftCate ca1
    llca1 = leftCate lca1
    rca1 = rightCate ca1
    isAvail = rightCate lca1 == rca1 && rca1 == ca2

-- Combinator B': B/A: P  C/B: Q  →  C/A: B'PQ
comB' :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comB' cate1 cate2
    | isAvail = (derivate lca2 "/" rca1, "B'", semComb (ConstTerm "B'") se1 se2, "NR", True)
    | otherwise = (nilCate, "B'", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    rca1 = rightCate ca1
    lca2 = leftCate ca2
    isAvail = leftCate ca1 == rightCate ca2

-- Combinator V: A: P  B: Q  ->  C/((C/B)/A): VPQ
comV :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comV cate1 cate2
    | isAvail = (derivate xCate "/" (derivate (derivate xCate "/" ca2) "/" ca1), "V", semComb (ConstTerm "V") se1 se2, "NR", True)
    | otherwise = (nilCate, "V", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    isAvail = True

-- Combinator S': B/A: P  (C/B)/A: Q  → C/A: S'PQ
comS' :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comS' cate1 cate2
    | isPrimCate ca1 || isPrimCate ca2 = (nilCate, "S'", "", "", False)
    | isPrimCate (leftCate ca2) = (nilCate, "S'", "", "", False)
    | isAvail = (derivate llca2 "/" rca2, "S'", semComb (ConstTerm "S'") se1 se2, "NR", True)
    | otherwise = (nilCate, "S'", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca2 = leftCate ca2
    rca2 = rightCate ca2
    llca2 = leftCate rca2
    rlca2 = rightCate rca2
    isAvail = leftCate ca1 == rlca2 && rightCate ca1 == rca2

-- Combinator R: A: P  (B/A)/C: Q  → B/C: RPQ
comR :: (Category, Seman, PhraStru) -> (Category, Seman, PhraStru) -> (Category, Tag, Seman, PhraStru, Act)
comR cate1 cate2
    | isPrimCate ca2 = (nilCate, "R", "", "", False)
    | isPrimCate (leftCate ca2) = (nilCate, "R", "", "", False)
    | isAvail = (derivate llca2 "/" rca2, "R", semComb (ConstTerm "R") se1 se2, "NR", True)
    | otherwise = (nilCate, "R", "", "", False)
    where
    ca1 = fst3 cate1
    se1 = snd3 cate1
    ca2 = fst3 cate2
    se2 = snd3 cate2
    lca2 = leftCate ca2
    rca2 = rightCate ca2
    llca2 = leftCate rca2
    rlca2 = rightCate rca2
    isAvail = ca1 == rlca2

{- All tags of context-sensitive category-converted rules:
   (s1)S/s, (s2)P/s, (s3)O/s, (s4)A/s, (s5)Hn/s, (s6)N/s,
   (v1)S/v, (v2)O/v, (v3)A/v, (v4)Hn/v, (v5)D/v, (v6)Cn/v, (v7)Cv/v, (v8)N/v, (v9)P/vt, (v10)OE/vt, (v11)Vt/vi, (v12)A/vd,
   (a1)S/a, (a2)P/a, (a3)V/a, (a4)O/a, (a5)D/a, (a6)Da/a, (a7)Cn/a, (a8)Cv/a, (a9)Ca/a, (a10)Hn/a, (a11)N/a,
   (n1)P/n, (n2)V/n, (n3)A/n, (n4)Cn/n, (n4)Cv/n, (n6)D/n, (n7)Da/n, (n8)ADJ/n, (n9)S/nd, (n10)O/nd, (n11)Hn/nd,
   (d1)S/d, (d2)O/d, (d3)A/d, (d4)Hn/d, (d5)Cv/d, (d6)N/d, (d7)ADJ/d, (d8)Da/d, (d9)Ds/d, (d10)Dx/d, (d11)Doe/d,
   (p1)D/p,
   (oe1)O/oe, (oe2)Hn/oe, (oe3)N/oe,
   (pe1)N/pe,
   (q1)A/q,
   (c1)Jf/c, (c2)Jb/c,
   (au1)U3d/u3
 -}

ccTags = ["S/s","P/s","O/s","A/s","Hn/s","N/s",
          "S/v","O/v","A/v","Hn/v","D/v","Cn/v","Cv/v","N/v","P/vt","OE/vt","Vt/vi","A/vd",
          "S/a","P/a","V/a","O/a","D/a","Da/a","Cn/a","Cv/a","Ca/a","Hn/a","N/a",
          "P/n","V/n","A/n","Cn/n","Cv/n","D/n","Da/n","ADJ/n","S/nd","O/nd","Hn/nd",
          "S/d","O/d","A/d","Hn/d","Cv/d","N/d","ADJ/d","Da/d","Ds/d","Dx/d","Doe/d",
          "D/p",
          "O/oe","Hn/oe","N/oe",
          "N/pe",
          "A/q",
          "Jf/c","Jb/c",
          "U3d/u3"]

{- The enumerated type Rule is for the tags of category-converted rules. Rule value throws away '/' because enumerated
   value can't include '/'.
 -}

data Rule = Ss | Ps | Os | As | Hns | Ns
          | Sv | Ov | Av | Hnv | Dv | Cnv | Cvv | Nv | Pvt | OEvt | Vtvi | Avd
          | Sa | Pa | Va | Oa | Da | Daa | Cna | Cva | Caa | Hna | Na
          | Pn | Vn | An | Cnn | Cvn | Dn | Dan | ADJn | Snd | Ond | Hnnd
          | Sd | Od | Ad | Hnd | Cvd | Nd | ADJd | Dad | Dsd | Dxd | Doed
          | Dp
          | Ooe | Hnoe | Noe
          | Npe
          | Aq
          | Jfc | Jbc
          | U3du3 deriving (Eq)

lexRule :: [Rule]
lexRule = [Ss, Ps, Os, As, Hns, Ns, Sv, Ov, Av, Hnv, Dv, Cnv, Cvv, Nv, Pvt, OEvt, Vtvi, Avd, Sa, Oa, Hna, Na, Pa, Va, Da, Daa, Cva, Cna, Caa, Pn, Vn, An, Cnn, Cvn, Dn, Dan, ADJn, Snd, Ond, Hnnd, Sd, Od, Ad, Hnd, Cvd, Nd, ADJd, Dad, Dsd, Dxd, Doed, Dp, Ooe, Hnoe, Noe, Npe, Aq, Jfc, Jbc, U3du3]

-- Define how the tag of a category-converted rule shows as a letter string.
instance Show Rule where
    show Ss = "S/s"
    show Ps = "P/s"
    show Os = "O/s"
    show As = "A/s"
    show Hns = "Hn/s"
    show Ns = "N/s"
    show Sv = "S/v"
    show Ov = "O/v"
    show Av = "A/v"
    show Hnv = "Hn/v"
    show Dv = "D/v"
    show Cnv = "Cn/v"
    show Cvv = "Cv/v"
    show Nv = "N/v"
    show Pvt = "P/vt"
    show OEvt = "OE/vt"
    show Vtvi = "Vt/vi"
    show Avd = "A/vd"
    show Sa = "S/a"
    show Oa = "O/a"
    show Pa = "P/a"
    show Va = "V/a"
    show Da = "D/a"
    show Daa = "Da/a"
    show Cna = "Cn/a"
    show Cva = "Cv/a"
    show Caa = "Ca/a"
    show Hna = "Hn/a"
    show Na = "N/a"
    show Pn = "P/n"
    show Vn = "V/n"
    show An = "A/n"
    show Cnn = "Cn/n"
    show Cvn = "Cv/n"
    show Dn = "D/n"
    show Dan = "Da/n"
    show ADJn = "ADJ/n"
    show Snd = "S/nd"
    show Ond = "O/nd"
    show Hnnd = "Hn/nd"
    show Sd = "S/d"
    show Od = "O/d"
    show Ad = "A/d"
    show Hnd = "Hn/d"
    show Cvd = "Cv/d"
    show Nd = "N/d"
    show ADJd = "ADJ/d"
    show Dad = "Da/d"
    show Dsd = "Ds/d"
    show Dxd = "Dx/d"
    show Doed = "Doe/d"
    show Dp = "D/p"
    show Ooe = "O/oe"
    show Hnoe = "Hn/oe"
    show Noe = "N/oe"
    show Npe = "N/pe"
    show Aq = "A/q"
    show Jfc = "Jf/c"
    show Jbc = "Jb/c"
    show U3du3 = "U3d/u3"

-- OnOff is the list of Rule members
type OnOff = [Rule]

-- Turn On a Rule
ruleOn :: Rule -> OnOff -> OnOff
ruleOn ru onOff
    | elem ru onOff = onOff
    | otherwise = ru:onOff

-- Turn Off a Rule
ruleOff :: Rule -> OnOff -> OnOff
ruleOff ru onOff
    | notElem ru onOff = onOff
    | otherwise = [x| x <- onOff, x /= ru]

-- Update rule switches. For "+N/s", turn on Ns; For "-P/a", turn off Pa.
updateOnOff :: [Rule] -> [String] -> [Rule]
updateOnOff onOff rws
    | rws == [] = onOff
    | rw1 == "+S/s" = updateOnOff (ruleOn Ss onOff) rwt
    | rw1 == "-S/s" = updateOnOff (ruleOff Ss onOff) rwt
    | rw1 == "+P/s" = updateOnOff (ruleOn Ps onOff) rwt
    | rw1 == "-P/s" = updateOnOff (ruleOff Ps onOff) rwt
    | rw1 == "+O/s" = updateOnOff (ruleOn Os onOff) rwt
    | rw1 == "-O/s" = updateOnOff (ruleOff Os onOff) rwt
    | rw1 == "+A/s" = updateOnOff (ruleOn As onOff) rwt
    | rw1 == "-A/s" = updateOnOff (ruleOff As onOff) rwt
    | rw1 == "+Hn/s" = updateOnOff (ruleOn Hns onOff) rwt
    | rw1 == "-Hn/s" = updateOnOff (ruleOff Hns onOff) rwt
    | rw1 == "+N/s" = updateOnOff (ruleOn Ns onOff) rwt
    | rw1 == "-N/s" = updateOnOff (ruleOff Ns onOff) rwt
    | rw1 == "+S/v" = updateOnOff (ruleOn Sv onOff) rwt
    | rw1 == "-S/v" = updateOnOff (ruleOff Sv onOff) rwt
    | rw1 == "+O/v" = updateOnOff (ruleOn Ov onOff) rwt
    | rw1 == "-O/v" = updateOnOff (ruleOff Ov onOff) rwt
    | rw1 == "+A/v" = updateOnOff (ruleOn Av onOff) rwt
    | rw1 == "-A/v" = updateOnOff (ruleOff Av onOff) rwt
    | rw1 == "+Hn/v" = updateOnOff (ruleOn Hnv onOff) rwt
    | rw1 == "-Hn/v" = updateOnOff (ruleOff Hnv onOff) rwt
    | rw1 == "+D/v" = updateOnOff (ruleOn Dv onOff) rwt
    | rw1 == "-D/v" = updateOnOff (ruleOff Dv onOff) rwt
    | rw1 == "+Cn/v" = updateOnOff (ruleOn Cnv onOff) rwt
    | rw1 == "-Cn/v" = updateOnOff (ruleOff Cnv onOff) rwt
    | rw1 == "+Cv/v" = updateOnOff (ruleOn Cvv onOff) rwt
    | rw1 == "-Cv/v" = updateOnOff (ruleOff Cvv onOff) rwt
    | rw1 == "+N/v" = updateOnOff (ruleOn Nv onOff) rwt
    | rw1 == "-N/v" = updateOnOff (ruleOff Nv onOff) rwt
    | rw1 == "+P/vt" = updateOnOff (ruleOn Pvt onOff) rwt
    | rw1 == "-P/vt" = updateOnOff (ruleOff Pvt onOff) rwt
    | rw1 == "+OE/vt" = updateOnOff (ruleOn OEvt onOff) rwt
    | rw1 == "-OE/vt" = updateOnOff (ruleOff OEvt onOff) rwt
    | rw1 == "+Vt/vi" = updateOnOff (ruleOn Vtvi onOff) rwt
    | rw1 == "-Vt/vi" = updateOnOff (ruleOff Vtvi onOff) rwt
    | rw1 == "+A/vd" = updateOnOff (ruleOn Avd onOff) rwt
    | rw1 == "-A/vd" = updateOnOff (ruleOff Avd onOff) rwt
    | rw1 == "+S/a" = updateOnOff (ruleOn Sa onOff) rwt
    | rw1 == "-S/a" = updateOnOff (ruleOff Sa onOff) rwt
    | rw1 == "+P/a" = updateOnOff (ruleOn Pa onOff) rwt
    | rw1 == "-P/a" = updateOnOff (ruleOff Pa onOff) rwt
    | rw1 == "+V/a" = updateOnOff (ruleOn Va onOff) rwt
    | rw1 == "-V/a" = updateOnOff (ruleOff Va onOff) rwt
    | rw1 == "+O/a" = updateOnOff (ruleOn Oa onOff) rwt
    | rw1 == "-O/a" = updateOnOff (ruleOff Oa onOff) rwt
    | rw1 == "+D/a" = updateOnOff (ruleOn Da onOff) rwt
    | rw1 == "-D/a" = updateOnOff (ruleOff Da onOff) rwt
    | rw1 == "+Da/a" = updateOnOff (ruleOn Daa onOff) rwt
    | rw1 == "-Da/a" = updateOnOff (ruleOff Daa onOff) rwt
    | rw1 == "+Cn/a" = updateOnOff (ruleOn Cna onOff) rwt
    | rw1 == "-Cn/a" = updateOnOff (ruleOff Cna onOff) rwt
    | rw1 == "+Cv/a" = updateOnOff (ruleOn Cva onOff) rwt
    | rw1 == "-Cv/a" = updateOnOff (ruleOff Cva onOff) rwt
    | rw1 == "+Ca/a" = updateOnOff (ruleOn Caa onOff) rwt
    | rw1 == "-Ca/a" = updateOnOff (ruleOff Caa onOff) rwt
    | rw1 == "+Hn/a" = updateOnOff (ruleOn Hna onOff) rwt
    | rw1 == "-Hn/a" = updateOnOff (ruleOff Hna onOff) rwt
    | rw1 == "+N/a" = updateOnOff (ruleOn Na onOff) rwt
    | rw1 == "-N/a" = updateOnOff (ruleOff Na onOff) rwt
    | rw1 == "+P/n" = updateOnOff (ruleOn Pn onOff) rwt
    | rw1 == "-P/n" = updateOnOff (ruleOff Pn onOff) rwt
    | rw1 == "+V/n" = updateOnOff (ruleOn Vn onOff) rwt
    | rw1 == "-V/n" = updateOnOff (ruleOff Vn onOff) rwt
    | rw1 == "+A/n" = updateOnOff (ruleOn An onOff) rwt
    | rw1 == "-A/n" = updateOnOff (ruleOff An onOff) rwt
    | rw1 == "+Cn/n" = updateOnOff (ruleOn Cnn onOff) rwt
    | rw1 == "-Cn/n" = updateOnOff (ruleOff Cnn onOff) rwt
    | rw1 == "+Cv/n" = updateOnOff (ruleOn Cvn onOff) rwt
    | rw1 == "-Cv/n" = updateOnOff (ruleOff Cvn onOff) rwt
    | rw1 == "+D/n" = updateOnOff (ruleOn Dn onOff) rwt
    | rw1 == "-D/n" = updateOnOff (ruleOff Dn onOff) rwt
    | rw1 == "+Da/n" = updateOnOff (ruleOn Dan onOff) rwt
    | rw1 == "-Da/n" = updateOnOff (ruleOff Dan onOff) rwt
    | rw1 == "+ADJ/n" = updateOnOff (ruleOn ADJn onOff) rwt
    | rw1 == "-ADJ/n" = updateOnOff (ruleOff ADJn onOff) rwt
    | rw1 == "+S/nd" = updateOnOff (ruleOn Snd onOff) rwt
    | rw1 == "-S/nd" = updateOnOff (ruleOff Snd onOff) rwt
    | rw1 == "+O/nd" = updateOnOff (ruleOn Ond onOff) rwt
    | rw1 == "-O/nd" = updateOnOff (ruleOff Ond onOff) rwt
    | rw1 == "+Hn/nd" = updateOnOff (ruleOn Hnnd onOff) rwt
    | rw1 == "-Hn/nd" = updateOnOff (ruleOff Hnnd onOff) rwt
    | rw1 == "+D/p" = updateOnOff (ruleOn Dp onOff) rwt
    | rw1 == "-D/p" = updateOnOff (ruleOff Dp onOff) rwt
    | rw1 == "+O/oe" = updateOnOff (ruleOn Ooe onOff) rwt
    | rw1 == "-O/oe" = updateOnOff (ruleOff Ooe onOff) rwt
    | rw1 == "+Hn/oe" = updateOnOff (ruleOn Hnoe onOff) rwt
    | rw1 == "-Hn/oe" = updateOnOff (ruleOff Hnoe onOff) rwt
    | rw1 == "+N/oe" = updateOnOff (ruleOn Noe onOff) rwt
    | rw1 == "-N/oe" = updateOnOff (ruleOff Noe onOff) rwt
    | rw1 == "+N/pe" = updateOnOff (ruleOn Npe onOff) rwt
    | rw1 == "-N/pe" = updateOnOff (ruleOff Npe onOff) rwt
    | rw1 == "+A/q" = updateOnOff (ruleOn Aq onOff) rwt
    | rw1 == "-A/q" = updateOnOff (ruleOff Aq onOff) rwt
    | rw1 == "+S/d" = updateOnOff (ruleOn Sd onOff) rwt
    | rw1 == "-S/d" = updateOnOff (ruleOff Sd onOff) rwt
    | rw1 == "+O/d" = updateOnOff (ruleOn Od onOff) rwt
    | rw1 == "-O/d" = updateOnOff (ruleOff Od onOff) rwt
    | rw1 == "+A/d" = updateOnOff (ruleOn Ad onOff) rwt
    | rw1 == "-A/d" = updateOnOff (ruleOff Ad onOff) rwt
    | rw1 == "+Hn/d" = updateOnOff (ruleOn Hnd onOff) rwt
    | rw1 == "-Hn/d" = updateOnOff (ruleOff Hnd onOff) rwt
    | rw1 == "+Cv/d" = updateOnOff (ruleOn Cvd onOff) rwt
    | rw1 == "-Cv/d" = updateOnOff (ruleOff Cvd onOff) rwt
    | rw1 == "+N/d" = updateOnOff (ruleOn Nd onOff) rwt
    | rw1 == "-N/d" = updateOnOff (ruleOff Nd onOff) rwt
    | rw1 == "+ADJ/d" = updateOnOff (ruleOn ADJd onOff) rwt
    | rw1 == "-ADJ/d" = updateOnOff (ruleOff ADJd onOff) rwt
    | rw1 == "+Da/d" = updateOnOff (ruleOn Dad onOff) rwt
    | rw1 == "-Da/d" = updateOnOff (ruleOff Dad onOff) rwt
    | rw1 == "+Ds/d" = updateOnOff (ruleOn Dsd onOff) rwt
    | rw1 == "-Ds/d" = updateOnOff (ruleOff Dsd onOff) rwt
    | rw1 == "+Dx/d" = updateOnOff (ruleOn Dxd onOff) rwt
    | rw1 == "-Dx/d" = updateOnOff (ruleOff Dxd onOff) rwt
    | rw1 == "+Doe/d" = updateOnOff (ruleOn Doed onOff) rwt
    | rw1 == "-Doe/d" = updateOnOff (ruleOff Doed onOff) rwt
    | rw1 == "+Jf/c" = updateOnOff (ruleOn Jfc onOff) rwt
    | rw1 == "-Jf/c" = updateOnOff (ruleOff Jfc onOff) rwt
    | rw1 == "+Jb/c" = updateOnOff (ruleOn Jbc onOff) rwt
    | rw1 == "-Jb/c" = updateOnOff (ruleOff Jbc onOff) rwt
    | rw1 == "+U3d/u3" = updateOnOff (ruleOn U3du3 onOff) rwt
    | rw1 == "-U3d/u3" = updateOnOff (ruleOff U3du3 onOff) rwt
    | otherwise = error $ "updateOnOff: Rule switch " ++ rw1 ++ " is not cognizable."
      where
        rw1 = head rws
        rwt = tail rws

-- Output [Rule] on console
showOnOff :: [Rule] -> IO ()
showOnOff [] = putStrLn ":: OnOff"
showOnOff (r:rs) = do
    putStr (show r)
    putStr " "
    showOnOff rs
