-- Copyright (c) 2023 China University of Water Resources and Electric Power,
-- All rights reserved.

module Category (
    Category(..),  -- Category and its all Constructors
    Sep,           -- String
    seps,          -- [Sep]
    Prim,          -- String
    primitives,    -- [Prim]
    nilCate,       -- Category
    xCate,         -- Category
    sCate,         -- Category
    npCate,        -- Category
    isNil,         -- Category -> Bool
    isX,           -- Category -> Bool
    isPrimitive,   -- Category -> Bool
    isDerivative,  -- Category -> Bool
    veriStrForCate,      -- String -> Bool
    getCateFromString,   --String -> Category
    indexOfSep,    -- Int -> Int -> String -> Int
    leftStr,       -- String -> String
    rightStr,      -- String -> String
    midSepStr,     -- String -> Sep
    leftCate,      -- Category -> Category
    rightCate,     -- Category -> Category
    midSep,        -- Category -> Sep
    derivate,      -- Category -> Sep -> Category -> Category
    pronCate,      -- Category, "np"
    pronCate4Numeral,     -- Category, "np/#np"
    ndCate,        -- Category, "np\*np"
    adjCate,       -- Category, "np/.np"
    predCate,      -- Category, "s\.np"
    verbCate,      -- Category, "(s\.np)/.np"
    verbCate2,     -- Category, "((s\.np)/.np)/.np"
    vCate,         -- [predCate, verbCate, verbCate2]
    vpCate,        -- [verbCate, verbCate2]
    advCate,       -- Category, "(s\.np)/#(s\.np)"
    advCate4Verb,  -- Category, "(s\.np)/#(s\.np)"
    advCate4Adj,   -- Category, "(np/.np)/*(np/.np)"
    advCate4Sent,  -- Category, "s/*s"
    advCate4DirecVerb, -- Category, "(s\.np)/x(s\.np)"
    advCate4OE,    -- Category, "(s/.np)/*(s/.np)"
    advCompCate,   -- ((s\.np)/#(s\.np))\*((s\.np)/#(s\.np))
    prep2AdvCate,  -- Category, "((s\.np)/#(s\.np))/*np"
    prep2CompCate, -- Category, "((s\.np)\x(s\.np))/*np"
    prep4BaCate,          -- Category, "((s/.np)\#np)/#((s\.np)/.np)"
    prep4BeiCate,         -- Category, "(s/#(s\.np))\#np"
    verbCompCate,         -- Category, "(s\.np)\x(s\.np)"
    nounCompCate,         -- Category, "np\*np"
    adjCompCate,          -- Category, "(np/.np)\*(np/.np)"
    numeralCate,          -- Category, "np/*np"
    quantifierCate,       -- Category, "(np/*np)\*(np/*np)"
    objectExtractionCate, -- Category, "s/.np"
    predicateExtractionCate,       -- Category, "s/#(s\.np)"
    aux1Cate,             -- Category, "(np/*np)\*np"
    aux2Cate,             -- Category, "((s\.np)/#(s\.np))\*(np/.np)"
    aux3Cate,             -- Category, "((s\.np)\x(s\.np))/*(np/.np)"
    aux3dCate,            -- Category, "((np/.np)\*(np/.np))/*((np/.np)/*(np/.np))"
    aux4Cate,             -- Category, "(s\.np)\x(s\.np)"
    aux5Cate,             -- Category, "X\#X"
    aux6Cate,             -- Category, "np/*((s\.np)/.np)"
    toneCate,             -- Category, "X\.X"
    conjCate,            -- Category, "(X\*X)/*X"
    conjCate4Backward,            -- Category, "X\*X"
    conjCate4Forward,            -- Category, "X/*X"
    prefixCate,           -- Category, "np/*np"
    postfixCate,          -- Category, "np\*X"
    baPhraseCate          -- Category, "((s\#np)/#((s\.np)/.np)"
    ) where

type Sep = String
seps :: [Sep]
seps = ["|"]

type Prim = String
primitives :: [Prim]
primitives = ["s", "np"]

-- Define data type Category which is enumerable.
data Category = Nil | X | Primitive Prim | Derivative Category Sep Category deriving (Eq)

-- Define relation Ord between two categories such that two categories can be compared.
instance Ord Category where
    Nil < Nil = False
    X < X = False
    Primitive a < Primitive b =  a < b
    Derivative a _ b < Derivative c _ d = a < c || a == c && b < d            -- Priority of "||" is higher than "&&"
    Nil < X = True
    Nil < Primitive _ = True
    Nil < Derivative _ _ _ = True
    X < Primitive _ = True
    X < Derivative _ _ _ = True
    Primitive _ < Derivative _ _ _ = True
    X < Nil = False
    Primitive _ < Nil = False
    Derivative _ _ _ < Nil = False
    Primitive _ < X = False
    Derivative _ _ _ < X = False
    Derivative _ _ _ < Primitive _ = False
    Nil <= Nil = True
    Nil <= X = True
    Nil <= Primitive _ = True
    Nil <= Derivative _ _ _ = True
    X <= Nil = False
    X <= X = True
    X <= Primitive _ = True
    X <= Derivative _ _ _ = True
    Primitive _ <= Nil = False
    Primitive _ <= X = False
    Primitive a <= Primitive c = a < c || a == c
    Primitive _ <= Derivative _ _ _ = True
    Derivative _ _ _ <= Nil = False
    Derivative _ _ _ <= X = False
    Derivative _ _ _ <= Primitive _ = False
    Derivative a _ b <= Derivative c _ d = a < c || a == c && b < d || a == c && b == d

-- Define how a category shows as a letter string.
instance Show Category where
    show Nil = "Nil"
    show X = "X"
    show (Primitive c) = c
    show (Derivative c1 s c2)
        | (isPrimitive c1 || isX c1) && (isPrimitive c2 || isX c2) = (show c1)++s++(show c2)
        | isDerivative c1 && (isPrimitive c2 || isX c2) = "("++(show c1)++")"++s++(show c2)
        | (isPrimitive c1 || isX c1) && isDerivative c2 = (show c1)++s++"("++(show c2)++")"
        | otherwise = "("++(show c1)++")"++s++"("++(show c2)++")"

-- Besides interior functions, data constructors are not seen from outside of modules. To have access to these constructors, related functions are defined.
nilCate :: Category
nilCate = Nil

xCate :: Category
xCate = X

sCate :: Category
sCate = getCateFromString "s"

npCate :: Category
npCate = getCateFromString "np"

isNil :: Category -> Bool
isNil Nil = True
isNil _ = False

isX :: Category -> Bool
isX X = True
isX _ = False

isPrimitive :: Category -> Bool
isPrimitive (Primitive _) = True
isPrimitive _ = False

isDerivative :: Category -> Bool
isDerivative (Derivative _ _ _) = True
isDerivative _ = False

veriStrForCate :: String -> Bool
veriStrForCate str
    | indexOfSep 0 0 str == -1 = elem str ["Nil","s","np","X"]
    | otherwise = veriStrForCate (leftStr str) && elem (midSepStr str) seps && veriStrForCate (rightStr str)

getCateFromString :: String -> Category
getCateFromString str
    | veriStrForCate str /= True = error $ "getCateFromString: " ++ str ++ " is not well-formated."
    | index == -1 && str == "Nil" = Nil
    | index == -1 && str == "X" = X
    | index == -1 && str == "s" = Primitive "s"
    | index == -1 && str == "np" = Primitive "np"
    | otherwise = derivate (getCateFromString (leftStr str)) [str!!index] (getCateFromString (rightStr str))
        where
        index = indexOfSep 0 0 str

-- Get the index of middle seperator, which will be -1 for category "Nil", "X", "s" and "np".
-- To remember how many left brackets have been met, the integer nlb is needed.
-- The index is initialized as 0.
indexOfSep :: Int -> Int -> String -> Int
indexOfSep nlb i str
    | i == length str = -1
    | x == '(' = indexOfSep (nlb + 1) (i+1) str
    | x == ')' = indexOfSep (nlb - 1) (i+1) str
    | x == '|' && nlb == 0 && indexOfSep nlb (i+1) str == -1 = i
    | x == '|' && nlb == 0 && indexOfSep nlb (i+1) str /= -1 = error $ "indexOfSep: Category symbol \"" ++ str ++ "\" does not conform two-division style."
    | otherwise = indexOfSep nlb (i+1) str
        where
        x = str!!i

leftStr :: String -> String
leftStr str
    | index == -1 = error "leftStr"
    | head lStr == '(' && last lStr /= ')' = error "leftStr lost ')'"
    | head lStr /= '(' && last lStr == ')' = error "leftStr lost '('"
    | head lStr == '(' && last lStr == ')' = tail (init lStr)
    | otherwise = lStr
        where
        index = indexOfSep 0 0 str
        lStr = take index str

rightStr :: String -> String
rightStr str
    | index == -1 = error "rightStr"
    | head rStr == '(' && last rStr /= ')' = error "rightStr lost ')'"
    | head rStr /= '(' && last rStr == ')' = error "rightStr lost '('"
    | head rStr == '(' && last rStr == ')' = tail (init rStr)
    | otherwise = rStr
        where
        index = indexOfSep 0 0 str
        rStr = drop (index + 1) str

midSepStr :: String -> Sep
midSepStr str
    | index == -1 = error "midSepStr: No seperator '|'."
    | otherwise = [str!!index]
        where
        index = indexOfSep 0 0 str

leftCate :: Category -> Category
leftCate Nil = error "leftCate: Nil"
leftCate X = error "leftCate: X"
leftCate (Primitive a) = error $ "leftCate: " ++ show (Primitive a)
leftCate (Derivative cate1 _ _) = cate1

rightCate :: Category -> Category
rightCate Nil = error "rightCate: Nil"
rightCate X = error "rightCate: X"
rightCate (Primitive a) = error $ "rightCate: " ++ show (Primitive a)
rightCate (Derivative _ _ cate2) = cate2

midSep :: Category -> Sep
midSep Nil = error "midSlash: Nil"
midSep X = error "midSlash: X"
midSep (Primitive _) = error "midSlash: Primitive _"
midSep (Derivative _ s _) = s

derivate :: Category -> Sep -> Category -> Category
derivate  cate1 sep cate2 = Derivative cate1 sep cate2

pronCate :: Category
pronCate = getCateFromString "np"

pronCate4Numeral :: Category
pronCate4Numeral = getCateFromString "np|np"

ndCate :: Category
ndCate = getCateFromString "np|np"

adjCate :: Category
adjCate = getCateFromString "np|np"

predCate :: Category
predCate = getCateFromString "s|np"

verbCate :: Category
verbCate = getCateFromString "(s|np)|np"

verbCate2 :: Category
verbCate2 = getCateFromString "((s|np)|np)|np"

vCate :: [Category]
vCate = [predCate, verbCate, verbCate2]

vpCate :: [Category]
vpCate = [verbCate, verbCate2]

advCate :: Category
advCate = getCateFromString "(s|np)|(s|np)"

advCate4Verb :: Category
advCate4Verb = getCateFromString "(s|np)|(s|np)"

advCate4Adj :: Category
advCate4Adj = getCateFromString "(np|np)|(np|np)"

advCate4Sent :: Category
advCate4Sent = getCateFromString "s|s"

advCate4DirecVerb :: Category
advCate4DirecVerb = getCateFromString "(s\\.np)/x(s\\.np)"

advCate4OE :: Category
advCate4OE = getCateFromString "(s/.np)/*(s/.np)"

advCompCate :: Category
advCompCate = getCateFromString "((s\\.np)/#(s\\.np))\\*((s\\.np)/#(s\\.np))"

-- Category of preposition which combines one following object to construct a adverbial, such as "走v 到p 华水n"
prep2AdvCate :: Category
prep2AdvCate = getCateFromString "((s\\.np)/#(s\\.np))/*np"

-- Category of preposition which combines one following object to construct a complement, such as "走v 到p 华水n"
prep2CompCate :: Category
prep2CompCate = getCateFromString "((s\\.np)\\x(s\\.np))/*np"

-- '把'
prep4BaCate :: Category
prep4BaCate = getCateFromString "((s/.np)\\#np)/#((s\\.np)/.np)"

-- '被'
prep4BeiCate :: Category
prep4BeiCate = getCateFromString "(s/#(s/.np))\\#np"

verbCompCate :: Category
verbCompCate = getCateFromString "(s\\.np)\\x(s\\.np)"

nounCompCate :: Category
nounCompCate = getCateFromString "np\\*np"

adjCompCate :: Category
adjCompCate = getCateFromString "(np/.np)\\*(np/.np)"

numeralCate :: Category
numeralCate = getCateFromString "np/*np"

quantifierCate :: Category
quantifierCate = getCateFromString "(np/*np)\\*(np/*np)"

objectExtractionCate :: Category
objectExtractionCate = getCateFromString "s/.np"

predicateExtractionCate :: Category
predicateExtractionCate = getCateFromString "s/#(s\\.np)"

-- Auxiliary word #1 is '的'
aux1Cate :: Category
aux1Cate = getCateFromString "(np/*np)\\*np"

-- Auxiliary word #2 is '地'
aux2Cate :: Category
aux2Cate = getCateFromString "((s\\.np)/#(s\\.np))\\*(np/.np)"

-- Auxiliary word #3 is '得'
aux3Cate :: Category
aux3Cate = getCateFromString "((s\\.np)\\x(s\\.np))/*(np/.np)"

-- Auxiliary word #3d is also '得', here 'd' means an adjective adverb follows.
aux3dCate :: Category
aux3dCate = getCateFromString "((np/.np)\\*(np/.np))/*((np/.np)/*(np/.np))"

-- Auxiliary word #4 is '着', '了', or '过'
aux4Cate :: Category
aux4Cate = getCateFromString "(s\\.np)\\x(s\\.np)"

-- Auxiliary word #5 is '等', '似的', '一样', and so on.
aux5Cate :: Category
aux5Cate = getCateFromString "X\\#X"

-- Auxiliary word #6 is '所', followed by transitive verb.
aux6Cate :: Category
aux6Cate = getCateFromString "np/*((s\\.np)/.np)"

-- Tone word is '呢', '啊', '了', '的', and so on.
toneCate :: Category
toneCate = getCateFromString "X\\.X"

-- Conjunction the left and the right.
conjCate :: Category
conjCate = getCateFromString "(X\\*X)/*X"

-- Conjunction the left.
conjCate4Backward :: Category
conjCate4Backward = getCateFromString "X\\*X"

-- Conjunction the right.
conjCate4Forward :: Category
conjCate4Forward = getCateFromString "X/*X"

-- Prefix words are '第'、'阿'、'初'
prefixCate :: Category
prefixCate = getCateFromString "np/*np"

-- Postfix words are '者'、'们'、'性'、'儿'
postfixCate :: Category
postfixCate = getCateFromString "np\\*X"

-- '把' phrase
baPhraseCate :: Category
baPhraseCate = getCateFromString "(s\\#np)/#((s\\.np)/.np)"
