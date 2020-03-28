{-# LANGUAGE DerivingVia #-}
{-# LANGUAGE RoleAnnotations #-}
module Main where

import Data.Functor.Classes
import Text.Read

import AutoLift

data Test a = Test Int a [a]
    deriving (Show, Read, Eq)
    deriving (Show1, Read1) via (Reflected1 Test)

{-

-- The following does not compile due to type role annotation

data BadTest a = BadTest a [a]
    deriving (Show, Read, Eq)
    deriving (Show1, Read1) via (Reflected1 BadTest)

type role BadTest nominal

-}

test :: Test Char
test = Test 1 'a' "bcd"

testShow :: String
testShow = show test

testShow1 :: String
testShow1 = showsPrec1 0 test ""

readStr :: String
readStr = "Test 2 'e' \"fg\"   "

testRead :: [(Test Char, String)]
testRead = readsPrec 0 readStr

testRead1 :: [(Test Char, String)]
testRead1 = readsPrec1 0 readStr

data Crest a b = Crest Int [a] [b]
    deriving (Show, Read, Eq)
    deriving (Show1, Read1) via (Reflected1 (Crest a))
    deriving (Show2, Read2) via (Reflected2 Crest)

crest :: Crest Char Bool
crest = Crest 2 "foo" [False, True]

crestShow, crestShow1, crestShow2 :: String
crestShow = show crest
crestShow1 = showsPrec1 0 crest ""
crestShow2 = showsPrec2 0 crest ""

crestReadStr :: String
crestReadStr = "Crest 3 \"foo\" [True] rest of text"

crestRead, crestRead1, crestRead2 :: [(Crest Char Bool, String)]
crestRead = readsPrec 0 crestReadStr
crestRead1 = readsPrec1 0 crestReadStr
crestRead2 = readsPrec2 0 crestReadStr

main :: IO ()
main = putStrLn . unlines $
  [ "testShow:  " ++ show testShow
  , "testShow1: " ++ show testShow1
  , "testShow == testShow1: " ++ show (testShow == testShow1)
  , ""
  , "testRead:  " ++ show testRead
  , "testRead1: " ++ show testRead1
  , "testRead == testRead1: " ++ show (testRead == testRead1)
  , ""
  , "crestShow:  " ++ show crestShow
  , "crestShow1: " ++ show crestShow1
  , "crestShow2: " ++ show crestShow2
  , "crestShow == crestShow1: " ++ show (crestShow == crestShow1)
  , "crestShow == crestShow2: " ++ show (crestShow == crestShow2)
  , ""
  , "crestRead:  " ++ show crestRead
  , "crestRead1: " ++ show crestRead1
  , "crestRead2: " ++ show crestRead2
  , "crestRead == crestRead1: " ++ show (crestRead == crestRead1)
  , "crestRead == crestRead2: " ++ show (crestRead == crestRead2)
  ]
