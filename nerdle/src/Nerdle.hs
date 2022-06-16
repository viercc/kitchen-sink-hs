
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
module Nerdle where

import Control.Applicative (liftA2, Alternative (..))
import Data.Ratio

import Data.Functor.Rep

import Control.Monad (guard)

import Util
import Digit

data NerdleChar = Digit !Digit | Equal | Plus | Minus | Mult | Divide
  deriving (Show, Read, Eq, Ord)

printNerdleChar :: NerdleChar -> Char
printNerdleChar nc = case nc of
    Digit d -> printDigit d
    Equal -> '='
    Plus -> '+'
    Minus -> '-'
    Mult -> '*'
    Divide -> '/'

readNerdleChar :: Char -> Maybe NerdleChar
readNerdleChar c = case c of
    '=' -> Just Equal
    '+' -> Just Plus
    '-' -> Just Minus
    '*' -> Just Mult
    '/' -> Just Divide
    _   -> Digit <$> charToDigit c

data EvalResult = ParseError | FalseEquation | TrueEquation
  deriving (Show, Read, Eq, Ord)

evalEquation :: [NerdleChar] -> EvalResult
evalEquation input = case liftA2 (==) lhsEval rhsEval of
  Nothing -> ParseError
  Just False -> FalseEquation
  Just True  -> TrueEquation
  where
    (lhsStr, rhsStr) = span (/= Equal) input
    lhsEval = evalExpr lhsStr >>= exactInteger
    rhsEval = case rhsStr of
      (Equal : rhsStr') -> evalInt rhsStr'
      _ -> Nothing

evalInt :: [NerdleChar] -> Maybe Integer
evalInt = fmap decimalValue . traverse digitOnly
  where
    digitOnly (Digit d) = Just d
    digitOnly _ = Nothing

evalExpr :: [NerdleChar] -> Maybe Rational
evalExpr = go []
  where
    go stack [] = case reduce stack of
      Just [Left y] -> Just y
      _ -> Nothing
    go stack (Digit d : rest) = case stack of
      Left x : stack' -> go (Left (10 * x + toQ d) : stack') rest
      _               -> go (Left (toQ d) : stack) rest
    go stack (Plus : rest) = reduce stack >>= \stack' -> go (Right Plus : stack') rest
    go stack (Minus : rest) = reduce stack >>= \stack' -> go (Right Minus : stack') rest
    go stack (Mult : rest) = reduceMulDiv stack >>= \stack' -> go (Right Mult : stack') rest
    go stack (Divide : rest) = reduceMulDiv stack >>= \stack' -> go (Right Divide : stack') rest
    go _ (Equal : _) = Nothing

    toQ = toRational . unDec

    reduce stack = case stack of
      [Left y] -> Just [Left y]
      Left y : Right Plus   : Left x : rest -> reduce (Left (x + y) : rest)
      Left y : Right Minus  : Left x : rest -> reduce (Left (x - y) : rest)
      Left y : Right Mult   : Left x : rest -> reduce (Left (x * y) : rest)
      Left y : Right Divide : Left x : rest | y /= 0 -> reduce (Left (x / y) : rest)
      _ -> Nothing

    reduceMulDiv stack = case stack of
      Left y : Right Mult   : Left x : rest -> reduceMulDiv (Left (x * y) : rest)
      Left y : Right Divide : Left x : rest | y /= 0    -> reduceMulDiv (Left (x / y) : rest)
                                            | otherwise -> Nothing
      Left _ : _ -> Just stack
      _ -> Nothing

exactInteger :: Rational -> Maybe Integer
exactInteger x | denominator x == 1 = Just $ numerator x
               | otherwise          = Nothing

printNerdleWord :: (Foldable t) => t NerdleChar -> String
printNerdleWord = foldMap (pure . printNerdleChar)

readNerdleWord :: String -> Maybe [NerdleChar]
readNerdleWord str =
  do str' <- traverse readNerdleChar str
     guard $ evalEquation str' == TrueEquation
     pure str'

enumDigits :: Int -> [[Digit]]
enumDigits n
  | n <= 0 = []
  | otherwise = sequenceA $ nonZeroDigits : replicate (n-1) digits
  where
    nonZeroDigits = toEnum <$> [1 .. 9]
    digits = toEnum <$> [0 .. 9]

enumNerdleExpr :: Int -> [[NerdleChar]]
enumNerdleExpr n
  | n <= 0    = []
  | n <= 2    = fmap Digit <$> enumDigits n
  | otherwise = {- n >= 3 -}
      (fmap Digit <$> enumDigits n) <|> oneOp
      where
        oneOp = do
          i <- [1 .. n - 2]
          x <- enumDigits i
          op <- [Plus, Minus, Mult, Divide]
          y <- enumNerdleExpr (n - i - 1)
          pure $ fmap Digit x ++ op : y

enumNerdleWord :: forall v. (Traversable v, Representable v) => [v NerdleChar]
enumNerdleWord = do
  xLen <- [3 .. n - 2]
  x <- enumNerdleExpr xLen
  Just y <- [ evalExpr x >>= exactInteger >>= traverse charToDigit . show ]
  -- the above line also eliminates y < 0 since (show y)
  -- produces string containing negative sign
  Just ans <- [repFromList (x ++ Equal : fmap Digit y)]
  pure ans
  where n = length (pureRep @v ())

