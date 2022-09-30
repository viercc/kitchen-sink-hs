module Nerdle where

import Control.Applicative (liftA2, Alternative (..))
import Data.Ratio

import Control.Monad (guard)
import Digit

data NerdleChar d = Digit !d | Equal | Plus | Minus | Mult | Divide
  deriving (Show, Read, Eq, Ord)

printNerdleChar :: Digit d => NerdleChar d -> Char
printNerdleChar nc = case nc of
    Digit d -> digitToChar d
    Equal -> '='
    Plus -> '+'
    Minus -> '-'
    Mult -> '*'
    Divide -> '/'

readNerdleChar :: Digit d => Char -> Maybe (NerdleChar d)
readNerdleChar c = case c of
    '=' -> Just Equal
    '+' -> Just Plus
    '-' -> Just Minus
    '*' -> Just Mult
    '/' -> Just Divide
    _   -> Digit <$> charToDigit c

data EvalResult = ParseError | FalseEquation | TrueEquation
  deriving (Show, Read, Eq, Ord)

evalEquation :: Digit d => [NerdleChar d] -> EvalResult
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

evalInt :: Digit d => [NerdleChar d] -> Maybe Integer
evalInt = fmap digitsValue . traverse digitOnly
  where
    digitOnly (Digit d) = Just d
    digitOnly _ = Nothing

spanDigits :: [NerdleChar d] -> ([d], [NerdleChar d])
spanDigits [] = ([], [])
spanDigits (c:rest) = case c of
  Digit d -> case spanDigits rest of
    ~(ds, rest') -> (d:ds, rest')
  _ -> ([], c:rest)

evalExpr :: Digit d => [NerdleChar d] -> Maybe Rational
evalExpr = go []
  where
    go stack [] = case reduce stack of
      Just [Left y] -> Just y
      _ -> Nothing
    go stack (Digit d : rest) = case spanDigits rest of
      (ds, rest') -> go (Left (toQ (d:ds)) : stack) rest'
    go stack (Plus : rest) = reduce stack >>= \stack' -> go (Right Plus : stack') rest
    go stack (Minus : rest) = reduce stack >>= \stack' -> go (Right Minus : stack') rest
    go stack (Mult : rest) = reduceMulDiv stack >>= \stack' -> go (Right Mult : stack') rest
    go stack (Divide : rest) = reduceMulDiv stack >>= \stack' -> go (Right Divide : stack') rest
    go _ (Equal : _) = Nothing

    toQ = toRational . digitsValue

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

printNerdleWord :: (Foldable t, Digit d) => t (NerdleChar d) -> String
printNerdleWord = foldMap (pure . printNerdleChar)

readNerdleWord :: Digit d => String -> Maybe [NerdleChar d]
readNerdleWord str =
  do str' <- traverse readNerdleChar str
     guard $ evalEquation str' == TrueEquation
     pure str'

enumDigits :: Digit d => Int -> [[d]]
enumDigits n
  | n <= 0 = []
  | otherwise = sequenceA $ nonZeroDigits : replicate (n-1) allDigits
  where
    nonZeroDigits = drop 1 allDigits

enumNerdleExpr :: Digit d => Int -> [[NerdleChar d]]
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

enumNerdleWord :: Digit d => Int -> [[NerdleChar d]]
enumNerdleWord n = do
  xLen <- [3 .. n - 2]
  x <- enumNerdleExpr xLen
  Just yVal <- [ evalExpr x >>= exactInteger ]
  guard (yVal >= 0)
  let y = integerToDigits yVal
  -- the above line also eliminates y < 0 since (show y)
  -- produces string containing negative sign
  guard $ xLen + 1 + length y == n
  pure (x ++ Equal : fmap Digit y)
