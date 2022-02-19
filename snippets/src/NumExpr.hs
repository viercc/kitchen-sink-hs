{-# LANGUAGE RankNTypes #-}
module NumExpr where

isNegate :: (forall a. Num a => a -> a) -> Bool
isNegate f = f (Var "x") == Fun "negate" [Var "x"]

data Expr = Var String | Literal Integer | Fun String [Expr]
    deriving (Eq, Show)

instance Num Expr where
    fromInteger = Literal
    a + b = Fun "+" [a,b]
    a - b = Fun "-" [a,b]
    -- etc.
    negate a = Fun "negate" [a]
