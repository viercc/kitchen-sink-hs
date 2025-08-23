{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeOperators #-}

-- | Regular languages
module Lang.RegularExpression where

import Data.String (IsString(..))

data Expr c = Lit c | Union [Expr c] | Concat [Expr c] | Star (Expr c)
  deriving (Show, Eq, Ord)

instance (c ~ Char) => IsString (Expr c) where
  fromString = Concat . fmap Lit
