{-# LANGUAGE PolyKinds #-}
-- | Writes "fake proof" of equalities between Haskell expressions.
--
--   It doesn't actually check the validity of the proof,
--   but it helps the compiler automatically checks for silly mistakes like
--   
--   - The expressions around @===@ are not well-formed
--   - Variable occurs without a definition
--   - Types of two expressions around @===@ don't match
module FakeProof(
  Equality(),
  proof,
  (===), byUsing,

  -- * Example
  exampleProof
) where

-- | Type of "fake proof" of equalities between @a@.
data Equality a = Equality -- ^ Do not export this constructor
  deriving Show

proof :: a -> Equality a
proof _ = Equality

infixr 1 ===
(===) :: a -> a -> a
(===) = const

infix 3 `byUsing`
byUsing :: a -> Equality b -> a
byUsing = const

-- * Example

-- |
--
-- > reverse (xs ++ ys) === reverse ys ++ reverse xs
exampleProof :: [a] -> [a] -> Equality [a]
exampleProof xs ys = proof $
  case xs of
    [] ->
          reverse ([] ++ ys) 
      === reverse ys
      === reverse ys ++ []
      === reverse ys ++ reverse []
    (x:xs') ->
          reverse ((x:xs') ++ ys)
      === reverse (x : xs' ++ ys)
      === reverse (xs' ++ ys) ++ [x]
      === (reverse ys ++ reverse xs') ++ [x] `byUsing` exampleProof xs' ys
      === reverse ys ++ (reverse xs' ++ [x])
      === reverse ys ++ (reverse (x:xs'))