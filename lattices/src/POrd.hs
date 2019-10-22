module POrd(
  POrdering(..),
  POrd(..),
  fromOrd,
  comparing
) where

import qualified Data.Set    as Set

-- | Comparison result of partial ordering
data POrdering = PLT | PEQ | PGT | PNON
  deriving (Show, Read, Eq, Ord, Enum)

fromOrd :: Ordering -> POrdering
fromOrd LT = PLT
fromOrd EQ = PEQ
fromOrd GT = PGT

-- | Combination of two partial ordering. The purpose of this instance is to
--   provide easy way to write a partial order on a product of two posets,
--   that is normally defined as:
--
-- >   (a1,a2) ⊆ (b1,b2) <=> (a1 ⊆ b1) && (a2 ⊆ b2)
--
instance Semigroup POrdering where
  (<>) PNON _   = PNON
  (<>) PEQ  y   = y
  (<>) PLT  PLT = PLT
  (<>) PLT  PEQ = PLT
  (<>) PLT  _   = PNON
  (<>) PGT PEQ  = PGT
  (<>) PGT PGT  = PGT
  (<>) PGT _    = PNON

instance Monoid POrdering where
  mempty = PEQ

-- | Partially ordered datatypes.
class Eq a => POrd a where
  pcompare :: a -> a -> POrdering
  pcompare a b =
    case (a <=? b, b <=? a) of
      (True, True)   -> PEQ
      (True, False)  -> PLT
      (False, True)  -> PGT
      (False, False) -> PNON

  comparable :: a -> a -> Bool
  comparable a b = not (nonComparable a b)

  nonComparable :: a -> a -> Bool
  nonComparable a b = pcompare a b == PNON

  (<=?),(<?),(>=?),(>?) :: a -> a -> Bool
  a <=? b = case pcompare a b of
    PEQ -> True
    PLT -> True
    _   -> False
  a <? b = pcompare a b == PLT
  a >=? b = b <=? a
  a >? b = b <? a

  {-# MINIMAL pcompare | (<=?) #-}

comparing :: (POrd b) => (a -> b) -> (a -> a -> POrdering)
comparing f x y = pcompare (f x) (f y)

-- | Partial ordering of Sets based on subset relation.
instance Ord a => POrd (Set.Set a) where
  pcompare as bs =
    case compare (Set.size as) (Set.size bs) of
      LT -> if Set.isSubsetOf as bs then PLT else PNON
      GT -> if Set.isSubsetOf bs as then PGT else PNON
      EQ -> if as == bs then PEQ else PNON
  (<=?) = Set.isSubsetOf
  (<?) = Set.isProperSubsetOf

-- | Product poset.
instance (POrd a, POrd b) => POrd (a, b) where
  pcompare (x1,x2) (y1,y2) = pcompare x1 y1 <> pcompare x2 y2
  (x1,x2) <=? (y1,y2) = x1 <=? y1 && x2 <=? y2

instance (POrd a, POrd b, POrd c) => POrd (a,b,c) where
  pcompare (x1,x2,x3) (y1,y2,y3) =
    pcompare x1 y1 <> pcompare x2 y2 <> pcompare x3 y3
  (x1,x2,x3) <=? (y1,y2,y3) = x1 <=? y1 && x2 <=? y2 && x3 <=? y3
