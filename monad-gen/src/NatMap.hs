{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE RoleAnnotations     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE StandaloneDeriving  #-}
module NatMap (
    NatMap(),
    size, fullSize,
    member, notMember,
    lookup,
    isTotal, toTotal,

    empty, identity,
    map1, mapMaybe1,
    fromNat, fromPartialNat,

    alter, update, adjust, insert, delete,
    alterK, updateK, adjustK, insertK,
    
    debug,
) where

import Prelude hiding (lookup)

import qualified Data.IntMap.Lazy as IM

import Data.Kind

import           Vec hiding (empty)
import           Enum1
import           Enum1.Extra


newtype NatMap (f :: Type -> Type) (g :: Type -> Type)
  = Mk (IM.IntMap (g Int))
type role NatMap nominal representational

deriving instance (Eq (g Int)) => Eq (NatMap f g)
deriving instance (Ord (g Int)) => Ord (NatMap f g)

idx :: Enum1 f => f a -> Int
idx = fromEnum1 1 (const 0)

-- Query --

size :: NatMap f g -> Int
size (Mk m) = IM.size m

fullSize :: forall f g. (Enum1 f) => NatMap f g -> Int
fullSize _ = size1 @f 1

isTotal :: (Enum1 f) => NatMap f g -> Bool
isTotal nm = size nm == fullSize nm

member, notMember :: (Enum1 f) => f a -> NatMap f g -> Bool
member fa (Mk m) = IM.member (idx fa) m
notMember fa = not . member fa

lookup :: (Enum1 f, CoEnum1 f, Functor g) => f a -> NatMap f g -> Maybe (g a)
lookup fa (Mk m) = fmap (toVec fa !) <$> IM.lookup (idx fa) m

toTotal :: (Enum1 f, CoEnum1 f, Functor g) => NatMap f g -> Maybe (f a -> g a)
toTotal nm@(Mk m) | isTotal nm = Just fg
                  | otherwise  = Nothing
  where fg fa = (toVec fa !) <$> (m IM.! idx fa)

-- Construct --
empty :: NatMap f g
empty = Mk IM.empty

identity :: (Enum1 f, Traversable f) => NatMap f f
identity = Mk . IM.fromList . toList $ indexed skolem

map1 :: (forall a. g a -> h a) -> NatMap f g -> NatMap f h
map1 gh (Mk m) = Mk (gh <$> m)

mapMaybe1 :: (forall a. g a -> Maybe (h a)) -> NatMap f g -> NatMap f h
mapMaybe1 gh' (Mk m) = Mk (IM.mapMaybe gh' m)

fromNat :: (Enum1 f, Traversable f)
        => (forall a. f a -> g a) -> NatMap f g
fromNat fg = map1 fg identity

fromPartialNat :: (Enum1 f, Traversable f)
               => (forall a. f a -> Maybe (g a)) -> NatMap f g
fromPartialNat fg' = mapMaybe1 fg' identity

-- Update --
wrapUpdator
  :: forall f g any.
     (Enum1 f, CoEnum1 f)
  => (Vec Int -> Int -> IM.IntMap (g Int) -> IM.IntMap (g Int))
  -> f any
  -> NatMap f g -> NatMap f g
wrapUpdator updator fu (Mk m) =
  let i = idx fu
      n = holeCount fu
      m' = updator (iota n) i m
  in Mk m'

alter :: forall f g any.
         (Enum1 f, CoEnum1 f)
      => (forall a. Vec a -> Maybe (g a) -> Maybe (g a))
      -> f any -> NatMap f g -> NatMap f g
alter updator = wrapUpdator $ \arg -> IM.alter (updator arg)

update :: forall f g any.
          (Enum1 f, CoEnum1 f)
       => (forall a. Vec a -> g a -> Maybe (g a))
       -> f any -> NatMap f g -> NatMap f g
update updator = wrapUpdator $ \arg -> IM.update (updator arg)

adjust :: forall f g any.
          (Enum1 f, CoEnum1 f)
       => (forall a. Vec a -> g a -> g a)
       -> f any -> NatMap f g -> NatMap f g
adjust updator = wrapUpdator $ \arg -> IM.adjust (updator arg)

insert :: forall f g any.
          (Enum1 f, CoEnum1 f)
       => (forall a. Vec a -> g a)
       -> f any -> NatMap f g -> NatMap f g
insert updator = wrapUpdator $ \arg i -> IM.insert i (updator arg)

delete :: forall f g any.
          (Enum1 f)
       => f any -> NatMap f g -> NatMap f g
delete fu (Mk m) = Mk (IM.delete (idx fu) m)

wrapUpdatorK
  :: forall f g any.
     (Enum1 f)
  => (Int -> IM.IntMap (g Int) -> IM.IntMap (g Int))
  -> f any -> NatMap f g -> NatMap f g
wrapUpdatorK updator fu (Mk m) =
  let i = idx fu
      m' = updator i m
  in Mk m'

alterK :: forall f g any.
          (Enum1 f)
       => (forall a. Maybe (g a) -> Maybe (g a))
       -> f any -> NatMap f g -> NatMap f g
alterK updator = wrapUpdatorK $ IM.alter updator

updateK :: forall f g any.
           (Enum1 f)
        => (forall a. g a -> Maybe (g a))
        -> f any -> NatMap f g -> NatMap f g
updateK updator = wrapUpdatorK $ IM.update updator

adjustK :: forall f g any.
           (Enum1 f)
        => (forall a. g a -> g a)
        -> f any -> NatMap f g -> NatMap f g
adjustK updator = wrapUpdatorK $ IM.adjust updator

insertK :: forall f g any.
           (Enum1 f)
        => (forall a. g a)
        -> f any -> NatMap f g -> NatMap f g
insertK updator = wrapUpdatorK $ \i -> IM.insert i updator

-- Debug --

debug :: forall f g.
         (Show (f Int), Show (g Int),
          Enum1 f, CoEnum1 f, Traversable f,
          Enum1 g, Functor g, Foldable g)
      => NatMap f g -> String
debug (Mk m) =
  let args = skolem @f
      strs = fmap show args
      maxLen = maximum (length <$> strs)
      mkRhs fx = validate fx <$> IM.lookup (idx fx) m
      validate fx gx = (all (\x -> 0 <= x && x < holeCount fx) gx, gx)
      prettyRhs Nothing = "undefined"
      prettyRhs (Just (v, gx)) = (if v then "" else "<invalid>") ++ show gx
      mkLine arg rhs = arg ++ replicate (maxLen - length arg) ' '
                       ++ " -> " ++ prettyRhs rhs
  in unlines . toList $ Vec.zipWith mkLine strs (mkRhs <$> args)
