{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE DerivingVia #-}
module LatticeLike(
  Zippable(..),
  Align(..),
  LatticeLike,
  Top(..),
  Bottom(..),

  Threeway(..),
  Pentagon(..),
  R(..),

  checkLatticeLike, checkZipUnit, checkAlignUnit,
  main
) where

import           Prelude               hiding (repeat, zip)
import qualified Prelude

import           Control.Applicative

import qualified Data.Align            as Al
import           Data.Functor.Classes
import           Data.These
import           Data.Maybe (mapMaybe)
import qualified Data.Foldable         as F

import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Functor.Compose
import           Data.Functor.Identity
import           Data.Functor.Product

import           Data.Tuple            (swap)
import           Data.Proxy

import AutoLift

import Test.QuickCheck

class (Functor f) => Zippable f where
  zip :: f a -> f b -> f (a,b)
  {-
     [zipIdempotence] @zip x x = fmap (\a -> (a,a)) x@
     [zipAssociative] @zip x (zip y z) = fmap assoc' $ zip (zip x y) z@
     [zipCommutative] @zip x y = fmap swap $ zip y x@
  -}

class (Functor f) => Align f where
  align :: f a -> f b -> f (These a b)
  {-
     [alignIdempotence] @align x x = fmap (\a -> These a a) x@
     [alignAssociative] @align x (align y z) = fmap assocT' $ align (align x y) z@
     [alignCommutative] @align x y = fmap swapT $ align y x@
   -}

class (Zippable f, Align f) => LatticeLike f
  {-
     [Absorption1] @fmap fst  $ zip x (align x y) = x@
     [Absorption2] @fmap fstT $ align x (zip x y) = fmap Just x@
  -}

class (Zippable f) => Top f where
  repeat :: a -> f a
  -- [zipUnit] @zip (repeat a) x = fmap (a,) x@

class (Align f) => Bottom f where
  nil :: f a
  -- [alignUnit] @align nil x = fmap That x@

assoc :: (a,(b,c)) -> ((a,b),c)
assoc (a,(b,c)) = ((a,b),c)

swapT :: These a b -> These b a
swapT (This a)    = That a
swapT (That b)    = This b
swapT (These a b) = These b a

assocT :: These a (These b c) -> These (These a b) c
assocT a_bc = case a_bc of
  This a -> This (This a)
  That bc -> case bc of
    This b    -> This (That b)
    That c    -> That c
    These b c -> These (That b) c
  These a bc -> case bc of
    This b    -> This (These a b)
    That c    -> These (This a) c
    These b c -> These (These a b) c

fstT :: These a b -> Maybe a
fstT (This a)    = Just a
fstT (That _)    = Nothing
fstT (These a _) = Just a

sndT :: These a b -> Maybe b
sndT = fstT . swapT

---- Instances ----

instance Zippable Maybe where zip = liftA2 (,)
instance Align Maybe    where align = Al.align
instance LatticeLike Maybe
instance Top Maybe      where  repeat = Just
instance Bottom Maybe   where  nil = Nothing

instance Zippable [] where zip = Prelude.zip
instance Align []    where align = Al.align
  -- ^ If you change @Al.align@ to @badAlign@, it does not pass
  --   laws test
instance LatticeLike []
instance Top []      where repeat = Prelude.repeat
instance Bottom []   where nil = []

badAlign :: [a] -> [b] -> [These a b]
badAlign [] bs = That <$> bs
badAlign as [] = This <$> as
badAlign as bs = zipWith These as bs

instance Zippable Identity where zip = liftA2 (,)
instance Align Identity    where align = liftA2 These
instance LatticeLike Identity
instance Top Identity      where repeat = Identity

instance Zippable ((->) e) where zip = liftA2 (,)
instance Align ((->) e)    where align = liftA2 These
instance LatticeLike ((->) e)
instance Top ((->) e)      where repeat = const


instance (Ord k) => Zippable (Map k) where zip = Map.intersectionWith (,)
instance (Ord k) => Align (Map k)    where align = Al.align
instance (Ord k) => LatticeLike (Map k)
instance (Ord k) => Bottom (Map k)   where nil = Map.empty

instance (Zippable f, Zippable g) => Zippable (Product f g) where
  zip (Pair fa ga) (Pair fb gb) = Pair (zip fa fb) (zip ga gb)

instance (Align f, Align g) => Align (Product f g) where
  align (Pair fa ga) (Pair fb gb) = Pair (align fa fb) (align ga gb)

instance (LatticeLike f, LatticeLike g) => LatticeLike (Product f g)

instance (Top f, Top g) => Top (Product f g) where
  repeat a = Pair (repeat a) (repeat a)

instance (Bottom f, Bottom g) => Bottom (Product f g) where
  nil = Pair nil nil


instance (Zippable f, Zippable g) => Zippable (Compose f g) where
  zip (Compose fga) (Compose fgb) =
    Compose $ uncurry zip <$> zip fga fgb

instance (Align f, Align g) => Align (Compose f g) where
  align (Compose fga) (Compose fgb) =
    Compose $ alignT <$> align fga fgb
      where
        alignT (This ga)     = This <$> ga
        alignT (That gb)     = That <$> gb
        alignT (These ga gb) = align ga gb

instance (LatticeLike f, LatticeLike g) => LatticeLike (Compose f g)

instance (Top f, Top g) => Top (Compose f g) where
  repeat a = Compose (repeat (repeat a))

instance (Bottom f, Align g) => Bottom (Compose f g) where
  nil = Compose nil

{- |

>   Two
>    |
>   One
>    |
>   None

-}

data Threeway a = None | One a | Two a a
  deriving (Show, Eq, Functor, Foldable, Traversable)
  deriving Show1 via (Reflected1 Threeway)

instance Zippable Threeway where
  zip None       _          = None
  zip _          None       = None
  zip (One a)    (One b)    = One (a,b)
  zip (One a)    (Two b _)  = One (a,b)
  zip (Two a _)  (One b)    = One (a,b)
  zip (Two a a') (Two b b') = Two (a,b) (a',b')

instance Align Threeway where
  align None      y           = fmap That y
  align x         None        = fmap This x
  align (One a)   (One b)     = One (These a b)
  align (One a)   (Two b b')  = Two (These a b) (That b')
  align (Two a a') (One b)    = Two (These a b) (This a')
  align (Two a a') (Two b b') = Two (These a b) (These a' b')

instance LatticeLike Threeway

instance Top Threeway where
  repeat a = Two a a

instance Bottom Threeway where
  nil = None

instance Eq1 Threeway where
  liftEq _ None None = True
  liftEq eqV (One a) (One b) = eqV a b
  liftEq eqV (Two a a') (Two b b') = eqV a b && eqV a' b'
  liftEq _ _ _ = False

instance Arbitrary a => Arbitrary (Threeway a) where
  arbitrary = arbitrary1
  shrink = shrink1

instance Arbitrary1 Threeway where
  liftArbitrary g = oneof [pure None, One <$> g, Two <$> g <*> g]
  liftShrink _ None = []
  liftShrink s (One a) = One <$> s a
  liftShrink s (Two a a') = (Two a <$> s a') ++ (Two <$> s a <*> pure a')

{- |

>    D4
>   /  \
>   |  D3
>   |  |
>   D1 D2
>   \  /
>    D0

-}

data Pentagon a = D0 | D1 a | D2 a | D3 a | D4 a a
  deriving (Show, Eq, Functor, Foldable, Traversable)
  deriving (Show1) via (Reflected1 Pentagon)

instance Zippable Pentagon where
  zip D0        _         = D0
  zip _         D0        = D0
  zip (D1 a)    (D1 b)    = D1 (a,b)
  zip (D2 _)    (D1 _)    = D0
  zip (D2 a)    (D2 b)    = D2 (a,b)
  zip (D3 _)    (D1 _)    = D0
  zip (D3 a)    (D2 b)    = D2 (a,b)
  zip (D3 a)    (D3 b)    = D3 (a,b)
  zip (D4 a _)  (D1 b)    = D1 (a,b)
  zip (D4 _ a)  (D2 b)    = D2 (a,b)
  zip (D4 _ a)  (D3 b)    = D3 (a,b)
  zip (D4 a a') (D4 b b') = D4 (a,b) (a',b')
  zip x y                 = swap <$> zip y x


instance Align Pentagon where
  align D0        y         = That <$> y
  align x         D0        = This <$> x
  
  align (D1 a)    (D1 b)    = D1 (These a b)
  align (D1 a)    (D2 b)    = D4 (This a) (That b)
  align (D1 a)    (D3 b)    = D4 (This a) (That b)
  align (D1 a)    (D4 b b') = D4 (These a b) (That b')

  align (D2 a)    (D1 b)    = D4 (That b) (This a)
  align (D2 a)    (D2 b)    = D2 (These a b)
  align (D2 a)    (D3 b)    = D3 (These a b)
  align (D2 a)    (D4 b b') = D4 (That b) (These a b')
  
  align (D3 a)    (D1 b)    = D4 (That b) (This a)
  align (D3 a)    (D2 b)    = D3 (These a b)
  align (D3 a)    (D3 b)    = D3 (These a b)
  align (D3 a)    (D4 b b') = D4 (That b) (These a b')
  
  align (D4 a a') (D1 b)    = D4 (These a b) (This a')
  align (D4 a a') (D2 b)    = D4 (This a) (These a' b)
  align (D4 a a') (D3 b)    = D4 (This a) (These a' b)
  align (D4 a a') (D4 b b') = D4 (These a b) (These a' b')

instance LatticeLike Pentagon

instance Top Pentagon where
  repeat a = D4 a a

instance Bottom Pentagon where
  nil = D0

instance Eq1 Pentagon where
  liftEq _ D0 D0 = True
  liftEq eqV (D1 a) (D1 b) = eqV a b
  liftEq eqV (D2 a) (D2 b) = eqV a b
  liftEq eqV (D3 a) (D3 b) = eqV a b
  liftEq eqV (D4 a a') (D4 b b') = eqV a b && eqV a' b'
  liftEq _ _ _ = False

instance Arbitrary a => Arbitrary (Pentagon a) where
  arbitrary = arbitrary1
  shrink = shrink1

instance Arbitrary1 Pentagon where
  liftArbitrary g = oneof [pure D0
                        , D1 <$> g
                        , D2 <$> g
                        , D3 <$> g
                        , D4 <$> g <*> g]
  liftShrink _ D0 = []
  liftShrink s (D1 a) = D1 <$> s a
  liftShrink s (D2 a) = D2 <$> s a
  liftShrink s (D3 a) = D3 <$> s a
  liftShrink s (D4 a a') = (D4 a <$> s a') ++ (D4 <$> s a <*> pure a')

newtype R a = Nest [[a]]
  deriving (Show, Eq, Functor, Foldable, Traversable)
  deriving (Show1) via (Reflected1 R)

instance Zippable R where
  zip (Nest ass) (Nest bss) = Nest $ zipR ass bss
    where
      zipR []   _     = []
      zipR _    []    = []
      zipR [xs] [ys]  = [zip xs ys]
      zipR xss  [ys] | sum (length <$> xss) <= length ys = aux xss ys
      zipR [xs] yss  | sum (length <$> yss) <= length xs = fmap (fmap swap) (aux yss xs)
      zipR xss  yss  | shape xss == shape yss            = zipWith zip xss yss
                     | otherwise                         = []
      
      shape = fmap length
      aux [] _ = []
      aux ([]:xss) ys = [] : aux xss ys
      aux ((x:xs):xss) ys =
        case ys of
          [] -> error "Should never happen!"
          (y:ys') -> case aux (xs:xss) ys' of
            [] -> error "Should never happen!"
            (zs:zss) -> ((x,y):zs):zss

instance Align R where
  align (Nest ass) (Nest bss)
    | null ass                = That <$> Nest bss
    | null bss                = This <$> Nest ass
    | shape ass == shape bss  = Nest $ zipWith (zipWith These) ass bss
    | otherwise               = Nest [align (concat ass) (concat bss)] 
    where
      shape = fmap (() <$)

instance LatticeLike R

instance Bottom R where
  nil = Nest []

instance Eq1 R where
  liftEq eq (Nest ass) (Nest bss) = liftEq (liftEq eq) ass bss

instance Arbitrary a => Arbitrary (R a) where
  arbitrary = arbitrary1
  shrink = shrink1

instance Arbitrary1 R where
  liftArbitrary gen = Nest <$>
    (scale sqrti $ liftArbitrary (liftArbitrary gen))
  liftShrink s (Nest ass) = Nest <$> liftShrink (liftShrink s) ass

sqrti :: Int -> Int
sqrti = round . (sqrt :: Double -> Double) . fromIntegral

---- Checks ----

propIdempotenceP
  :: forall f. (Zippable f,
                forall a. Show a => Show (f a),
                forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> Property
propIdempotenceP _ xs = zip xs xs === fmap (\x -> (x, x)) xs

propCommutativeP
  :: forall f. (Zippable f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> f Int -> Property
propCommutativeP _ xs ys = zip xs ys === fmap swap (zip ys xs)

propAssociativeP
  :: forall f. (Zippable f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> f Int -> f Char -> Property
propAssociativeP _ xs ys zs =
  fmap assoc (zip xs (zip ys zs)) === zip (zip xs ys) zs

propUnitP
  :: forall f. (Top f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> Int -> f Bool -> Property
propUnitP _ a xs = zip (repeat a) xs === fmap ((,) a) xs

propIdempotenceT
  :: forall f. (Align f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> Property
propIdempotenceT _ xs = align xs xs === fmap (\x -> These x x) xs

propCommutativeT
  :: forall f. (Align f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> f Int -> Property
propCommutativeT _ xs ys = align xs ys === fmap swapT (align ys xs)

propAssociativeT
  :: forall f. (Align f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> f Int -> f Char -> Property
propAssociativeT _ xs ys zs =
  fmap assocT (align xs (align ys zs)) === align (align xs ys) zs

propUnitT
  :: forall f. (Bottom f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> Property
propUnitT _ xs = align (nil :: f ()) xs === fmap That xs


propAbsorptionPT
  :: forall f. (LatticeLike f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> f Int -> Property
propAbsorptionPT _ xs ys = (fst <$> zip xs (align xs ys)) === xs

propAbsorptionTP
  :: forall f. (LatticeLike f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Bool -> f Int -> Property
propAbsorptionTP _ xs ys = (fstT <$> align xs (zip xs ys)) === (Just <$> xs)

propAlignToList
  :: forall f. (Align f, Foldable f, forall a. Show a => Show (f a), forall a. Eq a => Eq (f a))
  => Proxy f -> f Int -> f Int -> Property
propAlignToList _ xs ys =
  let xys = align xs ys
  in (F.toList xs === mapMaybe fstT (F.toList xys))
     .&&.
     (F.toList ys === mapMaybe sndT (F.toList xys))

qc :: Testable prop => prop -> IO ()
qc = quickCheckWith stdArgs{ maxSuccess = 500, maxSize = 100 }

checkLatticeLike
  :: forall f. (LatticeLike f
               , Foldable f
               , forall a. Show a => Show (f a)
               , forall a. Eq a => Eq (f a)
               , forall a. Arbitrary a => Arbitrary (f a))
  => Proxy f -> IO ()
checkLatticeLike al =
  do putStr "<zipIdempotence> "
     qc $ propIdempotenceP al
     putStr "<zipCommutative> "
     qc $ propCommutativeP al
     putStr "<zipAssociative> "
     qc $ propAssociativeP al
     
     putStr "<alignIdempotence> "
     qc $ propIdempotenceT al
     putStr "<alignCommutative> "
     qc $ propCommutativeT al
     putStr "<alignAssociative> "
     qc $ propAssociativeT al

     putStr "<absorptionPT> "
     qc $ propAbsorptionPT al
     putStr "<absorptionTP> "
     qc $ propAbsorptionTP al

     putStr "<alignToList> "
     qc $ propAlignToList al

checkZipUnit 
  :: forall f. (Top f
               , forall a. Show a => Show (f a)
               , forall a. Eq a => Eq (f a)
               , forall a. Arbitrary a => Arbitrary (f a))
  => Proxy f -> IO ()
checkZipUnit al =
  do putStr "<zipUnit>"
     qc $ propUnitP al

checkAlignUnit 
  :: forall f. (Bottom f
               , forall a. Show a => Show (f a)
               , forall a. Eq a => Eq (f a)
               , forall a. Arbitrary a => Arbitrary (f a))
  => Proxy f -> IO ()
checkAlignUnit al =
  do putStr "<alignUnit>"
     qc $ propUnitT al

------

main :: IO ()
main = do
  putStrLn "### Maybe ###"
  checkLatticeLike (Proxy :: Proxy Maybe)
  checkZipUnit (Proxy :: Proxy Maybe)
  checkAlignUnit (Proxy :: Proxy Maybe)
  putStrLn "### [] ###"
  checkLatticeLike (Proxy :: Proxy [])
  checkZipUnit (Proxy :: Proxy [])
  checkAlignUnit (Proxy :: Proxy [])
  putStrLn "### Map Int ###"
  checkLatticeLike (Proxy :: Proxy (Map Int))
  checkAlignUnit (Proxy :: Proxy (Map Int))
  putStrLn "### Product Maybe [] ###"
  checkLatticeLike (Proxy :: Proxy (Product Maybe []))
  checkZipUnit (Proxy :: Proxy (Product Maybe []))
  checkAlignUnit (Proxy :: Proxy (Product Maybe []))
  putStrLn "### Compose [] Maybe ###"
  checkLatticeLike (Proxy :: Proxy (Compose [] Maybe))
  checkZipUnit (Proxy :: Proxy (Compose [] Maybe))
  checkAlignUnit (Proxy :: Proxy (Compose [] Maybe))
  putStrLn "### Threeway ###"
  checkLatticeLike (Proxy :: Proxy Threeway)
  checkZipUnit (Proxy :: Proxy Threeway)
  checkAlignUnit (Proxy :: Proxy Threeway)
  putStrLn "### Pentagon ###"
  checkLatticeLike (Proxy :: Proxy Pentagon)
  checkZipUnit (Proxy :: Proxy Pentagon)
  checkAlignUnit (Proxy :: Proxy Pentagon)
  putStrLn "### R ###"
  checkLatticeLike (Proxy :: Proxy R)
  checkAlignUnit (Proxy :: Proxy R)

