{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Selective.Prism where

import Data.Bifunctor
import Control.Selective
import Control.Lens.Prism hiding (aside)

swapE :: Either a b -> Either b a
swapE = either Right Left

aside :: (Selective f) => f (Either c a) -> f (a -> b) -> f (Either c b)
aside f_cORa f_ab = select (second Left . swapE <$> f_cORa) (fmap Right <$> f_ab)

select' :: (Selective f) => f (Either a b) -> f (a -> b) -> f b
select' f_aORb f_ab = either id id <$> aside (swapE <$> f_aORb) f_ab

{-

select' f_aORb f_ab
 = either id id <$> aside (swapE <$> f_aORb) f_ab
 = either id id <$> select (second Left . swapE <$> swapE <$> f_aORb) (fmap Right <$> f_ab)
 = either id id <$> select (second Left <$> f_aORb) (fmap Right <$> f_ab)
   -- free theorem
 = select (second (either id id . Left) <$> f_aORb) (fmap (either id id . Left) <$> f_ab)
 = select (second id                    <$> f_aORb) (fmap id                    <$> f_ab)
 = select f_aORb f_ab

aside' f_cORa f_ab
 = select' (second Left . swapE <$> f_cORa) (fmap Right <$> f_ab)
 = either id id <$> aside (swapE . second Left . swapE <$> f_aORc) (fmap Right <$> f_ab)
 = either id id <$> aside (first Left  . swapE . swapE <$> f_aORc) (fmap Right <$> f_ab)
   -- free theorem
 = either id id . bimap Left Right <$> aside f_aORc f_ab
 = either Left Right <$> aside f_aORc f_ab
 = aside f_aORc f_ab

-}

underS :: forall f s t a b.
          (Selective f)
       => APrism s t a b
       -> f s -> f (a -> b) -> f t
underS pr fs fab = withPrism pr k
  where
    k :: (b -> t) -> (s -> Either t a) -> f t
    k inject_b match_s = either id inject_b <$> aside (match_s <$> fs) fab

aside' :: Selective f => f (Either c a) -> f (a -> b) -> f (Either c b)
aside' f_cORa f_ab = underS _Right f_cORa f_ab

{-

aside' f_cORa f_ab
 = underS _Right f_cORa f_ab
 = withPrism _Right f_cORa f_ab
 = either id inject_b <$> aside (match_s <$> f_cORa) f_ab
     where inject_b :: b -> Either c b
           inject_b = Right
           match_s  :: Either c a -> Either (Either c b) a
           match_s = first Left
 = either id Right <$> aside (first Left <$> f_cORa) f_ab
   -- Naturality
 = either Left Right <$> aside f_cORa f_ab
 = aside f_cORa f_ab

underS' pr fs fab
 = either id inject_b <$> aside' (match_s <$> fs) fab
     where pr = prism inject_b match_s
 = either id inject_b <$> underS _Right (match_s <$> fs) fab
 = either id inject_b <$> underS (prism Right (first Left)) (match_s <$> fs) fab
   -- Free theorem (DUBIOUS; CHECK LATER)
 = underS (prism (either id inject_b . Right) (first (either id inject_b) . first Left . match_s)) fs fab
 = underS (prism inject_b (first id . match_s)) fs fab
 = underS (prism inject_b match_s) fs fab
 = underS pr fs fab

-}
