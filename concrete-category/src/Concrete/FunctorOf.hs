{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.FunctorOf where

import Concrete.Span
import Concrete.Category

import Concrete.Span.Compose
import Concrete.Category.Discrete

class (Function (Ob c) (Ob d) f) => FunctorOf c d f | f c -> d, f d -> c where
    fmapAt :: f a fa -> f b fb -> c a b -> d fa fb

instance (Category c, s ~ Ob c) => FunctorOf c c (Diag s) where
    fmapAt (Diag _) (Diag _) ab = ab

type Id c = Diag (Ob c)

instance (FunctorOf c d f, FunctorOf d e g) => FunctorOf c e (Compose f g) where
    fmapAt (Compose fa gfa) (Compose fb gfb) ab = fmapAt gfa gfb (fmapAt fa fb ab)