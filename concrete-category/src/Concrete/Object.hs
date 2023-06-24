{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeOperators #-}
module Concrete.Object where

import Data.Proxy
import Data.Kind
import Data.Type.Equality ((:~:)(..))

type IsObject :: (k -> Type) -> k -> Constraint
class IsObject s a where
    isObject :: s a

instance IsObject Proxy a where
    isObject = Proxy

instance (a ~ b) => IsObject ((:~:) a) b where
    isObject = Refl
