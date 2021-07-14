{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneKindSignatures #-}
{-# LANGUAGE GADTs #-}
module CoerceUnder where

import Data.Coerce
import Data.Type.Coercion
import Data.Proxy
import Data.List (elemIndex)

newtype Foo = Foo Int
newtype Bar = Bar [Int]
newtype Myb a = Myb (Maybe a)

example :: Bar -> [Foo]
example = wrapBy (rule Foo & rule Bar & nil) reverse

example2 :: Foo -> Bar -> Myb Foo
example2 = wrapBy (rule Foo & rule Bar & rule1 Myb & nil) elemIndex

-- Interfaces

rule :: Coercible n o => (o -> n) -> Proxy (n ':-- o)
rule _ = Proxy

rule1 :: Coercible f g => (f a -> g a') -> Proxy (g ':-- f)
rule1 _ = Proxy

nil :: Proxy '[]
nil = Proxy

(&) :: Proxy a -> Proxy as -> Proxy (a ': as)
(&) _ _ = Proxy

infixr 6 &

unwrappingCoercion :: (Coercible s (ApplyRules r s)) => Proxy r -> Coercion s (ApplyRules r s)
unwrappingCoercion _ = Coercion

unwrapBy :: (Coercible s t, t ~ ApplyRules r s) => Proxy r -> s -> t
unwrapBy p = coerceWith (unwrappingCoercion p)

wrapBy :: (Coercible s t, t ~ ApplyRules r s) => Proxy r -> t -> s
wrapBy p = coerceWith (sym (unwrappingCoercion p))

data Rule where
    (:--) :: k -> k -> Rule

type ApplyRules r s = ApplyRulesImpl r r s
type ApplyRulesImpl :: [Rule] -> [Rule] -> k -> k
type family ApplyRulesImpl r r' s where
    ApplyRulesImpl r (n ':-- o ': rest) n = ApplyRulesImpl r r o
    ApplyRulesImpl r (_        ': rest) s = ApplyRulesImpl r rest s
    ApplyRulesImpl r '[] (s1 s2) = (ApplyRulesImpl r r s1) (ApplyRulesImpl r r s2)
    ApplyRulesImpl r '[] s = s
