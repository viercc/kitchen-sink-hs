#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
newtype TaggedState a b c x = TaggedState x

data Done

a :: TaggedState () b c x -> TaggedState Done b c x
a = undefined

b :: TaggedState a () c x -> TaggedState a Done c x
b = undefined

c :: TaggedState Done b () x -> TaggedState Done b Done x
c = undefined

d :: TaggedState a Done Done x -> TaggedState a Done Done x
d = undefined

e :: TaggedState a b c x -> TaggedState a b c x
e = undefined

process :: TaggedState () () () x -> TaggedState Done Done Done x
process = e . d . c . b . a

anotherProcess :: TaggedState () () () x -> TaggedState Done Done Done x
anotherProcess = d . c . a . b . e

main :: IO ()
main = putStrLn "Typechecks"
