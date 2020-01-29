{-# LANGUAGE PackageImports #-}
module Main where

-- -- This is error now.
-- import Clash

-- On the other hand, this seems OK;
import "mix-a" Clash  -- exports (Foo(..), foo)
import "mix-b" Clash  -- exports (Bar(..), bar)

-- -- Importing from "mix-c" makes @foo@ ambiguous, but GHC
-- -- correctly rejects to compile.
-- import "mix-c" Clash as Clash -- exports (Foo(..), foo)

main :: IO ()
main = do putStrLn foo
          putStrLn bar

{-

Then I got curious: is it OK to automatically translate

  import Clash

into

  import "mix-a" Clash
  import "mix-b" Clash
  import "mix-c" Clash

???

(1) Do this as a default, provide flag to warn.
(2) Do this as a default, provide flag to warn, and that warning is on by default.
(3) Do this only when enabled via a language extension pragma.
(4) Do this only when syntactically indicated, like this:

  import "*" Clash

-}
