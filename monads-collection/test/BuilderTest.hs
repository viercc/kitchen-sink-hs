{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE BangPatterns #-}
module Main where

import Control.Monad
import Control.Monad.State

import Monad.Builder

-- Makeshift lens

type Lens' o a = forall f. (Functor f) => (a -> f a) -> o -> f o

lens' :: (o -> a) -> (o -> a -> o) -> Lens' o a
lens' getter setter upd = \o -> setter o <$> upd (getter o)
{-# INLINE lens' #-}

-- Sample types

data S = MkS { s0 :: Int, s1 :: String }
  deriving (Show)

data O = MkO { _out0 :: Int, _out1 :: Maybe Int, _out2 :: String }
  deriving (Show)

out0 :: Lens' O Int
out0 = lens' _out0 (\o b -> o{_out0 = b})

out1 :: Lens' O (Maybe Int)
out1 = lens' _out1 (\o b -> o{_out1 = b})

out2 :: Lens' O String
out2 = lens' _out2 (\o b -> o{_out2 = b})

-- "Default output maker"

def, def_bad, def_fix :: S -> O
def ~MkS{..}    = MkO{ _out0=0, _out1=Just s0, _out2=s1 }
def_bad MkS{..} = MkO{ _out0=0, _out1=Just s0, _out2=s1 }

def_fix s = let ~(MkO{..}) = def_bad s in MkO{..}

test :: Builder S O ()
test =
  do !n <- gets s0
     output out2 $ show n
     modify $ \s -> s{ s0 = n + 1 }

test2 :: Builder S O ()
test2 = test >> test >> test

test3 :: Builder S O ()
test3 = forM_ [1..iter] (\_ -> output out1 Nothing)
  where iter :: Int
        iter = 1000000000

run :: (S -> O) -> Builder S O () -> IO ()
run mkDefault builder =
  print $ evalState (runBuilder mkDefault builder) MkS{ s0=5, s1="foo" }

main :: IO ()
main = 
  do run def test
     -- run def_bad test
     run def_fix test

     run def test2
     run def test3
