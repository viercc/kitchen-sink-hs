{-# LANGUAGE DerivingVia #-}
module LogRwd where

import Prelude hiding (log)
import Data.Bifunctor

import Control.Monad.State

{-
module LogRwdTransf(M : MONAD) = struct
  type ('a, 'b) log = ('a, 'b) argFunPair list
   and ('a, 'b) mon = ('a, 'b) log -> ('a * ('a, 'b) log) M.mon
   and ('a, 'b) argFunPair = ('a * ('a -> ('a, 'b) mon))
  type ('a, 'b) result = ('a * ('a, 'b) log) M.result
  let ret x = fun l -> M.ret (x, l)
  let bind m f = fun l -> M.bind (m l) (fun (x, s') -> f x s')
  let (>>=) = bind
  let lift m = fun l -> M.bind m (fun x -> M.ret (x, l))
  let run (m: ('a, 'b) mon) : ('a, 'b) result =
   M.run (M.bind (m []) (fun (x, l) -> M.ret (x, List.rev l)))
  let log (p : ('a, 'b) argFunPair) = fun l -> M.ret ((), p :: l)
  let sizeOfLog (s : ('a, 'b) result) = match s with _, l -> List.length l
  let nthFunPair (s : ('a, 'b) result) (n : int) = match s with _, l ->
      if n < 0 || n >= sizeOfLog s then List.nth l 0 else List.nth l n
  let navigate (s : ('a, 'b) result) (n : int) =
    match nthFunPair s n with x, f ->
      match run (f x) with r, _ -> s, r, n
  let bakward (s : ('a, 'b) result) (n : int) =
    let  k = sizeOfLog s
    in navigate s (if n < 0 || n > k then k - 1 else n - 1)
  let forward (s : ('a, 'b) result) (n : int) =
    let  k = sizeOfLog s
    in navigate s (if n < 0 || n > k then 0 else n + 1)
-}

newtype Mon m a b c = Mon { runMon :: StateT (Log m a b) m c }
  deriving (Functor, Applicative, Monad) via (StateT (Log m a b) m)

type Log m a b = [ArgFunPair m a b]
type ArgFunPair m a b = (a, a -> Mon m a b a)

{-

The parameter `b` is actually never used.

Nothing is lost by changing them to more simpler

newtype Mon m a b = Mon { runMon :: StateT (Log m a) m b }
type Log m a = [ArgFunPair m a]
type ArgFunPair m a = (a, a -> Mon m a a)

-}

------------------------------------

log :: (Monad m) => ArgFunPair m a b -> Mon m a b ()
log p = Mon (modify (p:))

run :: (Functor m) => Mon m a b c -> m (c, Log m a b)
run (Mon m) = fmap (second reverse) (runStateT m [])

navigate :: (Functor m) => (c, Log m a b) -> Int -> m a
navigate (_, l) n = let (x, f) = l !! n in fst <$> run (f x)

------------------------------------

log_fibCps :: (Monad m)
           => Int
           -> (Int -> Mon m Int b Int)
           -> m (Int, Log m Int b)
log_fibCps x f = run (fib x f)
  where
    fib n k =
      do log (n, k)
         if n <= 1
           then k 1
           else fib (n-1) $ \n1 -> fib (n-2) $ \n2 -> k (n1 + n2)
