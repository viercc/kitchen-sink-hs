module Main(main) where

import System.Environment

-- Prime number enumeration using minimum number of subtraction
-- (including comparison) and no division.
-- 
-- Purpose of it is a prototype for "everything is church-encoded"
-- programming languages like LazyK. Subtractions and divisions
-- of Church-encoded numerals are inefficient, each taking O(n).
-- So avoiding them is better for performance.
-- 
-- There are no practical reason to do it in Haskell,
-- since subtraction (, comparison) and division are cheap
-- compared to list operation.

main :: IO ()
main =
  do args <- getArgs
     let n = 100000 - 1
     case args of
       ("sieve":_)  -> print (primes !! n)
       ("td":_)     -> print (primesTD !! n)
       _            -> putStrLn "Primes [sieve | td]"

--------------------------------------------

primes :: [Int]
primes = mkPrimes ps
  where ps = mkPrimes ps

mkPrimes :: [Int] -> [Int]
mkPrimes ps = 2 : indices 3 (drop 3 (mkSieve ps))

mkSieve :: [Int] -> [Bool]
mkSieve = go 0 (repeat True)
  where
    go p ws [] = []
    go p ws (p':ps') =
      let delta = (p' - p) * (p' + p)
          (chunk,ws') = splitAt delta ws
          ws'' = zipWith (&&) ws' (wheel p')
      in chunk ++ go p' ws'' ps'
  
wheel :: Int -> [Bool]
wheel p = ws
  where ws = cycle (False : drop 1 (replicate p True))

indices :: Int -> [Bool] -> [Int]
indices n bs =
  [i | (i,b) <- zip [n..] bs, b]

-----------------------------------------------

-- | Trial division
mkPrimesTD :: [Int] -> [Int]
mkPrimesTD ps = 2 : filter (isPrime ps) [3..]
  where
    isPrime [] _ = True
    isPrime (p:ps) n
      | p * p > n    = True
      | rem n p == 0 = False
      | otherwise    = isPrime ps n

primesTD :: [Int]
primesTD = mkPrimesTD ps
  where ps = mkPrimesTD ps
