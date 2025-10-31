module Math.AAtomicPartition(
  -- * Main functions
  isAAtomic,
  aAtomicPartitions,
  aAtomicBFPartitions,
  aAtomicSBFPartitions,

  -- * Implementation details
  SubsetSums(),
  sums2,
  singletonSum,
) where

import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Math.BalanceFreePartition
import Control.Monad (guard)

{-
(分割の定義):
  非負整数 n の分割とは、正整数の降順リスト p = [a0, a1, ..., ak],
  sum p == n を満たすもの。

(A-atomic な分割):
  あらかじめ 1 より大きい整数からなる集合 A ⊂ ℕ を固定する。
  分割 p が A-atomic であるとは、
    「p の中から 2 個以上の要素を選んで足し合わせた和」が
     A のどの要素とも一致しない
  こと。

  ここで「2個以上」というのは、同じ値を複数回使ってもよい（多重集合）という意味。
  （つまり、p の部分多重集合の和で、ちょうど1個の要素からなる場合は禁止条件に関係しない。）

  例: A = {3,5} のとき、
    [7,3] は A-atomic。
      2個以上の要素から作れる和は 7+3=10 だけで、10 ∉ A。
    [1,1,3,5] は A-atomic ではない。
      1+1+3 = 5 ∈ A なのでアウト。
-}

-- | 与えられたパーティション p が A-atomic かどうかを素直に判定する関数。
--   （後で列挙結果のフィルタなどに使えるように分離しておく）
--
--   アルゴリズム:
--     全ての部分多重集合和のうち、サイズ>=2のものを列挙し、
--     それが A に含まれていないことをチェックする。
--
--   ただし素直にやると指数的なので、
--   実際の列挙本体ではよりインクリメンタルな枝刈りを使う。
isAAtomic :: IntSet   -- ^ A
          -> [Int]    -- ^ partition in descending order
          -> Bool
isAAtomic atoms parts =
    IntSet.disjoint (subsetSumsGE2 parts) atoms

-- | Set of sums of all submultisets of a multiset of Ints
data SubsetSums = SubsetSums {
    elems :: !IntSet, -- ^ set of distinct elements (= set of sums of exactly one element)
    sums2 :: !IntSet  -- ^ set of sums of two or more elements
  }
  deriving (Show, Eq)

instance Semigroup SubsetSums where
  -- Combine two underlying multisets
  SubsetSums a1 a2 <> SubsetSums b1 b2 = SubsetSums {
      elems = IntSet.unions
        [ a1, b1 ],
      sums2 = IntSet.unions
        [ a2, b2, a1_plus_b1 ]
    }
    where
      a1_plus_b1 = plusIntSet a1 b1

instance Monoid SubsetSums where
  -- Underlying multiset is empty
  mempty = SubsetSums IntSet.empty IntSet.empty

-- | SubsetSums for a singleton multiset
singletonSum :: Int -> SubsetSums
singletonSum a = SubsetSums (IntSet.singleton a) IntSet.empty

-- | > plusIntSet as bs = {a + b | a <- as, b <- bs }
plusIntSet :: IntSet -> IntSet -> IntSet
plusIntSet as bs
  | IntSet.size as > IntSet.size bs = plusIntSet bs as
  | IntSet.null as = IntSet.empty
  | otherwise = IntSet.unions [ IntSet.mapMonotonic (a +) bs | a <- IntSet.toAscList as ]

-- 全部分多重集合和のうち、サイズ>=2のものだけを集めた IntSet
subsetSumsGE2 :: [Int] -> IntSet
subsetSumsGE2 = sums2 . foldl' (<>) mempty . map singletonSum

-- | A-atomic な分割をすべて列挙する。
--   引数:
--      atoms : IntSet で表した集合 A
--      n0    : 合計 n0
--
--   戻り値:
--      A-atomic な分割を (降順リストとして) 全部返す。
--
--   方針は balance-free の列挙と似ていて、
--   「現在の部分的な分割 p」「p の部分多重集合和に関する状態」を持って
--   深さ優先で降順に延長していく。ただしここでは重複可。
aAtomicPartitions :: IntSet -> Int -> [[Int]]
aAtomicPartitions atoms n0 =
    map reverse $  -- 最終的には降順にしたいので reverse せず最初から降順で作ってもOK
    go n0 n0 [] mempty
  where
    -- go i n parts sums
    --    i     : いま選べるパーツの最大値 (降順制約のための上限)
    --    n     : 残りの合計
    --    parts : いままでに決めた部分分割 (降順, 合計 (n0-n))
    --    sums  : parts の SubsetSums
    --
    -- 枝刈り条件:
    --   sums2 と A が交差したら即アウト
    --   n < 0 もアウト
    --
    -- 終了条件:
    --   n == 0 なら parts が完成 (A-atomic 性は sums2∩A=∅ によって保証済)
    --
    go :: Int -> Int -> [Int] -> SubsetSums -> [[Int]]
    go i n parts sums
      | n < 0 = []
      | not (IntSet.disjoint (sums2 sums) atoms) = []
      | n == 0 = [parts]
      | i <= 0 = []
      | i > n  = go n n parts sums
      | otherwise =
          let sums' = singletonSum i <> sums
          in  go i (n - i) (i : parts) sums' ++ go (i - 1) n parts sums

{-
使い方イメージ:

  import qualified Data.IntSet as IntSet

  let atoms = IntSet.fromList [3,5]  -- A = {3,5}
  aAtomicPartitions atoms 10
    :: [[Int]]

で、10の A-atomic 分割を全部返す。

列挙の中で常に「2個以上の部分和集合」が A とぶつかった瞬間に捨てるので、
指数爆発は多少マシになる。（もちろん最悪は指数的なまま）
-}


-- | A-atomic /\ balance-free な分割をすべて列挙する。
--   引数:
--      atoms : IntSet で表した集合 A
--      n0    : 合計 n0
--
--   戻り値:
--      A-atomic かつ balance-free な分割を (BF (~ IntSet)として) 全部返す。
aAtomicBFPartitions :: IntSet -> Int -> [BF]
aAtomicBFPartitions atoms n0 =
    go n0 n0 IntSet.empty IntSet.empty mempty
  where
    -- go i n parts sums
    --    i       : いま選べるパーツの最大値 (降順制約のための上限)
    --    n       : 残りの合計
    --    parts   : いままでに決めた部分分割
    --    delta_p : parts の delta
    --    sums    : parts の SubsetSums
    --
    -- 枝刈り条件:
    --   delta が 0 を含んだら即アウト
    --   sums2 と A が交差したら即アウト
    --   n < 0 もアウト
    --
    -- 終了条件:
    --   n == 0 なら parts が完成
    --    (A-atomic 性は sums2∩A=∅ によって保証)
    --    (balance-free性は 0 ∉ delta によって保証)
    --
    go :: Int -> Int -> IntSet -> IntSet -> SubsetSums -> [BF]
    go i n parts delta_p sums
      | n < 0 = []
      | not (IntSet.disjoint (sums2 sums) atoms) = []
      | IntSet.member 0 delta_p = []
      | n == 0 = [BF parts]
      | i <= 0 = []
      | i > n  = go n n parts delta_p sums
      | otherwise =
          let parts' = IntSet.insert i parts
              sums' = singletonSum i <> sums
              delta_p' = updateDelta i delta_p
          in go i (n - i) parts' delta_p' sums' ++
             go (i - 1) n parts delta_p sums

-- | A-atomic /\ semi-balance-free な分割をすべて列挙する。
--   引数:
--      atoms : IntSet で表した集合 A
--      n0    : 合計 n0
--
--   戻り値:
--      A-atomic かつ semi-balance-free な分割を (SBFとして) 全部返す。
aAtomicSBFPartitions :: IntSet -> Int -> [SBF]
aAtomicSBFPartitions atoms n0 = do
  p' <- aAtomicBFPartitions atoms n0
  [SmallStep p'] ++ derive p'
  where
    -- 注意: A-atomicでない分割の細分はA-atomicでない。
    -- そのため、もともとA-atomicであるBFPartitionの細分としてしか
    -- A-atomic /\ semi-balance-free な分割は生じない。
    -- したがって、aAtomicBFPartitionsの結果から
    -- 'sbfpartitions'と同様に`BigStep`ケースを導出すればよい。
    --
    -- ただし、A-atomic /\ balance-free の細分が
    -- A-atomicでないケースは存在する。それは除外しなければならない。
    derive :: BF -> [SBF]
    derive (BF p') = do
      k <- [ a `div` 2 | a <- IntSet.toDescList p', even a ]
      let q = IntSet.delete (2 * k) p'
          delta_q = delta (IntSet.toList q)
          sums2_q = subsetSumsGE2 ([k,k] ++ IntSet.toList q)
      -- ([k,k] ++ q is semi-balance-free) if and only if:
      guard $ k `IntSet.member` q || k `IntSet.notMember` delta_q
      -- ([k,k] ++ q is A-atomic) if and only if:
      guard $ IntSet.disjoint atoms sums2_q
      return $ BigStep k (BF q)