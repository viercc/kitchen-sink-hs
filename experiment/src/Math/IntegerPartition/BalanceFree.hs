{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE InstanceSigs #-}
module Math.IntegerPartition.BalanceFree(
  -- * Main type and functions
  -- ** Balance-free
  BF(..),
  sumBF, lengthBF,
  bfpartitions,
  minimalBFPartitions,
  -- ** Semi-balance-free
  SBF(..),
  sumSBF, lengthSBF, prettySBF,
  sbfpartitions,
  minimalSBFPartitions,

  -- * Implementation details
  delta,
  updateDelta,

  -- * Visualization
  bfpartitionsDot,
  sbfpartitionsDot,

) where

import Control.Monad (guard)
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet
import Data.Ord (comparing, Down (..))
import Data.List (sortBy)
import qualified Data.Set as Set
import GHC.IsList (IsList(..))

import HasseDiagram (dotHasse)

---- Balance-free partitions

{-

(分割の定義): 非負整数 `n` の分割とは、正整数の重複集合（ここでは降順にソートされたリストで表現）
    `p = [a_0, a_1, ..., a_{n-1}]` であって、合計が `n` になるもの、すなわち`sum p == n`であるもの。

(分割の細分): `n` の分割 `p` が分割 `q` の細分であるとは、`p` の要素を適切に分割して `pparts = [[a11,a12,...], [a21, a22, ...], ...]`
    としたもの、すなわち `concat pparts` が `p` と順序を除いて一致するものであって、 `map sum pparts == q` を満たすような `pparts` が存在すること。
    （注:一般に与えられた分割の組`(p,q)`に対して`p`が`q`の細分であるか(==`pparts`が存在するか)を判定する問題は難しいらしい。）

    `p` が `q` の細分であることを `p ≼ q`, `p ≼ q`かつ`p /= q`であることを`p ≺ q`と表記する。

(balance-free分割): `n` の分割 `p` がbalance-freeであるとは、以下の同値な条件いずれか(したがって全て)を満たすこと。

    1. 以下の2条件を両方満たす

       * `p`が重複する要素をもたない i.e. `a_0 > a_1 > ...`
       * 任意の `q`に対して、 `p ≺ q`ならば`q`はbalance-free

    2. `p`の空でない部分（重複）集合であって互いに素な組`(pA,pB)`をどのようにとっても、それらの和は異なる: `sum pA /= sum pB`.

    3. `p`の空でない部分（重複）集合であって互いに異なる組`pA /= pB`をどのようにとっても、それらの和は異なる: `sum pA /= sum pB`.
-}

-- | Balance-free partitionは重複をもたないので
--   単なる `IntSet` で表される

newtype BF = BF IntSet
  deriving (Eq, Ord)

instance IsList BF where
  type Item BF = Int

  fromList :: [Int] -> BF
  fromList p
    | any (<= 0) p = error "Item of BF must be a positive integer"
    | 0 `IntSet.member` delta p = error $ "Balance-free constraint is broken: " ++ show p
    | otherwise = BF $ IntSet.fromList p
 
  toList :: BF -> [Int]
  toList (BF p) = IntSet.toDescList p 

instance Show BF where
  showsPrec prec bf = showsPrec prec (toList bf)

{-

balance-freeな分割を数え上げるために、
「ある分割 `p` に対して、`p`の*どちらかが空でない*部分集合の組`(pA,pB)`に対する`sum pA - sum pB`の集合」
を `delta p` と呼ぶことにします。 `p`がbalance-freeであることは、`delta p`が`0`を含まないことと同値です。

さて、`delta p`は以下のように再帰的に計算できます。
-}

delta :: [Int] -> IntSet
delta [] = IntSet.empty
delta (a : p) = updateDelta a (delta p)
  {-
  [注意] balance-freeの定義では*どちらも空でない*部分集合の組`(pA,pB)`を考えましたが、片方が空であるなら差が0になることはないので、
  `0`を含むかどうかを判定するためならば*どちらかが空でない*でも問題ありません。
  この定義を用いるのは、上記の再帰的定義を簡潔にするためです。
  -}

updateDelta :: Int -> IntSet -> IntSet
updateDelta a delta_p
  = IntSet.unions [ only_a, delta_p, delta_plus_a, delta_minus_a ]
  where
    only_a = IntSet.fromList [a, -a]
    delta_plus_a = IntSet.mapMonotonic (a +) delta_p
    delta_minus_a = IntSet.mapMonotonic (subtract a) delta_p


{-
特に`delta (a : p) ⊃ delta p`であることに注意すると、
多重集合をひとつづつ数を添加しながら数え上げているとき`0 ∈ delta p'`ならば
最終結果でも `0 ∈ delta (a0 : a1 : ... : p')`なので、効率的に"枝刈り"が可能です。
-}

bfpartitions :: Int -> [BF]
bfpartitions = map fst . bfpartitionsWithDelta

bfpartitionsWithDelta :: Int -> [(BF, IntSet)]
bfpartitionsWithDelta n0 = go n0 n0 IntSet.empty IntSet.empty
  where
    -- go i n p delta_p
    --     i: maximum part size
    --     n: remaining sum
    --     p: already decided partitions
    --     delta_p: `delta p` updated in sync with `p`
    go :: Int -> Int -> IntSet -> IntSet -> [(BF, IntSet)]
    go i n p delta_p
      | n < 0 = [] -- no negative sums
      | 0 `IntSet.member` delta_p = []
      | n == 0 = [(BF p, delta_p)]
      | i <= 0 = []
      | i > n = go n n p delta_p
      | otherwise =
          go i (n - i) (IntSet.insert i p) (updateDelta i delta_p)
            ++ go (i - 1) n p delta_p
{-

(semi-balance-free): semi-balance-freeは、balance-freeの定義から「互いに素な空でない部分集合の組`(pA,pB)`」を
「互いに素な空でない部分集合の組`(pA,pB)`であって、少なくとも一方は2個以上の要素をもつもの」に変更したもの。

    `p`がsemi-balance-free ⇔
    `p`の空でない部分（重複）集合であって互いに素な組`(pA,pB)`は、少なくとも一方が2個以上の要素を持てばそれらの和は異なる。

定義から明らかに、

* `p`がbalance-free ⇒ `p`がsemi-balance-free

です。また、次のことが言えます。

(semi-balance-freeなら重複ペアは高々一つ): semi-balance-freeな分割 `p` に含まれる重複した数字の組は高々一つ。

    [注意] ここでは `[k,k,k,j]` のような分割には重複した数字の組が*1つだけとれる*という数え方をしている。また、
    `[i,j,j,j,j,k]`には(同じペアが)2組`[j,j],[j,j]`と取れる、というように数えている。

    証明: もし2組の重複`[i,i,j,j]`がpに含まれたとすると、`pA = pB = [i,j]`を互いに素なようにとることができる。

(semi-balance-freeかつ重複ペアが存在しないならばbalance-free):
  semi-balance-freeな分割 `p` に含まれる重複した数字の組が無い、すなわちどの要素も互いに異なるならば、
  `p`の空でない部分（重複）集合であって互いに素な組`(pA,pB)`は`|pA| = |pB| = 1`のときでも和が異なる。
  したがって、そのような`p`はbalance-freeである。

したがって、semi-balance-freeな分割pは、以下のいずれかに重複なく当てはまります。

* pはbalance-freeである
* pは重複する数字の組`[k,k]`をちょうど1つ持つ

さて、`p'`が重複する数字の組`[k,k]`をちょうど1つ持つ場合において、その組`[k,k]`を
`[2*k]`で置き換えた新たな分割`p'`について考えると、次のことがわかります。

* semi-balance-freeな分割を粗くしてもsemi-balance-freeなので、`p'`はsemi-balance-freeです。
* `p'`は更にbalance-freeでもあります。実際、`p \\ [k,k]`は重複する要素を持たず、さらに`2*k`という要素も持ちません。
  （もし持っていれば`pA = [2*k], pB = [k,k]`の和が一致してしまう）
  「重複する要素がない」かつsemi-balance-free ⇔ balance-freeだったので、`p'`はbalance-freeです。

一方で、どんなbalance-freeな分割 `p' = [2*k] ++ ...` に対しても、
`p = [k, k] ++ ...`がsemi-balance-freeとは限りません。

　　実際、`p' = [4,3,2]` はbalance-freeであるが、`p = [4,3,1,1]`はsemi-balance-freeでない。

balance-freeな分割 `p' = [2*k] ++ q` に対して `[k,k] ++ q`がsemi-balance-freeとなる必要十分条件は、
`[k] ++ q`がsemi-balance-freeとなることです。

    証明:
      (必要性)semi-balance-freeな分割の部分(多重)集合は、定義からただちにsemi-balance-freeです。
      (十分性)`[k] ++ q`がsemi-balance-freeのとき、どちらかが2元以上の`[k,k] ++ q`の部分集合の組`(pA, pB)`を
      考えます。`(pA,pB)`が`k`をそれぞれいくつ含むかについて場合分けをします。
      一般性を失うことなく`pA`に含まれる`k`の個数 >= `pB`に含まれる`k`の個数と仮定でき、以下の4ケースで
      尽くされています。

      * `pA, pB` がどちらも`k`を含まないなら、それはbalance-freeな`q`の空でない部分集合の組でもあるので、
        和は等しくありません。
      * `pA, pB` がどちらも`k`を含むとき、`pA, pB`のどちらかは2個以上の元をもつので、
        `pA \\ [k], pB \\ [k]`の少なくとも一方は空ではありません。
        片方が空なときは明らかに和は等しくならず、両方が空でないときも`q`がbalance-freeなので和は等しくありません。
      * `pA` が`k`を2つ以上含む場合、`pA = pA' ++ [k,k]`に対して`(pA' ++ [2*k], pB)`は`p'`の部分集合の組なので、
        和は等しくありません。
      * `pA` が`k`を1つだけ含み`pB`は含まない場合、`(pA,pB)`は`[k] ++ q`の部分集合の組であり、`k ++ [q]`がsemi-balance-freeという
        仮定から和は等しくありません。

balance-freeな分割 `p' = [2*k] ++ q` に対して、`[k] ++ q`がsemi-balance-freeとなることは以下のように判定できます。

* `q`が`k`を含まないとき:

  * `[k] ++ q`がsemi-balance-free ⇔ `[k] ++ q`がbalance-free ⇔ `0 ∉ delta ([k] ++ q)` ⇔ `k ∉ delta q`

* `q`が`k`を含むとき（`p'`が`[k, 2*k]`を含んでいたときに生じうる）:

  * `[k] ++ q`は無条件にsemi-balance-free。実際、`(qA, qB)` s.t. `qA ++ qB ⊂ [k] ++ q`としてありうるパターン分けから

    * どちらも`k`を含まない  <= `q` が balance-free
    * どちらも`k`を含む     <= 両方から`k`を取り除いたとき、片方だけ空 or `q`がbalance-free
    * 片方に`k`が2つ含む    <= `2*k`に置き換えると `p'` が balance-free
    * 片方に1つだけ`k`を含む <= `q` が balance-free (`q`は`k`を含む！)

総合すると、semi-balance-freeな分割pは以下の方法ですべて列挙できます。

* balance-freeな分割 `p'` を列挙する。各`p'`に対して、以下のいずれも
  semi-balance-freeな分割であり、semi-balance-freeな分割はすべてこの方法で作られる。

  * `p'` 自体
  * `p'` に含まれる各偶数 `2*k`, `p = [2*k] ++ q`に対して、

    * `[k] ++ q`がsemi-balance-freeならば `[k,k] ++ q`はsemi-balance-free

-}

-- | semi-balance-free partitionはそれ自体balance-free (`SmallStep p`)か、
--   あるいは balance-free に同じ値 `k` のペアを一つ追加したもの (`BigStep k p`)
data SBF =
    SmallStep !BF
  | BigStep !Int !BF
  deriving (Show, Eq, Ord)

sbfpartitions :: Int -> [SBF]
sbfpartitions n0 = do
  p' <- bfpartitions n0
  [SmallStep p'] ++ derive p'
  where
    derive :: BF -> [SBF]
    derive (BF p') = do
      k <- [ a `div` 2 | a <- IntSet.toDescList p', even a ]
      let q = IntSet.delete (2 * k) p'
          delta_q = delta (IntSet.toList q)
      guard $ k `IntSet.member` q || k `IntSet.notMember` delta_q
      return $ BigStep k (BF q)

---------

prettySBF :: SBF -> String
prettySBF (SmallStep p) = show p
prettySBF (BigStep k p) = show [k,k] ++ "+" ++ show p

lengthSBF :: SBF -> Int
lengthSBF (SmallStep p) = lengthBF p
lengthSBF (BigStep _ p) = 2 + lengthBF p

sumSBF :: SBF -> Int
sumSBF (SmallStep p) = sumBF p
sumSBF (BigStep k p) = 2 * k + sumBF p

lengthBF :: BF -> Int
lengthBF (BF p) = IntSet.size p

sumBF :: BF -> Int
sumBF (BF p) = sum (IntSet.toList p)

-----------

minimalBFPartitions :: Int -> [BF]
minimalBFPartitions = loop Set.empty . sortBy (comparing (Down . lengthBF)) . bfpartitions
  where
    loop :: Set.Set BF -> [BF] -> [BF]
    loop _       [] = []
    loop parents (p : rest)
      | p `Set.member` parents = loop (Set.union (parentsOfBF p) parents) rest
      | otherwise              = p : loop (Set.union (parentsOfBF p) parents) rest

parentsOfBF :: BF -> Set.Set BF
parentsOfBF (BF p) = Set.fromList $ do
  a <- IntSet.toAscList p
  b <- IntSet.toAscList (IntSet.dropWhileAntitone (<= a) p)
  -- Since p is balance-free, (a + b) ∉ p
  -- Also balance-free is a property preserved by merger of its parts
  pure $ BF $ IntSet.insert (a + b) $ IntSet.delete a $ IntSet.delete b p

minimalSBFPartitions :: Int -> [SBF]
minimalSBFPartitions = loop Set.empty . sortBy (comparing (Down . lengthSBF)) . sbfpartitions
  where
    loop :: Set.Set SBF -> [SBF] -> [SBF]
    loop _       [] = []
    loop parents (p : rest)
      | p `Set.member` parents = loop (Set.union (parentsOfSBF p) parents) rest
      | otherwise              = p : loop (Set.union (parentsOfSBF p) parents) rest

parentsOfSBF :: SBF -> Set.Set SBF
parentsOfSBF (SmallStep p) = Set.mapMonotonic SmallStep (parentsOfBF p)
parentsOfSBF (BigStep k (BF p)) =
    let p' = BF $ IntSet.insert (2*k) p
    in  Set.insert (SmallStep p') $ Set.mapMonotonic (BigStep k) (parentsOfBF (BF p))
{-

ある `SBF` に対して、

* `p`がbalance-free のときは`BF`と同じ。

* `p = BigStep k p₀ = [k,k] ++ p₀` のとき、`p`をcoverする`q`は次のどちらか。

  * `q = [2*k] ++ p₀`
  * `p₀`をcoverする`q₀`に対して`q = [k,k] ++ q₀`。

    * `l /= k` に対して `q = [l,l] + q'` とはならない。
      実際、一方の`l`が`p`に存在する2つの部分の合併`a0+a1, [a0,a1] ⊂ p`であることはない。
      もしそうであれば、`l = a0 + a1`は`p`がsemi-balance-freeであるための条件に反している。
      しかし、2個の`l`が`p`にもともと含まれていることもできない。semi-balance-freeは
      同じ値の部分のペアを高々1つしかもてず、`k`のペアがすでに存在する。
      よってそのような`l`は存在しない。

-}

-------------------

-- | Outputs a Hasse diagram (of refinement poset) for balance-free partitions of @n@,
--   expressed in DOT language (refer Graphviz documentation for DOT)
bfpartitionsDot :: Int -> String
bfpartitionsDot n0 = dotHasse (bfpartitions n0) show (Set.toList . parentsOfBF)

-- | Outputs a Hasse diagram (of refinement poset) for semi-balance-free partitions of @n@,
--   expressed in DOT language (refer Graphviz documentation for DOT)
sbfpartitionsDot :: Int -> String
sbfpartitionsDot n0 = dotHasse (sbfpartitions n0) prettySBF (Set.toList . parentsOfSBF)
