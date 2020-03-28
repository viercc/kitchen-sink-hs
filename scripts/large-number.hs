#!/usr/bin/env cabal
{- cabal:
build-depends: base
-}
module Main where

-- デフォルトで提供される関数群を読み込まない。
import Prelude(id, const, (.))
import qualified Prelude

{-

型付ラムダ計算に自然数型と不動点オペレータ fix :: (a->a)->aを加えたものは
チューリング完全であり、巨大数の記述を行う体系として強力すぎる。
なぜならば、停止しない計算を記述することができてしまい、「長さ n のラムダ項
が計算しうる最大の値」を与える関数、おそらくビジービーバー関数と同程度の
強さになる。これは比較的よく知られているためあまり考察の対象とはしたくない。

そこで、強力ではあるが必ず停止する体系として、自然数と任意の型に対する
原始再帰を持つ体系を考える。
詳しくは知らないが、ゲーデルのDialectica interpretationというものがある
らしい。ペアノ算術の強さを考えるときに出てくるとか（よく知らない）
以下に、Haskell風の記法で型付きラムダ計算を表現しよう。

-}

-- 自然数
data Nat = Z | S Nat

-- 一般化された原始再帰
-- rec x f n = f (f (f ... (f x)))  -- fのn回反復
rec :: a -> (a -> a) -> Nat -> a
rec x f Z = x
rec x f (S n) = f (rec x f n)

{-
以下、この rec 以外に再帰を用いないことで、fixの無い単純型付ラムダ計算を
表現していると思ってもらいたい。
また、*単純*型付ラムダ計算には型変数は存在しないが、固定された
型を適宜持つ式に置換されていると思ってもらいたい。
計算能力に違いはない。

単純型付ラムダ計算+算術の体系を考える。
唯一の基底型として Nat を持ち、定数として
  Z :: Nat
  S :: Nat -> Nat
  すべての型τについて rec[τ] :: τ -> (τ -> τ) -> Nat -> τ
だけを持つ単純型付ラムダ計算を考え、その項をT-項と呼ぶことにする。
任意のT-項は、いかなる順序で簡約を行っても、必ず正規形になって停止する。

T-項の長さLEN(x)を、項xの部分項である変数項と定数項の数とする。

maxval(n)を、LEN(x)<=n なるNat型のT-項の集合 {x :: Nat | LEN(x) <= n}
の、評価結果の最大値として定義する。

maxval(n)はどれだけ強い関数か？
これは、有限の長さでどれだけ強い関数を実装できるかという問いに等しい。

加算・乗算・累乗といった原始再帰関数は簡単に実装できる。
実際、原始再帰は制限されたrecにほかならない。
そのため、maxval(n)はすべての原始再帰関数を抑えるクラス f_\omega(n)
以上の強さを持つ。

-}

add, mul, pow :: Nat -> Nat -> Nat
add n m = rec m S n
mul n m = rec Z (add n) m
pow n m = rec (S Z) (mul n) m

-- 記述の簡便のため、関数の反復適用を演算子として定義する。
(^#) :: (a -> a) -> Nat -> a -> a
(f ^# n) x = rec x f n

{-
Natの関数に対する再帰だけでなく、(Nat->Nat)や任意の型に対する再帰を
認めることは、原始再帰的でない関数、例えばAckermann関数なども実装できる
ようにする。

  ack Z     n     = S n
  ack (S m) Z     = ack m 1
  ack (S m) (S n) = ack m (ack (S m) n)
    ||
  ack Z     = S
  ack (S m) = rec (ack m 1) (ack m)
    ||
  ack = rec S (\g -> rec (g 1) g)
-}
ack :: Nat -> Nat -> Nat
ack = rec S (\g -> rec (g (S Z)) g)

{-
ふぃっしゅ数バージョン3のs(n)変換は、定義をそのまま引き写す形で実装できる。
  s 0     f x = (f ^# x) x
  s (n+1) f x = (s n ^# x) f x
-}
s :: Nat -> (Nat -> Nat) -> (Nat -> Nat)
s = rec (\f x -> (f ^# x) x)         -- = s 0
        (\s_n f x -> (s_n ^# x) f x) -- = s (n+1)

{-
ふぃっしゅ数バージョン5のm(n)変換は、定義そのままにnの関数として定義することは
できない。なぜなら、nによって型が異なるためだ。

m(n)変換の型を a とすると、m(n+1)変換の型は a -> aである。
型注釈を簡単に書くため、この関係を型エイリアスで書くことにする。
-}
type M a = a -> a


-- m(n)変換を、個別のnごとに定義すると以下のようになる。
m_1 :: M Nat
m_1 x = x `pow` x

m_2 :: M (M Nat)
m_2 f x = (f ^# x) x

m_3 :: M (M (M Nat))
m_3 f2 f1 x = (f2 ^# x) f1 x

m_4 :: M (M (M (M Nat)))
m_4 f3 f2 f1 x = (f3 ^# x) f2 f1 x

{-
同様のパターンで、O(n)の長さでm_nを別々に定義することができる。
ふぃっしゅ数バージョン5のF5を関数として書くことはできないが、F5(x)の値になる
式は
  m_1 = ...
  m_2 = ...
    :
  m_x = ...
  F3(x) = m_x m_{x-1} ... m_2 m_1 x
とO(x^2)の長さで書ける。
したがって、maxval(n^2) >= F5(n)。
F5はFast growing hierarchyのf_{\varepsilon_0}程度の強さだったから、
maxvalはこれ以上に強い。

maxvalはf_{\varepsilon_0}よりも強くは無いと考えている。
-}

----------------------------------------------------
-- GHCiで実際にHaskellのプログラムとして走らせるときに
-- 便利なよう、NumとShowのインスタンスにする。

instance Prelude.Num Nat where
    fromInteger 0 = Z
    fromInteger n = S Prelude.$! (Prelude.fromInteger (Prelude.pred n))
    
    (+) = add
    (*) = mul
    
    (-) = Prelude.undefined
    negate = Prelude.undefined
    abs = id
    signum = rec Z (const (S Z))

instance Prelude.Show Nat where
    show n = Prelude.show (i n)

i :: Nat -> Prelude.Integer
i = go 0
  where go a Z     = a
        go a (S n) = a `Prelude.seq` go (Prelude.succ a) n

main :: Prelude.IO ()
main = do
  p "ack 3 3   = " (ack 3 3)
  where
    p s n = Prelude.putStrLn (s Prelude.++ (Prelude.show n))
