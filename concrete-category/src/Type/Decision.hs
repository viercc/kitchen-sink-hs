{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}
module Type.Decision
  ( Not,
    Decision (..),
    dand,
    dor,
    dnot,
    equivalent
  )
where


import Data.Void

type Not p = p -> Void

-- | Either p or not p is proved
data Decision p = Proved p | Disproved (Not p)

dand :: Decision p -> Decision q -> Decision (p, q)
dand (Proved p) (Proved q) = Proved (p, q)
dand _ (Disproved notq) = Disproved (notq . snd)
dand (Disproved notp) _ = Disproved (notp . fst)

dor :: Decision p -> Decision q -> Decision (Either p q)
dor (Proved p) _ = Proved (Left p)
dor _ (Proved q) = Proved (Right q)
dor (Disproved notp) (Disproved notq) = Disproved (either notp notq)

dnot :: Decision p -> Decision (Not p)
dnot (Proved p) = Disproved ($ p)
dnot (Disproved p) = Proved p

equivalent :: (p -> q) -> (q -> p) -> Decision p -> Decision q
equivalent to from isP = case isP of
  Proved p -> Proved (to p)
  Disproved notP -> Disproved (notP . from)
