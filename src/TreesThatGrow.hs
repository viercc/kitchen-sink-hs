{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs     #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE EmptyCase #-}
module TreesThatGrow where

import Data.Proxy

type VarName = String

data Operator = Plus | Minus
  deriving (Show, Eq)

data NodeType = VarTag | AbsTag | AppTag | OpTag

data SyntaxF stage r =
    Var !(stage 'VarTag)  VarName
  | Abs !(stage 'AbsTag) VarName r
  | App !(stage 'AppTag) r r
  | Op  !(stage 'OpTag)  r Operator r

newtype Syntax stage = Mk (SyntaxF stage (Syntax stage))

type Stage1 = Proxy
data Stage2 (tag :: NodeType) where
  S2Var :: Stage2 'VarTag
  S2Abs :: Stage2 'AbsTag
  S2App :: Stage2 'AppTag
  -- No (Stage2 'OpTag)

data WithLoc stage tag = Loc SrcLoc !(stage tag)

type SrcLoc = (Int, Int)

eliminateOp :: Syntax Stage1 -> Syntax Stage2
eliminateOp = go
  where
    go (Mk fe) = case fe of
      Var _ x -> Mk $ Var S2Var x
      Abs _ v body -> Mk $ Abs S2Abs v (go body)
      App _ e1 e2 -> app2 (go e1) (go e2)
      Op _ e1 op e2 -> app2 (app2 (Mk (Var S2Var (show op))) (go e1)) (go e2)
    
    app2 e1 e2 = Mk $ App S2App e1 e2

thereIsNoOp :: Syntax Stage2 -> Bool
thereIsNoOp (Mk fe) =
  case fe of
    Var _ _ -> True
    Abs _ _ body -> thereIsNoOp body
    App _ e1 e2 -> thereIsNoOp e1 && thereIsNoOp e2
    Op tag _ _ _ -> case (tag :: Stage2 'OpTag) of { }
