{-# LANGUAGE GADTs                     #-}
{-# LANGUAGE EmptyCase                 #-}
{-# LANGUAGE RankNTypes                #-}
{-# LANGUAGE DataKinds                 #-}
{-# LANGUAGE PolyKinds                 #-}

{-# LANGUAGE DeriveFunctor             #-}
{-# LANGUAGE StandaloneDeriving        #-}

{-# LANGUAGE MultiParamTypeClasses     #-}
{-# LANGUAGE FlexibleContexts          #-}
{-# LANGUAGE FlexibleInstances         #-}
module TreesThatGrow where

import qualified Data.Set as Set

-- Let's define a type for syntax tree

type VarName = String

data NodeType = VarTag |  AbsTag | AppTag | LetTag

data SyntaxNode tag r where
    Var :: VarName -> SyntaxNode 'VarTag r
    Abs :: VarName -> r -> SyntaxNode 'AbsTag r
    App :: r -> r -> SyntaxNode 'AppTag r
    Let :: VarName -> r -> r -> SyntaxNode 'LetTag r

deriving instance Functor (SyntaxNode tag)

data Syntax stage where
  Mk :: !(stage tag) -> SyntaxNode tag (Syntax stage) -> Syntax stage

-- @Syntax stage@ can be thought as a @Fix@ of the following @Functor@
--
-- > type SyntaxF stage r = exists tag. (stage tag, SyntaxNode tag r)
-- > type Syntax stage = Fix (SyntaxF stage)

-- How these stages supposed to look like?

-- | Stage1 syntax can contain any type of nodes
data Stage1 (tag :: NodeType) = S1

-- | Stage2 syntax does not contain a node represented by 'Let'
data Stage2 (tag :: NodeType) where
  S2Var :: Stage2 'VarTag
  S2Abs :: Stage2 'AbsTag
  S2App :: Stage2 'AppTag

-- I use two type classes to reduce the verbosity

class Member (stage :: k -> *) (tag :: k) where
  -- | 'auto' indicates the type @stage tag@ is inhabited
  auto :: stage tag

class NotMember (stage :: k -> *) (tag :: k) where
  -- | 'autoNot' indicates there can not be a value for the type @stage tag@
  autoNot :: stage tag -> any

instance Member Stage1 tag where auto = S1

instance Member Stage2 'VarTag  where auto = S2Var
instance Member Stage2 'AbsTag where auto = S2Abs
instance Member Stage2 'AppTag where auto = S2App
instance NotMember Stage2 'LetTag where
  autoNot impossible = case impossible of { }

-- Smart constructors

var_ :: Member stage 'VarTag => VarName -> Syntax stage
var_ x = Mk auto (Var x)

abs_ :: Member stage 'AbsTag => VarName -> Syntax stage -> Syntax stage
abs_ v body = Mk auto (Abs v body)

app_ :: Member stage 'AppTag => Syntax stage -> Syntax stage -> Syntax stage
app_ e1 e2 = Mk auto (App e1 e2)

let_ :: Member stage 'LetTag => VarName -> Syntax stage -> Syntax stage
   -> Syntax stage
let_ v e1 e2 = Mk auto (Let v e1 e2)

-- Folding over Syntax

type FoldStep stage r = forall tag. stage tag -> SyntaxNode tag r -> r

foldSyntax :: forall stage r. FoldStep stage r -> Syntax stage -> r
foldSyntax step = let go (Mk tag node) = step tag (fmap go node) in go

-- How to use 'foldSyntax'

prettyPrint :: Syntax stage -> String
prettyPrint t = foldSyntax step t 0
  where
    parensIf True  str = "(" ++ str ++ ")"
    parensIf False str = str

    step :: FoldStep stage (Int -> String)
    step _ fe p = case fe of
      Var x       -> x
      Abs x e     -> parensIf (p > 0) $ "\\" ++ x ++ " -> " ++ e 0
      App e1 e2   -> parensIf (p > 10) $ e1 10 ++ " " ++ e2 11
      Let x e1 e2 -> parensIf (p > 0) $
        "let " ++ x ++ " = " ++ e1 0 ++ " in " ++ e2 0

-- Using above machinery, we can write the following 'eliminateLet'
-- function, and can represent the fact returned syntax does not
-- contain Let anywhere.

eliminateLet :: Syntax Stage1 -> Syntax Stage2
eliminateLet = foldSyntax $ \_ fe -> case fe of
  Var x       -> var_ x
  Abs x e     -> abs_ x e
  App e1 e2   -> app_ e1 e2
  Let x e1 e2 -> app_ (abs_ x e2) e1

-- 'freeVars' function on Stage2 syntax does not need to handle
-- Let case.

freeVars :: Syntax Stage2 -> Set.Set VarName
freeVars = foldSyntax $ \tag fe -> case fe of
  Var x     -> Set.singleton x
  Abs x e   -> Set.delete x e
  App e1 e2 -> Set.union e1 e2
  Let {}    -> autoNot tag

-- Example inputs

expr1, expr2 :: Syntax Stage1
expr1 = abs_ "x" (var_ "x")
expr2 = let_ "f" (abs_ "x" (abs_ "y" (var_ "x")))
             (app_ (app_ (var_ "f") (var_ "f")) (var_ "g"))
