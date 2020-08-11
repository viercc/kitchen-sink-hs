import qualified Data.IntMap as IM

data Op = Add | Sub | Mul | Div
  deriving (Show, Eq)

precOp :: Op -> Int
precOp Add = 6
precOp Sub = 6
precOp Mul = 7
precOp Div = 7

showOp :: Op -> String
showOp Add = "+"
showOp Sub = "-"
showOp Mul = "*"
showOp Div = "/"

data Expr = Lit Int | Arith Expr Op Expr
  deriving (Eq)

eval :: Expr -> Int
eval (Lit n)        = n
eval (Arith x op y) = evalOp op (eval x) (eval y)

evalOp :: Op -> Int -> Int -> Int
evalOp Add = (+)
evalOp Sub = (-)
evalOp Mul = (*)
evalOp Div = div

instance Show Expr where
  showsPrec p (Lit n) = showsPrec p n
  showsPrec p (Arith x op y) =
    showParen (p > q) $ showsPrec q x . (opStr ++) . showsPrec (q+1) y
    where
      q = precOp op
      opStr = " " ++ showOp op ++ " "

tryMake :: Int -> [Int] -> [Expr]
tryMake n [] = error $ "tryMake " ++ show n ++ "[]"
tryMake n [x] = [ Lit x | n == x ]
tryMake n (x:xs) =
  [ Arith (Lit x) Add e | e <- tryMake (n - x) xs ] ++
  [ Arith (Lit x) Sub e | e <- tryMake (x - n) xs ] ++
  [ Arith e Sub (Lit x) | e <- tryMake (n + x) xs ] ++
  [ Arith (Lit x) Mul e | x `divides` n, e <- tryMake (n `div` x) xs ] ++
  [ Arith (Lit x) Div e | n /= 0, n `divides` x, e <- tryMake (x `div` n) xs ] ++
  [ Arith e Div (Lit x) | e <- tryMake (n * x) xs ]

divides :: Int -> Int -> Bool
x `divides` y = rem y x == 0
