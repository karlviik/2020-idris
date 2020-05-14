
-- Consider the following datatype of arithmetic expressions:
Name : Type
Name = String

data Expr : Type where
  Num : Int -> Expr
  Add : Expr -> Expr -> Expr
  Mul : Expr -> Expr -> Expr
  Sub : Expr -> Expr -> Expr
  Div : Expr -> Expr -> Expr
  Var : Name -> Expr

-- with associated Show instance:
Show Expr where
  show (Num x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Var x) = x

exampleExpr : Expr
exampleExpr = Add (Num 2) (Mul (Num 3) (Num 5))

-- Write a function that returns the number of operations in an expression
size : Expr -> Nat
size (Num x) = Z
size (Add x y) = 1 + (size x) + (size y)
size (Mul x y) = 1 + (size x) + (size y)
size (Sub x y) = 1 + (size x) + (size y)
size (Div x y) = 1 + (size x) + (size y)
size (Var x) = Z

-- A Context is an assignment of Names to Ints , represented as follows:
Context : Type
Context = List (Name,Int)

-- returns what the input name stands for in the input context, if anything.
find : Name -> Context -> Maybe Int
find name [] = Nothing
find name ((a, b) :: xs) = if name == a then Just b else find name xs

-- Write a function that evaluates an expression
verify : Maybe Double -> Maybe Double -> Maybe (Double, Double)
verify x y =  case x of
                Nothing => Nothing
                Just num => case y of
                  Nothing => Nothing
                  Just nam => Just (num, nam)

eval : Context -> Expr -> Maybe Double
eval context (Num y) = Just (cast y)
eval context (Add y z) = case verify (eval context y) (eval context z) of
                          Nothing => Nothing
                          Just (a, b) => Just (a + b)
eval context (Mul y z) = case verify (eval context y) (eval context z) of
                          Nothing => Nothing
                          Just (a, b) => Just (a * b)
eval context (Sub y z) = case verify (eval context y) (eval context z) of
                          Nothing => Nothing
                          Just (a, b) => Just (a - b)
eval context (Div y z) = case verify (eval context y) (eval context z) of
                          Nothing => Nothing
                          Just (a, b) => Just (a / b)
eval context (Var name) = case find name context of
                            Nothing => Nothing
                            Just x => Just (cast x)



-- (More Difficult / Optional) Write a parser for your type of expressions

parseExpr : String -> Maybe Expr

-- The representation of Exprs as strings is up to you.
