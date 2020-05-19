-----------------------------------------------
-------------------- 1 & 2 --------------------
-----------------------------------------------
import Data.String

-- cast
increment: Int -> Double
increment x = cast x + 1

-- tuple
zip_it: List a -> List b -> List (a, b)

-- data structure
record Address where
  constructor MkAaddress
  number: Int
  street, city: String
  postcode: Int
  country: String

record Street where
  constructor MkStreet
  number: Int
  street: String

getStreet: Address -> Street
getStreet x = MkStreet (number x) (street x)

setStreet: Street -> Address -> Address
-- set_StructureParamName value whereToPutIt
-- structureParamName StructureWhereToGetThatParamName
setStreet x y = set_number (number x) (set_street (street x) y)

-- unpack StrintToTurnIntoListOfChars
-- pack listOfCharsToTurnIntoString
-- sort listToSortNaturally
-- take howMany listToTakeHowManyFirstElements
-- map function list
-- sum ListOfNumbersToSum
-- filter funcOfElemToBool listOfElems
-- mod number ToDivideByNum
-- parseInteger stringToParse
-- words stringToTurnIntoListOfWords
-- repl promptToShow functionOfStrToStrForInput IO()

-----------------------------------------------
-------------------- 3 & 4 --------------------
-----------------------------------------------

forgetfirst: {k: Nat} -> (Fin (S k) -> ty) -> (Fin k -> ty)
forgetfirst f FZ = f (FS FZ)
forgetfirst f (FS x) = f (FS (FS x))

-- zipWith functionOfA&BToC listOrVect
-- show thingToConvertToString
Matrix : (m: Nat) -> (n: Nat) -> Type -> Type
Matrix m n t = Vect m (Vect n t)
-- replicate howManyTimes whatToReplicate
transposeVector: {n: Nat} -> Vect n t -> Vect n (Vect 1 t)
transposeVector [] = []
transposeVector (x :: xs) = [x] :: transposeVector xs

transposeMatrix: {t: Type} -> {m, n: Nat} -> Matrix m n t -> Matrix n m t
transposeMatrix {m = Z} {n = n} x = replicate n []
transposeMatrix {m = (S k)} {n = n} (x :: xs) = zipWith (++) (transposeVector x) (transposeMatrix xs)

runner_sum: Nat -> IO Nat
runner_sum k = do
                putStrLn "enter a number:"
                a <- getLine
                case the (Maybe Nat) (parsePositive a) of
                  Just x => runner_sum (k + x)
                  Nothing => pure k
running_sum: IO Nat
running_sum = runner_sum 0

-----------------------------------------------
-------------------- 5 & 6 --------------------
-----------------------------------------------

zero_to_nine : (Nat -> Maybe Nat)
zero_to_nine n = if n < 10 then Just n else Nothing

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

Path : Type
Path = List Bool

-- foldr functionThatTakesTwoElementsAndProducesOutput lastElement list
andList : List Bool -> Bool
andList xs = foldr (\a, b => a && b) True xs

-- foldTree lastOrPrevElement --
----- functionThatTakesResultsFromBothBranchesAndGivesResultType
---------- tree
foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
foldTree l n Leaf = l
foldTree l n (Node tl x tr) = n (foldTree l n tl) x (foldTree l n tr)


-----------------------------------------------
-------------------- 7 & 8 --------------------
-----------------------------------------------

Name : Type
Name = String

data Expr : Type where
  Num : Int -> Expr
  Add : Expr -> Expr -> Expr
  Mul : Expr -> Expr -> Expr
  Sub : Expr -> Expr -> Expr
  Div : Expr -> Expr -> Expr
  Var : Name -> Expr

-- showing expr, defining how it's done
Show Expr where
  show (Num x) = show x
  show (Add x y) = "(" ++ show x ++ " + " ++ show y ++ ")"
  show (Sub x y) = "(" ++ show x ++ " - " ++ show y ++ ")"
  show (Div x y) = "(" ++ show x ++ " / " ++ show y ++ ")"
  show (Mul x y) = "(" ++ show x ++ " * " ++ show y ++ ")"
  show (Var x) = x

data  TreeShape  :  Type  where
	LeafShape  :  TreeShape
	NodeShape  :  (l : TreeShape) -> (r : TreeShape) -> TreeShape
data  Tree  :  TreeShape -> Type -> Type  where
	Leaf  :  Tree LeafShape a
	Node  :  (left : Tree l a) -> (this : a) -> (right : Tree r a) ->
		Tree (NodeShape l r) a

learn_shape  :  (tree : ShapelessTree.Tree type) -> ShapelyTree.Tree (get_shape tree) type
learn_shape Leaf = Leaf
learn_shape (Node left this right) = Node (learn_shape left) this (learn_shape right)


-----------------------------------------------
-------------------- 9 & 10 -------------------
-----------------------------------------------
-- interface for Preorder, leq type type -> yes or no
-- interface  <Interface Name> [Interface Variables]  where
-- 	[Interface Methods]

interface   Preorder (a : Type)  where
  leq : a -> a -> Bool

-- elem elementYoureSearchingFor listYou'reSearchingFrom
implementation   Eq a => Preorder (List a)  where
  leq [] ys  =  True
  leq (x :: xs) ys  =
    case elem x ys of
      False => False
      True => leq xs (delete x ys)

implementation [Multiset]  Eq a => Eq (List a)  where
  xs == ys  =  leq xs ys

-- [1,2] == [2,1] = False
-- (==) @{Multiset} [1,2] [2,1] = True

-- use the semigroup instance for strings:
hi  :  String
hi  =  "hello" <+> " " <+> "world"


--  redefine the Semigroup instance for List:
implementation [ListSemigroup] Semigroup (List a)  where
	-- (<+>)  :  List a -> List a -> List a
	(<+>)  =  (++)

--  redefine the Monoid instance for List:
implementation [ListMonoid] Monoid (List a) using ListSemigroup where
	-- neutral  :  List a
	neutral  =  []

consolidate : List (Maybe a) -> Maybe (List a)
consolidate [] = pure []
consolidate (x :: xs) = pure (++) <*> (pure (\y => [y]) <*> x) <*> consolidate xs



-----------------------------------------------
------------------- 11 & 12 -------------------
-----------------------------------------------
import Syntax.PreorderReasoning
((m_s + n) + (m_s * n))
  ={ sym plus_assoc }=
(m_s + (n + (m_s * n)))
  QED
reverse_vect  :  Vect n a -> Vect n a
reverse_vect [] = []
reverse_vect (x :: xs) {n = (S n_s)} {a = a} = replace {P = \y => Vect y a} plus_one_is_succ ((reverse_vect xs) ++ [x])

plus_one_is_succ : {a: Nat} -> a + 1 = S a
plus_one_is_succ {a = Z} = Refl
plus_one_is_succ {a = (S k)} = cong {f = S} plus_one_is_succ


implementation [custom] DecEq a => DecEq (Vect n a)  where
  decEq [] []  =  Yes Refl
  decEq (x :: xs) (y :: ys)  =
    case decEq x y of
      Yes prf_h =>
        case decEq xs ys of
          Yes prf_t => Yes (cons_equal prf_h prf_t)
          No contra => No (tails_differ contra)
      No contra => No (heads_differ contra)
