import Data.Vect
import Syntax.PreorderReasoning

-- Author: Karl Viik
-- helpers & data types & interfaces from lecure files

---------------------------------- Problem 1 ----------------------------------

---- SHAPELY TREE ----
data  TreeShape  :  Type  where
	LeafShape  :  TreeShape
	NodeShape  :  (l : TreeShape) -> (r : TreeShape) -> TreeShape

data  Tree  :  TreeShape -> Type -> Type  where
	Leaf  :  Tree LeafShape a
	Node  :  (left : Tree l a) -> (this : a) -> (right : Tree r a) ->
		Tree (NodeShape l r) a
---- END OF SHAPELY TREE ----


implementation Eq type => Eq (Tree shape type) where
  Leaf == Leaf  =  True
  (Node left_1 this_1 right_1) == (Node left_2 this_2 right_2)  =
    this_1 == this_2 && left_1 == left_2 && right_1 == right_2


---------------------------------- Problem 2 ----------------------------------

---- INTERFACE ----
interface  Bifunctor (t : Type -> Type -> Type)  where
	bimap  :  (a -> b) -> (c -> d) -> t a c -> t b d
---- END OF INTERFACE ----


implementation Bifunctor Either where
  bimap f1 f2 (Left l) = Left (f1 l)
  bimap f1 f2 (Right r) = Right (f2 r)


---------------------------------- Problem 3 ----------------------------------


---- HELPERS ----
head  :  Tree (NodeShape l r) a -> a
head (Node left this right) = this

left_tail  :  Tree (NodeShape l r) a -> Tree l a
left_tail (Node left this right)  =  left

right_tail  :  Tree (NodeShape l r) a -> Tree r a
right_tail (Node left this right)  =  right
---- END OF HLELPERS ----


implementation Functor (Tree shape) where
  map f Leaf = Leaf
  map f (Node left this right) = Node (map f left) (f this) (map f right)

implementation Applicative (Tree shape) where
  pure {shape = LeafShape} value = Leaf
  pure {shape = (NodeShape l r)} value = Node (pure value) value (pure value)
  (<*>) Leaf Leaf = Leaf
  (<*>) (Node left_fs f right_fs) (Node left_v val right_v) =
    Node (left_fs <*> left_v) (f val) (right_fs <*> right_v)

implementation Monad (Tree shape) where
  join {shape = LeafShape} Leaf = Leaf
  join {shape = (NodeShape l r)} (Node left this right) =
    Node (join (onlyLeft left)) (head this) (join (onlyRight right))
    where
      onlyLeft : Tree justAShape (Tree (NodeShape lefty righty) a) -> Tree justAShape (Tree lefty a)
      onlyLeft Leaf = Leaf
      onlyLeft (Node left val right) =
        Node (onlyLeft left) (left_tail val) (onlyLeft right)
      onlyRight : Tree justAShape (Tree (NodeShape lefty righty) a) -> Tree justAShape (Tree righty a)
      onlyRight Leaf = Leaf
      onlyRight (Node left val right) =
        Node (onlyRight left) (right_tail val) (onlyRight right)


---------------------------------- Problem 4 ----------------------------------

---- HELPERS ----
pred_equal  :  {m , n : Nat} -> S m = S n -> m = n
pred_equal Refl = Refl

plus_zero_right  :  {n : Nat} -> n + 0 = n
plus_zero_right {n = Z}  =  Refl
plus_zero_right {n = (S n)}  =  cong {f = S} plus_zero_right

plus_succ_right  :  {m , n : Nat} -> m + (S n) = S (m + n)
plus_succ_right {m = Z} {n = n}  =  Refl
plus_succ_right {m = (S m)} {n = n}  =  cong {f = S} plus_succ_right
---- END OF HELPERS ----


plus_inj_right  :  {m, n, n': Nat} -> m + n = m + n' -> n = n'
plus_inj_right {m = Z} Refl = Refl
plus_inj_right {m = (S k)} w = plus_inj_right (pred_equal w)

plus_inj_left : {m, n, n': Nat} -> n + m = n' + m -> n = n'
plus_inj_left {m = Z} {n = n} {n' = n'} prf =
	(n)
		={ sym plus_zero_right }=
	(n + 0)
		={ prf }=
	(n' + 0)
		={ plus_zero_right }=
	(n')
		QED
plus_inj_left {m = (S k)} prf = plus_inj_left (pred_equal (successor_out prf)) where
	successor_out : a + (S c) = b + (S c) -> S (a + c) = S (b + c)
	successor_out {a = a} {b = b} {c = c} prf =
		(S (a + c))
			={ sym plus_succ_right }=
		(a + (S c))
			={ prf }=
		(b + (S c))
			={ plus_succ_right }=
		(S (b + c))
			QED


---------------------------------- Problem 5 ----------------------------------


---- DATATYPE ----
data  Even  :  (n : Nat) -> Type  where
	Z_even   :  Even Z
	SS_even  :  Even n -> Even (S (S n))
---- END OF DATATYPE ----

---- HELPERS ----
plus_zero_left  :  {n : Nat} -> 0 + n = n
plus_zero_left  =  Refl

plus_succ_left  :  {m , n : Nat} -> (S m) + n = S (m + n)
plus_succ_left  =  Refl

plus_sym  :  {m , n : Nat} -> m + n = n + m
plus_sym {m = Z} {n = n}  =
	(0 + n)
		={ plus_zero_left }=
	(n)
		={ sym plus_zero_right }=
	(n + 0)
		QED
plus_sym {m = (S m)} {n = n}  =
	(S m + n)
		={ plus_succ_left }=
	(S (m + n))
		={ cong {f = S} plus_sym }=
	(S (n + m))
		={ sym plus_succ_right }=
	(n + S m)
		QED
---- END OF HELPERS ----


even_plus_sym  :  {m , n : Nat} -> Even (m + n) -> Even (n + m)
even_plus_sym {m = m} {n = n} evone = replace {P = \x => Even x} plus_sym evone


---------------------------------- Problem 6 ----------------------------------

---- HELPER ----
plus_one_is_succ : {a: Nat} -> a + 1 = S a
plus_one_is_succ {a = Z} = Refl
plus_one_is_succ {a = (S k)} = cong {f = S} plus_one_is_succ
---- END OF HELPER ----


rotate_vect  :  Nat -> Vect n a -> Vect n a
rotate_vect Z xs = xs
rotate_vect (S k) [] = []
rotate_vect (S k) (x :: xs) = rotate_vect k (replace {P = \x => Vect x a} plus_one_is_succ (xs ++ [x]))
