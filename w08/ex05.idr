tabulate: List a -> (Nat -> Maybe a)
tabulate [] k = Nothing
tabulate (x :: xs) Z = Just x
tabulate (x :: xs) (S k) = tabulate xs k

recover_helper: Nat -> (Nat -> Maybe a) -> List a
recover_helper k f = case f k of
                      Nothing => []
                      Just something => something :: (recover_helper (S k) f)

recover : (Nat -> Maybe a) -> List a
recover f = (recover_helper 0 f)

zero_to_nine : (Nat -> Maybe Nat)
zero_to_nine n = if n < 10 then Just n else Nothing

-- recover_all : (Nat -> Maybe a) -> List a Impossible, example for when the first thing starts from 12389

tabTail : (Nat -> Maybe a) -> (Nat -> Maybe a)
tabTail f = \x => f (x + 1)

tabMap : (a -> b) -> (Nat -> Maybe a) -> (Nat -> Maybe b)
tabMap f g k = case g k of
                Nothing => Nothing
                Just bla => Just (f bla)

---------------------------------------TREE------------------------------------

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

example_tree : Tree Nat
example_tree = Node (Node (Node Leaf 1 Leaf) 2 (Node Leaf 3 Leaf)) 4 (Node Leaf 5 (Node Leaf 6 Leaf))

in_order : Tree a -> List a
in_order Leaf = []
in_order (Node x y z) = (in_order x) ++ [y] ++ (in_order z)

pre_order : Tree a -> List a
pre_order Leaf = []
pre_order (Node x y z) = [y] ++ (pre_order x) ++ (pre_order z)

post_order : Tree a -> List a
post_order Leaf = []
post_order (Node x y z) = (post_order x) ++ (post_order z) ++ [y]

insert : Nat -> Tree Nat -> Tree Nat
insert k Leaf = Node Leaf k Leaf
insert k (Node x y z) = if k <= y then Node (insert k x) y z else Node x y (insert k z)

tree_builder : List Nat -> Tree Nat -> Tree Nat
tree_builder [] tree = tree
tree_builder (x :: xs) tree = tree_builder xs (insert x tree)

sort : List Nat -> List Nat
sort xs = in_order (tree_builder xs Leaf)

Path : Type
Path = List Bool

follow : Path -> Tree a -> Maybe a
follow [] Leaf = Nothing
follow [] (Node x y z) = Just y
follow (x :: xs) Leaf = Nothing
follow (False :: xs) (Node x y z) = follow xs x
follow (True :: xs) (Node x y z) = follow xs z

path_to : Nat -> Tree Nat -> Maybe Path
path_to k Leaf = Nothing
path_to k (Node x y z) = if k == y
                          then Just []
                          else if k < y
                            then case path_to k x of
                              Nothing => Nothing
                              Just path => Just (False :: path)
                            else case path_to k z of
                              Nothing => Nothing
                              Just path => Just (True :: path)
