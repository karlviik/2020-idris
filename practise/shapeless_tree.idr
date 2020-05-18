module ShapelessTree

% default total
% auto_implicits on
% access public export


-- a (node-labeled binary) Tree is like a List with two tails:
data  Tree  :  Type -> Type  where
	Leaf  :  Tree a                                                         --  c.f. Nil
	Node  :  (left : Tree a) -> (this : a) -> (right : Tree a) -> Tree a    --  c.f. ( :: )
-- if we give names to the arguments, Idris will use them in case splits




-- example: tree zipping:
zip_tree  :  Tree a -> Tree b -> Tree (Pair a b)
zip_tree Leaf Leaf  =  Leaf
zip_tree Leaf (Node left this right)  =  Leaf  --  shouldn't really happen
zip_tree (Node left this right) Leaf  =  Leaf  --  shouldn't really happen
zip_tree (Node left1 this1 right1) (Node left2 this2 right2)  =
	Node (zip_tree left1 left2) (this1 , this2) (zip_tree right1 right2)




-- We can replace an element at a given position in a tree, as we did with lists.
-- In a list, a position is determined by a Nat index.
-- In a tree, a position is determined by a path:

-- (possibly) a path to a position in a tree (Leaf or Node):
data  Path  :  Type  where
	Here  :  Path
	Left  :  (path : Path) -> Path
	Right :  (path : Path) -> Path


-- example: node replacement
-- (possibly) replace the node at the given position:
-- (split first on the tree: for a Leaf we should retun Nothing regardless of path)
replace_node  :  (new : a) -> Path -> Tree a -> Maybe (Tree a)
replace_node new path Leaf  =  Nothing
replace_node new Here (Node left this right)  =  Just (Node left new right)
replace_node new (Left path) (Node left this right)  =
	case  replace_node new path left  of
		Nothing  =>  Nothing
		Just new_left  =>  Just (Node new_left this right)
replace_node new (Right path) (Node left this right)  =
	case  replace_node new path right  of
		Nothing  =>  Nothing
		Just new_right  =>  Just (Node left this new_right)

-- The Nothing cases are really just noise.
-- We only need them to deal with bad input.




-- example: tree concatenation
{-
        ^
      / s \
     ----^-
       / b \
      ------
 -}
-- (possibly) graft one tree onto another at a given leaf path:
tree_graft  :  (branch : Tree a) -> (stalk : Tree a) ->
	(path : Path) -> Maybe (Tree a)
tree_graft branch Leaf Here  =  Just branch
tree_graft branch Leaf (Left path)  =  Nothing
tree_graft branch Leaf (Right path)  =  Nothing
tree_graft branch (Node left this right) Here  =  Nothing
tree_graft branch (Node left this right) (Left path)  =
	case  tree_graft branch left path  of
		Nothing  =>  Nothing
		Just new_left  =>  Just (Node new_left this right)
tree_graft branch (Node left this right) (Right path)  =  --  reflect the left case
	case  tree_graft branch right path  of
		Nothing  =>  Nothing
		Just new_right  =>  Just (Node left this new_right)

-- Again, there's a lot of Maybe noise.
-- "There's got to be a better way!"

