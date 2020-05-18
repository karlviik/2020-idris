module ShapelyTree

% default total
% auto_implicits on
% access public export

{-
  Recall that the shape of a List was a Nat.
  The shape of a tree is something more complex:
          3                        ■
        /  \                     /   \
      1     5                  ■      ■
     / \   / \                / \    / \
    0  2  4  6               ■  ■   ■  ■
 -}


-- a type of shapes of trees
data  TreeShape  :  Type  where
	LeafShape  :  TreeShape
	NodeShape  :  (l : TreeShape) -> (r : TreeShape) -> TreeShape


-- trees indexed by their shape:
data  Tree  :  TreeShape -> Type -> Type  where
	Leaf  :  Tree LeafShape a
	Node  :  (left : Tree l a) -> (this : a) -> (right : Tree r a) ->
		Tree (NodeShape l r) a




-- zip together two trees of the same shape:
-- (this is exactly the same program as before, leaving out the bad cases)
zip_tree  :  Tree shape a -> Tree shape b -> Tree shape (Pair a b)
zip_tree Leaf Leaf  =  Leaf                                      -- search
zip_tree (Node left1 this1 right1) (Node left2 this2 right2)  =  --  search
	Node (zip_tree left1 left2) (this1 , this2) (zip_tree right1 right2)




-- We will make our paths more expressive by giving them as indices
-- the shape that the path leads to and the shape that the path is in:
data  PathTo  :  (target_shape : TreeShape) -> (tree_shape : TreeShape) -> Type  where
	Here  :  PathTo target_shape target_shape
	Left  :  (path : PathTo target_shape l) -> PathTo target_shape (NodeShape l r)
	Right :  (path : PathTo target_shape r) -> PathTo target_shape (NodeShape l r)




-- example: node replacement
-- replace the node at the given position:
-- (note that the tree shape is invariant)
replace_node  :  (new : a) -> PathTo (NodeShape l r) shape ->
	Tree shape a -> Tree shape a
replace_node new Here (Node left this right)  =  Node left new right
replace_node new (Left path) (Node left this right)  =
	Node (replace_node new path left) this right
replace_node new (Right path) (Node left this right)  =
	Node left this (replace_node new path right)

-- this is the same program as before, but without the bad cases;
-- so we don't need Maybe anymore.




-- (introduce as needed for tree_graft)
-- tree shape concatenation; i.e. grafting one tree shape onto another at a leaf
shape_graft  :  (branch_shape : TreeShape) -> (stalk_shape : TreeShape) ->
	(path : PathTo LeafShape stalk_shape) -> TreeShape
shape_graft branch_shape LeafShape Here  =  branch_shape
shape_graft branch_shape (NodeShape l r) (Left path)  =
	NodeShape (shape_graft branch_shape l path) r
shape_graft branch_shape (NodeShape l r) (Right path)  =
	NodeShape l (shape_graft branch_shape r path)

-- example: tree concatenation
-- graft one tree onto another at a given leaf path
-- (note the use of functions on types)
tree_graft  :  (branch : Tree branch_shape a) -> (stalk : Tree stalk_shape a) ->
	(path : PathTo LeafShape stalk_shape) ->
	Tree (shape_graft branch_shape stalk_shape path) a
tree_graft branch Leaf Here  =  branch                     --  search
tree_graft branch (Node left here right)  (Left path)  =   --  search
	Node (tree_graft branch left path) here right
tree_graft branch (Node left here right)  (Right path)  =  --  search
	Node left here (tree_graft branch right path)

-- again, it's the same program as before, but without the bad cases or Maybes.

