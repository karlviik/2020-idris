import shapeless_tree
import shapely_tree


-- Task 1
zipwith_shapeless_tree  :  (a -> b -> c) -> Tree a -> Tree b -> Tree c
zipwith_shapeless_tree f Leaf y = Leaf
zipwith_shapeless_tree f (Node left this right) Leaf = Leaf
zipwith_shapeless_tree f (Node left_1 this_1 right_1) (Node left_2 this_2 right_2) = Node (zipwith_shapeless_tree f left_1 left_2) (f this_1 this_2) (zipwith_shapeless_tree f right_1 right_2)


-- Task 2
zipwith_shapely_tree  :  (a -> b -> c) -> Tree shape a -> Tree shape b -> Tree shape c
zipwith_shapely_tree f Leaf Leaf = Leaf
zipwith_shapely_tree f (Node left1 this1 right1) (Node left2 this2 right2) = Node (zipwith_shapely_tree f left1 left2) (f this1 this2) (zipwith_shapely_tree f right1 right2)


-- Task 3
unzip_tree  :  Tree shape (Pair a b) -> Pair (Tree shape a) (Tree shape b)
unzip_tree Leaf = (Leaf, Leaf)
unzip_tree (Node left (a, b) right) = let (lltree, lrtree) = unzip_tree left
                                          (rltree, rrtree) = unzip_tree right
                                      in (Node lltree a rltree, Node lrtree b rrtree)


-- Task 4
forget_shape  :  ShapelyTree.Tree shape type -> ShapelessTree.Tree type
forget_shape Leaf = Leaf
forget_shape (Node left this right) = Node (forget_shape left) this (forget_shape right)


-- Task 5
get_shape : ShapelessTree.Tree type -> ShapelyTree.TreeShape
get_shape Leaf = LeafShape
get_shape (Node left this right) = NodeShape (get_shape left) (get_shape right)

learn_shape  :  (tree : ShapelessTree.Tree type) -> ShapelyTree.Tree (get_shape tree) type
learn_shape Leaf = Leaf
learn_shape (Node left this right) = Node (learn_shape left) this (learn_shape right)


-- Task 6
flip_shape : TreeShape -> TreeShape
flip_shape LeafShape = LeafShape
flip_shape (NodeShape l r) = NodeShape (flip_shape r) (flip_shape l)

reflect_tree  :  Tree shape type -> Tree (flip_shape shape) type
reflect_tree Leaf = Leaf
reflect_tree (Node left this right) = Node (reflect_tree right) this (reflect_tree left)


-- Task 7
combine_shapes : TreeShape -> TreeShape -> TreeShape
combine_shapes LeafShape y = LeafShape
combine_shapes (NodeShape l r) LeafShape = LeafShape
combine_shapes (NodeShape l r) (NodeShape x y) = NodeShape (combine_shapes l x) (combine_shapes r y)

prune_tree  :  (template_shape : TreeShape) -> Tree tree_shape type -> Tree (combine_shapes template_shape tree_shape) type
prune_tree LeafShape x = Leaf
prune_tree (NodeShape l r) Leaf = Leaf
prune_tree (NodeShape l r) (Node left this right) = Node (prune_tree l left) this (prune_tree r right)
