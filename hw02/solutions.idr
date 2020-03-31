import Data.String

----------------------GIVEN STUFF-----------------------------------

-- given data type
data RoseTree : Type -> Type where
   Rose : a -> List (RoseTree a) -> RoseTree a

-- given example tree
exampleTree : RoseTree Nat
exampleTree = Rose 6 [Rose 7 [Rose 4 [], Rose 3 [], Rose 8 [ Rose 9 [], Rose 10 []]]]

-- helper for drawing the tree
draw : RoseTree String -> List String
draw (Rose x ts') = lines x ++ drawSubTrees ts'
 where
   shift : String -> String -> List String -> List String
   shift first other more =
      zipWith (++) (first :: (replicate (length more) other)) more
   drawSubTrees : List (RoseTree String) -> List String
   drawSubTrees [] = []
   drawSubTrees [t] =
     "|" :: shift "'- " "   " (draw t)
   drawSubTrees (t :: ts) =
     "|" :: shift "+- " "|  " (draw t) ++ drawSubTrees ts

Show a => Show (RoseTree a) where
  show t = unlines (draw (stringify t))
    where
      stringify : RoseTree a -> RoseTree String
      stringify (Rose x xs) = Rose (show x) (map stringify xs)

-- datatype we'll be using
data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

KVStore : Type -> Type
KVStore a = Tree (Nat,a)
------------------- PART ONE -------------------


-- Write a function foldRoseTree, which implements the fold for RoseTree.
-- second parameter isn't used in these tasks, but leaving it in in case the functionality of it is required, it being adding certain Roses to all Rose lists.
foldRoseTree : (a -> List b -> b) -> List b -> RoseTree a -> b
foldRoseTree f e (Rose x xs) = f x (foldr (\a, bs => foldRoseTree f e a :: bs) e xs)

-- Write a function mapRoseTree : (a -> b) -> RoseTree a -> RoseTree b, which behaves analogously to the other map functions we have seen.
mapRoseTree : (a -> b) -> RoseTree a -> RoseTree b
mapRoseTree f x = foldRoseTree (\y, ys => Rose (f y) ys) [] x

-- Write a function flattenRose : RoseTree a -> List a that returns a pre-order traversal of the given tree.
flattenRose : RoseTree a -> List a
flattenRose x = foldRoseTree (\y, ys => y :: (foldr (\a, b => a ++ b) [] ys)) [] x

-- Write a function reverseRose : RoseTree a -> RoseTree a that reverses the given tree.
reverseRose : RoseTree a -> RoseTree a
reverseRose x = foldRoseTree (\y, ys => Rose y (reverse ys)) [] x

-- Write a function sumRose : RoseTree Nat -> Nat which sums the contents of the given tree.
sumRose : RoseTree Nat -> Nat
sumRose x = foldRoseTree (\y, ys => y + (sum ys)) [] x

-- Write a function maxRose : Rose Nat -> Nat which computes the largest entry in the given tree.
maxRose : RoseTree Nat -> Nat
maxRose x = foldRoseTree (\y, ys => max y (foldr (\a, b => max a b) Z ys)) [] x


------------------- PART TWO -------------------

-- Write a function that inserts the first argument into the key-value store, returning the result.
insert : (Nat,a) -> KVStore a -> KVStore a
insert x Leaf = Node Leaf x Leaf
insert (k,v) (Node l (nk,nv) r) = if k == nk
                                  then Node l (k,v) r
                                  else if k < nk
                                    then Node (insert (k,v) l) (nk,nv) r
                                    else Node l (nk,nv) (insert (k,v) r)


-- Write a function that draws a key-value store of strings by first converting it to a rose tree, and drawing that.
treeToRoseTree : Tree a -> Maybe (RoseTree a)
treeToRoseTree Leaf = Nothing
treeToRoseTree (Node x y z) = let left = case treeToRoseTree x of
                                          Nothing => []
                                          Just a => [a]
                                  right = case treeToRoseTree z of
                                          Nothing => []
                                          Just a => [a]
                              in Just (Rose y (left ++ right))

drawStore : KVStore String -> IO ()
drawStore x = case treeToRoseTree x of
                Nothing => putStrLn "'tis an emptry tree"
                Just roseTree => putStrLn (show (the (RoseTree String) (foldRoseTree (\(k,v), xs => Rose ((show k) ++ " => " ++ v) xs) [] roseTree)))

exampleStore : KVStore String
exampleStore = insert (7, "apple") $
               insert (6 , "papaya") $
               insert (4 , "mango") $
   	           insert (3 , "orange") $
 		           insert (7 , "cabbage") $
               insert (10 , "pineapple") $
               insert (5 , "banana") Leaf


-- Write a function that deletes the node with the given key (in any) from the store , returning the result. Again, be sure that the result of a deletion remains a binary search tree.
----------------- helpers -----------------
getAndRemoveMaxNode : KVStore a -> Maybe (KVStore a,(Nat,a))
getAndRemoveMaxNode Leaf = Nothing
getAndRemoveMaxNode (Node Leaf y Leaf) = Just (Leaf,y)
getAndRemoveMaxNode (Node (Node x z w) y Leaf) = Just (Node x z w,y)
getAndRemoveMaxNode (Node x y (Node z w s)) = let Just (Node a b c,k) = getAndRemoveMaxNode (Node z w s)
                                              in Just (Node x y (Node a b c),k)

getAndRemoveMinNode : KVStore a -> Maybe (KVStore a,(Nat,a))
getAndRemoveMinNode Leaf = Nothing
getAndRemoveMinNode (Node Leaf y Leaf) = Just (Leaf,y)
getAndRemoveMinNode (Node Leaf y (Node x z w)) = Just (Node x z w,y)
getAndRemoveMinNode (Node (Node z w s) y x) = let Just (Node a b c,k) = getAndRemoveMinNode (Node z w s)
                                              in Just (Node (Node a b c) y x,k)

delete : Nat -> KVStore a -> KVStore a
delete k Leaf = Leaf
delete k (Node x (a, b) z) =  if k < a
                              then Node (delete k x) (a, b) z
                              else if k > a
                                then Node x (a, b) (delete k z)
                                else case Node x (a, b) z of
                                  Node (Node xa xb xc) (a, b) z => let Just (subTree, subPair) = getAndRemoveMaxNode (Node xa xb xc) in Node subTree subPair z
                                  Node Leaf (a, b) (Node za zb zc) => let Just (subTree, subPair) = getAndRemoveMinNode (Node za zb zc) in Node x subPair subTree
                                  Node Leaf (a, b) Leaf => Leaf


-- Write a function edit : KVStore String -> IO (KVStore String)
-- > :exec (edit exampleStore) -> this didn't seem to work for me: https://i.imgur.com/KdQiSwq.png so I wrapped it for testing
edit : KVStore String -> IO (KVStore String)
edit x = let invalidness = do
                            putStrLn "Invalid command."
                            edit x
         in do
            putStrLn "\nThe current tree is: \n"
            drawStore x
            putStrLn "Please enter a command: '. Nat' for removing and 'Nat String' for removing, 'done' to exit."
            input <- getLine
            case words input of
              [] => invalidness
              (a :: []) => if a == "done" then pure x else invalidness
              (a :: b :: rest) => if a == "."
                then case parsePositive b of
                  Nothing => invalidness
                  Just pos => edit (delete (toNat pos) x)
                else case parsePositive a of
                  Nothing => invalidness
                  Just pos => edit (insert (toNat pos, unwords (b :: rest)) x)


wrapper : KVStore String -> IO ()
wrapper x = do
              s <- edit x
              putStrLn "Thanks, I guess"
