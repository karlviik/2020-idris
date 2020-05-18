foldNat : b -> (b -> b) -> Nat -> b
foldNat z s Z = z
foldNat z s (S n) = s (foldNat z s n)

foldList : (a -> b -> b) -> b -> List a -> b
foldList = foldr

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
foldTree l n Leaf = l
foldTree l n (Node tl x tr) = n (foldTree l n tl) x (foldTree l n tr)

--------------------------------------------------------------------------------

-- maybe empty case could be false?
andList : List Bool -> Bool
andList xs = foldList (\a, b => a && b) True xs

-- maybe empty case could be true?
orList  : List Bool -> Bool
orList xs = foldList (\a, b => a || b) False xs

multList : List Nat -> Nat
multList [] = 0
multList (x :: xs) = foldList (\a, b => a * b) 1 (x :: xs)

addList  : List Nat -> Nat
addList xs = foldList (\a, b => a + b) 0 xs

exp : Nat -> Nat -> Nat
exp k Z = 1
exp k (S j) = foldNat k (\x => x * k) j

flatten : List (List a) -> List a
flatten xs = foldList (\a, b => a ++ b) [] xs

filter : (a -> Bool) -> List a -> List a
filter f xs = foldList (\a, b => if f a then a :: b else b) [] xs

-- foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
reverseTree : Tree a -> Tree a
reverseTree tree = foldTree Leaf (\l, m, r => Node r m l) tree

andTree  : Tree Bool -> Bool
andTree x = foldTree True (\l, m, r => l && m && r) x

orTree   : Tree Bool -> Bool
orTree x = foldTree False (\l, m, r => l || m || r) x

addTree  : Tree Nat -> Nat
addTree x = foldTree 0 (\l, m, r => l + m + r) x

multTree : Tree Nat -> Nat
multTree x = foldTree 1 (\l, m, r => l * m * r) x

in_order   : Tree a -> List a
in_order x = foldTree [] (\l, m, r => l ++ (m :: r)) x

pre_order  : Tree a -> List a
pre_order x = foldTree [] (\l, m, r => (m :: l) ++ r) x

post_order : Tree a -> List a
post_order x = foldTree [] (\l, m, r => l ++ r ++ [m]) x

beadthFirst : Tree a -> List a
beadthFirst x = flatten (foldTree [] (\ls, m, rs => [m] :: (zipWith (\a, b => a ++ b) ls rs)) x)
