increment: Int -> Double
increment x = cast x + 1

add: Int -> Int -> Int
add x y = x + y

len: (List Int) -> Int
len [] = 0
len (x :: xs) = 1 + len xs

addnats: Nat -> Nat -> Nat
addnats Z j = j
addnats (S k) j = S (addnats k j)

multnats: Nat -> Nat -> Nat
multnats Z j = Z
multnats (S k) j = j + (multnats k j)

repeat: ty -> Nat -> (List ty)
repeat x Z = []
repeat x (S k) = x :: (repeat x k)

stutter: (List ty) -> Nat -> (List ty)
stutter [] k = []
stutter (x :: xs) k = (repeat x k) ++ (stutter xs k)

zip_it: List ty -> List tya -> List (ty, tya)
zip_it [] ys = []
zip_it xs [] = []
zip_it (x :: xs) (y :: ys) = (x, y) :: (zip_it xs ys)

record Address where
  constructor MkAaddress
  number: Int
  street, city: String
  postcode: Int
  country: String
