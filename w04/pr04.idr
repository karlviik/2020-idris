import Data.Vect

Matrix : (m: Nat) -> (n: Nat) -> Type -> Type
Matrix m n t = Vect m (Vect n t)


add: {m, n : Nat} -> Matrix m n Integer -> Matrix m n Integer -> Matrix m n Integer
add [] [] = []
add (x :: xs) (y :: ys) = (zipWith (+) x y) :: (add xs ys)

transposeVector: {n: Nat} -> Vect n t -> Vect n (Vect 1 t)
transposeVector [] = []
transposeVector (x :: xs) = [x] :: transposeVector xs

transposeMatrix: {t: Type} -> {m, n: Nat} -> Matrix m n t -> Matrix n m t
transposeMatrix {m = Z} {n = n} x = replicate n []
transposeMatrix {m = (S k)} {n = n} (x :: xs) = zipWith (++) (transposeVector x) (transposeMatrix xs)

sumofproducts: {n : Nat} -> Vect n Integer -> Vect n Integer -> Integer
sumofproducts xs ys = sum (zipWith (*) xs ys)

mult: {m : Nat} -> {n : Nat} -> Matrix m n Integer -> {p : Nat} -> Matrix n p Integer -> Matrix m p Integer
mult [] y = []
mult (x :: xs) y =  let rest_rows = mult xs y
                        first_row = map (\foo => sumofproducts foo x) (transposeMatrix y)
                    in  first_row :: rest_rows

elem_mult: {m , n : Nat} -> Fin m -> Integer -> Matrix m n Integer -> Matrix m n Integer
elem_mult FZ factor (x :: xs) = x :: xs
elem_mult (FS FZ) factor (y :: xs) = (map (\x => x * factor) y) :: xs
elem_mult (FS (FS x)) factor (y :: xs) = y :: (elem_mult (FS x) factor xs)
