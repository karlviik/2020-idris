import Data.Vect

addvect1: Vect n Int -> Vect n Int -> Vect n Int
addvect1 [] [] = []
addvect1 (x :: xs) (y :: ys) = (x + y) :: addvect1 xs ys

addvect2: Vect n Int -> Vect n Int -> Vect n Int
addvect2 = zipWith (+)

-- hacky or so
getnth1: Nat -> Vect n Int -> Int
getnth1 Z [] = 0
getnth1 Z (x :: xs) = x
getnth1 (S k) [] = 0
getnth1 (S k) (x :: xs) = getnth1 k xs

getnth2: Fin n -> Vect n Int -> Int
getnth2 FZ (x :: xs) = x
getnth2 (FS x) (y :: xs) = getnth2 x xs

getnthy: Vect n ty -> Fin n -> ty
getnthy (x :: xs) FZ = x
getnthy (y :: xs) (FS x) = getnthy xs x

forgetfirst: {k: Nat} -> (Fin (S k) -> ty) -> (Fin k -> ty)
forgetfirst f FZ = f (FS FZ)
forgetfirst f (FS x) = f (FS (FS x))

vectfromquery1: {m: Nat} -> (Fin m -> ty) -> Vect m ty
vectfromquery1 {m = Z} f = []
vectfromquery1 {m = (S k)} f = (f 0) :: (vectfromquery1 (forgetfirst f))

-- create a matrix type
Matrix : (m: Nat) -> (n: Nat) -> Type
Matrix m n = Vect m (Vect n Int)

addmatrix: Matrix m n -> Matrix m n -> Matrix m n
addmatrix = zipWith addvect2

allzeros: (m: Nat) -> Vect m Int
allzeros m = replicate m 0

identity: (m: Nat) -> Matrix m m
identity Z = []
identity (S k) = (1 :: allzeros k) :: map (\x => 0 :: x) (identity k)

sumofwhatevers: Vect m Int -> Vect m Int -> Int
sumofwhatevers xs ys = sum (zipWith (*) xs ys)

getijth: (i: Fin m) -> (j: Fin n) -> Matrix m n -> Int
getijth i j x = getnthy (getnthy x i) j

matrixfromquery: {m: Nat} -> {n: Nat} -> (Fin m -> Fin n -> Int) -> Matrix m n
matrixfromquery {m = Z} {n = n} f = []
matrixfromquery {m = (S k)} {n = n} f = vectfromquery1 (f 0) :: (matrixfromquery (forgetfirst f))

getrow: Fin m -> Matrix m n -> Vect n Int
getrow x y = getnthy y x

getcolumn: Fin n -> Matrix m n -> Vect m Int
getcolumn k a = vectfromquery1 (\l => getijth l k a)

getijthproduct: Matrix m n -> Matrix n p -> Fin m -> Fin p -> Int
getijthproduct a b k l = sumofwhatevers (getrow k a) (getcolumn l b)

multiplicationnn: Matrix m n -> Matrix n p -> Matrix m p
multiplicationnn x y = matrixfromquery (getijthproduct x y)
