import Data.Vect

pair: (c -> a) -> (c -> b) -> (c -> (a, b))
pair f g x = (f x, g x)

copair: (a -> c) -> (b -> c) -> (Either a b -> c)
copair f g (Left l) = f l
copair f g (Right r) = g r

showw: Either Bool Int -> String
-- show = copair you can use that thing here now
showw (Left l) = "Bool: " ++ show l
showw (Right r) = "Int: " ++ show r

fourints: Vect 4 Int
fourints = [1, 2, 3, 4]

sixints: Vect 6 Int
sixints = [5, 6, 7, 8, 9, 10]

tenints: Vect 10 Int
tenints = sixints ++ fourints

add : Vect m Int -> Vect m Int -> Vect m Int
add = zipWith (+)
-- add [] [] = []
-- add (x :: xs) (y :: ys) = x + y :: (add xs ys)

concat: Vect m ty -> Vect n ty -> Vect (m + n) ty
-- concat [] [] = []
-- concat [] (x :: xs) = x :: xs
-- concat (x :: xs) [] = x :: concat xs []
-- concat (x :: xs) (y :: ys) = y :: concat xs (y :: ys)
concat [] [] = []
concat [] (x :: xs) = x :: xs
concat (x :: xs) [] = x :: concat xs []
concat (x :: xs) (y :: ys) = y :: concat xs (y :: ys)
