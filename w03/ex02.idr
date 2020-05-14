import Data.String

-- first thing
myReverse: List ty -> List ty
myReverse xs = rev' xs []
              where
                rev' : (xs : List ty) -> (acc : List ty) -> List ty
                rev' [] acc = acc
                rev' (x :: xs) acc = rev' xs (x :: acc)


-- second thing
sumsquares: Nat -> Int
sumsquares Z = 0
sumsquares (S k) = cast (sum (map (\x => x * x) [0..k]))


-- thrid thing
maybe_int: Maybe Int -> Int
maybe_int Nothing = 0
maybe_int (Just x) = x

add_numbers: String -> String
add_numbers x = cast (sum (map (\x => maybe_int (parseInteger x)) (words x)))

interactive_addition: IO()
interactive_addition = repl "\nspace-separated numbers to add: " (add_numbers)


-- fourth thing
getAllDivisors: Int -> List Int
getAllDivisors y = filter
                (\x => not (x == 0) && mod y x == 0)
                [(-abs y)..(abs y)]

getDivisors: Nat -> List Nat
getDivisors y = filter
                (\x => not (x == 0) && mod y x == 0)
                [0..y]


-- fifth thing
isPrim: Nat -> Bool
isPrim k = length (getDivisors k) == 2
