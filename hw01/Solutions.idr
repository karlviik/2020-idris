import Data.List

-- first thing
differences: List Integer -> List Integer
differences [] = []
differences (x :: []) = []
differences (x :: (y :: xs)) = (y - x) :: (differences (y :: xs))

-- second thing
titlecase: String -> String
titlecase x = packUnWords (map (\(y :: ys) => (toUpper y) :: ys) (unPackWords x))
            where
              unPackWords: String -> List (List Char)
              unPackWords x = map (\x => unpack x) (words x)
              packUnWords: List (List Char) -> String
              packUnWords xs = unwords (map (\x => pack x) xs)

-- third thing
interactive_titlecase: IO()
-- interactive_titlecase = do  lineInput <- getLine
--                             putStrLn (titlecase lineInput)
--                             interactive_titlecase
interactive_titlecase = repl "\n" titlecase

-- fourth thing
avg_vowels: String -> Double
avg_vowels x = average (map (\y => length (filter is_vowel y)) (((map unpack) . words) x))
              where
                is_vowel: Char -> Bool
                is_vowel x = elem (toUpper x) ['A', 'E', 'I', 'O', 'U']
                average: List Nat -> Double
                average [] = 0
                average (y :: xs) = let l = y :: xs
                                    in (cast (sum l)) / (cast (length l))

-- fifth thing
satInBoth : (Eq t) => (t -> Bool) -> List t -> List t -> List t
satInBoth f xs ys = filter f (intersect xs ys)

-- sixth thing
ack : Nat -> Nat -> Nat
ack Z j = j + 1
ack (S k) Z = ack k 1
ack (S k) (S j) = ack k (ack (S k) j)

-- seventh thing
least_greatest: List Integer -> Integer -> (Integer, Integer)
least_greatest y x = min_max' y (x, x)
                        where
                          min_max': List Integer -> (Integer , Integer) -> (Integer , Integer)
                          min_max' [] x = x
                          min_max' (z :: xs) (xa, xb) = min_max' xs (min z xa, max z xb)

-- eighth thing
sumevens: Nat -> Nat
sumevens Z = Z
sumevens (S k) = (S k) * k

-- ninth thing
sum_primes: Nat -> Nat
sum_primes Z = 0
sum_primes (S k) = if (isPrim (S k))
                  then (S k) + (sum_primes k)
                  else sum_primes k
                  where
                    getAllDivisors: Int -> List Int
                    getAllDivisors y = filter
                                    (\x => not (x == 0) && mod y x == 0)
                                    [(-abs y)..(abs y)]
                    getDivisors: Nat -> List Nat
                    getDivisors y = filter
                                    (\x => not (x == 0) && mod y x == 0)
                                    [0..y]
                    isPrim: Nat -> Bool
                    isPrim k = length (getDivisors k) == 2
