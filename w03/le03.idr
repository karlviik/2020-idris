-- kkk: List String -> Int
-- kkk = length ((filter (\xs => xs == 0) x) . (\map (\x => parseInteger x) xs )) x

compose: (b -> c) -> (a -> b) -> a -> c
compose f g x = f (g x)
