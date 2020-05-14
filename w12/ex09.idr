import Data.Vect

interface   Preorder (a : Type)  where
  leq : a -> a -> Bool

-- Task 1
implementation   Eq a => Preorder (List a)  where
  leq [] ys  =  True
  leq (x :: xs) ys  =
    case elem x ys of
      False => False
      True => leq xs (delete x ys)

-- leq [] [5]  =  True
-- leq [2 , 1] [1 , 2]  =  True
-- leq [1 , 1 , 2] [1 , 2 , 2]  =  False


-- Task 2
implementation [Multiset]  Eq a => Eq (List a)  where
  xs == ys  =  leq xs ys

-- [1,2] == [2,1] = False
-- (==) @{Multiset} [1,2] [2,1] = True


-- Task 3
consolidate : List (Maybe a) -> Maybe (List a)
consolidate [] = pure []
consolidate (x :: xs) = pure (++) <*> (pure (\y => [y]) <*> x) <*> consolidate xs

  -- case x of
  --   Nothing => Nothing
  --   Just jx => pure (jx :: ) <*> consolidate xs

-- xs -> List (Maybe a)
-- pure xs -> Maybe (List (Maybe a))

-- consolidate [] = Just []
-- consolidate (x :: xs) =
--   case x of
--     Nothing => Nothing
--     Just x => case consolidate xs of
--                 Nothing => Nothing
--                 Just xs => Just (x :: xs)

-- consolidate [Just 1 , Just 2 , Just 3]  =  Just [1 , 2 , 3]
-- consolidate [Just 1 , Nothing , Just 3]  =  Nothing


-- Task 4
applicify  :  {t : Type -> Type} -> Applicative t => (op : a -> a -> a) -> t a -> t a -> t a
applicify op x y = pure op <*> x <*> y

infixl 7 +?
(+?)  :  Num a => Maybe a -> Maybe a -> Maybe a
(+?)  =  applicify (+)

infixl 7 +*
(+*)  :  Num a => Vect n a -> Vect n a -> Vect n a
(+*)  =  applicify (+)

-- Task 5


-- Task 6
