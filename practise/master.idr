-----------------------------------------------
-------------------- 1 & 2 --------------------
-----------------------------------------------
import Data.String

-- cast
increment: Int -> Double
increment x = cast x + 1

-- tuple
zip_it: List a -> List b -> List (a, b)

-- data structure
record Address where
  constructor MkAaddress
  number: Int
  street, city: String
  postcode: Int
  country: String

record Street where
  constructor MkStreet
  number: Int
  street: String

getStreet: Address -> Street
getStreet x = MkStreet (number x) (street x)

setStreet: Street -> Address -> Address
-- set_StructureParamName value whereToPutIt
-- structureParamName StructureWhereToGetThatParamName
setStreet x y = set_number (number x) (set_street (street x) y)

-- unpack StrintToTurnIntoListOfChars
-- pack listOfCharsToTurnIntoString
-- sort listToSortNaturally
-- take howMany listToTakeHowManyFirstElements
-- map function list
-- sum ListOfNumbersToSum
-- filter funcOfElemToBool listOfElems
-- mod number ToDivideByNum
-- parseInteger stringToParse
-- words stringToTurnIntoListOfWords
-- repl promptToShow functionOfStrToStrForInput IO()

-----------------------------------------------
-------------------- 3 & 4 --------------------
-----------------------------------------------

-- zipWith functionOfA&BToC listOrVect
-- show thingToConvertToString
Matrix : (m: Nat) -> (n: Nat) -> Type -> Type
Matrix m n t = Vect m (Vect n t)
-- replicate howManyTimes whatToReplicate
transposeVector: {n: Nat} -> Vect n t -> Vect n (Vect 1 t)
transposeVector [] = []
transposeVector (x :: xs) = [x] :: transposeVector xs

transposeMatrix: {t: Type} -> {m, n: Nat} -> Matrix m n t -> Matrix n m t
transposeMatrix {m = Z} {n = n} x = replicate n []
transposeMatrix {m = (S k)} {n = n} (x :: xs) = zipWith (++) (transposeVector x) (transposeMatrix xs)

runner_sum: Nat -> IO Nat
runner_sum k = do
                putStrLn "enter a number:"
                a <- getLine
                case the (Maybe Nat) (parsePositive a) of
                  Just x => runner_sum (k + x)
                  Nothing => pure k
running_sum: IO Nat
running_sum = runner_sum 0

-----------------------------------------------
-------------------- 5 & 6 --------------------
-----------------------------------------------

zero_to_nine : (Nat -> Maybe Nat)
zero_to_nine n = if n < 10 then Just n else Nothing

data Tree : Type -> Type where
  Leaf : Tree a
  Node : Tree a -> a -> Tree a -> Tree a

Path : Type
Path = List Bool

-- foldr functionThatTakesTwoElementsAndProducesOutput lastElement list
andList : List Bool -> Bool
andList xs = foldr (\a, b => a && b) True xs

-- foldTree lastOrPrevElement --
----- functionThatTakesResultsFromBothBranchesAndGivesResultType
---------- tree
foldTree : b -> (b -> a -> b -> b) -> Tree a -> b
foldTree l n Leaf = l
foldTree l n (Node tl x tr) = n (foldTree l n tl) x (foldTree l n tr)
