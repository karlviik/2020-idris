myReverse: List ty -> List ty
myReverse [] = []
myReverse (x :: xs) = myReverse xs ++ [x]

revString: String -> String
revString x = pack (myReverse (unpack x))

palindrome: String -> Bool
palindrome x = x == (revString x)

myCycle: List ty -> Nat -> List ty
myCycle xs Z = []
myCycle xs (S k) = xs ++ (myCycle xs k)

odds: List ty -> List ty
odds [] = []
odds (x :: []) = x :: []
odds (x :: (y :: xs)) = x :: (odds xs)

evens: List ty -> List ty
evens [] = []
evens (x :: []) = []
evens (x :: (y :: xs)) = y :: (evens xs)

deal: List ty -> (List ty, List ty)
deal xs = ((odds xs), (evens xs))

top_three : Ord a => List a -> List a
top_three xs = take 3 (myReverse (sort xs))

myUnzipFirst: List (ty, ty') -> List ty
myUnzipFirst [] = []
myUnzipFirst ((x, y) :: xys) = x :: (myUnzipFirst xys)

myUnzipSecond: List (ty, ty') -> List ty'
myUnzipSecond [] = []
myUnzipSecond ((x, y) :: xys) = y :: (myUnzipSecond xys)

myUnzip: List (ty, ty') -> (List ty, List ty')
myUnzip xs = (myUnzipFirst xs, myUnzipSecond xs)

record Address where
  constructor MkAddress
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
setStreet x y = set_number (number x) (set_street (street x) y)
