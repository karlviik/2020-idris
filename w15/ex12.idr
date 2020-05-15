import le12
import Data.Vect

-- Task 1
contrapositive  :  (a -> b) -> Not b -> Not a
contrapositive f x = \y => x (f y)

-- Task 2
%hint
dni  :  a -> Not $ Not a
dni x = \y => (y x)

-- Task 3
tne  :  Not $ Not $ Not a -> Not a
tne not_not_not = \val => not_not_not (\not => not_not_not (\not_2 => not val))

-- Task 4
dm1  :  Not a `Or` Not b -> Not (a `And` b)
dm1 (Left l) = \(a, b) => l a
dm1 (Right r) = \(a, b) => r b

dm2  :  Not a `And` Not b -> Not (a `Or` b)
dm2 (af, bf) = \arg =>
  case arg of
    Left aarg => af aarg
    Right barg => bf barg

-- Task 5
%hint
cons_equal  :  {xs , ys  : Vect n a} -> x = y -> xs = ys -> x :: xs = y :: ys
cons_equal Refl Refl = Refl

%hint
decons_equal  :  {xs , ys  : Vect n a} -> x :: xs = y :: ys -> (x = y) `And` (xs = ys)
decons_equal Refl = (Refl, Refl)

-- Task 6
heads_differ  :  {xs , ys  : Vect n a} -> Not (x = y) -> Not (x :: xs = y :: ys)
heads_differ not_eq_h = \Refl => not_eq_h Refl

tails_differ : {xs , ys  : Vect n a} -> Not (xs = ys) -> Not (x :: xs = y :: ys)
tails_differ not_eq_t = \Refl => not_eq_t Refl


-- Task 7
test : {xs , ys  : Vect n a} -> Not (x :: xs = y :: ys) -> (x = y) -> Not (xs = ys)
test not_eq_pre head_eq = \heady => not_eq_pre (cons_equal head_eq heady)

decons_differ  :  DecEq a => {xs , ys  : Vect n a} -> Not (x :: xs = y :: ys) -> Not (x = y) `Or` Not (xs = ys)
decons_differ not_eq {x = x} {y = y} {xs = xs} {ys = ys} =
  case decEq x y of
    Yes prf_h => Right (test not_eq prf_h)
    No contra => Left contra


-- Task 8
implementation [custom] DecEq a => DecEq (Vect n a)  where
  decEq [] []  =  Yes Refl
  decEq (x :: xs) (y :: ys)  =
    case decEq x y of
      Yes prf_h =>
        case decEq xs ys of
          Yes prf_t => Yes (cons_equal prf_h prf_t)
          No contra => No (tails_differ contra)
      No contra => No (heads_differ contra)
