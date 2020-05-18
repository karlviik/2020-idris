module le11

import Data.Vect
import Syntax.PreorderReasoning

% default total
% auto_implicits on
% access public export


{-  Equality as a Boolean-Valued Function  -}


-- equality as a boolean-valued function:
is_equal  :  Nat -> Nat -> Bool
is_equal Z Z  =  True
is_equal (S m) (S n)  =  is_equal m n
is_equal _ _  =  False


-- "boolean blindness":

bounded_pred  :  Nat -> Nat
bounded_pred n  =  case  is_equal n 0  of
	False  =>  -- can't write n - 1 here
		case  n  of
			Z  =>  Z
			(S n)  =>  n
	True  =>  0

-- Even when is_equal n 0 is False,
-- as far as Idris is concerned n is still an arbitrary Nat



{-  Equality as an Indexed Type  -}


data  Equals  :  (x : a) -> (y : b) -> Type  where
	Reflexivity  :  {x : a} -> Equals x x    --  primitive evidence that
	                                         --  anything is equal to itself


-- The only way to construct a term of type  Equals x y
-- is if the terms  (x : a)  and  (y : b)  are computationally the same
-- which requires that the types  a  and  b  be computationally the same too.


four_is_four  :  Equals (2 + 2) (2 * 2)
four_is_four  =  Reflexivity

true_is_true  :  Equals (False || True) (not (False && True))
true_is_true  =  Reflexivity


-- Idris has a version of Equals in the standard library
-- called  (=)  with constructor  Refl.


{-    On Dependent Pattern Matching

 -  A term of type  x = y  acts a proof that  x  and  y  are equal.

 -  A variable of type  x = y  acts as an assumption that  x  and  y  are equal.

 -  Because the only constructor,  Refl, has type  x = x,
    case analysis of an assumption of type  x = y  triggers a discovery
    that  x  and  y  must be the same thing.
 -}


 -- adding a zero:


plus_zero_left  :  {n : Nat} -> 0 + n = n
plus_zero_left  =  Refl




namespace  scratch_1

	private
	plus_zero_right  :  {n : Nat} -> n + 0 = n
	plus_zero_right {n = Z}  =  Refl
	plus_zero_right {n = (S n)}  =  succ_equal plus_zero_right
		where
			succ_equal  :  i = j -> S i = S j
			succ_equal Refl  =  Refl

% hide plus_zero_right  --  so we can reuse the name


-- This succ_equal is pretty nice, let's try to generalize it.




-- Every function should preserve equality:
congruence  :  (f : a -> b) -> x = y -> f x = f y
congruence f Refl  =  Refl


-- Idris has a version of  congruence  in the standard library called  cong.
-- Inconveniently, it takes the function as an implicit argument called  f.



%hint
plus_zero_right  :  {n : Nat} -> n + 0 = n
plus_zero_right {n = Z}  =  Refl
plus_zero_right {n = (S n)}  =  cong {f = S} plus_zero_right




-- how about adding a successor?


plus_succ_left  :  {m , n : Nat} -> (S m) + n = S (m + n)
plus_succ_left  =  Refl



%hint
plus_succ_right  :  {m , n : Nat} -> m + (S n) = S (m + n)
plus_succ_right {m = Z} {n = n}  =  Refl
plus_succ_right {m = (S m)} {n = n}  =  cong {f = S} plus_succ_right




-- There's a fair amount of computation happening there
-- and it's starting to get hard to remember what's going on.
-- That may be fine for Idris, but it's not great for humans.


-- Let's build up some basic facts about equality
-- so that we can try to work at a higher level of abstraction.


-- Equality is a symmetric relation:
symmetry  :  x = y -> y = x
symmetry Refl  =  Refl


-- Idris has a version of  symmetry  in the standard library called  sym.




-- Equality is a transitive relation:
transitivity  :  from = via -> via = to -> from = to
transitivity Refl  =  id


-- Idris has a version of  transitivity  in the standard library called  trans.




-- Using the preorder structure we can write equality proofs
-- in a more human-friendly way:

namespace  scratch_2
	private

	plus_sym  :  {m , n : Nat} -> m + n = n + m
	plus_sym {m = Z} {n = n}  =
		transitivity {from = 0 + n} plus_zero_left {via = n} (sym plus_zero_right)
	plus_sym {m = (S m)} {n = n}  =
		transitivity {from = S m + n} plus_succ_left {via = S (m + n)} $
		transitivity (cong {f = S} plus_sym) {via = S (n + m)} (sym plus_succ_right)

% hide plus_sym  --  so we can reuse the name




-- This is still pretty clunky.
-- Idris offers syntic sugar to write more readable equality proofs by transitivity.
-- In order to use it we must import the Syntax.PreorderReasoning module.


-- symmetry of addition:
%hint
plus_sym  :  {m , n : Nat} -> m + n = n + m
plus_sym {m = Z} {n = n}  =
	(0 + n)
		={ plus_zero_left }=
	(n)
		={ sym plus_zero_right }=
	(n + 0)
		QED
plus_sym {m = (S m)} {n = n}  =
	(S m + n)
		={ plus_succ_left }=
	(S (m + n))
		={ cong {f = S} plus_sym }=
	(S (n + m))
		={ sym plus_succ_right }=
	(n + S m)
		QED



-- once we have proved some basic properties, we can reason more like humans:

-- associativity of addition:
%hint
plus_assoc  :  {m , n , p : Nat} -> m + (n + p) = (m + n) + p
plus_assoc {m = m} {n = Z} {p = p}  =
	(m + (0 + p))
		={ cong {f = (m + )} plus_zero_left }=
	(m + p)
		={ cong {f = ( + p)} (sym plus_zero_right) }=
	((m + 0) + p)
		QED
plus_assoc {m = m} {n = (S n)} {p = p}  =
	(m + (S n + p))
		={ cong {f = (m + )} plus_succ_left }=
	(m + S (n + p))
		={ plus_succ_right }=
	(S (m + (n + p)))
		={ cong {f = S} plus_assoc }=
	(S ((m + n) + p))
		={ sym plus_succ_left }=
	(S(m + n) + p)
		={ cong {f = ( + p)} (sym plus_succ_right) }=
	((m + S n) + p)
		QED




{-  Equality of Types  -}


-- If we know that two types are equal then we can coerce between them:
coerce  :  {a , b : Type} -> a = b -> a -> b
coerce  Refl  =  id




-- Because an indexed type is a function from the indexing type to  Type,
-- we can use  cong  to extend an equality to an indexed type:
vect_length_sym  :  Vect (m + n) a = Vect (n + m) a
vect_length_sym  =  cong {f = \ t => Vect t a} plus_sym




-- now we can prove the elusive lemma about twisted Vect concatenation:
namespace  scratch_3
	private

	twisted_concat  :  Vect m a -> Vect n a -> Vect (n + m) a
	twisted_concat xs ys  =  coerce vect_length_sym (xs ++ ys)

% hide twisted_concat  --  so we can reuse the name




-- This pattern of coercing along an indexed type equality is very common.
-- It often goes by the name "transport":
transport  :  {a : Type} -> (fiber : a -> Type) ->
	{x , y : a} -> (path : x = y) ->
	fiber x -> fiber y
transport fiber Refl  =  id

{-
	              fiber  x                                 fiber  y
	              ________                                 ________
	             /        \                               /        \
	            /    p     \    transport fiber path     / tr... p  \
	           |            |    ------------------>    |            |
	            \          /                             \          /
	             \________/                               \________/
	                                      path
	                  x    ===============================    y           : a

 -}


-- Using  transport  we can write twisted vector concatenation as a one-liner:
namespace  scratch_4
	private

	twisted_concat  :  Vect m a -> Vect n a -> Vect (n + m) a
	twisted_concat xs ys  =  transport (\t => Vect t a) plus_sym (xs ++ ys)

% hide twisted_concat  --  so we can reuse the name




-- Idris has a version of  transport  in the standard library called  replace.
-- Inconveniently, it takes the type constructor as an implicit argument called  P.


-- Let's use it to write  twisted_concat  from scratch, without relying on  (++)

twisted_concat  :  Vect m a -> Vect n a -> Vect (n + m) a
twisted_concat [] ys  =
	replace {P = \ t => Vect t a} (sym plus_zero_right) ys
twisted_concat (x :: xs) ys  =
	replace {P = \ t => Vect t a} (sym plus_succ_right) (x :: twisted_concat xs ys)
