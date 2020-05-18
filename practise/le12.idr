module Lecture_12

import Data.Vect

import even  --  from lecture 10

% default total
% auto_implicits on
% access public export




{-  Negation as a Boolean Operation  -}


-- oddness as a boolean-valued function:
is_odd  :  Nat -> Bool
is_odd n  =  not (is_even n)


-- how to write negation as an operation on types??




{-  Empty Types  -}


{-

 - In the "propositions-as-types" interpretation, a proof is interpreted 
   as a value of the type corresponding to the proposition it validates.

 - To claim a proposition is false is to assert that there can be no proofs of it.

 - A proposition with no proofs corresponds to a type with no values.

 -}


data  Empty : Type  where
	--  no constructors!


-- Writing a function from an empty type to any other type is easy.
-- Such functions are trivial because there are zero cases to consider:

whatever  :  Empty -> a
whatever x  impossible




-- But writing functions to an empty type is not possible...


-- ...unless either the function is not total:

partial
hopeless  :  Nat -> Empty      --  this function has the right type,
hopeless n  =  hopeless (S n)  --  but it will never return a value




-- ...or else the domain of the function is empty too:

pointless  :  Fin 0 -> Empty  --  there are zero cases to consider
pointless n  impossible




{-  Negation as Refutation  -}


-- We can use a total function to an empty type
-- to express negation as an operation on propositions-as-types:

refute  :  Type -> Type
refute a  =  a -> Empty




namespace  scratch_1
	
	zero_not_succ  :  refute (Z = S n)
	zero_not_succ Refl  impossible

% hide zero_not_succ  --  so we can reuse the name




{-  In the Idris standard library:

 - there is an empty type (like our "Empty") called "Void",

 - there is a type-level negation function (like our "refute") called "Not",

 - there is a trivial function from Void to any type (like our "whatever") called "void".

 -}


%hint
zero_not_succ  :  Not (Z = S n)
zero_not_succ Refl  impossible




-- The logical "principle of explosion" or "ex contradictione quodlibet"
-- asserts that from the combination of a proposition and its negation
-- we may conclude anything whatsoever.
-- We can express this in Idris as well:

contradiction  :  a -> (Not a) -> b
contradiction a_true a_false  =  void (a_false a_true)




--  Recall the type Even : Nat -> Type from lecture 10


-- We can define the predicat of being odd as the negation of being even:

odd  :  Nat -> Type
odd n  =  Not (Even n)




-- Of course, one is odd:

%hint
one_odd  :  odd 1
one_odd Z_even  impossible
one_odd (SS_even n)  impossible




-- We can show that the successor of an even number is odd
-- by induction on Even n:

%hint
succ_even_odd  :  Even n -> odd (S n)
succ_even_odd Z_even  =  one_odd
succ_even_odd (SS_even n_even)  =
	let
		ih  =  succ_even_odd n_even
	in
		ih . pp_even




-- We can also show that the successor of an odd number is even.
-- Note that we can't pattern match on  n_odd : odd n
-- because  odd  is not an inductively defined type.
-- However, we can still pattern match on  n : Nat:

%hint
succ_odd_even  :  odd n -> Even (S n)
succ_odd_even {n = Z} zero_odd  =  contradiction Z_even zero_odd
succ_odd_even {n = (S Z)} one_odd  =  SS_even Z_even
succ_odd_even {n = (S (S n))} ssn_odd  =
	SS_even (succ_odd_even {n = n} (ssn_odd . SS_even))






{-  Decidable Propositions  -}


{-

 - A proposition is decidable if we can either affirm it by providing a proof of it,
   or else refute it by providing a proof of its negation.

 - Under the propositions-as-types interpretation this corresponds to
   either producing a value of the given type,
   or else showing the type to be uninhabited
   by defining a total function to an empty type.

 -}


data  Decide  :  (proposition : Type) -> Type  where
	-- like the boolean True, but with a proof:
	Affirm  :  (demonstration : proposition) -> Decide proposition
	-- like the boolean False, but with a proof:
	Refute  :  (refutation : Not proposition) -> Decide proposition




yes_two_plus_two_is_four  :  Decide (2 + 2 = 4)
yes_two_plus_two_is_four  =  Affirm Refl


no_two_plus_two_is_not_five  :  Decide (2 + 2 = 5)
no_two_plus_two_is_not_five  =  Refute $
	\ x => case  x  of
		Refl impossible


-- The Idris standard library has a version of the "Decide" type constructor called "Dec",
-- with constructors called "Yes" and "No" (:printdef Dec)




{-

 - A predicate is decidable if for each possible argument
   we can either affirm that the predicate holds of the given argument,
   or else refute that the predicate holds of the given argument.

 - This corresponds to either producing a value in the fiber type of the given index,
   or else showing the fiber type of the given index to be uninhabited
   by defining a total function from it to an empty type.

 -}



-- given any Nat, we can decide whether or not it's even:

decide_even  :  (n : Nat) -> Dec (Even n)
decide_even Z  =  Yes Z_even
decide_even (S n)  =  case  decide_even n  of
	(Yes n_even)  =>  No (succ_even_odd n_even)
	(No n_odd)  =>  Yes (succ_odd_even n_odd)




is_four_even  :  Dec (Even 4)
is_four_even  =  decide_even _


is_three_even  :  Dec (Even 3)
is_three_even  =  decide_even _







-- the lemma from lab 11:

pred_equal  :  S m = S n -> m = n
pred_equal Refl  =  Refl


-- given any pair of Nats, we can decide whether or not they're equal:

decide_equal  :  (m , n : Nat) -> Dec (m = n)
decide_equal Z Z  =  Yes Refl
decide_equal Z (S n)  =  No zero_not_succ
decide_equal (S m) Z  =  No (zero_not_succ . sym)
decide_equal (S m) (S n)  =
	case  decide_equal m n  of
		Yes m_n_equal  =>  Yes (cong m_n_equal)
		No m_n_differ  =>  No (m_n_differ . pred_equal)




does_two_equal_two  :  Dec (the Nat (1 + 1) = the Nat (2 * 2 - 2))
does_two_equal_two  =  decide_equal _ _


does_three_equal_four  :  Dec (the Nat 3 = the Nat 4)
does_three_equal_four  =  decide_equal _ _






{-  Verified Interfaces  -}


{-

 - Idris provides verified interfaces for empty types and for types with decidable equality:

	Uninhabited  :  Type -> Constraint
		uninhabited  :  {a : Type} -> Uninhabited a => a -> Void

	DecEq  :  Type -> Constraint
		decEq  :  {a : Type} -> DecEq a => (x , y : a) -> Dec (x = y)

 -}




	-- The standard library has default implementations of
	-- Uninhabited (Z = S n)  and  Uninhabited (S n = Z).
	-- We can extend these to any differing Nats:

implementation  Uninhabited (m = n) => Uninhabited (S m = S n)  where
	uninhabited sm_sn_equal  =
		let
			m_n_equal = pred_equal sm_sn_equal
		in
			uninhabited m_n_equal


-- The Uninhabited interface provides a method, absurd : Uninhabited a => a -> b.
-- This is like "void", but for arbitrary empty types.

absurd_nat  :  (Z + 3 = Z + 4) -> Bool
absurd_nat contra  =  absurd contra




{-  Constructive Logic  -}

{-

 - Using the propositions-as-types interpretation,
   we can express and prove properties of our programs
   within our programs themselves.

 - We have seen how to express that a proposition is true
   by constructing an value of the corresponding type.

 - We have also seen how to express that a proposition is false
   by constructing a total refutation function
   from the corresponding type to an empty type.

 - We can also combine propositions by using logical connectives.

 -}


-- a proof of the proposition  a and b
-- is a proof of  a  together with a proof of  b.

And  :  (a : Type) -> (b : Type) -> Type
And  =  Pair


-- a proof of the proposition  a or b
-- is either a proof of  a  or else a proof of  b,
-- together with the knowledge of which.

Or  :  (a : Type) -> (b : Type) -> Type
Or  =  Either


{-

 - This brings us to the beginning of the study of Type Theory.

 - We will explore some of the properties of the constructive logic
   realized by the propositions-as-types interpretation this week in lab.

 -}

