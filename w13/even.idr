module Even

% default total
% auto_implicits on
% access public export


{-  Predicates as Boolean-Valued Functions  -}


-- evenness as a boolean-valued function:
is_even  :  Nat -> Bool
is_even Z  =  True
is_even (S Z)  =  False
is_even (S (S n))  =  is_even n


four_is_even  :  Bool
four_is_even  =  is_even 4

six_is_even  :  Bool
six_is_even  =  is_even 6


-- From the perspective of propositions as Booleans,
-- there are only two propositions, True and False.

true_is_true  :  Bool
true_is_true  =  four_is_even == six_is_even

-- Fermat's Last Theorem and 1 + 1 == 2 have the same value.

-- A different perspective is that each logical proposition is distinct,
-- and that a proof of a proposition is a conceptual object in its own right.




{-  Predicates as Indexed Types  -}


-- evenness as an Nat-indexed type:
data  Even  :  (n : Nat) -> Type  where
	Z_even   :  Even Z                    --  primitive evidence that 0 is even
	SS_even  :  Even n -> Even (S (S n))  --  primitive evidence that the
	                                      --  double successor of an even is even

{-
	                                                            SS_even
	                                        SS_even            (SS_even
	                    SS_even            (SS_even            (SS_even
	 Z_even              Z_even              Z_even)             Z_even))
	
	
	  0  |--->  1  |--->  2  |--->  3  |--->  4  |--->  5  |--->  6         ...
	       S         S         S         S         S         S
 -}


-- We can construct elements of type Even n only when n is even,
-- and each Even (2 * m) contains exactly one element.


four_even  :  Even 4
four_even  =  SS_even (SS_even Z_even)

six_even  :  Even 6
six_even  =  SS_even (four_even)


-- We can think of a term of type Even n as a proof that n is even,
-- and we can manipulate these proofs just like any other expressions in our programs.




{-  Proving Properties by Constructing Terms  -}


{-    On Dependent Pattern Matching

 -  A term of type Even n acts a proof that n is even.

 -  A variable of type Even n acts as an assumption that n is even.

 -  We can use pattern matching to examine the forms that such an assumption can have.

 -  Because the type Even n is indexed by the type Nat, case analyzing
    a proof of Even n gives us information about the Nat n as well.
 -}


-- The constructor SS_even says that the double-successor of an even number is even.
-- We can prove the converse as well:
pp_even  :  Even (S (S n)) -> Even n
pp_even (SS_even n_even)  =  n_even




-- even plus even is even:
-- (We do induction on the first proof because Nat addition
-- is defined by recursion on its first argument.)
even_plus_even  :  Even m -> Even n -> Even (m + n)
even_plus_even Z_even n_even  =  n_even
even_plus_even (SS_even m_even) n_even  =  SS_even (even_plus_even m_even n_even)




{-    On Proof Engineering

 -  For a variety of reasons, Idris may not show you all the information you may want
    about an intermediate proof state.

 -  We will learn about a variety of strategies to deal with this.
    Today we focus on two.

-}


-- even times even is even:


-- by the "lemma" strategy:
namespace  by_lemma
	private
	even_times_even  :  Even m -> Even n -> Even (m * n)
	even_times_even Z_even n_even  =  Z_even
	even_times_even {m = (S (S m))} (SS_even m_even) {n = n} n_even  =
		even_plus_even n_even n_plus_m_times_n_even
	where
		m_times_n_even  :  Even (m * n)
		m_times_n_even  =  even_times_even m_even n_even
		--
		n_plus_m_times_n_even  :  Even (n + (m * n))
		n_plus_m_times_n_even  =  even_plus_even n_even m_times_n_even

% hide even_times_even  --  so we can reuse the name


-- by the "explication" strategy:
namespace  by_explication
	private
	even_times_even  :  Even m -> Even n -> Even (m * n)
	even_times_even Z_even n_even  =  Z_even
	even_times_even {m = (S (S m))} (SS_even m_even) {n = n} n_even  =
		even_plus_even {m = n} {n = n + (m * n)} n_even
		(even_plus_even {m = n} {n = m * n} n_even (even_times_even m_even n_even))

% hide even_times_even  --  so we can reuse the name


-- cleaned up version:
even_times_even  :  Even m -> Even n -> Even (m * n)
even_times_even Z_even n_even  =  Z_even
even_times_even (SS_even m_even) n_even  =
	even_plus_even n_even (even_plus_even n_even (even_times_even m_even n_even))


