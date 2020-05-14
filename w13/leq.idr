module LEQ

% default total
% auto_implicits on
% access public export


{-  Binary Relations as Boolean-Valued Functions  -}


-- preorder as a boolean-valued function:
is_leq  :  Nat -> Nat -> Bool
is_leq Z n  =  True
is_leq (S m) Z  =  False
is_leq (S m) (S n)  =  is_leq m n


three_is_leq_five  :  Bool
three_is_leq_five  =  is_leq 3 5

four_is_leq_six  :  Bool
four_is_leq_six  =  is_leq 4 6




{-  Binary Relations as Indexed Types  -}


-- preorder as an Nat*Nat-indexed type:
data  LEQ  :  (m : Nat) -> (n : Nat) -> Type  where
	Z_leq  :  LEQ Z n                     --  primitive evidence that 0 comes first
	S_leq  :  LEQ m n -> LEQ (S m) (S n)  --  primitive evidence that successor preserves order


{-
	\ n   0               1               2               3        ...
	m /-----------------------------------------------------------------
	0 |  Z≤              Z≤              Z≤              Z≤
	1 |                S≤ Z≤           S≤ Z≤           S≤ Z≤
	2 |                              S≤ (S≤ Z≤)      S≤ (S≤ Z≤)
	3 |                                            S≤ (S≤ (S≤ Z≤))
	. |
	. |
	. |
 -}


-- We can construct elements of type LEQ m n only when m ≤ n,
-- and each set type contains just one element.


three_leq_five  :  LEQ 3 5
three_leq_five  =  S_leq (S_leq (S_leq Z_leq))

four_leq_six  :  LEQ 4 6
four_leq_six  =  S_leq three_leq_five


-- We can think of a term of type LEQ m n as a proof that m ≤ n.



{-  LEQ is a Preorder  -}


-- LEQ is a reflexive relation:
leq_refl  :  LEQ n n
leq_refl {n = Z}  =  Z_leq
leq_refl {n = (S n)}  =  S_leq leq_refl




-- LEQ is a transitive relation:
-- (note that Idris lets you reorder the implicit arguments)
leq_trans  :  LEQ l m -> LEQ m n -> LEQ l n
leq_trans Z_leq _  =  Z_leq
leq_trans {l = S l} (S_leq l_leq_m) {m = S m} (S_leq m_leq_n) {n = S n}  =
	S_leq (leq_trans l_leq_m m_leq_n)




-- a verified preorder interface:
-- unlike last week, we don't just give a Bool,
-- but instead we give a proof:
interface  Preorder  (rel : a -> a -> Type)  where
	reflexive  :  {x : a} -> rel x x
	transitive :  {x , y , z : a} -> rel x y -> rel y z -> rel x z


-- of which LEQ is an instance:
implementation  Preorder LEQ  where
	reflexive  =  leq_refl
	transitive  =  leq_trans




{-  Some LEQ Properties  -}


-- The constructor S_leq says that if m ≤ n then S m ≤ S n.
-- We can prove the converse as well:
leq_pred  :  LEQ (S m) (S n) -> LEQ m n
leq_pred (S_leq m_leq_n)  =  m_leq_n


-- The constructor Z_leq says that for any n we have that 0 ≤ n.
-- We can also show that for any n we have n ≤ S n:
succ_larger  :  LEQ n (S n)
succ_larger {n = Z}  =  Z_leq
succ_larger {n = S n}  =  S_leq succ_larger


-- As we build up a theory we can move away from relying on the inductive 
-- structure directly and use more abstract forms of reasoning.
pred_smaller  :  LEQ (S m) n -> LEQ m n
pred_smaller sm_leq_n  =  transitive succ_larger sm_leq_n



