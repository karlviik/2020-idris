import even
import leq

data   Positive  :  Nat -> Type   where
  One_positive  :  Positive (S Z)
  S_positive     :  Positive n -> Positive (S n)

-- Task 1
even_times_one  :  Even n -> Even (n * 1)
even_times_one Z_even = Z_even
even_times_one (SS_even x) = SS_even (even_times_one x)

-- Task 2
-- second

-- Task 3
pow_even_pos  :  Even m -> Positive n -> Even (power m n)
pow_even_pos x One_positive = even_times_one x
pow_even_pos x (S_positive y) = even_times_even x (pow_even_pos x y)

-- Task 4
zero_plus_right  :  LEQ (m + 0) (m + n)
zero_plus_right {m = Z} = Z_leq
zero_plus_right {m = (S k)} = S_leq zero_plus_right

zero_plus_left  :  LEQ (0 + n) (m + n)
zero_plus_left {n = Z} = Z_leq
zero_plus_left {n = (S k)} {m = Z} = S_leq leq_refl
zero_plus_left {n = (S k)} {m = (S j)} = S_leq (pred_smaller zero_plus_left)

-- Task 5
plus_mono_right : LEQ n0 n1 -> LEQ (m + n0) (m + n1)
plus_mono_right Z_leq = zero_plus_right
plus_mono_right (S_leq x) {m = Z} = S_leq x
plus_mono_right (S_leq x) {m = (S k)} = S_leq (plus_mono_right (S_leq x))

plus_mono_left  :  LEQ m0 m1 -> LEQ (m0 + n) (m1 + n)
plus_mono_left Z_leq = zero_plus_left
plus_mono_left (S_leq x) = S_leq (plus_mono_left x)


-- Task 6
plus_mono  :  LEQ m0 m1 -> LEQ n0 n1 -> LEQ (m0 + n0) (m1 + n1)
plus_mono x y = transitive (plus_mono_left x) (plus_mono_right y)
