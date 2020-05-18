import Data.Vect
import le11
import Syntax.PreorderReasoning

-- Task 1
times_zero_left   :  {n : Nat} -> 0 * n = 0
times_zero_left = Refl

times_zero_right  :  {n : Nat} -> n * 0 = 0
times_zero_right {n = Z} = Refl
times_zero_right {n = (S k)} = times_zero_right


-- Task 2
times_succ_left   :  {m , n : Nat} -> (S m) * n = (m * n) + n
times_succ_left = plus_sym

times_succ_right  :  {m , n : Nat} -> m * (S n) = m + (m * n)
times_succ_right {m = Z} = Refl
times_succ_right {m = (S m_s)} {n = n} = cong {f = S} timothy where
  timothy: (n + (m_s * (S n))) = (m_s + (n + (m_s * n)))
  timothy =
    (n + (m_s * (S n)))
      ={ cong {f = (n + ) } times_succ_right }=
    (n + (m_s + (m_s * n)))
      ={ plus_assoc }=
    ((n + m_s) + (m_s * n))
      ={ cong {f = ( + (m_s * n))} plus_sym }=
    ((m_s + n) + (m_s * n))
      ={ sym plus_assoc }=
    (m_s + (n + (m_s * n)))
      QED


-- Task 3
times_one_left    :  {n : Nat} -> 1 * n = n
times_one_left = plus_zero_right

times_one_right  :  {n : Nat} -> n * 1 = n
times_one_right {n = n} =
  (n * 1)
    ={ times_succ_right }=
  (n + (n * 0))
    ={ cong {f = (n + )} times_zero_right }=
  (n + 0)
    ={ plus_zero_right }=
  (n)
    QED

-- Task 4
times_sym  :  {m , n : Nat} -> m * n = n * m
times_sym {m = Z} = sym times_zero_right
times_sym {m = (S m_s)} {n = n} =
  ( n + (m_s * n) )
    ={ cong {f = (n +) } times_sym }=
  ( n + (n * m_s) )
    ={ sym times_succ_right }=
  (n * (S m_s))
    QED

-- Task 5
plus_one_is_succ : {a: Nat} -> a + 1 = S a
plus_one_is_succ {a = Z} = Refl
plus_one_is_succ {a = (S k)} = cong {f = S} plus_one_is_succ

twisted_cons  :  a -> Vect n a -> Vect (n + 1) a
twisted_cons x xs {n = n} {a = a} = replace {P = \x => Vect x a} (sym plus_one_is_succ) (x :: xs)

-- Task 6
reverse_vect  :  Vect n a -> Vect n a
reverse_vect [] = []
reverse_vect (x :: xs) {n = (S n_s)} {a = a} = replace {P = \y => Vect y a} plus_one_is_succ ((reverse_vect xs) ++ [x])
