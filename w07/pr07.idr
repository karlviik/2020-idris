import Data.String

runner_sum: Nat -> IO Nat
runner_sum k = do
                putStrLn "enter a number:"
                a <- getLine
                case the (Maybe Nat) (parsePositive a) of
                  Just x => runner_sum (k + x)
                  Nothing => pure k


running_sum: IO Nat
running_sum = runner_sum 0


in_sequence: List (IO ()) -> IO ()
in_sequence [] = pure ()
in_sequence (x :: xs) = do
                        x
                        in_sequence xs


collect_results : List (IO a) -> IO (List a)
collect_results [] = pure []
collect_results (x :: xs) = do
                              bla <- x
                              rest <- collect_results xs
                              pure (bla :: rest)


once_definitely : String -> String -> (String -> Maybe a) -> IO a
once_definitely prompt err fun = do
                                  putStrLn prompt
                                  input <- getLine
                                  case fun input of
                                    Nothing => do
                                      putStrLn err
                                      once_definitely prompt err fun
                                    Just a => pure a


palindrome: String -> Bool
palindrome x = x == (reverse x)

ensure_palindrome : Nat -> Maybe Nat
ensure_palindrome k = case palindrome (show k) of
                        True => Just k
                        False => Nothing


ensure_odd : Nat -> Maybe Nat
ensure_odd k = case mod k 2 of
                Z => Nothing
                S Z => Just k


getDivisors: Nat -> List Nat
getDivisors y = filter
                (\x => not (x == 0) && mod y x == 0)
                [0..y]

isPrim: Nat -> Bool
isPrim k = length (getDivisors k) == 2

ensure_prime : Nat -> Maybe Nat
ensure_prime k = case isPrim k of
                  True => Just k
                  False => Nothing

unify_properties : List (Nat -> Maybe Nat) -> (Nat -> Maybe Nat)
unify_properties [] input = Just input
unify_properties (fun :: funs) input = case fun input of
                                        Nothing => Nothing
                                        Just a => unify_properties funs a

compute_some_stuff: Nat -> Nat -> Nat -> Nat
compute_some_stuff Z sum_so_far cur_num = sum_so_far
compute_some_stuff (S k) sum_so_far cur_num = case unify_properties [ensure_odd, ensure_prime, ensure_palindrome] cur_num of
                                                Just bla => compute_some_stuff k (sum_so_far + bla) (S cur_num)
                                                Nothing => compute_some_stuff (S k) sum_so_far (S cur_num)
