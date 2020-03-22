-- By: Karl Viik
-- NOTE: position is (y, x)
------------------------------------------------
-- Functional Programming Assignment Skeleton --
------------------------------------------------

import Data.String -- we need this!

-----------------------------------------------
-- Part One: Representaiton, valid, get, set --
-----------------------------------------------
-- supports world sizes between 1 - 500, make sure to make your terminal big enough to fit all of it
MapSize : Nat
MapSize = 10

||| The game has two players, one who plays with the white pieces, the other the black pieces. We refer to the players by the colour of their pieces.
data Player : Type where
  White : Player
  Black : Player

-- returns true if they are same colour
compare_players: Player -> Player -> Bool
compare_players White White = True
compare_players White Black = False
compare_players Black White = False
compare_players Black Black = True

||| Possible contents of a space on the board. Each space contains either Nothing, a White piece, or a Black piece.
Space : Type
Space = Maybe Player

-- returns true if player occupies the space
occupies: Player -> Space -> Bool
occupies x Nothing = False
occupies x (Just y) = compare_players x y


||| Your representation of the board. The is going to involve Spaces.
Board : Type
Board = List (List Space)

||| Board positions, according to the indexing scheme detailed in the provided section, with the code that draws the board. (Possibly also with the assignment?).
Position : Type
Position = (Nat, Nat)

||| A function that determines whether or not a given pair of Nats actually indexes a position on the game board, according to our coordinate scheme.
valid : Position -> Bool
valid (y, x) = (cast (2 * MapSize) - 1 > (cast x))
                && (cast (2 * MapSize) - 1 > (cast y))
                && (cast MapSize + (- cast y) - 1 <= (cast x))
                && (cast (3 * (MapSize - 1)) + (- cast y) >= (cast x))

||| Get the contents of the given position, on the given board. Note that this only makes sense if the position is valid.
get : Board -> Position -> Space
get board (y, x) = if valid (y, x)
            then case index' y board of
              Nothing => Nothing -- not actually really needed
              Just row => case index' x row of
                Nothing => Nothing -- not actually really needed
                Just space => space
            else Nothing

||| Given a valid position, a board, and the thing we want to occupy that position (a Space), returns the result of putting that thing in the appropriate position (which is a board).
insert_to_pos: Nat -> Space -> List Space -> List Space
insert_to_pos Z space (x :: xs) = space :: xs
insert_to_pos (S k) space (x :: xs) = x :: (insert_to_pos k space xs)

set : Board -> Position -> Space -> Board
set (z :: zs) (Z, x) space = insert_to_pos x space z :: zs
set (z :: zs) ((S k), x) space = z :: set zs (k, x) space

--------------------------------------------
-- Part Two: winning_move and losing_move --
--------------------------------------------
if_n_in_given_row: List Space -> Nat -> Nat -> Player -> Bool
if_n_in_given_row row goal Z player = True
if_n_in_given_row [] goal (S k) player = False
if_n_in_given_row (space :: spaces) goal (S k) player = let pre = if_n_in_given_row spaces goal
                                                        in if occupies player space
                                                          then pre k player
                                                          else pre goal player

check_for_n_in_row: Board -> Nat -> Player -> Bool
check_for_n_in_row [] amount player = False
check_for_n_in_row (x :: xs) amount player = if if_n_in_given_row x amount amount player
                                              then True
                                              else check_for_n_in_row xs amount player

tally_given_row: List Space -> List Nat -> Player -> Nat -> (Bool, List Nat) -- bool shows if goal was reached
tally_given_row [] tallies player goal = (False, tallies)
tally_given_row (space :: spaces) tallies player goal = if occupies player space
                                                          then case tallies of
                                                            [] => if goal <= 1
                                                              then (True, [])
                                                              else case tally_given_row spaces [] player goal of
                                                                (False, remaining) => (False, 1 :: remaining)
                                                                (True, _) => (True, [])
                                                            (tally :: rest) => if goal <= tally + 1
                                                              then (True, [])
                                                              else case tally_given_row spaces rest player goal of
                                                                (False, remaining) => (False, (tally + 1) :: remaining)
                                                                (True, _) => (True, [])
                                                          else case tallies of
                                                            [] => case tally_given_row spaces [] player goal of
                                                              (bool, remaining) => (bool, 0 :: remaining)
                                                            (tally :: rest) => case tally_given_row spaces rest player goal of
                                                              (bool, remaining) => (bool, 0 :: remaining)

check_for_n_in_diag: Board -> Nat -> List Nat -> Player -> Bool
check_for_n_in_diag [] k j y = False
check_for_n_in_diag (row :: rows) goal tallies player = case tally_given_row row tallies player goal of
                                                          (True, _) => True
                                                          (False, (tally :: rest)) => check_for_n_in_diag rows goal rest player


||| If a player plays one of their pieces at the given position on the given board, do they win the game? Note that the position supplied must be valid for this to make sense.
winning_move : Position -> Player -> Board -> Bool
winning_move pos player board = let new_board = set board pos (Just player)
                                    transposed_new_board = transpose new_board
                                in check_for_n_in_row new_board 4 player
                                 || check_for_n_in_row transposed_new_board 4 player
                                 || check_for_n_in_diag new_board 4 [] player

||| If a player plays one of their pieces at the given position on the given board, do they lose the game? Note that the position supplied must be valid for this to make sense.
losing_move : Position -> Player -> Board -> Bool
losing_move pos player board = let new_board = set board pos (Just player)
                                   transposed_new_board = transpose new_board
                                in check_for_n_in_row new_board 3 player
                                 || check_for_n_in_row transposed_new_board 3 player
                                 || check_for_n_in_diag new_board 3 [] player

-----------------------
-- Drawing The Board --
-----------------------

-- The draw_ functions are provided to help you with your assignment. In particular, once
-- you have implemented `valid : Position -> Bool` and `get : Board -> Position -> Space`,
-- you can draw `b : Board` by executing `draw_board valid get b`. For example, if b is
-- the empty board, this results in:

-- 0:      - - - - -
-- 1:     - - - - - -
-- 2:    - - - - - - -
-- 3:   - - - - - - - -
-- 4:  - - - - - - - - -
-- 5:   - - - - - - - -
-- 6:    - - - - - - -   \
-- 7:     - - - - - -   \ \
-- 8:      - - - - -   \ \ \
--                    \ \ \ \
--           \ \ \ \ \ \ \ \ \
--           :0:1:2:3:4:5:6:7:8


||| (draw_spaces n) is the string composed of n spaces.
draw_spaces : Nat -> String
draw_spaces n = pack (replicate n ' ')

||| (draw_guides n) is the string containing n copies of " \\".
draw_guides : Nat -> String
draw_guides n = concat (replicate n " \\")

||| draw_nothing is the empty string. The exists for the sake of consistent form.
draw_nothing : String
draw_nothing = ""

||| (draw_player p) is the single-character string reprsenting player p on the board.
draw_player : Player -> String
draw_player White = "w"
draw_player Black = "b"

||| (draw_space s) is the single-character string representing space s on the board.
draw_space : Space -> String
draw_space Nothing = "-"
draw_space (Just x) = draw_player x

||| (draw_row xs) draws the spaces in the given row, with spaces in between.
draw_row : List Space -> String
draw_row = concat . (intersperse " ") . (map draw_space)

||| Once you have implemented get and valid (see part one), (draw_board get valid b) displays board b as specified at the beginning of this section.
draw_board : (get : Board -> Position -> Space) -> (valid : Position -> Bool)
           -> Board -> IO ()
draw_board get valid b =
  (putStr . unlines)
  ((zipWith3 (\x, y => (++) (x ++ y))
             left_things row_strings right_things)
    ++ bottom_things)
  where
  valid_positions : List (List Position)
  valid_positions = let bounds = toNat (cast (MapSize * 2) - 2)
                    in map (filter valid) (map (\i => zip (replicate (S bounds) i) [0..bounds]) [0..bounds])

  row_strings : List String
  row_strings = map (draw_row . map (get b)) valid_positions

  generate_left_things: Nat -> Nat -> List String
  generate_left_things currow lastrow = let one_with_max = div lastrow 2
                                            diff = toNat (abs ((cast one_with_max) + (-cast currow)))
                                        in if currow <= lastrow
                                          then (show currow
                                            ++ ":"
                                            ++ draw_spaces (2 + toNat (cast (length (show lastrow)) + (-cast (length (show currow)))) + diff))
                                            :: generate_left_things (S currow) lastrow
                                          else []

  left_things : List String
  left_things = generate_left_things 0 (toNat (cast (MapSize * 2) - 2))


  generate_right_things: Nat -> Nat -> List String
  generate_right_things currow lastrow = let diff = (cast currow) + (-cast MapSize)
                                         in if currow <= lastrow
                                          then if currow <= MapSize
                                            then draw_nothing :: generate_right_things (S currow) lastrow
                                            else (draw_spaces 2
                                              ++ draw_guides (toNat diff))
                                              :: generate_right_things (S currow) lastrow
                                          else []

  right_things : List String
  right_things = generate_right_things 0 (toNat (cast (MapSize * 2) - 2))


  generate_bottom_string: Nat -> Nat -> String
  generate_bottom_string cur max = if cur <= max
                                    then ":" ++ show cur ++ generate_bottom_string (S cur) max
                                    else ""

  add_buffers: Nat -> String -> String
  add_buffers len x = if len == 1
                        then ":" ++ x
                        else if len == 2
                          then ":" ++ x ++ if length (x) == 1 then " " else ""
                          else if length (x) == 1
                            then " " ++ x ++ " "
                            else if length (x) == 2
                              then " " ++ x
                              else x


  generate_bottom_top_string: Nat -> Nat -> String
  generate_bottom_top_string cur max = if cur <= max
                                        then if mod cur 2 == 0
                                          then add_buffers (length (show max)) (show cur) ++ generate_bottom_top_string (S cur) max
                                          else "\\" ++ generate_bottom_top_string (S cur) max
                                        else ""

  generate_bottom_bot_string: Nat -> Nat -> String
  generate_bottom_bot_string cur max = if cur <= max
                                        then if mod cur 2 == 1
                                          then add_buffers (length (show max)) (show cur) ++ generate_bottom_bot_string (S cur) max
                                          else " " ++ generate_bottom_bot_string (S cur) max
                                        else ""

  bottom_things : List String
  bottom_things = let mappy = toNat (cast MapSize - 1)
                      diagonal = toNat (cast (2 * MapSize) - 1)
                      first_two = [ draw_spaces (2 + length (show diagonal) + 3 * MapSize) ++ draw_guides mappy
                      , draw_spaces (3 + length (show diagonal) + MapSize)  ++ draw_guides diagonal]
                  in if length (show diagonal) == 1
                    then first_two ++ [draw_spaces (4 + length (show diagonal) + MapSize) ++ generate_bottom_string 0 (toNat (cast diagonal - 1))]
                    else first_two
                      ++ [draw_spaces (4 + length (show diagonal) + MapSize) ++ generate_bottom_top_string 0 (toNat (cast diagonal - 1))]
                      ++ [draw_spaces (6 + length (show diagonal) + MapSize) ++ generate_bottom_bot_string 0 (toNat (cast diagonal - 1))]

empty_board: Board
empty_board = let diag = toNat (cast (2 * MapSize) - 1)
              in replicate diag (replicate diag (the Space Nothing))

---------------------------------
-- Part 3: An Interactive Game --
---------------------------------

ask_for_position: Board -> IO Position
ask_for_position board = do
                          input <- getLine
                          case words input of
                            [] => invalidness "Incomplete position, try again: "
                            (y :: []) => invalidness "Incomplete position, try again: "
                            (y :: x :: rest) => case parsePositive y of
                                                  Nothing => invalidness "y coord is not a valid nat, try again: "
                                                  Just ya => case parsePositive x of
                                                              Nothing => invalidness "x coord is not a valid nat, try again: "
                                                              Just xa => let position = (toNat ya, toNat xa)
                                                                         in if valid position
                                                                           then if case get board position of
                                                                                    Nothing => True
                                                                                    Just _ => False
                                                                                then pure position
                                                                                else invalidness "Selected position is already occupied, try again: "
                                                                           else invalidness "Selected position is not on the board, try again: "
                         where
                            invalidness: String -> IO Position
                            invalidness err = do
                                                putStr err
                                                ask_for_position board

board_and_string: Board -> String -> IO ()
board_and_string board string = do
                                  draw_board get valid board
                                  putStr string

game_loop: Board -> Nat -> Player -> IO ()
game_loop board Z turn = board_and_string board "Draw!\n"
game_loop board (S slots_left) turn = let player_str = case turn of
                                                        Black => "B"
                                                        White => "W"
                                          opponent_str = case turn of
                                                        Black => "W"
                                                        White => "B"
                                          opponent = case turn of
                                                        Black => White
                                                        White => Black
                                      in do
                                        board_and_string board ("Player " ++ player_str ++ "?: ")
                                        pos <- ask_for_position board
                                        if winning_move pos turn board
                                          then board_and_string (set board pos (Just turn)) ("Player " ++ player_str ++ " wins!\n")
                                          else if losing_move pos turn board
                                            then board_and_string (set board pos (Just turn)) ("Player " ++ opponent_str ++ " wins!\n")
                                            else game_loop (set board pos (Just turn)) slots_left opponent



calc_board_slots: Nat
calc_board_slots = toNat (6 * (cast (calcy MapSize) + (-cast MapSize)) + 1)
                  where
                    calcy: Nat -> Nat
                    calcy Z = 0
                    calcy (S k) = (S k) + (calcy k)

||| Finally, implement a playable game of four-not-three using what you have built so far.  Player B moves firs
new_game : IO ()
new_game = do
            putStrLn "Black starts, get 4 in row, don't get 3 in row\nFirst coordinate is vertical, second horizontal\nInsert moves by separating coordinates with a space"
            game_loop empty_board calc_board_slots Black


-- Once you have implemented new_game, you can compile this file with "idris <file_name> -o game" to obtain an executable!
main : IO ()
main = new_game
