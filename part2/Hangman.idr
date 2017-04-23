module Hangman

import Data.Vect

data WordState : (guessesRemaining : Nat) -> (letters : Nat) -> Type where
  MkWordState : (word : String) ->                   -- word to guess
                (missing : Vect letters Char) ->     -- letters in the word that have not been guessed yet
                WordState guessesRemaining letters   -- guessesRemaining is an implicit argument tracked in the type

data Finished : Type where
  Lost : (game : WordState 0 (S letters)) -> Finished
  Won  : (game : WordState (S guesses) 0) -> Finished

data ValidInput : List Char -> Type where
  Letter : (c : Char) -> ValidInput [c]

emptyList : ValidInput [] -> Void
emptyList (Letter _) impossible

tooManyChars : ValidInput (x :: y :: xs) -> Void
tooManyChars (Letter _) impossible

isValidInput : (cs : List Char) -> Dec (ValidInput cs)
isValidInput [] = No emptyList
isValidInput (x :: []) = Yes (Letter x)
isValidInput (x :: y :: xs) = No tooManyChars

isValidString : (s : String) -> Dec (ValidInput (unpack s))
isValidString s = isValidInput (unpack s)

-- Returns the user guess along with a predicate on x (the input must be valid)
readGuess : IO (x ** ValidInput x)
readGuess = do putStr "Guess:"
               x <- getLine
               case isValidString x of
                    (Yes prf) => pure (_ ** prf)
                    (No contra) => do putStrLn "Incorrect guess..."
                                      readGuess


removeElem : (value : a) ->
             (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: xs) {prf = Here} = xs
removeElem {n = Z} value (x :: []) {prf = (There later)} = absurd later
removeElem {n = (S k)} value (x :: xs) {prf = (There later)} = x :: removeElem value xs

processGuess : (letter : Char) ->
               WordState (S guesses) (S letters) ->
               Either (WordState guesses (S letters))
                      (WordState (S guesses) letters)
processGuess letter (MkWordState word missing) =
  case isElem letter missing of
       (Yes prf) => Right $ MkWordState word (removeElem letter missing)
       (No contra) => Left $ MkWordState word missing

game : WordState (S guesses) (S letters) -> IO Finished
game {guesses} {letters} st = do
  (_ ** (Letter c)) <- readGuess
  case processGuess c st of
       (Left l) => do
         putStrLn "Wrong"
         case guesses of
              Z => pure $ Lost l
              (S k) => game l
       (Right r) => do
         putStrLn "Right!"
         case letters of
              Z => pure $ Won r
              (S k) => game r

main : IO ()
main = do
  result <- game {guesses=2} (MkWordState "test" ['t', 'e', 's'])
  case result of
       (Lost (MkWordState word missing)) => putStrLn $ "You lose... The word was " ++ word
       (Won (MkWordState word missing)) => putStrLn "You win!!"
