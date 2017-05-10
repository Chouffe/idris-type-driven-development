module Hangman

import Data.Vect

%default total

letters : String -> List Char
letters = nub . map toUpper . unpack

data GuessResult = Correct | Incorrect

data GameState : Type where
  NotRunning : GameState
  Running : (guesses : Nat) -> (letters : Nat) -> GameState

data GameCmd : (ty : Type) -> GameState -> (ty -> GameState) -> Type where

  NewGame : (word : String) -> GameCmd () NotRunning (const (Running 6 (length (letters word))))
  Won : GameCmd () (Running (S guesses) Z) (const NotRunning)
  Lost : GameCmd () (Running Z (S letters)) (const NotRunning)
  Guess : (c : Char) -> GameCmd  GuessResult (Running (S guesses) (S letters)) (\res => case res of
              Correct => (Running (S guesses) letters)
              Incorrect => (Running guesses (S letters)))

  -- User Interaction
  ShowState : GameCmd () state (const state)
  Message : String -> GameCmd () state (const state)
  ReadGuess : GameCmd Char state (const state)

  Pure : (res : ty) -> GameCmd ty (stateFn res) stateFn
  (>>=) : GameCmd a state1 state2Fn -> ((res : a) -> GameCmd b (state2Fn res) state3Fn) -> GameCmd b state1 state3Fn

-- Type for describing potentially infinite game loops
namespace Loop
  data GameLoop : (ty : Type) -> GameState -> (ty -> GameState) -> Type where
    Exit :  GameLoop () NotRunning (const NotRunning)  -- Cant exit a game that still running
    (>>=) : GameCmd a state1 state2Fn -> ((res : a) -> Inf (GameLoop b (state2Fn res) state3Fn)) -> GameLoop b state1 state3Fn

gameLoop : GameLoop () (Running (S guesses) (S letters)) (const NotRunning)
gameLoop {guesses} {letters} = do
  ShowState
  g <- ReadGuess
  ok <- Guess g
  case ok of
       Correct => case letters of
                       Z => do Won
                               ShowState
                               Exit
                       (S k) => do Message "Correct"
                                   gameLoop
       Incorrect => case guesses of
                         Z => do Lost
                                 ShowState
                                 Exit
                         (S k) => do Message "Incorrect"
                                     gameLoop

hangman : GameLoop () NotRunning (const NotRunning)
hangman = do NewGame "testing"
             gameLoop

-- So far, you have only defined a data type that describes the actions in the game.
-- In order to run the game, you need to define a concrete representation of the game state and a function that translates gameLoop to a sequence of IO actions

-- Defining a concrete GameState
data Game : GameState -> Type where
  GameStart : Game NotRunning
  GameWon : (word : String) -> Game NotRunning
  GameLost : (word : String) -> Game NotRunning
  InProgress : (word : String) -> (guesses : Nat) -> (missing : Vect letters Char) -> Game (Running guesses letters)  -- Game in progress with guesses and letters remaining

Show (Game g) where
  show GameStart = "Starting"
  show (GameWon word) = "Game won: word was " ++ word
  show (GameLost word) = "Game lost: word was " ++ word
  show (InProgress word guesses missing) =  "\n" ++ pack (map hideMissing (unpack word)) ++ "\n" ++ show guesses ++ " guesses left"
    where
      hideMissing : Char -> Char
      hideMissing c = if c `elem` missing then '-' else c

data GameResult : (ty : Type) -> (ty -> GameState) -> Type where
  OK : (res : ty) -> Game (outStateFn res) -> GameResult ty outStateFn
  OutOfFuel : GameResult ty outStateFn

data Fuel = Dry | More (Lazy Fuel)

ok : (res : ty) -> Game (outStateFn res) -> IO (GameResult ty outStateFn)
ok res st = pure $ OK res st

removeElem : (value : a) -> (xs : Vect (S n) a) ->
             {auto prf : Elem value xs} ->
             Vect n a
removeElem value (value :: ys) {prf = Here} = ys
removeElem {n = Z} value (y :: []) {prf = There later} = absurd later
removeElem {n = (S k)} value (y :: ys) {prf = There later} = y :: removeElem value ys

runCmd : Fuel -> Game inState -> GameCmd ty inState outStateFn -> IO (GameResult ty outStateFn)
runCmd fuel state (NewGame word) = ok () (InProgress (toUpper word) _ (fromList (letters word)))
runCmd fuel (InProgress word _ missing) Won = ok () (GameWon word)
runCmd fuel (InProgress word _ missing) Lost = ok () (GameLost word)
runCmd fuel (InProgress word _ missing) (Guess c) = case isElem c missing of
                                                         (Yes prf) => ok Correct (InProgress word _ (removeElem c missing))
                                                         (No contra) => ok Incorrect $ InProgress word _ missing  -- The guesses argument to InProgress is inferred from the type and decreases

runCmd fuel state ShowState = do printLn state
                                 ok () state
runCmd fuel state (Message x) = do printLn x
                                   ok () state
-- This may run indefinitelly so it consumes fuel when there is an invalid input
-- As a result, runCmd is total because it either consumes fuel or process a command on each recursive call
runCmd (More fuel) state ReadGuess = do
  putStr "Guess: "
  input <- getLine
  case unpack input of
       [x] => if isAlpha x
                 then ok (toUpper x) state
                 else do putStrLn "Invalid input"
                         runCmd fuel state ReadGuess
       _ => do putStrLn "Invalid input"
               runCmd fuel state ReadGuess
runCmd Dry _ _ = pure OutOfFuel
runCmd fuel state (Pure res) = ok res state
runCmd fuel state (cmd >>= next) = do
  OK cmdRes newSt <- runCmd fuel state cmd | OutOfFuel => pure OutOfFuel
  runCmd fuel newSt (next cmdRes)

run : Fuel -> Game inState -> GameLoop ty inState outStateFn -> IO (GameResult ty outStateFn)
run Dry _ _ = pure OutOfFuel
run (More fuel) st Exit = ok () st
run (More fuel) st (cmd >>= next) = do
  OK cmdRes newSt <- runCmd fuel st cmd | OutOfFuel => pure OutOfFuel
  run fuel newSt (next cmdRes)

%default partial

forever : Fuel
forever = More forever

main : IO ()
main = do run forever GameStart hangman
          pure ()

-- We have separated the description of the rules (in GameCmd and GameLoop) from the execution of the rules (in runCmd and run)
-- Essentially, GameCmd and GameLoop define an interface for constructing a valid game of Hangman, correctly following the rules.
-- Any well typed total function using these types MUST be a correct implementation of the rules, or it would not have type checked!
