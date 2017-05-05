module ArithState

import Data.Primitives.Views
import Fuel
import System

------------
-- GameState
------------

-- Automatically defines projection functions
-- correct, attempted
record Score where
  constructor MkScore
  correct : Nat
  attempted : Nat

-- Automatically defines projection functions
-- score, difficulty
record GameState where
  constructor MkGameState
  score : Score
  difficulty : Int

Show GameState where
  show st = show (correct (score st)) ++ "/" ++
                show (attempted (score st)) ++ "\n" ++
                "Difficulty: " ++ show (difficulty st)

initState : GameState
initState = MkGameState (MkScore 0 0) 12

-- Record update syntax
setDifficulty : Int -> GameState -> GameState
setDifficulty k state = record { difficulty = k } state

-- Nested record update syntax
addWrong : GameState -> GameState
addWrong state = record { score->attempted = attempted (score state) + 1 } state

addCorrect : GameState -> GameState
addCorrect state = record { score->attempted = attempted (score state) + 1
                          , score->correct = correct (score state) + 1
                        } state

-- There is a Lens notation
addWrong' : GameState -> GameState
addWrong' = record { score->attempted $= (+1) }

addCorrect' : GameState -> GameState
addCorrect' = record { score->attempted $= (+1)
                     , score->correct $= (+1)
                     }

data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  GetRandom : Command Int
  GetGameState : Command GameState
  PutGameState : GameState -> Command ()

  Pure : a -> Command a
  Bind : Command a -> (a -> Command b) -> Command b

Functor Command where
  map f x = Bind x (\val => Pure (f val))

Applicative Command where
  pure = Pure
  f <*> x = Bind f (\f' =>
            Bind x (\x' =>
            Pure $ f' x'))

Monad Command where
  (>>=) = Bind

updateGameState : (GameState -> GameState) -> Command ()
updateGameState f = Bind GetGameState (\st => PutGameState (f st))

-- runCommand : Command a -> IO a
-- runCommand (PutStr x) = putStr x
-- runCommand GetLine = getLine
-- runCommand GetRandom = ?runCommand_rhs_3
-- runCommand GetGameState = ?runCommand_rhs_4
-- runCommand (PutGameState x) = ?runCommand_rhs_5
-- runCommand (Pure x) = pure x
-- runCommand (Bind x f) = do
--   result <- runCommand x
--   runCommand $ f result

runCommand' : Stream Int -> GameState -> Command a -> IO (a, Stream Int, GameState)
runCommand' xs x (PutStr y) = do
  putStr y
  pure ((), xs, x)

runCommand' xs x GetLine = do
  str <- getLine
  pure (str, xs, x)

runCommand' (value :: xs) x GetRandom = pure (getRandom value (difficulty x), xs, x)
  where
    getRandom : Int -> Int -> Int
    getRandom val max with (divides val max)
      getRandom val 0 | DivByZero = 1
      getRandom ((max * div) + rem) max | (DivBy prf) = abs rem + 1

runCommand' xs x GetGameState = pure (x, xs, x)
runCommand' xs x (PutGameState y) = pure ((), xs, y)
runCommand' xs x (Pure y) = pure (y, xs, x)
runCommand' xs x (Bind action cont) = do
  (val, xs', x') <- runCommand' xs x action
  runCommand' xs' x' (cont val)


namespace ConsoleIODo
  data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do

data Input = Answer Int
           | QuitCmd

mutual
  total
  correct : ConsoleIO GameState
  correct = do
    PutStr "Correct!\n"
    updateGameState addCorrect
    quiz

  total
  wrong : Int -> ConsoleIO GameState
  wrong answer = do
    PutStr $ "Wrong, the answer is " ++ show answer ++ "\n"
    st <- GetGameState
    PutGameState (addWrong st)
    quiz

  total
  readInput : (prompt : String) -> Command Input
  readInput prompt =
    if toLower prompt == "quit"
       then Pure QuitCmd
       else Pure $ Answer $ cast prompt

  total
  quiz : ConsoleIO GameState
  quiz = do
    num1 <- GetRandom
    num2 <- GetRandom
    st <- GetGameState
    PutStr $ show st ++ "\n"

    input <- readInput $ show num1 ++ " * " ++ show num2 ++ "? "
    case input of
         (Answer answer) => if answer == num1 * num2
                               then correct
                               else wrong (num1 * num2)
         QuitCmd => Quit st

total
run : Fuel -> Stream Int -> GameState -> ConsoleIO a -> IO (Maybe a, Stream Int, GameState)
run _ xs st (Quit x) = pure $ (Just x, xs, st)
run (More fuel) xs st (Do m cont) = do
  (result, xs', st') <- runCommand' xs st m
  run fuel xs' st' (cont result)
run Dry xs st _ = pure (Nothing, xs, st)

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
 (seed' `shiftR` 2) :: randoms seed'

partial
main : IO ()
main = do
  seed <- time
  (Just score, _, state) <- run forever (randoms (fromInteger seed))  initState quiz
      | _ => putStrLn "Run out of fuel"
  putStrLn $ "Final score: "  ++ show state
