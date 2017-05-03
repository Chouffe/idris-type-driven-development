module ArithCmdDo

import Fuel

-- Extending command to allow sequences of commands
data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String
  ReadFile : String -> Command (Either FileError String)
  WriteFile : String -> String -> Command (Either FileError ())

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

-- Type for user input
data Input = Answer Int
           | QuitCmd

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
runCommand (ReadFile filepath) = readFile filepath
runCommand (WriteFile filepath contents) = writeFile filepath contents
runCommand (Pure x) = pure x
runCommand (Bind c f) = do
  result <- runCommand c
  runCommand (f result)

namespace CommandDo
  (>>=)  : Command a -> (a -> Command b) -> Command b
  (>>=) = Bind

namespace ConsoleIODo
  data ConsoleIO : Type -> Type where
    Quit : a -> ConsoleIO a
    Do : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b

  (>>=) : Command a -> (a -> Inf (ConsoleIO b)) -> ConsoleIO b
  (>>=) = Do


-- Parsing input
readInput : (prompt : String) -> Command Input
readInput prompt = do
  PutStr prompt
  input <- GetLine
  if toLower input == "quit"
     then Pure QuitCmd
     else Pure $ Answer $ cast input

mutual
  correct : Stream Int -> (score : Nat) -> ConsoleIO Nat
  correct nums score = do
    PutStr "Correct!\n"
    quiz nums (score + 1)

  wrong : Stream Int -> Int -> (score : Nat) -> ConsoleIO Nat
  wrong nums ans score = do
    PutStr $ "Wrong, the answer is " ++ show ans ++ "\n"
    quiz nums score

  quiz : Stream Int -> (score : Nat) -> ConsoleIO Nat
  quiz (n1 :: n2 :: ns) score = do
    PutStr $ "Score so far: " ++ show score ++ "\n"
    input <- readInput (show n1 ++ " * " ++ show n2 ++ "?")
    case input of
         Answer answer => if answer == n1 * n2
                             then correct ns score
                             else wrong ns (n1 * n2) score
         QuitCmd => Quit score

-- Exercises

-- Implement a Shell

data ShellInput = Cat String
                | Copy String String
                | Exit

namespace ShellIODo
  data ShellIO : Type -> Type where
       Do : Command a -> (a -> Inf (ShellIO b)) -> ShellIO b
       Quit : a -> ShellIO a

  (>>=) : Command a -> (a -> Inf (ShellIO b)) -> ShellIO b
  (>>=) = Do

readShellInput : (prompt : String) -> Command (Maybe ShellInput)
readShellInput prompt = do
  input <- GetLine
  if input == "exit"
     then Pure $ Just $ Exit
     else case words input of
               "cat"::filepath::_             => Pure $ Just $ Cat filepath
               "copy"::source::destination::_ => Pure $ Just $ Copy source destination
               _                              => Pure Nothing

mutual
  shell : (prompt : String) -> ShellIO ()
  shell prompt = do
    minput <- readShellInput prompt
    case minput of
         Nothing => do PutStr "Unrecognized command..."
                       shell prompt
         (Just input) => handleInput prompt input

  handleInput : (prompt : String) -> ShellInput -> ShellIO ()
  handleInput prompt (Cat filepath) = do
    Right content <- ReadFile filepath
          | Left error => do PutStr ("Error: " ++ show error)
                             shell prompt
    PutStr content
    shell prompt
  handleInput prompt (Copy source destination) = do
     Right content <- ReadFile source
          | Left error => do PutStr ("Error: " ++ show error)
                             shell prompt
     Right result <- WriteFile content destination
          | Left error =>  do PutStr ("Error: " ++ show error)
                              shell prompt
     shell prompt
  handleInput prompt Exit = Quit ()


run : Fuel -> ShellIO a -> IO (Maybe a)
run fuel (Quit value) = pure $ Just value
run (More fuel) (Do action cont) = do
  result <- runCommand action
  run fuel (cont result)
run Dry _ = pure Nothing

main : IO ()
main = do
  run forever (shell "> ")
  pure ()
