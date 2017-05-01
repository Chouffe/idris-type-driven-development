module ArithCmdDo

-- Extending command to allow sequences of commands
data Command : Type -> Type where
  PutStr : String -> Command ()
  GetLine : Command String

  Pure : ty -> Command ty
  Bind : Command a -> (a -> Command b) -> Command b

-- Type for user input
data Input = Answer Int
           | QuitCmd

runCommand : Command a -> IO a
runCommand (PutStr x) = putStr x
runCommand GetLine = getLine
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
