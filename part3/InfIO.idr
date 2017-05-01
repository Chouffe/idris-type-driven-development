module InfIO

public export
data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

-- Allows us to use do Notation for the InfIO type
export
(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

total
loopPrint : String -> InfIO
loopPrint msg = Do (putStrLn msg) (\_ => loopPrint msg)
-- loopPrint msg = do
--   putStrLn msg
--   loopPrint msg

run : InfIO -> IO ()
run (Do action cont) = do
  result <- action
  run (cont result)

data Fuel = Dry | More Fuel

tank : Nat -> Fuel
tank Z = Dry
tank (S k) = More (tank k)

total
totalRun1 : Fuel -> InfIO -> IO ()
totalRun1 Dry _ = putStrLn "Out of fuel..."
totalRun1 (More fuel) (Do action cont) = do
  result <- action
  totalRun1 fuel (cont result)

data LFuel = LDry | LMore (Lazy LFuel)

-- Non total function because it introduces non termination
forever : LFuel
forever = LMore forever  -- Generates fuel as needed

totalRun2 : LFuel -> InfIO -> IO ()
totalRun2 LDry _ = pure ()
totalRun2 (LMore fuel) (Do action cont) = do
  result <- action
  totalRun2 fuel (cont result)

totalRepl : (prompt : String) -> (action : String -> IO String) -> InfIO
totalRepl prompt action = do
  putStr prompt
  input <- getLine
  Do (action input) (\_ => totalRepl prompt action)
