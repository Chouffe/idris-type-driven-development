module ArithTotal

import Data.Primitives.Views
import System

%default total  -- unless stated otherwise

data InfIO : Type where
  Do : IO a -> (a -> Inf InfIO) -> InfIO

-- Allows us to use do Notation for the InfIO type
(>>=) : IO a -> (a -> Inf InfIO) -> InfIO
(>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

run : Fuel -> InfIO -> IO ()
run Dry _ = pure ()
run (More fuel) (Do action cont) = do
  result <- action
  run fuel (cont result)

partial
forever : Fuel
forever = More forever

quiz : Stream Int -> (score : Nat) -> InfIO
quiz (n1 :: n2 :: ns) score = do
  putStrLn $ "Score: " ++ show score
  putStrLn $ show n1 ++ " * " ++ show n2 ++ "?"
  answer <- getLine
  if (cast answer == n1 * n2)
     then do
       putStrLn "Correct!"
       quiz ns (score + 1)
    else do
      putStrLn $ "Wrong, the answer is " ++ show (n1 + n2)
      quiz ns score

randoms : Int -> Stream Int
randoms seed = let seed' = 1664525 * seed + 1013904223 in
									 (seed' `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
where
  bound : Int -> Int
  bound x with (divides x 12)
    bound ((12 * div) + rem) | (DivBy prf) = abs rem + 1

partial
main : IO ()
main = do
  seed <- time
  run forever $ quiz (arithInputs (fromInteger seed)) 0
