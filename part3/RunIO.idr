module RunIO

import InfIO
import Fuel


data RunIO : Type -> Type where
  Quit : a -> RunIO a
  Do : IO a -> (a -> Inf (RunIO b)) -> RunIO b

(>>=) : IO a -> (a -> Inf (RunIO b)) -> RunIO b
(>>=) = Do

total
greet : RunIO ()
greet = do
  putStr "Enter your name: "
  name <- getLine
  if name == ""
     then do
       putStrLn "Bye Bye!"
       Quit ()
    else do
      putStrLn $ "Hello " ++ name
      greet

run : Fuel -> RunIO a -> IO (Maybe a)
run fuel (Quit value) = pure $ Just value
run (More fuel) (Do action cont) = do
  result <- action
  run fuel (cont result)
run Dry _ = pure Nothing

partial
main : IO ()
main = do run forever greet
          pure ()
