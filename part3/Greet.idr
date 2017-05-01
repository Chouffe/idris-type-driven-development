module Greet

import InfIO

greet : InfIO
greet = do putStr "Enter your name: "
           name <- getLine
           putStrLn $ "Hello " ++ name
           greet
-- One issue with the InfIO type is that there is no way to gracefully quit the program (Only C-c)
-- Introducing a small variation on InfIO can make it work

run : InfIO -> IO ()
run (Do action cont) = do
  result <- action
  run (cont result)
