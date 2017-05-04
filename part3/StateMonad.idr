module StateMonad

import Control.Monad.State

addIfPositive : Integer -> State Integer Bool
addIfPositive x = do
  when (x > 0) $ do
    current <- get
    put (current + x)
  pure (x > 0)

addPositives : List Integer -> State Integer Nat
addPositives xs = do
  added <- traverse addIfPositive xs
  pure $ length $ filter id added
