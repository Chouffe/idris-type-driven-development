module Arith

import Data.Primitives.Views

randoms : Int -> Stream Int
randoms seed = let seed' = 1448393 * seed + 2124898391 in
                   (seed `shiftR` 2) :: randoms seed'

arithInputs : Int -> Stream Int
arithInputs seed = map bound (randoms seed)
  where
    bound : Int -> Int
    bound x with (divides x 12)
      bound ((12 * div) + rem) | (DivBy prf) = rem + 1

data Face : Type where
  Heads : Face
  Tails : Face

coinFlips : (count : Nat) -> Stream Int -> List Face
coinFlips count xs = take count $ map getFace xs
  where
    getFace : Int -> Face
    getFace x = if mod x 2 == 0
                   then Heads
                   else Tails
