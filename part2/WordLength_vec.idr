module WordLength

import Data.Vect

total allLengths : Vect n String -> Vect n Nat
allLengths = map length

allL : Vect n String -> Vect n Nat
allL [] = []
allL (x :: xs) = ?allL_rhs_2

