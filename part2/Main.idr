module Main

import Data.Vect

xor : Bool -> Bool -> Bool
xor False False = False
xor False True = True
xor True False = True
xor True True = False

describeList : List Int -> String

allLengths : List String -> List Nat
allLengths [] = []
allLengths (word :: words) = length word :: allLengths words

isEven : Nat -> Bool
isEven Z = True
isEven (S k) = not (isEven k)

-- Vectors
fourInts : Vect 4 Int
fourInts = [0, 1, 2, 3]

sixInts : Vect 6 Int
sixInts = [4, 5, 6, 7, 8, 9]

tenInts : Vect 10 Int
tenInts = fourInts ++ sixInts

allLengths' : Vect n String -> Vect n Nat
allLengths' = map length
