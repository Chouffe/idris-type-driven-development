module Streams

labelWith : Stream a -> List b -> List (a, b)
labelWith xs [] = []
labelWith (value :: xs) (y :: ys) = (value, y) :: labelWith xs ys

label : List a -> List (Integer, a)
label = labelWith [0..]
-- label = labelWith (iterate (+1) 0)

everyOther : Stream a -> Stream a
everyOther (x :: y :: xs) = x :: everyOther xs
