module Sort

import Data.Vect

total sort : Ord a => Vect n a -> Vect n a
sort [] = []
sort (x :: xs) = insert x $ sort xs
  where
    insert : Ord a => a -> Vect m a -> Vect (S m) a
    insert e [] = [e]
    insert e (y :: ys) = if e < y
                            then e :: y :: ys
                            else y :: insert e ys
