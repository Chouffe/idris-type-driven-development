module Vect

import Data.Fin

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : (x : a) -> (xs : Vect k a) -> Vect (S k) a

append : Vect n elem -> Vect m elem -> Vect (n + m) elem
append [] y = y
append (x :: xs) y = x :: append xs y

zip : Vect n a -> Vect n b -> Vect n (a, b)
zip [] [] = []
zip (x :: xs) (y :: ys) = (x, y) :: zip xs ys

-- Bound safe lookups!! non inclusive upper bound of n
index : Fin n -> Vect n a -> a
index FZ (x :: _) = x
index (FS x) (_ :: xs) = index x xs

take : (k : Fin n) -> Vect n a -> Vect (finToNat k) a
take FZ _ = []
take (FS y) (x :: xs) = x :: take y xs

sumEntries : Num a => (pos : Integer) -> Vect n a -> Vect n a -> Maybe a
sumEntries {n} pos xs ys = case integerToFin pos n of
                                Nothing => Nothing
                                Just idx => Just $ index idx xs + index idx ys
