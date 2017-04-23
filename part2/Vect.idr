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

removeElem1 : DecEq a => (value : a) -> Vect (S n) a -> Maybe (Vect n a)
removeElem1 value (x :: []) = case decEq x value of
                                   (Yes Refl) => Just []
                                   (No contra) => Nothing
removeElem1 value (x :: y :: xs) = case decEq x value of
                                        (Yes Refl) => Just $ y :: xs
                                        (No contra) => map (x::) $ removeElem1 value (y :: xs)

removeElem2 : DecEq a => (value : a) -> Vect (S n) a -> (newLength ** Vect newLength a)
removeElem2 value (x :: []) = case decEq value x of
                                   (Yes Refl) => (_ ** [])
                                   (No contra) => (_ ** [x])
removeElem2 value (x :: y :: xs) = case decEq x value of
                                        (Yes Refl) => (_ ** (y :: xs))
                                        (No contra) => let (_ ** ys) = removeElem2 value (y :: xs) in
                                                           (_ ** x :: ys)

data Elem : a -> Vect k a -> Type where
  Here : Elem x (x :: xs)
  There : (later : Elem x xs) -> Elem x (y :: xs)

Uninhabited (Elem x []) where
  uninhabited Here impossible

maryInVector : Elem "Mary" ["Peter", "Paul", "Mary"]
maryInVector = There (There Here)

removeElem3 : (value : a) ->
              (xs : Vect (S n) a) ->
              (prf : Elem value xs) ->
              Vect n a
removeElem3 value (value :: xs) Here = xs
removeElem3 {n = Z} value (x :: []) (There later) = absurd later
removeElem3 {n = (S k)} value (x :: xs) (There later) = x :: removeElem3 value xs later


removeElem4 : (value : a) ->
              (xs : Vect (S n) a) ->
              {auto prf : Elem value xs} ->
              Vect n a
removeElem4 value (value :: xs) {prf = Here} = xs
removeElem4 {n = Z} value (x :: []) {prf = (There later)} = absurd later
removeElem4 {n = (S k)} value (x :: xs) {prf = (There later)} = x :: removeElem4 value xs

notInNil : Elem value [] -> Void
notInNil Here impossible
notInNil (There _) impossible

notInTail : (notHere : (value = x) -> Void) ->
            (notThere : Elem value xs -> Void) ->
            Elem value (x :: xs) -> Void
notInTail notHere notThere Here = notHere Refl
notInTail notHere notThere (There later) = notThere later

isElem : DecEq ty => (value : ty) -> (xs : Vect n ty) -> Dec (Elem value xs)
isElem value [] = No notInNil
isElem value (x :: xs) = case decEq value x of
                              (Yes Refl) => (Yes Here)
                              (No notHere) => case isElem value xs of
                                                   (Yes Here) => Yes (There Here)
                                                   (Yes (There later)) => Yes (There (There later))
                                                   (No notThere) => No (notInTail notHere notThere)
