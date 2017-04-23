module List

data Elem : a -> List a -> Type where
  Here : Elem x (x :: xs)
  There : Elem x xs -> Elem x (y :: xs)

data Last : List a -> a -> Type where
  LastOne : Last [value] value
  LastCons : (prf : Last xs value) -> Last (y :: xs) value

Uninhabited (Last [] value) where
  uninhabited _ impossible

last123 : Last [1, 2, 3] 3
last123 = LastCons (LastCons LastOne)

notInNil : Last [] value -> Void
notInNil LastOne impossible
notInNil (LastCons _) impossible

notInNil2 : (notHere : (x = value) -> Void) -> Last [x] value -> Void
notInNil2 notHere LastOne = notHere Refl
notInNil2 notHere (LastCons prf) = absurd prf

notInTail : (notThere : Last (y :: xs) value -> Void) -> Last (x :: (y :: xs)) value -> Void
notInTail notThere (LastCons prf) = notThere prf

isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No notInNil
isLast (x :: []) value = case decEq x value of
                              (Yes Refl) => Yes LastOne
                              (No notHere) => No (notInNil2 notHere)
isLast (x :: y :: xs) value = case isLast (y :: xs) value of
                                   (Yes LastOne) => Yes (LastCons LastOne)
                                   (Yes (LastCons prf)) => Yes (LastCons (LastCons prf))
                                   (No notThere) => No (notInTail notThere)
