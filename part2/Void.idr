module Void

-- import Data.Vect'

data Vect' : Nat -> Type -> Type where
  Nil : Vect' Z a
  (::) : a -> Vect' k a -> Vect' (S k) a

-- Void: A type with no values
-- Express something that can't happen
-- data Void : Type  -- No constructors

twoPlusTwoNotFive : 2 + 2 = 5 -> Void
twoPlusTwoNotFive Refl impossible

-- Important to check that a function that returns Void is a total function
loop : Void
loop = loop
-- loop is not total (due to recursive path)

valueNotSucc : (x : Nat) -> x = S x -> Void
valueNotSucc _ Refl impossible

-- If you were able to provide a value of the empty type, you'd be able to produce a value of any type. If you have a proof that an impossible value has happened, you can do anything (called absurd in haskell)
-- void : Void -> a
-- If you know what cant happen, you can use this knowledge to express limitations about what can happen. You can express more precisely what a function is intended to do

-- Limitations with our previous approach
-- checkEqNat : (num1 : Nat) -> (num2 : Nat) -> Maybe (num1 = num2)
-- checkEqNat num1 num2 = Nothing
-- What we want is to produce either
--  -- a proof that they are equal (of type num1 = num2) or a proof that they are not equal (of type num1 = num2 -> Void)
-- you'd like to state that checking whether num1 = num2 is a decidable property

-- Defined in the Prelude
-- data Dec : (prop : Type) -> Type where
--   Yes : (prf : prop) -> Dec prop
--   No : (contra : prop -> Void) -> Dec prop

-- the (Dec (2 + 2 = 4)) (Yes Refl)
-- the (Dec (2 + 2 = 5)) (No twoPlusTwoNotFive)

zeroNotSucc : (0 = S k) -> Void
zeroNotSucc Refl impossible

succNotZero : (S k = 0) -> Void
succNotZero Refl impossible

noRec : (contra : (k = j) -> Void) -> (S k = S j) -> Void
noRec contra Refl = contra Refl

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Dec (n1 = n2)
checkEqNat Z Z = Yes Refl
checkEqNat Z (S k) = No zeroNotSucc
checkEqNat (S k) Z = No succNotZero
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Yes prf => Yes (cong prf)
                              No contra => No (noRec contra)

-- DecEq: an interface for decidable equality
-- interface DecEq ty where
--     decEq : (val1 : ty) -> (val2 : ty) -> Dec (val1 = val2)

-- exactLength : (len : Nat) -> (input : Vect' m a) -> Maybe (Vect' len a)
-- exactLength {m} len input = case decEq m len of
--                                  (Yes Refl) => Just input
--                                  (No _) => Nothing

headUnequal : DecEq a =>
              {xs : Vect' n a} ->
              {ys : Vect' n a} ->
              (contra : (x = y) -> Void) ->
              ((x :: xs) = (y :: ys)) -> Void
headUnequal {xs = []} {ys = []} contra Refl = contra Refl
headUnequal {xs = (y :: ys)} {ys = (y :: ys)} contra Refl = contra Refl

tailUnequal : DecEq a =>
              {xs : Vect' n a} ->
              {ys : Vect' n a} ->
              (contra : (xs = ys) -> Void) ->
              ((x :: xs) = (y :: ys)) -> Void
tailUnequal {xs = []} {ys = []} contra Refl = contra Refl
tailUnequal {xs = (y :: ys)} {ys = (y :: ys)} contra Refl = contra Refl

DecEq a => DecEq (Vect' n a) where
  decEq : (xs : Vect' n a) -> (ys : Vect' n a) -> Dec (xs = ys)
  decEq [] [] = Yes Refl
  decEq (x :: xs) (y :: ys) = case decEq x y of
                                   No contra => No (headUnequal contra)
                                   Yes prf => case decEq xs ys of
                                                   Yes prf => Yes Refl
                                                   No => (tailUnequal xs ys)
