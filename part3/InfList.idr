module InfList

data InfList : Type -> Type where
  (::) : (value : elem) -> Inf (InfList elem) -> InfList elem
  -- The Inf generic type marks the InfList elem argument as potentially infinite

%name InfList xs, yz, zs

-- states that its argument should only be evaluated when its result is forced
-- Delay : (value : ty) -> Inf ty
-- Returns the result from a delayed computation
-- Force : (computation : Inf ty) -> ty

total
countFrom : Integer -> InfList Integer
countFrom x = x :: Delay (countFrom (x + 1))

-- Idris considers countFrom total although it produces an infinite list of integers
-- Properties of total functions:
-- if total, a function will never crash due to a missing case (all well typed inputs are covered)
-- will always return a well typed result
-- will always return within a finite time

-- countFrom makes a delayed recursive call

-- Definition:
-- Terminates with a well typed result
-- Produces a non-empty finite prefix of a well typed infinite result in finite time

-- Processing infinite lists
getPrefix : (count : Nat) -> InfList ty -> List ty
getPrefix Z _ = []
getPrefix (S k) (value :: xs) = value :: getPrefix k xs
-- getPrefix 10 (countFrom 0)

-- Idris defines the Stream Datatype in the Prelude
-- data Stream : Type -> Type where
-- 	(::) : (value : elem) -> Inf (Stream elem) -> Stream elem

-- repeat : elem -> Stream elem
-- take : (n : Nat) -> (xs : Stream elem) -> List elem
-- iterate : (f : elem -> elem) -> (x : elem) -> Stream elem

-- Syntactic Sugar for Stream Generation
-- [1..]
-- [1,3..]

Functor InfList where
  map f (x :: xs) = f x :: map f xs
