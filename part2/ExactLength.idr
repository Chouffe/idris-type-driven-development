module ExactLength

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

-- exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
-- exactLength {m} len input =
  -- Not possible this way... == is not informative enough to guarantee that m and len are equal even if it returns True
  -- case m == len of
  --      True => Just input
  --      False => Nothing

data EqNat : (n1 : Nat) -> (n2 : Nat) -> Type where
  Same : (n : Nat) -> EqNat n n

sameS : (eq : EqNat k j) -> EqNat (S k) (S j)
sameS (Same k) = (Same (S k))

checkEqNat : (n1 : Nat) -> (n2 : Nat) -> Maybe (EqNat n1 n2)
checkEqNat Z Z = Just (Same 0)
checkEqNat Z (S k) = Nothing
checkEqNat (S k) Z = Nothing
checkEqNat (S k) (S j) = case checkEqNat k j of
                              Nothing => Nothing
                              Just eq => Just $ (sameS eq)

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
exactLength {m} len input = case checkEqNat len m of
                                 Nothing => Nothing
                                 (Just (Same k)) => Just input  -- We have evidence that m and len are equal

-- Equality Type in Idris
-- data (=) : a -> b -> Type where    -- Takes two generic arguments a and b
--      Refl : x = x   -- Like Same but x is an implicit argument
-- The name Refl is short for Reflexive: a value is equal to itself
checkEqNat' : (n1 : Nat) -> (n2 : Nat) -> Maybe (n1 = n2)
checkEqNat' Z Z = Just Refl
checkEqNat' Z (S k) = Nothing
checkEqNat' (S k) Z = Nothing
checkEqNat' (S k) (S j) = case checkEqNat' k j of
                               Nothing => Nothing
                               Just prf => Just (cong prf)

-- Exercises
sameCons : {xs : List a} -> {ys : List a} -> xs = ys -> x :: xs = x :: ys
sameCons prf = cong prf

sameLists : {xs : List a} -> {ys : List a} -> x = y -> xs = ys -> x :: xs = y :: ys
sameLists Refl Refl = Refl

data ThreeEq : a -> b -> c -> Type where
  TSame : (x : a) -> ThreeEq x x x

allSameS : (x, y, z : Nat) -> ThreeEq x y z -> ThreeEq (S x) (S y) (S z)
allSameS z z z (TSame z) = TSame (S z)
-- If x y and z are all equal, then S x, S y and S z are all equal too

