module ExactLength

data Vect : Nat -> Type -> Type where
  Nil : Vect Z a
  (::) : a -> Vect k a -> Vect (S k) a

exactLength : (len : Nat) -> (input : Vect m a) -> Maybe (Vect len a)
-- exactLength {m} len input =
  -- Not possible this way... == is not informative enough to guarantee that m and len are equal even if it returns True
  -- case m == len of
  --      True => Just input
  --      False => Nothing

data EqNat : (n1 : Nat) -> (n2 : Nat) -> Type where
  Same : (n : Nat) -> EqNat n n
