module PracticalEquality

import Data.Vect


-- Equality in Practice: Often used when defining functions on types that are indexed by numbers (like Vect, Fin)
myReverse : Vect n elem -> Vect n elem
myReverse [] = []
myReverse {n = S k} (x :: xs) = let result = myReverse xs ++ [x] in rewrite plusCommutative 1 k in result
-- proving that plus is commutative and then returning the result

-- We can do better: the problem here is that the actual body is complected with the commutativity proof

reverseProof : Vect (len + 1) elem -> Vect (S len) elem
reverseProof {len} ys = rewrite plusCommutative 1 len in ys

myReverse' : Vect n elem -> Vect n elem
myReverse' [] = []
myReverse' (x :: xs) = reverseProof (myReverse' xs ++ [x])
-- By introducing ?reverseProof, we are able to keep the relevant computation part of myReverse' separate from the details of the proof

reverseProofNil : Vect n a -> Vect (plus n 0) a
reverseProofNil {n = Z} [] = []
reverseProofNil {n = (S k)} (x :: xs) = x :: reverseProofNil xs

reverseProofXs : Vect (S (plus n len)) a -> Vect (plus n (S len)) a
reverseProofXs {n = Z} {len = len} xs = xs
reverseProofXs {n = (S k)} {len = len} (x :: xs) = x :: (reverseProofXs xs)

-- Efficient myReverse'
myReverse'' : Vect n elem -> Vect n elem
myReverse'' xs = reverse' [] xs
  where
    reverse' : Vect n a -> Vect m a -> Vect (n + m) a
    reverse' acc [] = reverseProofNil acc
    reverse' acc (x :: ys) = reverseProofXs $ reverse' (x :: acc) ys

-- Type checking and evaluation in Idris
test1 : Vect 4 Int
test1 = [1, 2, 3, 4]

test2 : Vect (2 + 2) Int
test2 = test1

-- Need to explain to Idris that `plus` is commutative
-- plusCommutative : (left : Nat) -> (right : Nat) -> left + right = right + left

append_nil : Vect m elem -> Vect (plus m 0) elem
append_nil {m} xs = rewrite plusZeroRightNeutral m in ?todo

append_xs : Vect (S (m + k)) elem -> Vect (plus m (S k)) elem
append_xs {m} {k} xs = rewrite sym (plusSuccRightSucc m k) in xs

myAppend : Vect n elem -> Vect m elem -> Vect (n + m) elem
myAppend [] ys = ?append_nil ys
myAppend (x :: xs) ys = ?append_xs $ x :: myAppend xs ys

plusCommutesZ : plus 0 m = plus m 0
plusCommutesZ {m = Z} = Refl
plusCommutesZ {m = (S k)} = rewrite plusCommutesZ {m = k} in Refl

plusCommutesS : S (plus m k) = plus m (S k)
plusCommutesS {m = Z} {k = k} = Refl
plusCommutesS {m = (S j)} {k = k} = rewrite plusCommutesS {m = j} {k = k} in Refl
-- rewrite plusSuccRightSucc m k in Refl

-- Exercises
myPlusCommutes : (n : Nat) -> (m : Nat) -> n + m = m + n
myPlusCommutes Z m = plusCommutesZ
myPlusCommutes (S k) m = rewrite myPlusCommutes k m in ?plusCommutesS
