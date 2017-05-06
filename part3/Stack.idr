module Stack

import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  Pure : a -> StackCmd a height height
  (>>=) : StackCmd a height1 height2 -> (a -> StackCmd b height2 height3) -> StackCmd b height1 height3

testAdd : StackCmd Integer 0 0
testAdd = do
  Push 10
  Push 20
  n1 <- Pop
  n2 <- Pop
  Pure $ n1 + n2

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do
  n1 <- Pop
  n2 <- Pop
  Push $ n1 + n2

-- Implementing the stack using Vect
runStack : (stk : Vect inHeight Integer) ->
           StackCmd a inHeight outHeight ->
           (a, Vect outHeight Integer)
runStack stk (Push x) = ((), x :: stk)
runStack (x :: xs) Pop = (x, xs)
runStack (x :: xs) Top = (x, x :: xs)
runStack stk (Pure x) = (x, stk)
runStack stk (x >>= f) = let (val, stk') = runStack stk x in
                             runStack stk' (f val)

-- runStack [] testAdd = (30, [])
-- runStack [10, 20] doAdd = ((), [30])

-- runStack [10, 20] (do doAdd; doAdd) would result in a compule time error :)
-- By putting the height of the stack in the type, you explicitely specify the pre/post conditions on each operiations
