module StackIO

import Data.Vect

data StackCmd : Type -> Nat -> Nat -> Type where
  Push : Integer -> StackCmd () height (S height)
  Pop : StackCmd Integer (S height) height
  Top : StackCmd Integer (S height) (S height)

  GetStr : StackCmd String height height
  PutStr : String -> StackCmd () height height

  Pure : a -> StackCmd a height height
  (>>=) : StackCmd a height1 height2 -> (a -> StackCmd b height2 height3) -> StackCmd b height1 height3

-- The effects library allows you to combine effects like state and IO without having to definer a new type like StackCmd here
runStack : (stk : Vect inHeight Integer) ->
           StackCmd a inHeight outHeight ->
           IO (a, Vect outHeight Integer)
runStack stk (Push x) = pure ((), x :: stk)
runStack (x :: xs) Pop = pure (x, xs)
runStack (x :: xs) Top = pure (x, x :: xs)
runStack stk GetStr = do
  str <- getLine
  pure (str, stk)
runStack stk (PutStr x) = do
  putStr x
  pure ((), stk)
runStack stk (Pure x) = pure (x, stk)
runStack stk (x >>= f) = do
  (val, stk') <- runStack stk x
  runStack stk' (f val)

data StackIO : Nat -> Type where
  Do : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1

namespace StackDo
  (>>=) : StackCmd a height1 height2 -> (a -> Inf (StackIO height2)) -> StackIO height1
  (>>=) = Do

data Fuel = Dry | More (Lazy Fuel)

partial
forever : Fuel
forever = More forever

run : Fuel -> Vect height Integer -> StackIO height -> IO ()
run (More fuel) xs (Do cmd cont) = do
  (val, xs') <- runStack xs cmd
  run fuel xs' (cont val)
run Dry xs x = pure ()

data StackInput = Number Integer
                | Add
                | Subtract
                | Multiply
                | Negate
                | Discard
                | Duplicate

parseInput : String -> Maybe StackInput
parseInput "" = Nothing
parseInput "add" = Just Add
parseInput "subtract" = Just Subtract
parseInput "multiply" = Just Multiply
parseInput "negate" = Just Negate
parseInput "discard" = Just Discard
parseInput "duplicate" = Just Duplicate
parseInput x = if all isDigit (unpack x)
                  then Just $ Number $ cast x
                  else Nothing

doAdd : StackCmd () (S (S height)) (S height)
doAdd = do
  n1 <- Pop
  n2 <- Pop
  Push $ n1 + n2

doSubtract : StackCmd () (S (S height)) (S height)
doSubtract = do
  n1 <- Pop
  n2 <- Pop
  Push $ n1 - n2

doMultiply : StackCmd () (S (S height)) (S height)
doMultiply = do
  n1 <- Pop
  n2 <- Pop
  Push $ n1 * n2

doNegate : StackCmd () (S height) (S height)
doNegate = do
  n <- Pop
  Push $ 0 - n

doDiscard : StackCmd Integer (S height) height
doDiscard = do
  n <- Pop
  PutStr $ "Discarded " ++ show n
  Pure n

doDuplicate : StackCmd () (S height) (S (S height))
doDuplicate = do
  n <- Top
  Push n

mutual
  total
  tryAdd : StackIO height
  tryAdd {height = S (S k)} = do
    doAdd
    result <- Top
    PutStr $ show result
    stackCalc
  tryAdd {height = _} = do
    PutStr "Fewer than 2 items on the stack\n"
    stackCalc

  trySubtract : StackIO height
  trySubtract {height = S (S k)} = do
    doSubtract
    result <- Top
    PutStr $ show result
    stackCalc
  trySubtract {height = _} = do
    PutStr "Fewer than 2 items on the stack\n"
    stackCalc

  tryMultiply : StackIO height
  tryMultiply {height = S (S k)} = do
    doMultiply
    result <- Top
    PutStr $ show result
    stackCalc
  tryMultiply {height = _} = do
    PutStr "Fewer than 2 items on the stack\n"
    stackCalc

  tryNegate : StackIO height
  tryNegate {height = (S k)} = do
    doNegate
    result <- Top
    PutStr $ show result
    stackCalc
  tryNegate {height = _} = do
    PutStr "Fewer than 1 item on the stack\n"
    stackCalc

  tryDiscard : StackIO height
  tryDiscard {height = (S k)} = do
    doDiscard
    stackCalc
  tryDiscard {height = _} = do
    PutStr "Fewer than 1 item on the stack\n"
    stackCalc

  tryDuplicate : StackIO height
  tryDuplicate {height = (S k)} = do
    doDuplicate
    stackCalc
  tryDuplicate {height = _} = do
    PutStr "Fewer than 1 item on the stack\n"
    stackCalc

  total
  stackCalc : StackIO height
  stackCalc = do
    PutStr "> "
    input <- GetStr
    case parseInput input of
         Nothing => do PutStr "Invalid Input\n"
                       stackCalc
         Just (Number x) => do Push x
                               stackCalc
         Just Add => tryAdd
         Just Subtract => trySubtract
         Just Multiply => tryMultiply
         Just Negate => tryNegate
         Just Discard => tryDiscard
         Just Duplicate => tryDuplicate

main : IO ()
main = run forever [] stackCalc

-- By separating the looping part (StackIO) from the terminatiing component (StackCmd), you can be sure that stackCalc has the following properties
-- + It will continue running indefinitely
-- + It will never crash due to user input that is not handled
-- + It will never crash due to a stack overflow

