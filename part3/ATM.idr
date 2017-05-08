module ATM

import Data.Vect

PIN : Type
PIN = Vect 4 Char

-- The possible states of an ATM
data ATMState = Ready         -- waiting for a card to be inserted
              | CardInserted  -- card inside the ATM be the system has not yet checked a PIN entry against the card
              | Session       -- card inside the ATM, the user has entered a valid PIN for the card

data PINCheck = CorrectPIN
              | IncorrectPIN

data ATMCmd : (ty : Type) -> ATMState -> (ty -> ATMState) -> Type where
  InsertCard : ATMCmd () Ready (const CardInserted)
  -- TODO: Isnt quite right because a card can be ejected when there is no card in the machine...
  EjectCard : ATMCmd () state (const Ready)
  GetPIN : ATMCmd PIN CardInserted (const CardInserted)
  -- Only move to the Session state if the PIN is correct
  CheckPIN : PIN -> ATMCmd PINCheck CardInserted (\res => case res of
                                                               CorrectPIN => Session
                                                               IncorrectPIN => CardInserted)
  Dispense : (amount : Nat) -> ATMCmd () Session (const Session)
  GetAmount : ATMCmd Nat state (const state)

  Message : String -> ATMCmd () state (const state)

  Pure : (res : ty) -> ATMCmd ty (stateFn res) stateFn
  (>>=) : ATMCmd a state1 state2Fn -> ((res : a) -> ATMCmd b (state2Fn res) state3Fn) -> ATMCmd b state1 state3Fn

atm : ATMCmd () Ready (const Ready)
atm = do InsertCard
         pin <- GetPIN
         pinOK <- CheckPIN pin
         Message "Checking Card"
         case pinOK of
              CorrectPIN => do cash <- GetAmount
                               Dispense cash
                               EjectCard
                               Message "Please remove your card and cash"
              IncorrectPIN => do Message "Incorrect PIN"
                                 EjectCard
-- As long as atm type checks, you can be certain that you have maintained the important security property: the machine will only dispense cash when there's a card in the machine and the PIN has been entered correctly

testPIN : Vect 4 Char
testPIN = ['1', '2', '3' , '4']

readVect : (n : Nat) -> IO (Vect n Char)
readVect Z = pure []
readVect (S k) = do ch <- getChar
                    chs <- readVect k
                    pure $ ch :: chs

-- To try the atm function, you can execute ATMCmd actions in the IO monad
runATM : ATMCmd res inState outStateFn -> IO res
runATM InsertCard = do putStrLn "Please Insert your card (press enter)"
                       _ <- getLine
                       pure ()
runATM EjectCard = putStrLn "Card ejected"
runATM GetPIN = do putStrLn "Enter PIN: "
                   readVect 4
runATM (CheckPIN pin) = if pin == testPIN
                           then pure CorrectPIN
                           else pure IncorrectPIN
runATM GetAmount = do putStr "How much would you like? "
                      x <- getLine
                      pure (cast x)
runATM (Dispense amount) = putStrLn $ "Here is " ++ show amount
runATM (Message msg) = putStrLn msg
runATM (Pure res) = pure res
runATM (x >>= f) = do
  x' <- runATM x
  runATM (f x')
