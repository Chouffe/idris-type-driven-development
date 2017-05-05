module Door

-- data DoorCmd : Type -> Type where
--   Open : DoorCmd ()
--   Close : DoorCmd ()
--   RingBell : DoorCmd ()
--   Pure : a -> DoorCmd a
--   (>>=) : DoorCmd a -> (a -> DoorCmd b) -> DoorCmd b

-- Example of sequence of operations
-- doorProg : DoorCmd ()
-- doorProg = do
--   RingBell
--   Open
--   Close

-- Cannot describe invalid sequences of operations that dont follow the protocol
-- doorProgBad : DoorCmd ()
-- doorProgBad = do
--   Open
--   Open
--   RingBell

-- You can avoid this and limit functions with DoorCmd to valid sequences of operations by keeping track of the Door's State in the type of the DoorCmd operations

data DoorState = DoorClosed | DoorOpened  -- Two possible states of a Door

data DoorCmd : Type -> DoorState -> DoorState -> Type where
  Open : DoorCmd () DoorClosed DoorOpened
  Close : DoorCmd () DoorOpened DoorClosed
  -- RingBell : DoorCmd () DoorClosed DoorClosed
  RingBell : DoorCmd () state state  -- Ringing the bell can work in any state
  Pure : a -> DoorCmd a state state
  (>>=) : DoorCmd a state1 state2 -> (a -> DoorCmd b state2 state3) -> DoorCmd b state1 state3

-- Each command's type takes three arguments
-- - the type of the value produced by the command
-- - the input state of the door
-- - the output state of the door

-- The type of doorProg includes pre/post conditions in types!!
doorProg : DoorCmd () DoorClosed DoorClosed
doorProg = do
  RingBell
  Open
  Close

-- This will not compile :-)
-- doorProgBad : DoorCmd () DoorClosed DoorClosed
-- doorProgBad = do
--   Open
--   Open
--   RingBell

doorProgTest : DoorCmd () DoorClosed DoorClosed
doorProgTest = do RingBell
                  Open
                  RingBell
                  Close

-- Not all systems have an exact number of states that you can determine in advance

-- Exercises:
namespace GuessGame
  data GuessCmd : Type -> Nat -> Nat -> Type where
    Try : Integer -> GuessCmd Ordering (S guesses) guesses
    Pure : a -> GuessCmd a state state
    (>>=) : GuessCmd a state1 state2 -> (a -> GuessCmd b state2 state3) -> GuessCmd b state1 state3


  threeGuesses : GuessCmd () 3 0
  threeGuesses = do Try 10
                    Try 20
                    Try 15
                    Pure ()

  -- Should not type check
  -- noGuesses : GuessCmd () 0 0
  -- noGuesses = do Try 10
  --                Pure ()


namespace MatterExo
  data Matter = Solid | Liquid | Gas

  data MatterCmd : Type -> Matter -> Matter -> Type where
    Boil : MatterCmd () Liquid Gas
    Melt : MatterCmd () Solid Liquid
    Condense : MatterCmd () Gas Liquid
    Freeze : MatterCmd () Liquid Solid

    Pure : a -> MatterCmd a state state
    (>>=) : MatterCmd a state1 state2 -> (a -> MatterCmd b state2 state3) -> MatterCmd b state1 state3

  iceSteam : MatterCmd () Solid Gas
  iceSteam = do Melt
                Boil

  steamIce : MatterCmd () Gas Solid
  steamIce = do Condense
                Freeze

  overMelt : MatterCmd () Solid Gas
  overMelt = do Melt
                Boil

