module DoorJam

data DoorResult = OK | Jammed

data DoorState = DoorOpen | DoorClosed

data DoorCmd : (ty : Type) -> DoorState -> (ty -> DoorState) -> Type where
  Open : DoorCmd DoorResult DoorClosed (\res => case res of
                                                     OK => DoorOpen
                                                     Jammed => DoorClosed)
  Close : DoorCmd () DoorOpen (const DoorClosed)
  RingBell : DoorCmd () DoorClosed (const DoorClosed)

  Display : String -> DoorCmd () state (const state)

  Pure : (res : ty) -> DoorCmd ty (stateFn res) stateFn
  (>>=) : DoorCmd a state1 state2Fn -> ((res : a) -> DoorCmd b (state2Fn res) state3Fn) -> DoorCmd b state1 state3Fn

-- doorProg : DoorCmd () DoorClosed (const DoorClosed)
-- doorProg = do
--   RingBell
--   jam <- Open
--   case jam of
--        OK => do Display "Glad to be of Service"
--                 Close
--        Jammed => Display "Door Jammed"

doorProg : DoorCmd () DoorClosed (const DoorClosed)
doorProg = do
  RingBell
  OK <- Open | Jammed => Display "Door Jammed"
  Display "Glad to be of Service"
  Close
-- This example describes a protocol in the type and it explicitely says where an operation might fail
-- In doorProg, the type of Open means that you need to check its result before you can proceed with any further operations that change the state

logOpen : DoorCmd DoorResult DoorClosed (\res => case res of
                                                      OK => DoorOpen
                                                      Jammed => DoorClosed)

-- Pure allows you to define functions like the following where the call to Pure changes the State
logOpen = do Display "Trying to open the door"
             OK <- Open | Jammed => do Display "Jammed"
                                       Pure Jammed
             Display "Success"
             -- ?pure_ok
             Pure OK
