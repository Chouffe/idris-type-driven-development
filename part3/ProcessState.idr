module ProcessState

import System.Concurrency.Channels

data Message = Add Nat Nat

data MessagePID = MkMessage PID

data ProcState = NoRequest
               | Sent
               | Complete

data Process : Type -> (inState : ProcState) -> (outState : ProcState) -> Type where
  Request : MessagePID -> Message -> Process Nat state state
  Respond : ((msg : Message) -> Process Nat NoRequest NoRequest) -> Process (Maybe Message) st Sent  -- When processing, stays in the NoRequest state to ensure you dont start processing a new response before completing this one
  Spawn : Process () NoRequest Complete -> Process (Maybe MessagePID) st st  -- You can only spawn a process if its a looping process (from NoRequest to Complete)
  Loop : Inf (Process a NoRequest Complete) -> Process a Sent Complete  -- Can only loop with a process that goes from NoRequest to Complete
  Action : IO a -> Process a state state
  Pure a : a -> Process a state state
  (>>=) : Process a state1 state2 -> (a -> Process b state2 state3) -> Process b state1 state3

-- Process () NoRequest Complete is the type of a process that responds to a request and then loops.
-- Process () NoRequest Sent is the type of a process that responds to one or more requests and then terminates
-- Process () NoRequest NoRequest is the type of a process that responds to no requests and then terminates.

Service : Type -> Type
Servie a = Process a NoRequest Complete

Client : Type -> Type
Client a = Process a NoRequest NoRequest

procAdder : Service ()
procAdder = do Respond (\msg => case msg of
                                     Add n1 n2 => Pure $ n1 + n2)
               Loop procAdder

-- procAdderBad1 and procAdderBad2 no longer type check

procMain : Client ()
procMain = do Just adderId <- Spawn procAdder | Nothing => Action $ putStrLn "Spawn failed"
              answer <- Request adderId $ Add 2 3
              Action $ printLn answer

-- All requests of type Message are sent responses of type Nat
-- Every process started with Spawn is guaranteed to loop indefinitely and respond to requests on every iterations
-- everytime a process sends a Request to a service started with Spawn, it will receive a response in finite time as long as the service is defined in total functions

-- You can write type safe concurrent programs that cant deadlock. Because every request is guaranteed to receive a response eventually
