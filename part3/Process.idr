module Process

import System.Concurrency.Channels

data Message = Add Nat Nat
data MessagePID = MkMessage PID

data Process : Type -> Type where
  Action : IO a -> Process a                          -- A process consisting of a single IO action
  Spawn : Process () -> Process (Maybe MessagePID)
  Request : MessagePID -> Message -> Process (Maybe Nat)
  Respond : ((msg : Message) -> Process Nat) -> Process (Maybe Message)
  Loop : Inf (Process a) -> Process a                 -- Explicitely loops, executing a potentially infinite process
  Pure : a -> Process a                               -- A process with no action, producing a pure value
  (>>=) : Process a -> (a -> Process b) -> Process b  -- Sequences two subprocesses and supports do notation

                                                                                                   data Fuel = Dry | More Fuel

partial
forever : Fuel
forever = More forever

total
run : Fuel -> Process t -> IO (Maybe t)
run Dry _ = pure Nothing
run fuel (Action act) = do res <- act
                           pure $ Just res
run fuel (Spawn proc) = do Just pid <- spawn $ run proc | Nothing => pure Nothing
                           pure $ Just $ MkMessage pid
run fuel (Request (MkMessage process) msg) = do
  Just chan <- connect process | _ => pure Nothing
  ok <- unsafeSend chan msg
  if ok
     then do Just x <- unsafeRecv Nat chan | Nothing => pure $ Just Nothing
             pure $ Just $ Just x
     else pure $ Just Nothing
run (Respond calc) = do
  Just sender <- listen 1 | Nothing => pure $ Just Nothing  -- Waits for 1 second for an incoming connection
  Just msg <- unsafeRecv Message sender | Nothing => pure $ Just Nothing -- Gets the message
  res <- run (calc msg)  -- Calculate the response to the message
  unsafeSend sender res  -- sends the response of type Nat
  pure $ Just $ Just msg
run (More fuel) (Loop act) = run fuel act  -- This will prevent the run function to be total, solution is to include a Fuel and reduce it when looping
run fuel (Pure val) = pure $ Just val
run fuel (act >>= next) = do
  Just x <- run act | Nothing => pure Nothing
  run fuel (next x)

-- Using IO in Action allows arbitrary IO actions in processes (writing to the console, but also unsafe communication primitives).
-- It could be restricted by a more precise command type (cf chapter 11)

total
procAdder : Process ()
procAdder = do Respond (\msg => case msg of
                                     Add x y => Pure $ x + y)
               Loop procAdder

procMain : Process ()
procMain = do
  Just process <- Spawn procAdder | Nothing => Action $ putStrLn "spawn failed"
  Just answer <- Request process (Add 3 4) | Nothing => Action $ putStrLn "Request failed"
  Action $ putStrLn $ "the answer is " ++ show answer

-- Unlike the previous version, procMain cant expect to receive a String rather than Nat. The communication protocol is encapsulated (using Request and Respond)
-- Some issues:
-- + procAdder is not total... Need to use Loop to include Inf

partial
runProc : Process () -> IO ()
runProc proc = do run forever proc
                  pure ()

-- There is no guarantee that a looping process will respond to messages
procAdderBad1 : Process ()
procAdderBad1 = do Action $ putStrLn "Out of the office today"
                   Loop procAdderBad1

-- They both type check and are both total but neither will respond to any messages
procAdderBad2 : Process ()
procAdderBad2 = Loop procAdderBad2

-- The meaning of totality:
-- you are guaranteed that a function behaves in exactly the way described by its type. So it all depend on whether a type is precise enough.
-- Process is not precise enough to guarantee that a process contains a Respond command before any Loop
-- Process is too specific to the problem of writing a concurrent sevice to add numbers
