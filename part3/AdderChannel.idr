module AdderChannel

import System.Concurrency.Channels
import Control.Monad

data Message = Add Nat Nat

adder : IO ()
adder = do Just senderChan <- listen 1 | Nothing => adder
           Just (Add n1 n2) <- unsafeRecv Message senderChan | Nothing => adder
           ok <- unsafeSend senderChan (n1 + n2)
           adder

main : IO ()
main = do Just adderId <- spawn adder | Nothing => "Spawn failed"
          Just chan <- connect adderId | Nothing => "Connection failed"
          ok <- unsafeSend chan (Add 2 3)
          Just answer <- unsafeRecv Nat chan | Nothing => putStrLn "Send failed"
          printLn answer

-- Now that the processes are setup, main can send a message to adder and adder can reply
-- The following primitives are available (but UNSAFE)
-- unsafeSend: Sends a message of any type
-- unsafeRecv: Receives a message of an expected type

-- unsafeSend : Channel -> (val : a) -> IO Bool
-- unsafeRecv : (expected : Type) -> Channel -> IO (Maybe expected)

-- Problems with channels
-- + type errors
-- + blocking
-- There is no guarantees about how processes coordinate with each other
-- For example: adder sends a Nat in reply to main but what if main is expecting to receive a string???
-- Unpredictable behavior and will likely crash at runtime
-- main might send a second message on the same channel and expect a reply (it can block forever...)
-- Although channels are unsafe, you can use them as a primitive for defining type-safe communication
-- We can write a Type for describing the coordination. Then write a run function that executes the description using the unsafe primitives

-- Problems to consider and capture in a Tyep:
-- + the type of the message that main sends is the same type that adder expects to receive
-- + main sends a message to adder but adder does not reply
-- + adder has stopped running when main sends a message
-- + deadlock main and adder

-- Need to think about what to send (Type) and when to send it (Protocol)
