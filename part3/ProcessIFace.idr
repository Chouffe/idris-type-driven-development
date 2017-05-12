module ProcessIFace

data MessagePID : (iface : reqType -> Type) -> Type where
  MkMessage : PID -> MessagePID iface

data ProcState = NoRequest
               | Sent
               | Complete

data Process : (iface : reqType -> Type) ->  -- Interface Process responds to
               Type ->                       -- Return type of Process
               (inState : ProcState) ->      -- Input State of Process
               (outState : ProcState) ->     -- Output State of Process
               Type where
  Request : MessagePID serviceIFace ->         -- serviceIFace has type (serviceReqType -> Type)
            (msg : serviceReqType) ->
            Process iface (serviceIFace msg) st st
  Respond : ((msg : serviceReqType) -> Process iface (iface msg) NoRequest NoRequest) ->
            Process iface (Maybe reqType) NoRequest Complete  -- The response type is calculated by iface msg
  Spawn : Process iface () NoRequest Complete ->
          Process iface (Maybe (MessagePID iface)) st st  -- the PID had type MessagePID iface
  Loop : Inf (Process iface a NoRequest Complete) ->
         Process iface a Sent Complete  -- Can only loop with a process that goes from NoRequest to Complete
  Action : IO a -> Process iface a st st
  Pure : a -> Process iface a st st
  (>>=) : Process a iface state1 state2 ->
          (a -> Process b iface state2 state3) ->
          Process b iface state2 state3


-- iface not responding to any request could be express this way
NoRecv : Void -> Type
NoRecv = const Void

-- Example
-- procMain : Process NoRecv () NoRequest NoRequest

-- A Service has an interface
Service : (iface : reqType -> Type) -> Type -> Type
Service iface a = Process iface a NoRequest Complete

-- A Client receives no Requests
Client : Type -> Type
Client a = Process NoRecv a NoRequest NoRequest

-- When designing data types, especially types that express strong guarantees like Process, its often a good idea to begin by trying to solve a specific problem before moving on to a more generic solution
