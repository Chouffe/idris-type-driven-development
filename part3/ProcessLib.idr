module ProcessLib

import System.Concurrency.Channels

%default total

export
data MessagePID : (iface : reqType -> Type) -> Type where

public export
ata ProcState = NoRequest | Sent | Complete

public export
data Process : (iface : reqType -> Type) ->
               Type ->
               (in_state : ProcState) ->
               (out_state : ProcState) ->
               Type where


public export
data Fuel

export partial
forever : Fuel

export
run : Fuel -> Process iface t in_state out_state -> IO (Maybe t)

public export
NoRecv : Void -> Type

public export
Service : (iface : reqType -> Type) -> Type -> Type

public export
Client : Type -> Type

export partial
runProc : Process iface () in_state out_state -> IO ()
