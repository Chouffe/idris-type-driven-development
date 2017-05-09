module VendingCmd

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data CoinResult = Inserted | Rejected

data MachineCmd : (ty : Type) -> VendState -> (ty -> VendState) -> Type where
  InsertCoin : MachineCmd CoinResult (pounds, chocs) (\res => case res of
                                                           Inserted => (S pounds, chocs)
                                                           Ejected => (pounds, chocs))
  Vend :       MachineCmd () (S pounds, S chocs) (const (pounds, chocs))
  GetCoins :   MachineCmd () (pounds, chocs)     (const (Z, chocs))
  Refill :     (bars : Nat) -> MachineCmd () (Z, chocs) (const (Z, bars + chocs))
  Display :    String -> MachineCmd () state (const state)
  GetInput :   MachineCmd (Maybe Input) state (const state)

  Pure : (res : a) -> MachineCmd a (stateFn res) stateFn
  (>>=) : MachineCmd a state1 state2Fn -> ((res : a) -> MachineCmd b (state2Fn res) state3Fn) -> MachineCmd b state1 state3Fn

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2Fn -> ((res : a) -> Inf (MachineIO (state2Fn res))) -> MachineIO state1

namespace MachineDo
  -- Supports Do notation for infinite sequences of machine state transitions
  (>>=) : MachineCmd a state1 state2Fn -> ((res : a) -> Inf (MachineIO (state2Fn res))) -> MachineIO state1
  (>>=) = Do



mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = Z} = do Display "Out of pounds"
                         machineLoop
  vend {chocs = Z} = do Display "Out of chocs"
                        machineLoop
  vend {pounds = S l} {chocs = S k} = do Vend
                                         machineLoop

  refill : (k : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} k = do Refill k
                             machineLoop
  refill {pounds = S l} _ = do Display "Not empty"
                               machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop = do
    Just x <- GetInput | Nothing => do Display "Invalid input"
                                       machineLoop
    case x of
         COIN => do Inserted <- InsertCoin | Rejected => machineLoop
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change returned"
                      machineLoop
         (REFILL k) => refill k
