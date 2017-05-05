module Vending

VendState : Type
VendState = (Nat, Nat)

data Input = COIN
           | VEND
           | CHANGE
           | REFILL Nat

data MachineCmd : Type -> VendState -> VendState -> Type where
  InsertCoin : MachineCmd () (pounds, chocs)     (S pounds, chocs)
  Vend :       MachineCmd () (S pounds, S chocs) (pounds, chocs)
  GetCoins :   MachineCmd () (pounds, chocs)     (Z, chocs)
  Refill :     (bars : Nat) -> MachineCmd () (Z, chocs) (Z, bars + chocs)
  Display :    String -> MachineCmd () state state
  GetInput :   MachineCmd (Maybe Input) state state

  Pure : a -> MachineCmd a state state
  (>>=) : MachineCmd a state1 state2 -> (a -> MachineCmd b state2 state3) -> MachineCmd b state1 state3

data MachineIO : VendState -> Type where
  Do : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1

namespace MachineDo
  -- Supports Do notation for infinite sequences of machine state transitions
  (>>=) : MachineCmd a state1 state2 -> (a -> Inf (MachineIO state2)) -> MachineIO state1
  (>>=) = Do

mutual
  vend : MachineIO (pounds, chocs)
  vend {pounds = Z} = do Display "Insert a coin"
                         machineLoop
  vend {chocs = Z} = do Display "Out of stock"
                        machineLoop
  vend {pounds = S k} {chocs = S l} = do Vend
                                         Display "Enjoy!"
                                         machineLoop

  refill : (n : Nat) -> MachineIO (pounds, chocs)
  refill {pounds = Z} n = do Refill n
                             machineLoop

  refill {pounds = (S k)} n = do Display "Can't refill: Coins in the machine"
                                 machineLoop

  machineLoop : MachineIO (pounds, chocs)
  machineLoop = do
    Just x <- GetInput
       | Nothing => do Display "Invalid input"
                       machineLoop
    case x of
         COIN => do InsertCoin
                    machineLoop
         VEND => vend
         CHANGE => do GetCoins
                      Display "Change returned"
                      machineLoop
         (REFILL k) => refill k
