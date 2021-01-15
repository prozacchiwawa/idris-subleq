import SignedNat
import Memory

data SubleqMachine : Nat -> mem -> Type where
  SLQ : (n : Nat) -> (m : mem) -> SubleqMachine n m
