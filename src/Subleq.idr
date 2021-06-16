import SignedNat
import Memory

public export
data SubleqMachine : Nat -> Type -> Type where
  SLQ : (n : Nat) -> (m : mem) -> SubleqMachine n mem

public export
data SubleqMachineAction : Nat -> Nat -> Bool -> Nat -> Type where
  SMA : (pc : Nat) -> (w : Nat) -> (s : Bool) -> (v : Nat) -> SubleqMachineAction pc w s v

public export
getMemOf : SubleqMachine n m -> m
getMemOf (SLQ _ m) = m

public export
getPCOf : SubleqMachine n m -> Nat
getPCOf (SLQ pc _) = pc

public export
getStoreAddress :
  {pc : Nat} ->
  (s : SubleqMachine pc (Memory p q r)) ->
  Nat
getStoreAddress s = typeOfReadMag (MAddr (S pc)) (getMemOf s)

public export
indirect :
  (at : Nat) ->
  (s : SubleqMachine pc (Memory p q r)) ->
  (SignedNat
    (typeOfReadSign (MAddr (typeOfReadMag (MAddr at) (getMemOf s))) (getMemOf s))
    (typeOfReadMag (MAddr (typeOfReadMag (MAddr at) (getMemOf s))) (getMemOf s))
  )
indirect at s =
  createSignedNat
    (typeOfReadSign (MAddr (typeOfReadMag (MAddr at) (getMemOf s))) (getMemOf s))
    (typeOfReadMag (MAddr (typeOfReadMag (MAddr at) (getMemOf s))) (getMemOf s))

public export
getStoreValue :
  {pc : Nat} ->
  (s : SubleqMachine pc (Memory p q r)) ->
  (SignedNat
    (signOfSubtraction (indirect (S pc) s) (indirect pc s))
    (magOfSubtraction (indirect (S pc) s) (indirect pc s))
  )
getStoreValue s = subSN (indirect (S pc) s) (indirect pc s)

public export
getNewPC :
  {pc : Nat} ->
  (s : SubleqMachine pc (Memory p q r)) ->
  Nat
getNewPC s =
  if gtrSN (getStoreValue s) (Pos 0) then
    (S (S (S (getPCOf s))))
  else
    typeOfReadMag (MAddr (S (S pc))) (getMemOf s)

public export
actionToTake :
  {pc : Nat} ->
  (s : SubleqMachine pc (Memory p q r)) ->
  (SubleqMachineAction
    (getNewPC s)
    (getStoreAddress s)
    (signOfSN (getStoreValue s))
    (magOfSN (getStoreValue s))
  )
actionToTake s =
  SMA
    (getNewPC s)
    (getStoreAddress s)
    (signOfSN (getStoreValue s))
    (magOfSN (getStoreValue s))

public export
memTypeAfterApplyingAction :
  (m : Memory p q r) ->
  SubleqMachineAction pc w s v ->
  Type
memTypeAfterApplyingAction m (SMA _ w s v) =
  typeOfModRam (modTypeInterface (Just w) m (createSignedNat s v))

public export
memValueAfterApplyingAction :
  (m : Memory p q r) ->
  (s : SubleqMachineAction pc w sign mag) ->
  memTypeAfterApplyingAction m s
memValueAfterApplyingAction m (SMA _ w sign mag) =
  modifyRam (MAddr w) m (createSignedNat sign mag)

public export
machineValueAfterApplyingAction :
  {newpc : Nat} ->
  (sm : SubleqMachine pc (Memory p q r)) ->
  (s : SubleqMachineAction newpc w sign mag) ->
  SubleqMachine newpc (memTypeAfterApplyingAction (getMemOf sm) s)
machineValueAfterApplyingAction sm s =
  SLQ newpc (memValueAfterApplyingAction (getMemOf sm) s)

readMag : MemoryAddress n -> Memory p q r -> Nat
readMag (MAddr Z) (MEnd _ q) = q
readMag (MAddr (S i)) (MEnd _ _) = 0
readMag (MAddr Z) (MWord _ q _) = q
readMag (MAddr (S i)) (MWord _ _ r) with (r)
  readMag (MAddr (S i)) (MWord _ _ r) | (MEnd e f) =
    readMag (MAddr i) (MEnd e f)
  readMag (MAddr (S i)) (MWord _ _ r) | (MWord e f g) =
    readMag (MAddr i) (MWord e f g)

public export
step :
  {pc : Nat} ->
  {p : Bool} ->
  {q : Nat} ->
  {r : rest} ->
  (s : SubleqMachine pc (Memory p q r)) ->
  SubleqMachine (getNewPC s) (memTypeAfterApplyingAction (getMemOf s) (actionToTake s))
step s = machineValueAfterApplyingAction s (actionToTake s)
