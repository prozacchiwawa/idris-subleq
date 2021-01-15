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
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadSign (MemoryAddress (S pc)) mem
  , TypeOfReadMag (MemoryAddress (S pc)) mem
  ) => Nat
getStoreAddress s = typeOfReadMag (MAddr (S pc)) (getMemOf s)

public export
pfst : (a,b) -> a
pfst (a,b) = a

public export
psnd : (a,b) -> b
psnd (a,b) = b

public export
getStoreValue :
  {pc : Nat} ->
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadSign (MemoryAddress pc) mem
  , TypeOfReadMag (MemoryAddress pc) mem
  , TypeOfReadSign (MemoryAddress (S pc)) mem
  , TypeOfReadMag (MemoryAddress (S pc)) mem
  , TypeOfReadSign (MemoryAddress (S (S pc))) mem
  , TypeOfReadMag (MemoryAddress (S (S pc))) mem
  ) =>
  ( SubSN
      (SignedNat
        (typeOfReadSign (MAddr (S pc)) (getMemOf s))
        (typeOfReadMag (MAddr (S pc)) (getMemOf s))
      )
      (SignedNat
        (typeOfReadSign (MAddr pc) (getMemOf s))
        (typeOfReadMag (MAddr pc) (getMemOf s))
      )
  ) =>
  (SignedNat
    (pfst (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s))))
    (psnd (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s))))
  )
getStoreValue s =
  createSignedNat
    (pfst (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s))))
    (psnd (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s))))

public export
getNewPC : {pc : Nat} ->
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadSign (MemoryAddress pc) mem
  , TypeOfReadMag (MemoryAddress pc) mem
  , TypeOfReadSign (MemoryAddress (S pc)) mem
  , TypeOfReadMag (MemoryAddress (S pc)) mem
  , TypeOfReadSign (MemoryAddress (S (S pc))) mem
  , TypeOfReadMag (MemoryAddress (S (S pc))) mem
  ) =>
  ( SubSN
      (SignedNat
        (typeOfReadSign (MAddr (S pc)) (getMemOf s))
        (typeOfReadMag (MAddr (S pc)) (getMemOf s))
      )
      (SignedNat
        (typeOfReadSign (MAddr pc) (getMemOf s))
        (typeOfReadMag (MAddr pc) (getMemOf s))
      )
  ) =>
  ( GreaterSN
     (SignedNat
       (pfst
         (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s)))
       )
       (psnd
         (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s)))
       )
     )
     (SignedNat False 0)
  ) => Nat
getNewPC s =
  if gtrSN (getStoreValue s) (Pos 0) then
    (S (S (S (getPCOf s))))
  else
    typeOfReadMag (MAddr (S (S pc))) (getMemOf s)

public export
actionToTake :
  {pc : Nat} ->
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadSign (MemoryAddress pc) mem
  , TypeOfReadMag (MemoryAddress pc) mem
  , TypeOfReadSign (MemoryAddress (S pc)) mem
  , TypeOfReadMag (MemoryAddress (S pc)) mem
  , TypeOfReadSign (MemoryAddress (S (S pc))) mem
  , TypeOfReadMag (MemoryAddress (S (S pc))) mem
  ) =>
  ( SubSN
    (SignedNat
      (typeOfReadSign (MAddr (S pc)) (getMemOf s))
      (typeOfReadMag (MAddr (S pc)) (getMemOf s))
    )
    (SignedNat
      (typeOfReadSign (MAddr pc) (getMemOf s))
      (typeOfReadMag (MAddr pc) (getMemOf s))
    )
  ) =>
  ( GreaterSN
     (SignedNat
       (pfst
         (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s)))
       )
       (psnd
         (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s)))
       )
     )
     (SignedNat False 0)
  ) =>
  ( SignSN
      (pfst
        (subSN
          (readRam (MAddr (S pc)) (getMemOf s))
          (readRam (MAddr pc) (getMemOf s))
        )
      )
      (psnd
        (subSN
          (readRam (MAddr (S pc)) (getMemOf s))
          (readRam (MAddr pc) (getMemOf s))
        )
      )
  , MagnitudeSN
      (SignedNat
        (pfst
          (subSN
            (readRam (MAddr (S pc)) (getMemOf s))
            (readRam (MAddr pc) (getMemOf s))
          )
        )
        (psnd
          (subSN
            (readRam (MAddr (S pc)) (getMemOf s))
            (readRam (MAddr pc) (getMemOf s)))
          )
        )
  ) =>
  (SubleqMachineAction
    (getNewPC s)
    (getStoreAddress s)
    (signToBool (signSN (getStoreValue s)))
   (magSN (getStoreValue s))
  )
actionToTake s = SMA (getNewPC s) (getStoreAddress s) (signToBool (signSN (getStoreValue s))) (magSN (getStoreValue s))

public export
memTypeAfterApplyingAction : ModTypeInterface mem => (m : mem) -> SubleqMachineAction pc w s v -> Type
memTypeAfterApplyingAction m (SMA _ w s v) = typeOfModRam (modTypeInterface (Just w) m (createSignedNat s v))

public export
memValueAfterApplyingAction : ModTypeInterface mem => (m : mem) -> (s : SubleqMachineAction pc w sign mag) -> memTypeAfterApplyingAction m s
memValueAfterApplyingAction m (SMA _ w sign mag) = modifyRam (MAddr w) m (createSignedNat sign mag)

public export
machineValueAfterApplyingAction : ModTypeInterface mem => {newpc : Nat} -> (sm : SubleqMachine pc mem) -> (s : SubleqMachineAction newpc w sign mag) -> SubleqMachine newpc (memTypeAfterApplyingAction (getMemOf sm) s)
machineValueAfterApplyingAction sm s =
  SLQ newpc (memValueAfterApplyingAction (getMemOf sm) s)

public export
step :
  {pc : Nat} ->
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadSign (MemoryAddress pc) mem
  , TypeOfReadMag (MemoryAddress pc) mem
  , TypeOfReadSign (MemoryAddress (S pc)) mem
  , TypeOfReadMag (MemoryAddress (S pc)) mem
  , TypeOfReadSign (MemoryAddress (S (S pc))) mem
  , TypeOfReadMag (MemoryAddress (S (S pc))) mem
  ) =>
  ( SubSN
    (SignedNat
      (typeOfReadSign (MAddr (S pc)) (getMemOf s))
      (typeOfReadMag (MAddr (S pc)) (getMemOf s))
    )
    (SignedNat
      (typeOfReadSign (MAddr pc) (getMemOf s))
      (typeOfReadMag (MAddr pc) (getMemOf s))
    )
  ) =>
  ( GreaterSN
      (SignedNat
        (typeOfReadSign (MAddr (S pc)) (getMemOf s))
        (typeOfReadMag (MAddr (S pc)) (getMemOf s))
      )
      (SignedNat False 0)
  ) =>
  ( SignSN
      (pfst
        (subSN
          (readRam (MAddr (S pc)) (getMemOf s))
          (readRam (MAddr pc) (getMemOf s))
        )
      )
      (psnd
        (subSN
          (readRam (MAddr (S pc)) (getMemOf s))
          (readRam (MAddr pc) (getMemOf s))
        )
      )
  , MagnitudeSN
      (SignedNat
        (pfst
          (subSN
            (readRam (MAddr (S pc)) (getMemOf s))
            (readRam (MAddr pc) (getMemOf s))
          )
        )
        (psnd
          (subSN
            (readRam (MAddr (S pc)) (getMemOf s))
            (readRam (MAddr pc) (getMemOf s)))
          )
        )
  ) =>
  ( GreaterSN
     (SignedNat
       (pfst
         (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s)))
       )
       (psnd
         (subSN (readRam (MAddr (S pc)) (getMemOf s)) (readRam (MAddr pc) (getMemOf s)))
       )
     )
     (SignedNat False 0)
  ) =>
  ( ModTypeInterface mem ) =>
  SubleqMachine (getNewPC s) (memTypeAfterApplyingAction (getMemOf s) (actionToTake s))
step s = machineValueAfterApplyingAction s (actionToTake s)
