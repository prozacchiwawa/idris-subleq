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
  ( TypeOfReadMag (MemoryAddress (S pc)) mem
  ) => Nat
getStoreAddress s = typeOfReadMag (MAddr (S pc)) (getMemOf s)

public export
indirect :
  (at : Nat) ->
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadMag (MemoryAddress at) mem ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr at) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr at) (getMemOf s))) mem
  ) =>
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
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadMag (MemoryAddress pc) mem ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  ) =>
  ( TypeOfReadMag (MemoryAddress (S pc)) mem ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  ) =>
  ( SubSN
    (SignedNat
      (typeOfReadSign
        (MAddr (typeOfReadMag (MAddr (S pc)) (getMemOf s))) (getMemOf s)
      )
      (typeOfReadMag
        (MAddr (typeOfReadMag (MAddr (S pc)) (getMemOf s))) (getMemOf s)
      )
    )
    (SignedNat
      (typeOfReadSign
        (MAddr (typeOfReadMag (MAddr pc) (getMemOf s))) (getMemOf s)
      )
      (typeOfReadMag
        (MAddr (typeOfReadMag (MAddr pc) (getMemOf s))) (getMemOf s)
      )
    )
  ) =>
  (SignedNat
    (pfst (subSN (indirect (S pc) s) (indirect pc s)))
    (psnd (subSN (indirect (S pc) s) (indirect pc s)))
  )
getStoreValue s = signedNatFromSub (subSN (indirect (S pc) s) (indirect pc s))

public export
getNewPC :
  {pc : Nat} ->
  (s : SubleqMachine pc mem) ->
  ( TypeOfReadMag (MemoryAddress pc) mem ) =>
  ( TypeOfReadMag (MemoryAddress (S pc)) mem ) =>
  ( TypeOfReadMag (MemoryAddress (S (S pc))) mem ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  ) =>
  ( SubSN
     (SignedNat
       (typeOfReadSign
         (MAddr
           (typeOfReadMag (MAddr (S pc)) (getMemOf s))
         )
         (getMemOf s)
       )
       (typeOfReadMag
         (MAddr
           (typeOfReadMag (MAddr (S pc)) (getMemOf s))
         )
         (getMemOf s)
       )
     )
     (SignedNat
       (typeOfReadSign
         (MAddr
           (typeOfReadMag (MAddr pc) (getMemOf s))
         )
         (getMemOf s)
       )
       (typeOfReadMag
         (MAddr
           (typeOfReadMag (MAddr pc) (getMemOf s))
         )
         (getMemOf s)
       )
     )
  ) =>
  ( GreaterSN
     (SignedNat
       (pfst (subSN (indirect (S pc) s) (indirect pc s)))
       (psnd (subSN (indirect (S pc) s) (indirect pc s)))
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
  ( TypeOfReadMag (MemoryAddress pc) mem ) =>
  ( TypeOfReadMag (MemoryAddress (S pc)) mem ) =>
  ( TypeOfReadMag (MemoryAddress (S (S pc))) mem ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  ) =>
  ( SubSN
     (SignedNat
       (typeOfReadSign
         (MAddr
           (typeOfReadMag (MAddr (S pc)) (getMemOf s))
         )
         (getMemOf s)
       )
       (typeOfReadMag
         (MAddr
           (typeOfReadMag (MAddr (S pc)) (getMemOf s))
         )
         (getMemOf s)
       )
     )
     (SignedNat
       (typeOfReadSign
         (MAddr
           (typeOfReadMag (MAddr pc) (getMemOf s))
         )
         (getMemOf s)
       )
       (typeOfReadMag
         (MAddr
           (typeOfReadMag (MAddr pc) (getMemOf s))
         )
         (getMemOf s)
       )
     )
  ) =>
  ( SignSN
      (pfst (subSN (indirect (S pc) s) (indirect pc s)))
      (psnd (subSN (indirect (S pc) s) (indirect pc s)))
  ) =>
  ( MagnitudeSN
      (SignedNat
        (pfst (subSN (indirect (S pc) s) (indirect pc s)))
        (psnd (subSN (indirect (S pc) s) (indirect pc s)))
      )
  ) =>
  ( GreaterSN
     (SignedNat
       (pfst (subSN (indirect (S pc) s) (indirect pc s)))
       (psnd (subSN (indirect (S pc) s) (indirect pc s)))
     )
     (SignedNat False 0)
  ) =>
  (SubleqMachineAction
    (getNewPC s)
    (getStoreAddress s)
    (signToBool (signSN (getStoreValue s)))
    (magSN (getStoreValue s))
  )
actionToTake s =
  SMA
    (getNewPC s)
    (getStoreAddress s)
    (signToBool (signSN (getStoreValue s)))
    (magSN (getStoreValue s))

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
  ( TypeOfReadMag (MemoryAddress pc) mem ) =>
  ( TypeOfReadMag (MemoryAddress (S pc)) mem ) =>
  ( TypeOfReadMag (MemoryAddress (S (S pc))) mem ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr pc) (getMemOf s))) mem
  ) =>
  ( TypeOfReadSign (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  , TypeOfReadMag (MemoryAddress (typeOfReadMag (MAddr (S pc)) (getMemOf s))) mem
  ) =>
  ( SubSN
      (SignedNat
        (typeOfReadSign
          (MAddr
            (typeOfReadMag (MAddr (S pc)) (getMemOf s))
          )
          (getMemOf s)
        )
        (typeOfReadMag
          (MAddr
            (typeOfReadMag (MAddr (S pc)) (getMemOf s))
          )
          (getMemOf s)
        )
      )
      (SignedNat
        (typeOfReadSign
          (MAddr
            (typeOfReadMag (MAddr pc) (getMemOf s))
          )
          (getMemOf s)
        )
        (typeOfReadMag
          (MAddr
            (typeOfReadMag (MAddr pc) (getMemOf s))
          )
          (getMemOf s)
        )
      )
  ) =>
  ( SignSN
      (pfst (subSN (indirect (S pc) s) (indirect pc s)))
      (psnd (subSN (indirect (S pc) s) (indirect pc s)))
  ) =>
  ( MagnitudeSN
      (SignedNat
        (pfst (subSN (indirect (S pc) s) (indirect pc s)))
        (psnd (subSN (indirect (S pc) s) (indirect pc s)))
      )
  ) =>
  ( GreaterSN
     (SignedNat
       (pfst (subSN (indirect (S pc) s) (indirect pc s)))
       (psnd (subSN (indirect (S pc) s) (indirect pc s)))
     )
     (SignedNat False 0)
  ) =>
  ( ModTypeInterface mem ) =>
  SubleqMachine (getNewPC s) (memTypeAfterApplyingAction (getMemOf s) (actionToTake s))
step s = machineValueAfterApplyingAction s (actionToTake s)
