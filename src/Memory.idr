module Memory

import SignedNat

public export
data Memory : Bool -> Nat -> mem -> Type where
  MWord : (s : Bool) -> (v : Nat) -> Memory t w rest -> Memory s v (Memory t w rest)
  MEnd : (s : Bool) -> (v : Nat) -> Memory s v Unit

public export
data MemoryAddress : Nat -> Type where
  MAddr : (n:Nat) -> MemoryAddress n

public export
interface TypeOfReadSign maddr mem where
  typeOfReadSign : maddr -> mem -> Bool

public export
implementation TypeOfReadSign maddr Unit where
  typeOfReadSign _ _ = False

public export
implementation TypeOfReadSign (MemoryAddress Z) (Memory s v rest) where
  typeOfReadSign _ (MEnd False _) = False
  typeOfReadSign _ (MEnd True _) = True
  typeOfReadSign _ (MWord False _ _) = False
  typeOfReadSign _ (MWord True _ _) = True

public export
implementation TypeOfReadSign (MemoryAddress (S n)) (Memory s v Unit) where
  typeOfReadSign _ _ = False

public export
implementation (TypeOfReadSign (MemoryAddress n) rest) => TypeOfReadSign (MemoryAddress (S n)) (Memory s v rest) where
  typeOfReadSign (MAddr (S n)) (MEnd _ _) = False
  typeOfReadSign (MAddr (S n)) (MWord _ _ rest) = typeOfReadSign (MAddr n) rest

public export
interface TypeOfReadMag maddr mem where
  typeOfReadMag : maddr -> mem -> Nat

public export
implementation TypeOfReadMag maddr Unit where
  typeOfReadMag _ _ = 0

public export
implementation TypeOfReadMag (MemoryAddress Z) (Memory s v rest) where
  typeOfReadMag _ (MEnd False mag) = mag
  typeOfReadMag _ (MEnd True mag) = mag
  typeOfReadMag _ (MWord False mag _) = mag
  typeOfReadMag _ (MWord True mag _) = mag

public export
implementation (TypeOfReadMag (MemoryAddress n) rest) => TypeOfReadMag (MemoryAddress (S n)) (Memory s v rest) where
  typeOfReadMag (MAddr (S n)) (MEnd _ _) = 0
  typeOfReadMag (MAddr (S n)) (MWord _ _ rest) = typeOfReadMag (MAddr n) rest

public export
readRam : (TypeOfReadSign maddr mem, TypeOfReadMag maddr mem) => (a : maddr) -> (m : mem) -> (SignedNat (typeOfReadSign a m) (typeOfReadMag a m))
readRam maddr mem = createSignedNat (typeOfReadSign maddr mem) (typeOfReadMag maddr mem)

public export
proofWord1IsPos4 : readRam (MAddr 1) (MWord False 3 (MWord False 4 (MEnd False 5))) = Pos 4
proofWord1IsPos4 = Refl

public export
interface ExtractSign mem where
  extractSign : mem -> Bool

public export
implementation ExtractSign (Memory s v rest) where
  extractSign (MEnd s _) = s
  extractSign (MWord s _ _) = s

public export
implementation ExtractSign any where
  extractSign _ = False

public export
interface ExtractMag mem where
  extractMag : mem -> Nat

public export
implementation ExtractMag (Memory s v rest) where
  extractMag (MEnd _ v) = v
  extractMag (MWord _ v _) = v

public export
implementation ExtractMag any where
  extractMag _ = 0

public export
intoMemory : (a : Bool) -> (b : Nat) -> (Type -> Type)
intoMemory a b = Memory a b

public export
proofIntoMemoryAddsMemory : (a : Bool) -> (b : Nat) -> (t : Type) -> intoMemory a b t = Memory a b t
proofIntoMemoryAddsMemory a b t = Refl

public export
proofOfIntoMemory : (a : Bool) -> (b : Nat) -> (f : Type -> Type) -> (f = intoMemory a b) -> (t : Type) -> f t = Memory a b t
proofOfIntoMemory a b f prf t =
 rewrite prf in
 Refl

public export
data BrokenMemory : Type where
  Broken : (s : Bool) -> (v : Nat) -> (b : Type -> Type) -> (prf : ((t : Type) -> b t = Memory s v t)) -> Maybe BrokenMemory -> BrokenMemory

public export
broken : Bool -> Nat -> Maybe BrokenMemory -> BrokenMemory

public export
typeOfBroken : (b : BrokenMemory) -> Type
typeOfBroken (Broken s v makeNext prf follow) =
  case follow of
    Just r => makeNext (typeOfBroken r)
    Nothing => makeNext Unit

public export
typeOfModRam : Maybe BrokenMemory -> Type
typeOfModRam Nothing = Unit
typeOfModRam (Just b) = typeOfBroken b

public export
intoMemoryBNIsMemoryBN : (b : Bool) -> (n : Nat) -> intoMemory b n = Memory b n
intoMemoryBNIsMemoryBN b n = Refl

broken b n r =
  let
    imp : (t : Type) -> (intoMemory b n) t = Memory b n t
    imp = proofOfIntoMemory b n (intoMemory b n) Refl
  in
  Broken b n (intoMemory b n) imp r

public export
interface RestOf mem where
  restOf : mem -> Maybe BrokenMemory

public export
interface ModTypeInterface mem where
  modTypeInterface : Maybe Nat -> mem -> SignedNat x v -> Maybe BrokenMemory

public export
implementation ModTypeInterface (Memory s t rest) where
  modTypeInterface Nothing (MEnd s v) _ = Just (broken s v Nothing)
  modTypeInterface Nothing (MWord s v r) _ =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface Nothing r (Pos 0)
    in
    Just (broken s v t)
  modTypeInterface (Just Z) (MEnd s v) (Pos e) =
    Just (broken s v Nothing)
  modTypeInterface (Just Z) (MEnd s v) (Neg e) =
    Just (broken s v Nothing)
  modTypeInterface (Just Z) (MWord s v r) (Pos e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface Nothing r (Pos e)
    in
    Just (broken False e t)
  modTypeInterface (Just Z) (MWord s v r) (Neg e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface Nothing r (Pos e)
    in
    Just (broken True e t)
  modTypeInterface (Just (S n)) (MEnd s v) a =
    Just (broken s v Nothing)
  modTypeInterface (Just (S n)) (MWord s v r) (Pos e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface (Just n) r (Pos e)
    in
    Just (broken s v t)
  modTypeInterface (Just (S n)) (MWord s v r) (Neg e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface (Just n) r (Neg e)
    in
    Just (broken s v t)

public export
implementation ModTypeInterface Unit where
  modTypeInterface _ _ _ = Nothing

public export
implementation (ExtractSign rest, ExtractMag rest, RestOf rest) => RestOf (Memory s v rest) where
  restOf (MEnd _ _) = Nothing
  restOf (MWord s v r) = modTypeInterface Nothing r (Pos 0)

public export
implementation RestOf any where
  restOf _ = Nothing

public export
typeOfModRamNothingIsUnit : typeOfModRam Nothing = Unit
typeOfModRamNothingIsUnit = Refl

public export
typeOfModRamJustRIsTypeOfBrokenR : (a : Bool) -> (b : Nat) -> (r : BrokenMemory) -> typeOfBroken (broken a b (Just r)) = Memory a b (typeOfBroken r)
typeOfModRamJustRIsTypeOfBrokenR a b r = Refl

public export
getSignFromBroken : BrokenMemory -> Bool
getSignFromBroken (Broken b _ _ _ _) = b

public export
getMagFromBroken : BrokenMemory -> Nat
getMagFromBroken (Broken _ m _ _ _) = m

public export
getNextTypeFromBroken : BrokenMemory -> Type
getNextTypeFromBroken (Broken _ _ f _ Nothing) = Unit
getNextTypeFromBroken (Broken _ _ f _ (Just r)) = typeOfBroken r

public export
modRamValue : (b : Maybe BrokenMemory) -> (typeOfModRam b)

public export
unbrokenNext : (b : BrokenMemory) -> typeOfBroken b

public export
mwordSatisfiesTypeOfBrokenR : (b : BrokenMemory) -> typeOfBroken b = Memory (getSignFromBroken b) (getMagFromBroken b) (getNextTypeFromBroken b)
mwordSatisfiesTypeOfBrokenR b@(Broken s v mt prf (Just r)) =
  rewrite sym (prf (typeOfBroken r)) in
  Refl
mwordSatisfiesTypeOfBrokenR b@(Broken s v mt prf Nothing) =
  rewrite prf Unit in
  Refl

public export
convertTail : (b : BrokenMemory) -> typeOfBroken b -> Memory (getSignFromBroken b) (getMagFromBroken b) (getNextTypeFromBroken b)
convertTail b@(Broken s v mt prf x@(Just rr)) r =
  rewrite sym (mwordSatisfiesTypeOfBrokenR b) in
  let
    ctail = convertTail rr (unbrokenNext rr)

    res = MWord s v ctail
  in
  rewrite prf (typeOfBroken rr) in
  rewrite mwordSatisfiesTypeOfBrokenR rr in
  res

convertTail b@(Broken s v mt prf Nothing) r =
  rewrite sym (mwordSatisfiesTypeOfBrokenR b) in
  rewrite prf Unit in
  let
    res = MEnd s v
  in
  res

unbrokenNext b@(Broken s v mt prf Nothing) =
  rewrite prf Unit in
  MEnd s v
unbrokenNext b@(Broken s v mt prf (Just r)) =
  let
    next = unbrokenNext r
  in
  rewrite prf (typeOfBroken r) in
  rewrite mwordSatisfiesTypeOfBrokenR r in
  let
    res = MWord s v (convertTail r next)
  in
  res

modRamValue Nothing = ()
modRamValue (Just b) = unbrokenNext b

public export
modifyRam : ModTypeInterface mem => {n : Nat} -> MemoryAddress n -> (m : mem) -> (a : SignedNat q x) -> typeOfModRam (modTypeInterface (Just n) m a)
modifyRam ma m a = modRamValue (modTypeInterface (Just n) m a)
