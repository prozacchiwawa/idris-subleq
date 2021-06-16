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
typeOfReadSign : MemoryAddress n -> Memory s v rest -> Bool
typeOfReadSign (MAddr Z) (MEnd s _) = s
typeOfReadSign (MAddr (S i)) (MEnd _ _) = False
typeOfReadSign (MAddr Z) (MWord s _ _) = s
typeOfReadSign (MAddr (S i)) (MWord _ _ r) = typeOfReadSign (MAddr i) r

public export
typeOfReadMag : MemoryAddress n -> Memory s v rest -> Nat
typeOfReadMag (MAddr Z) (MEnd _ v) = v
typeOfReadMag (MAddr (S i)) (MEnd _ v) = 0
typeOfReadMag (MAddr Z) (MWord _ v _) = v
typeOfReadMag (MAddr (S i)) (MWord _ _ r) = typeOfReadMag (MAddr i) r

public export
readRam :
  (a : MemoryAddress n) ->
  (m : Memory s v r) ->
  (SignedNat (typeOfReadSign a m) (typeOfReadMag a m))
readRam maddr mem =
  createSignedNat (typeOfReadSign maddr mem) (typeOfReadMag maddr mem)

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
typeOfModRam_ : Maybe BrokenMemory -> Type
typeOfModRam_ Nothing = Unit
typeOfModRam_ (Just b) = typeOfBroken b

public export
typeOfModRam : BrokenMemory -> Type
typeOfModRam b = typeOfBroken b

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
  modTypeInterface_ : Maybe Nat -> mem -> SignedNat x v -> Maybe BrokenMemory

public export
implementation ModTypeInterface (Memory s t rest) where
  modTypeInterface_ Nothing (MEnd s v) _ = Just (broken s v Nothing)
  modTypeInterface_ Nothing (MWord s v r) _ =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface_ Nothing r (Pos 0)
    in
    Just (broken s v t)
  modTypeInterface_ (Just Z) (MEnd s v) (Pos e) =
    Just (broken s v Nothing)
  modTypeInterface_ (Just Z) (MEnd s v) (Neg e) =
    Just (broken s v Nothing)
  modTypeInterface_ (Just Z) (MWord s v r) (Pos e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface_ Nothing r (Pos e)
    in
    Just (broken False e t)
  modTypeInterface_ (Just Z) (MWord s v r) (Neg e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface_ Nothing r (Pos e)
    in
    Just (broken True e t)
  modTypeInterface_ (Just (S n)) (MEnd s v) a =
    Just (broken s v Nothing)
  modTypeInterface_ (Just (S n)) (MWord s v r) (Pos e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface_ (Just n) r (Pos e)
    in
    Just (broken s v t)
  modTypeInterface_ (Just (S n)) (MWord s v r) (Neg e) =
    let
      t : Maybe BrokenMemory
      t = modTypeInterface_ (Just n) r (Neg e)
    in
    Just (broken s v t)

public export
implementation ModTypeInterface Unit where
  modTypeInterface_ _ _ _ = Nothing

public export
modTypeInterface : Maybe Nat -> Memory s v rest -> SignedNat p q -> BrokenMemory
modTypeInterface Nothing (MEnd s v) _ = broken s v Nothing
modTypeInterface Nothing (MWord s v r) x = broken s v (Just (modTypeInterface Nothing r x))
modTypeInterface (Just Z) (MEnd s v) (Pos m) =
  broken False m Nothing
modTypeInterface (Just Z) (MEnd s v) (Neg m) =
  broken True m Nothing
modTypeInterface (Just Z) (MWord s v r) (Pos m) =
  broken False m (Just (modTypeInterface Nothing r (Pos m)))
modTypeInterface (Just Z) (MWord s v r) (Neg m) =
  broken True m (Just (modTypeInterface Nothing r (Neg m)))
modTypeInterface (Just (S i)) (MEnd s v) _ =
  broken s v Nothing
modTypeInterface (Just (S i)) (MWord s v r) x =
  broken s v (Just (modTypeInterface (Just i) r x))

public export
implementation (ExtractSign rest, ExtractMag rest, RestOf rest) => RestOf (Memory s v rest) where
  restOf (MEnd _ _) = Nothing
  restOf (MWord s v r) = Just (modTypeInterface Nothing r (Pos 0))

public export
implementation RestOf any where
  restOf _ = Nothing

public export
typeOfModRamNothingIsUnit : typeOfModRam_ Nothing = Unit
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
modRamValue_ : (b : Maybe BrokenMemory) -> (typeOfModRam_ b)

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
convertTail : (b : BrokenMemory) -> typeOfBroken b = Memory (getSignFromBroken b) (getMagFromBroken b) (getNextTypeFromBroken b)
convertTail b@(Broken s v mt prf x@(Just rr)) =
  rewrite sym (mwordSatisfiesTypeOfBrokenR b) in
  Refl
convertTail b@(Broken s v mt prf Nothing) =
  rewrite prf Unit in
  Refl

makeMWord : (b : BrokenMemory) -> Memory (getSignFromBroken b) (getMagFromBroken b) (getNextTypeFromBroken b)
makeMWord b =
  rewrite sym (convertTail b) in
  unbrokenNext b

unbrokenNext b@(Broken s v mt prf Nothing) =
  rewrite prf Unit in
  MEnd s v
unbrokenNext b@(Broken s v mt prf (Just r)) =
  let
    next = unbrokenNext r
  in
  rewrite prf (typeOfBroken r) in
  rewrite mwordSatisfiesTypeOfBrokenR r in
  MWord s v (makeMWord r)

modRamValue_ Nothing = ()
modRamValue_ (Just b) = unbrokenNext b

modRamValue : (b : BrokenMemory) -> typeOfBroken b
modRamValue b = unbrokenNext b

public export
modifyRam :
  {n : Nat} ->
  MemoryAddress n ->
  (m : Memory s v rest) ->
  (a : SignedNat q x) ->
  typeOfModRam (modTypeInterface (Just n) m a)
modifyRam ma m a = modRamValue (modTypeInterface (Just n) m a)
