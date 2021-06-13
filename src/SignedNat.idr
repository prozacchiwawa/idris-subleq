module SignedNat

public export
data SignedNat : Bool -> Nat -> Type where
  Neg : (n:Nat) -> SignedNat True n
  Pos : (n:Nat) -> SignedNat False n

public export
interface NextMag s n where
  nextMag : SignedNat s n -> SignedNat s (S n)

public export
interface GenerateSN s n where
  generateSN : SignedNat s n

public export
implementation GenerateSN False Z where
  generateSN = Pos Z

public export
implementation (GenerateSN s n, NextMag s n) => GenerateSN s (S n) where
  generateSN =
    nextMag oneLess
    where
      oneLess : SignedNat s n
      oneLess = generateSN

public export
data SNMag : Nat -> Type where
  SNM : (n:Nat) -> SNMag n

public export
extToNat : {n : Nat} -> SNMag n -> Nat
extToNat _ = n

public export
interface MagnitudeSN sn where
  magSN : sn -> Nat

public export
interface MagnitudeExtract s n where
  magExt : Maybe (SignedNat s n) -> SNMag n

public export
implementation MagnitudeSN (SignedNat True Z) where
  magSN _ = Z

public export
implementation (MagnitudeSN (SignedNat True n)) => MagnitudeSN (SignedNat True (S n)) where
  magSN (Neg (S n)) = S (magSN (Neg n))

public export
implementation MagnitudeSN (SignedNat False Z) where
  magSN _ = Z

public export
implementation (MagnitudeSN (SignedNat False n)) => MagnitudeSN (SignedNat False (S n)) where
  magSN (Pos (S n)) = S (magSN (Pos n))

public export
data SNSign : Bool -> Type where
  SNS : (b : Bool) -> SNSign b

public export
interface SignSN s v where
  signSN : SignedNat s v -> SNSign s

public export
implementation SignSN False v where
  signSN _ = SNS False

public export
implementation SignSN True v where
  signSN _ = SNS True

public export
signToBool : {b : Bool} -> SNSign b -> Bool
signToBool _ = b

public export
interface GreaterSN sna snb where
  gtrSN_ : sna -> snb -> Bool

public export
implementation GreaterSN (SignedNat False Z) (SignedNat True Z) where
  gtrSN_ _ _ = False

public export
implementation GreaterSN (SignedNat False Z) (SignedNat True (S _)) where
  gtrSN_ _ _ = False

public export
implementation GreaterSN (SignedNat False (S _)) (SignedNat True Z) where
  gtrSN_ _ _ = True

public export
implementation GreaterSN (SignedNat False (S _)) (SignedNat True (S _)) where
  gtrSN_ _ _ = True

public export
implementation GreaterSN (SignedNat True _) (SignedNat False _) where
  gtrSN_ _ _ = False

public export
implementation GreaterSN (SignedNat False Z) (SignedNat False Z) where
  gtrSN_ _ _ = False

public export
implementation GreaterSN (SignedNat False Z) (SignedNat False (S b)) where
  gtrSN_ _ _ = False

public export
implementation GreaterSN (SignedNat False (S a)) (SignedNat False Z) where
  gtrSN_ _ _ = True

public export
implementation (GreaterSN (SignedNat False a) (SignedNat False b)) => GreaterSN (SignedNat False (S a)) (SignedNat False (S b)) where
  gtrSN_ (Pos (S a)) (Pos (S b)) = gtrSN_ (Pos a) (Pos b)

public export
implementation GreaterSN (SignedNat True _) (SignedNat True Z) where
  gtrSN_ _ _ = False

public export
implementation GreaterSN (SignedNat True Z) (SignedNat True (S a)) where
  gtrSN_ _ _ = True

public export
implementation (GreaterSN (SignedNat True a) (SignedNat True b)) => GreaterSN (SignedNat True (S a)) (SignedNat True (S b)) where
  gtrSN_ (Neg (S a)) (Neg (S b)) = gtrSN_ (Neg a) (Neg b)

public export
gtrSN : {sn1b : Bool} -> {sn1n : Nat} -> {sn2b : Bool} -> {sn2n : Nat} -> SignedNat sn1b sn1n -> SignedNat sn2b sn2n -> Bool
gtrSN s1 s2 with (sn1b, sn2b)
  gtrSN s1 s2 | (False, False) with (sn1n, sn2n)
    gtrSN s1 s2 | (False, False) | (Z, Z) = gtrSN_ (Pos Z) (Pos Z)
    gtrSN s1 s2 | (False, False) | (Z, (S n)) = gtrSN_ (Pos Z) (Pos (S n))
    gtrSN s1 s2 | (False, False) | ((S m), Z) = gtrSN_ (Pos (S m)) (Pos Z)
    gtrSN s1 s2 | (False, False) | ((S m), (S n)) = gtrSN (Pos (S m)) (Pos (S n))
  gtrSN s1 s2 | (False, True) with (sn1n, sn2n)
    gtrSN s1 s2 | (False, True) | (Z, Z) = gtrSN_ (Pos Z) (Neg Z)
    gtrSN s1 s2 | (False, True) | (Z, (S n)) = gtrSN_ (Pos Z) (Neg (S n))
    gtrSN s1 s2 | (False, True) | ((S m), Z) = gtrSN_ (Pos (S m)) (Neg Z)
    gtrSN s1 s2 | (False, True) | ((S m), (S n)) = gtrSN_ (Pos (S m)) (Neg (S n))
  gtrSN s1 s2 | (True, False) with (sn1n, sn2n)
    gtrSN s1 s2 | (True, False) | (Z, Z) = gtrSN_ (Neg Z) (Pos Z)
    gtrSN s1 s2 | (True, False) | (Z, (S n)) = gtrSN_ (Neg Z) (Pos (S n))
    gtrSN s1 s2 | (True, False) | ((S m), Z) = gtrSN_ (Neg (S m)) (Pos Z)
    gtrSN s1 s2 | (True, False) | ((S m), (S n)) = gtrSN_ (Neg (S m)) (Pos (S n))
  gtrSN s1 s2 | (True, True) with (sn1n, sn2n)
    gtrSN s1 s2 | (True, True) | (Z, Z) = gtrSN_ (Neg Z) (Neg Z)
    gtrSN s1 s2 | (True, True) | (Z, (S n)) = gtrSN_ (Neg Z) (Neg (S n))
    gtrSN s1 s2 | (True, True) | ((S m), Z) = gtrSN_ (Neg (S m)) (Neg Z)
    gtrSN s1 s2 | (True, True) | ((S m), (S n)) = gtrSN (Neg m) (Neg n)

proveNegZNotGtrPosZ : gtrSN (Neg 0) (Pos 0) = False
proveNegZNotGtrPosZ = Refl

proveNeg15GreaterThanNeg30 : gtrSN (Neg 15) (Neg 30) = True
proveNeg15GreaterThanNeg30 = Refl

public export
leqSN : {snab : Bool} -> {snan : Nat} -> {snbb : Bool} -> {snbn : Nat} -> (SignedNat snab snan) -> (SignedNat snbb snbn) -> Bool
leqSN a b = not (gtrSN a b)

public export
createSignedNat : (b:Bool) -> (m:Nat) -> SignedNat b m
createSignedNat False v = Pos v
createSignedNat True v = Neg v

public export
magSNIsMagnitude : (s : Bool) -> (n : Nat) -> (MagnitudeExtract s n) => extToNat (magExt (Just (createSignedNat s n))) = n
magSNIsMagnitude s n = Refl

public export
interface SubSN sna snb where
  subSN : sna -> snb -> (Bool, Nat)

public export
implementation SubSN (SignedNat _ _) (SignedNat _ Z) where
  subSN (Neg x) _ = (True, x)
  subSN (Pos x) _ = (False, x)

public export
implementation SubSN (SignedNat True _) (SignedNat False _) where
  subSN (Neg x) (Pos y) = (True, x + y)

public export
implementation SubSN (SignedNat False _) (SignedNat True _) where
  subSN (Pos x) (Neg y) = (False, x + y)

public export
implementation SubSN (SignedNat False Z) (SignedNat False (S n)) where
  subSN (Pos Z) (Pos (S n)) = subSN (Neg 1) (Pos n)

public export
implementation SubSN (SignedNat True Z) (SignedNat False (S n)) where
  subSN (Neg Z) (Pos (S n)) = subSN (Neg 1) (Pos n)

public export
implementation SubSN (SignedNat False n) (SignedNat False m) => SubSN (SignedNat False (S n)) (SignedNat False (S m)) where
  subSN (Pos (S n)) (Pos (S m)) = subSN (Pos n) (Pos m)

public export
implementation SubSN (SignedNat True n) (SignedNat True m) => SubSN (SignedNat True (S n)) (SignedNat True (S m)) where
  subSN (Neg (S n)) (Neg (S m)) = subSN (Neg n) (Neg m)

public export
pfst : (a,b) -> a
pfst (a,b) = a

public export
psnd : (a,b) -> b
psnd (a,b) = b

public export
signedNatFromSub : (sb : (Bool,Nat)) -> SignedNat (pfst sb) (psnd sb)
signedNatFromSub sb = createSignedNat (pfst sb) (psnd sb)
