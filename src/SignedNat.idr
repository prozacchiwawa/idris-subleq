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

interface GreaterSN sna snb where
  gtrSN : sna -> snb -> Bool

implementation GreaterSN (SignedNat False Z) (SignedNat True Z) where
  gtrSN _ _ = False

implementation GreaterSN (SignedNat False (S _)) (SignedNat True _) where
  gtrSN _ _ = True

implementation GreaterSN (SignedNat True _) (SignedNat False _) where
  gtrSN _ _ = False

implementation GreaterSN (SignedNat False Z) (SignedNat False _) where
  gtrSN _ _ = False

implementation GreaterSN (SignedNat False (S a)) (SignedNat False Z) where
  gtrSN _ _ = True

implementation (GreaterSN (SignedNat False a) (SignedNat False b)) => GreaterSN (SignedNat False (S a)) (SignedNat False (S b)) where
  gtrSN (Pos (S a)) (Pos (S b)) = gtrSN (Pos a) (Pos b)

implementation GreaterSN (SignedNat True _) (SignedNat True Z) where
  gtrSN _ _ = False

implementation GreaterSN (SignedNat True Z) (SignedNat True (S a)) where
  gtrSN _ _ = True

implementation (GreaterSN (SignedNat True a) (SignedNat True b)) => GreaterSN (SignedNat True (S a)) (SignedNat True (S b)) where
  gtrSN (Neg (S a)) (Neg (S b)) = gtrSN (Neg a) (Neg b)

proveNegZNotGtrPosZ : gtrSN (Neg 0) (Pos 0) = False
proveNegZNotGtrPosZ = Refl

proveNeg15GreaterThanNeg30 : gtrSN (Neg 15) (Neg 30) = True
proveNeg15GreaterThanNeg30 = Refl

interface LessEqSN sna snb where
  leqSN : sna -> snb -> Bool

implementation GreaterSN sna snb => LessEqSN sna snb where
  leqSN a b = not (gtrSN a b)

public export
createSignedNat : (b:Bool) -> (m:Nat) -> SignedNat b m
createSignedNat False v = Pos v
createSignedNat True v = Neg v

public export
magSNIsMagnitude : (s : Bool) -> (n : Nat) -> (MagnitudeExtract s n) => extToNat (magExt (Just (createSignedNat s n))) = n
magSNIsMagnitude s n = Refl
