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
signOfSN : {s : Bool} -> SignedNat s v -> Bool
signOfSN (Pos _) = False
signOfSN (Neg _) = True

public export
magOfSN : {v : Nat} -> SignedNat s v -> Nat
magOfSN (Pos v) = v
magOfSN (Neg v) = v

public export
gtrSN : SignedNat s1 v1 -> SignedNat s2 v2 -> Bool
gtrSN (Pos 0) (Pos 0) = False
gtrSN (Pos 0) (Neg 0) = False
gtrSN (Neg 0) (Pos 0) = False
gtrSN (Neg 0) (Neg 0) = False
gtrSN (Pos 0) (Pos (S _)) = False
gtrSN (Pos 0) (Neg (S _)) = True
gtrSN (Neg 0) (Pos (S _)) = False
gtrSN (Neg 0) (Neg (S _)) = True
gtrSN (Pos (S _)) (Pos 0) = True
gtrSN (Pos (S _)) (Neg _) = True
gtrSN (Pos (S m)) (Pos (S n)) = gtrSN (Pos m) (Pos n)
gtrSN (Neg (S _)) (Neg 0) = False
gtrSN (Neg (S m)) (Neg (S n)) = gtrSN (Neg m) (Neg n)
gtrSN (Neg (S _)) (Pos _) = False

proveNegZNotGtrPosZ : gtrSN (Neg 0) (Pos 0) = False
proveNegZNotGtrPosZ = Refl

proveNeg15GreaterThanNeg30 : gtrSN (Neg 15) (Neg 30) = True
proveNeg15GreaterThanNeg30 = Refl

public export
leqSN : SignedNat s1 v1 -> SignedNat s2 v2 -> Bool
leqSN a b = not (gtrSN a b)

public export
createSignedNat : (b:Bool) -> (m:Nat) -> SignedNat b m
createSignedNat False v = Pos v
createSignedNat True v = Neg v

public export
magSNIsMagnitude : (s : Bool) -> (n : Nat) -> (MagnitudeExtract s n) => extToNat (magExt (Just (createSignedNat s n))) = n
magSNIsMagnitude s n = Refl

public export
pfst : (a,b) -> a
pfst (a,b) = a

public export
psnd : (a,b) -> b
psnd (a,b) = b

public export
signOfSubtraction : (SignedNat s1 v1) -> (SignedNat s2 v2) -> Bool
signOfSubtraction (Pos Z) (Pos Z) = False
signOfSubtraction (Pos Z) (Neg Z) = False
signOfSubtraction (Neg Z) (Pos Z) = False
signOfSubtraction (Neg Z) (Neg Z) = False
signOfSubtraction (Pos Z) (Pos _) = True
signOfSubtraction (Neg Z) (Pos _) = True
signOfSubtraction (Pos Z) (Neg _) = False
signOfSubtraction (Neg Z) (Neg _) = False
signOfSubtraction (Pos (S m)) (Pos (S n)) =
  signOfSubtraction (Pos m) (Pos n)
signOfSubtraction (Pos (S _)) (Pos 0) = False
signOfSubtraction (Neg (S _)) (Pos 0) = False
signOfSubtraction (Pos (S _)) (Neg 0) = False
signOfSubtraction (Neg (S _)) (Neg 0) = False
signOfSubtraction (Pos (S _)) (Neg (S _)) = False
signOfSubtraction (Neg (S _)) (Pos (S _)) = True
signOfSubtraction (Neg (S m)) (Neg (S n)) =
  signOfSubtraction (Neg m) (Neg n)

public export
magOfSubtraction : (SignedNat s1 v1) -> (SignedNat s2 v2) -> Nat
magOfSubtraction (Pos Z) (Pos n) = n
magOfSubtraction (Neg Z) (Pos n) = n
magOfSubtraction (Pos Z) (Neg n) = n
magOfSubtraction (Neg Z) (Neg n) = n
magOfSubtraction (Pos (S m)) (Pos (S n)) =
  magOfSubtraction (Pos m) (Pos n)
magOfSubtraction (Pos (S m)) (Pos 0) = m
magOfSubtraction (Neg (S m)) (Pos 0) = m
magOfSubtraction (Pos (S m)) (Neg 0) = m
magOfSubtraction (Neg (S m)) (Neg 0) = m
magOfSubtraction (Pos (S m)) (Neg (S n)) = m + n
magOfSubtraction (Neg (S m)) (Pos (S n)) = m + n
magOfSubtraction (Neg (S m)) (Neg (S n)) =
  magOfSubtraction (Neg m) (Neg n)

public export
subSN :
  {s1 : Bool} ->
  {v1 : Nat} ->
  {s2 : Bool} ->
  {v2 : Nat} ->
  SignedNat s1 v1 ->
  SignedNat s2 v2 ->
  SignedNat
    (signOfSubtraction (createSignedNat s1 v1) (createSignedNat s2 v2))
    (magOfSubtraction (createSignedNat s1 v1) (createSignedNat s2 v2))
subSN _ _ =
  createSignedNat
    (signOfSubtraction (createSignedNat s1 v1) (createSignedNat s2 v2))
    (magOfSubtraction (createSignedNat s1 v1) (createSignedNat s2 v2))
