module PLFA.Part1.Relations

import public PLFA.Part1.Induction

%default total

-- region order
public export
data LE : Nat -> Nat -> Type where
  LZ : LE Z n
  LS : LE m n -> LE (S m) (S n)

public export
leRefl : (n : Nat) -> LE n n
leRefl Z = LZ
leRefl (S n) = LS (leRefl n)

public export
leTrans : LE m n -> LE n p -> LE m p
leTrans LZ q = LZ
leTrans (LS p) (LS q) = LS (leTrans p q)

public export
leAntisym : LE m n -> LE n m -> m = n
leAntisym LZ LZ = Refl
leAntisym (LS p) (LS q) = cong S (leAntisym p q)

public export
lePred : LE (S m) (S n) -> LE m n
lePred (LS p) = p

public export
leZero : LE n Z -> n = Z
leZero LZ = Refl

public export
leStep : LE m n -> LE m (S n)
leStep LZ = LZ
leStep (LS p) = LS (leStep p)

public export
leTotal : (m, n : Nat) -> Either (LE m n) (LE n m)
leTotal Z n = Left LZ
leTotal (S m) Z = Right LZ
leTotal (S m) (S n) = case leTotal m n of
  Left p => Left (LS p)
  Right p => Right (LS p)

public export
addMono : {m, n, p, q : Nat} -> LE m n -> LE p q -> LE (add m p) (add n q)
addMono LZ q = leTrans q (rightBound _ _)
  where
  rightBound : (n, q : Nat) -> LE q (add n q)
  rightBound Z q = leRefl q
  rightBound (S n) q = leStep (rightBound n q)
addMono (LS p) q = LS (addMono p q)

public export
addBound : (m, n : Nat) -> LE m (add m n)
addBound Z n = LZ
addBound (S m) n = LS (addBound m n)

public export
mulMono : {m, n, p, q : Nat} -> LE m n -> LE p q -> LE (mul m p) (mul n q)
mulMono LZ q = LZ
mulMono (LS p) q = addMono q (mulMono p q)

public export
LT : Nat -> Nat -> Type
LT m n = LE (S m) n

public export
ltTrans : LT m n -> LT n p -> LT m p
ltTrans p q = leTrans (leStep p) q

public export
ltToLe : LT m n -> LE m n
ltToLe (LS p) = leStep p

public export
ltIrreflexive : (n : Nat) -> LT n n -> Void
ltIrreflexive Z p impossible
ltIrreflexive (S n) (LS p) = ltIrreflexive n p

public export
ltAddMono : {m, n, p, q : Nat} -> LT m n -> LT p q -> LT (add m p) (add n q)
ltAddMono p q = addMono p (ltToLe q)

public export
data Trichotomy : Nat -> Nat -> Type where
  Below : LT m n -> Trichotomy m n
  Equal : m = n -> Trichotomy m n
  Above : LT n m -> Trichotomy m n

public export
trichotomy : (m, n : Nat) -> Trichotomy m n
trichotomy Z Z = Equal Refl
trichotomy Z (S n) = Below (LS LZ)
trichotomy (S m) Z = Above (LS LZ)
trichotomy (S m) (S n) = case trichotomy m n of
  Below p => Below (LS p)
  Equal p => Equal (cong S p)
  Above p => Above (LS p)

public export
twoLEfour : LE 2 4
twoLEfour = LS (LS LZ)
-- endregion order

-- region parity
mutual
  public export
  data Even : Nat -> Type where
    EvenZ : Even Z
    EvenS : Odd n -> Even (S n)

  public export
  data Odd : Nat -> Type where
    OddS : Even n -> Odd (S n)

mutual
  public export
  evenPlusEven : Even m -> Even n -> Even (add m n)
  evenPlusEven EvenZ q = q
  evenPlusEven (EvenS p) q = EvenS (oddPlusEven p q)

  public export
  oddPlusEven : Odd m -> Even n -> Odd (add m n)
  oddPlusEven (OddS p) q = OddS (evenPlusEven p q)

mutual
  public export
  evenPlusOdd : Even m -> Odd n -> Odd (add m n)
  evenPlusOdd EvenZ q = q
  evenPlusOdd (EvenS p) q = OddS (oddPlusOdd p q)

  public export
  oddPlusOdd : Odd m -> Odd n -> Even (add m n)
  oddPlusOdd (OddS p) q = EvenS (evenPlusOdd p q)

public export
fourEven : Even 4
fourEven = EvenS (OddS (EvenS (OddS EvenZ)))
-- endregion parity

-- region canonical
public export
data One : Bin -> Type where
  Leading : One (B1 Empty)
  One0 : One b -> One (B0 b)
  One1 : One b -> One (B1 b)

public export
data Canonical : Bin -> Type where
  CanonZero : Canonical (B0 Empty)
  CanonPositive : One b -> Canonical b

public export
oneInc : One b -> One (inc b)
oneInc Leading = One0 Leading
oneInc (One0 p) = One1 p
oneInc (One1 p) = One0 (oneInc p)

public export
canonicalInc : Canonical b -> Canonical (inc b)
canonicalInc CanonZero = CanonPositive Leading
canonicalInc (CanonPositive p) = CanonPositive (oneInc p)

public export
canonicalTo : (n : Nat) -> Canonical (toBin n)
canonicalTo Z = CanonZero
canonicalTo (S n) = canonicalInc (canonicalTo n)

public export
onePositive : {b : Bin} -> One b -> LE 1 (fromBin b)
onePositive Leading = LS LZ
onePositive (One0 {b} p) = leTrans (onePositive p) (addBound (fromBin b) (fromBin b))
onePositive (One1 p) = LS LZ

public export
toDoublePositive : (n : Nat) -> toBin (add (S n) (S n)) = B0 (toBin (S n))
toDoublePositive Z = Refl
toDoublePositive (S n) = trans (cong toBin (doubleSucc (S n)))
  (cong (\b => inc (inc b)) (toDoublePositive n))

public export
toDouble : (n : Nat) -> LE 1 n -> toBin (add n n) = B0 (toBin n)
toDouble Z p impossible
toDouble (S n) p = toDoublePositive n

public export
oneRoundTrip : {b : Bin} -> One b -> toBin (fromBin b) = b
oneRoundTrip Leading = Refl
oneRoundTrip (One0 {b} p) = trans (toDouble (fromBin b) (onePositive p))
  (cong B0 (oneRoundTrip p))
oneRoundTrip (One1 {b} p) = trans (cong inc (toDouble (fromBin b) (onePositive p)))
  (cong B1 (oneRoundTrip p))

public export
canonicalRoundTrip : {b : Bin} -> Canonical b -> toBin (fromBin b) = b
canonicalRoundTrip CanonZero = Refl
canonicalRoundTrip (CanonPositive p) = oneRoundTrip p

public export
oneUnique : (p, q : One b) -> p = q
oneUnique Leading Leading = Refl
oneUnique (One0 p) (One0 q) = cong One0 (oneUnique p q)
oneUnique (One1 p) (One1 q) = cong One1 (oneUnique p q)

public export
canonicalUnique : (p, q : Canonical b) -> p = q
canonicalUnique CanonZero CanonZero = Refl
canonicalUnique CanonZero (CanonPositive (One0 p)) impossible
canonicalUnique (CanonPositive (One0 p)) CanonZero impossible
canonicalUnique (CanonPositive p) (CanonPositive q) = cong CanonPositive (oneUnique p q)
-- endregion canonical
