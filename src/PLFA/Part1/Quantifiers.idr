module PLFA.Part1.Quantifiers

import public PLFA.Part1.Negation

%default total

-- region universals
public export
forallElim : {p : a -> Type} -> ((x : a) -> p x) -> (x : a) -> p x
forallElim f x = f x

public export
forallProduct : {p, q : a -> Type} ->
  Iff ((x : a) -> (p x, q x)) (((x : a) -> p x), ((x : a) -> q x))
forallProduct = MkIff (\f => (\x => fst (f x), \x => snd (f x)))
  (\(f, g), x => (f x, g x))

public export
forallProductRound : {p, q : a -> Type} ->
  (f : (x : a) -> (p x, q x)) -> (x : a) -> (fst (f x), snd (f x)) = f x
forallProductRound f x = pairEta (f x)

public export
sumForall : {p, q : a -> Type} ->
  Either ((x : a) -> p x) ((x : a) -> q x) -> (x : a) -> Either (p x) (q x)
sumForall (Left f) x = Left (f x)
sumForall (Right g) x = Right (g x)

public export
data Tri = Aa | Bb | Cc

public export
triTabulate : {p : Tri -> Type} -> (p Aa, (p Bb, p Cc)) -> (t : Tri) -> p t
triTabulate (x, (y, z)) Aa = x
triTabulate (x, (y, z)) Bb = y
triTabulate (x, (y, z)) Cc = z

public export
forallTri : {p : Tri -> Type} -> Iff ((t : Tri) -> p t) (p Aa, (p Bb, p Cc))
forallTri = MkIff (\f => (f Aa, (f Bb, f Cc))) triTabulate

public export
triRound : {p : Tri -> Type} -> (f : (t : Tri) -> p t) -> (t : Tri) ->
  triTabulate {p} (f Aa, (f Bb, f Cc)) t = f t
triRound f Aa = Refl
triRound f Bb = Refl
triRound f Cc = Refl
-- endregion universals

-- region existentials
public export
existsElim : {p : a -> Type} -> ((x : a) -> p x -> c) -> (x : a ** p x) -> c
existsElim f (x ** px) = f x px

public export
existsCurry : {p : a -> Type} ->
  Iff ((x : a) -> p x -> c) ((x : a ** p x) -> c)
existsCurry = MkIff existsElim (\f, x, px => f (x ** px))

public export
existsCurryRound : {p : a -> Type} -> (f : (x : a ** p x) -> c) ->
  (w : (x : a ** p x)) -> existsElim (\x, px => f (x ** px)) w = f w
existsCurryRound f (x ** px) = Refl

public export
existsSumTo : {p, q : a -> Type} ->
  (x : a ** Either (p x) (q x)) -> Either (x : a ** p x) (x : a ** q x)
existsSumTo (x ** Left px) = Left (x ** px)
existsSumTo (x ** Right qx) = Right (x ** qx)

public export
existsSumFrom : {p, q : a -> Type} ->
  Either (x : a ** p x) (x : a ** q x) -> (x : a ** Either (p x) (q x))
existsSumFrom (Left (x ** px)) = (x ** Left px)
existsSumFrom (Right (x ** qx)) = (x ** Right qx)

public export
existsSum : {p, q : a -> Type} ->
  Iso (x : a ** Either (p x) (q x)) (Either (x : a ** p x) (x : a ** q x))
existsSum = MkIso existsSumTo existsSumFrom left right
  where
  left : (w : (x : a ** Either (p x) (q x))) -> existsSumFrom (existsSumTo w) = w
  left (x ** Left px) = Refl
  left (x ** Right qx) = Refl
  right : (s : Either (x : a ** p x) (x : a ** q x)) -> existsSumTo (existsSumFrom s) = s
  right (Left (x ** px)) = Refl
  right (Right (x ** qx)) = Refl

public export
existsProduct : {p, q : a -> Type} ->
  (x : a ** (p x, q x)) -> ((x : a ** p x), (x : a ** q x))
existsProduct (x ** (px, qx)) = ((x ** px), (x ** qx))

public export
existsTriTo : {p : Tri -> Type} -> (t : Tri ** p t) -> Either (p Aa) (Either (p Bb) (p Cc))
existsTriTo (Aa ** x) = Left x
existsTriTo (Bb ** y) = Right (Left y)
existsTriTo (Cc ** z) = Right (Right z)

public export
existsTriFrom : {p : Tri -> Type} -> Either (p Aa) (Either (p Bb) (p Cc)) -> (t : Tri ** p t)
existsTriFrom (Left x) = (Aa ** x)
existsTriFrom (Right (Left y)) = (Bb ** y)
existsTriFrom (Right (Right z)) = (Cc ** z)

public export
existsTri : {p : Tri -> Type} -> Iso (t : Tri ** p t) (Either (p Aa) (Either (p Bb) (p Cc)))
existsTri {p} = MkIso existsTriTo existsTriFrom left right
  where
  left : (w : (t : Tri ** p t)) -> existsTriFrom (existsTriTo w) = w
  left (Aa ** x) = Refl
  left (Bb ** y) = Refl
  left (Cc ** z) = Refl
  right : (s : Either (p Aa) (Either (p Bb) (p Cc))) -> existsTriTo {p} (existsTriFrom {p} s) = s
  right (Left x) = Refl
  right (Right (Left y)) = Refl
  right (Right (Right z)) = Refl
-- endregion existentials

-- region parity-witnesses
mutual
  public export
  evenWitness : Even n -> (k : Nat ** mul k 2 = n)
  evenWitness EvenZ = (0 ** Refl)
  evenWitness (EvenS p) = case oddWitness p of
    (k ** eq) => (S k ** cong S eq)

  public export
  oddWitness : Odd n -> (k : Nat ** S (mul k 2) = n)
  oddWitness (OddS p) = case evenWitness p of
    (k ** eq) => (k ** cong S eq)

public export
evenDouble : (k : Nat) -> Even (mul k 2)
evenDouble Z = EvenZ
evenDouble (S k) = EvenS (OddS (evenDouble k))

public export
witnessEven : (k : Nat ** mul k 2 = n) -> Even n
witnessEven (k ** eq) = transport Even eq (evenDouble k)

public export
witnessOdd : (k : Nat ** S (mul k 2) = n) -> Odd n
witnessOdd (k ** eq) = transport Odd eq (OddS (evenDouble k))

public export
evenWitnessLeft : Even n -> (k : Nat ** mul 2 k = n)
evenWitnessLeft p = case evenWitness p of
  (k ** eq) => (k ** trans (mulComm 2 k) eq)

public export
oddWitnessLeft : Odd n -> (k : Nat ** add (mul 2 k) 1 = n)
oddWitnessLeft p = case oddWitness p of
  (k ** eq) => (k ** trans (addComm (mul 2 k) 1) (trans (cong S (mulComm 2 k)) eq))

public export
leWitness : {m, n : Nat} -> LE m n -> (k : Nat ** add k m = n)
leWitness {n} LZ = (n ** addZeroRight n)
leWitness (LS {m} p) = case leWitness p of
  (k ** eq) => (k ** trans (addSuccRight k m) (cong S eq))

public export
witnessLE : {m : Nat} -> (k : Nat ** add k m = n) -> LE m n
witnessLE {m} (k ** eq) = transport (LE m) (trans (addComm m k) eq) (addBound m k)
public export
witnessEvenLeft : (k : Nat ** mul 2 k = n) -> Even n
witnessEvenLeft (k ** eq) = witnessEven (k ** trans (mulComm k 2) eq)

public export
witnessOddLeft : (k : Nat ** add (mul 2 k) 1 = n) -> Odd n
witnessOddLeft (k ** eq) = witnessOdd (k **
  trans (cong S (mulComm k 2)) (trans (sym (addComm (mul 2 k) 1)) eq))

public export
leExists : {m, n : Nat} -> Iff (LE m n) (k : Nat ** add k m = n)
leExists = MkIff leWitness witnessLE
-- endregion parity-witnesses

-- region negated-quantifiers
public export
notExists : {p : a -> Type} -> Iff (Refutes (x : a ** p x)) ((x : a) -> Refutes (p x))
notExists = MkIff (\n, x, px => n (x ** px)) (\f, (x ** px) => f x px)

public export
existsNot : {p : a -> Type} -> (x : a ** Refutes (p x)) -> Refutes ((x : a) -> p x)
existsNot (x ** nx) f = nx (f x)
-- endregion negated-quantifiers

-- region canonical-isomorphism
public export
CanonicalBin : Type
CanonicalBin = (b : Bin ** Canonical b)

public export
canonicalPairEqual : {b, c : Bin} -> (p : Canonical b) -> (q : Canonical c) ->
  b = c -> the CanonicalBin (b ** p) = (c ** q)
canonicalPairEqual {b} p q Refl = cong (\r => (b ** r)) (canonicalUnique p q)

public export
canonicalIso : Iso Nat CanonicalBin
canonicalIso = MkIso (\n => (toBin n ** canonicalTo n))
  (\w => fromBin (fst w)) fromTo right
  where
  right : (w : CanonicalBin) -> (toBin (fromBin (fst w)) ** canonicalTo (fromBin (fst w))) = w
  right (b ** p) = canonicalPairEqual (canonicalTo (fromBin b)) p (canonicalRoundTrip p)
-- endregion canonical-isomorphism
