module PLFA.Part1.Negation

import public PLFA.Part1.Connectives

%default total

-- region constructive
public export
Refutes : Type -> Type
Refutes a = a -> Void

public export
notElim : Refutes a -> a -> b
notElim na x = explode (na x)

public export
doubleNegIntro : a -> Refutes (Refutes a)
doubleNegIntro x na = na x

public export
tripleNegElim : Refutes (Refutes (Refutes a)) -> Refutes a
tripleNegElim nnna x = nnna (doubleNegIntro x)

public export
contraposition : (a -> b) -> Refutes b -> Refutes a
contraposition f nb x = nb (f x)

public export
oneNotTwo : Refutes (the Nat 1 = 2)
oneNotTwo Refl impossible

public export
zeroNotSucc : Refutes (Z = S n)
zeroNotSucc Refl impossible

public export
negationsPointwise : (na, na' : Refutes a) -> (x : a) -> na x = na' x
negationsPointwise na na' x = explode (na x)

public export
notSum : Iff (Refutes (Either a b)) (Refutes a, Refutes b)
notSum = MkIff (\n => (\x => n (Left x), \y => n (Right y)))
  (\(na, nb) => sumCase na nb)

public export
notSumRound : (n : Refutes (Either a b)) -> (s : Either a b) ->
  sumCase (\x => n (Left x)) (\y => n (Right y)) s = n s
notSumRound n s = explode (n s)

public export
excludedMiddleIrrefutable : Refutes (Refutes (Either a (Refutes a)))
excludedMiddleIrrefutable reject = reject (Right (\x => reject (Left x)))
-- endregion constructive

-- region strict-order
public export
ltNotEqual : (m : Nat) -> LT m n -> Refutes (m = n)
ltNotEqual m p Refl = ltIrreflexive m p

public export
ltAsymmetric : (m : Nat) -> LT m n -> Refutes (LT n m)
ltAsymmetric m p q = ltIrreflexive m (leTrans p (ltToLe q))

public export
data ExclusiveTri : Nat -> Nat -> Type where
  StrictlyBelow : LT m n -> Refutes (m = n) -> Refutes (LT n m) -> ExclusiveTri m n
  ExactlyEqual : m = n -> Refutes (LT m n) -> Refutes (LT n m) -> ExclusiveTri m n
  StrictlyAbove : LT n m -> Refutes (m = n) -> Refutes (LT m n) -> ExclusiveTri m n

public export
exclusiveTrichotomy : (m, n : Nat) -> ExclusiveTri m n
exclusiveTrichotomy m n = case trichotomy m n of
  Below p => StrictlyBelow p (ltNotEqual m p) (ltAsymmetric m p)
  Equal Refl => ExactlyEqual Refl (ltIrreflexive m) (ltIrreflexive m)
  Above p => StrictlyAbove p (\eq => ltNotEqual n p (sym eq)) (ltAsymmetric n p)
-- endregion strict-order

-- region classical
public export
ExcludedMiddle : Type
ExcludedMiddle = (a : Type) -> Either a (Refutes a)

public export
DoubleNegationElimination : Type
DoubleNegationElimination = (a : Type) -> Refutes (Refutes a) -> a

public export
Peirce : Type
Peirce = (a, b : Type) -> ((a -> b) -> a) -> a

public export
ImplicationDisjunction : Type
ImplicationDisjunction = (a, b : Type) -> (a -> b) -> Either (Refutes a) b

public export
DeMorgan : Type
DeMorgan = (a, b : Type) -> Refutes (Refutes a, Refutes b) -> Either a b

public export
emToDne : ExcludedMiddle -> DoubleNegationElimination
emToDne em a nna = case em a of
  Left x => x
  Right na => explode (nna na)

public export
dneToEm : DoubleNegationElimination -> ExcludedMiddle
dneToEm dne a = dne (Either a (Refutes a)) excludedMiddleIrrefutable

public export
emToPeirce : ExcludedMiddle -> Peirce
emToPeirce em a b f = case em a of
  Left x => x
  Right na => f (\x => explode (na x))

public export
peirceToDne : Peirce -> DoubleNegationElimination
peirceToDne p a nna = p a Void (\na => explode (nna na))

public export
peirceToEm : Peirce -> ExcludedMiddle
peirceToEm p = dneToEm (peirceToDne p)

public export
emToImplication : ExcludedMiddle -> ImplicationDisjunction
emToImplication em a b f = case em a of
  Left x => Right (f x)
  Right na => Left na

public export
implicationToEm : ImplicationDisjunction -> ExcludedMiddle
implicationToEm principle a = case principle a a id of
  Left na => Right na
  Right x => Left x

public export
emToDeMorgan : ExcludedMiddle -> DeMorgan
emToDeMorgan em a b reject = case em a of
  Left x => Left x
  Right na => case em b of
    Left y => Right y
    Right nb => explode (reject (na, nb))

public export
deMorganToEm : DeMorgan -> ExcludedMiddle
deMorganToEm principle a = principle a (Refutes a) (\(na, nna) => nna na)
-- endregion classical

-- region stability
public export
Stable : Type -> Type
Stable a = Refutes (Refutes a) -> a

public export
negationStable : Stable (Refutes a)
negationStable = tripleNegElim

public export
productStable : Stable a -> Stable b -> Stable (a, b)
productStable sa sb nnab =
  (sa (\na => nnab (\(x, y) => na x)), sb (\nb => nnab (\(x, y) => nb y)))
-- endregion stability
