module PLFA.Part1.Isomorphism

import public PLFA.Part1.Equality

%default total

-- region maps
public export
compose : (b -> c) -> (a -> b) -> a -> c
compose g f x = g (f x)

public export
Pointwise : {a, b : Type} -> (a -> b) -> (a -> b) -> Type
Pointwise f g = (x : a) -> f x = g x

public export
addRightRecursive : Nat -> Nat -> Nat
addRightRecursive m Z = m
addRightRecursive m (S n) = S (addRightRecursive m n)

public export
sameApplications : (m, n : Nat) -> addRightRecursive m n = add m n
sameApplications m Z = sym (addZeroRight m)
sameApplications m (S n) = trans (cong S (sameApplications m n)) (sym (addSuccRight m n))
-- endregion maps

-- region isomorphism
public export
record Iso (a : Type) (b : Type) where
  constructor MkIso
  forward : a -> b
  backward : b -> a
  leftInverse : (x : a) -> backward (forward x) = x
  rightInverse : (y : b) -> forward (backward y) = y

public export
isoRefl : Iso a a
isoRefl = MkIso id id (\x => Refl) (\x => Refl)

public export
isoSym : Iso a b -> Iso b a
isoSym i = MkIso i.backward i.forward i.rightInverse i.leftInverse

public export
isoTrans : Iso a b -> Iso b c -> Iso a c
isoTrans i j = MkIso (compose j.forward i.forward) (compose i.backward j.backward)
  (\x => trans (cong i.backward (j.leftInverse (i.forward x))) (i.leftInverse x))
  (\z => trans (cong j.forward (i.rightInverse (j.backward z))) (j.rightInverse z))
-- endregion isomorphism

-- region embedding
public export
record Embedding (a : Type) (b : Type) where
  constructor MkEmbedding
  embed : a -> b
  project : b -> a
  retract : (x : a) -> project (embed x) = x

public export
embedRefl : Embedding a a
embedRefl = MkEmbedding id id (\x => Refl)

public export
embedTrans : Embedding a b -> Embedding b c -> Embedding a c
embedTrans i j = MkEmbedding (compose j.embed i.embed) (compose i.project j.project)
  (\x => trans (cong i.project (j.retract (i.embed x))) (i.retract x))

public export
isoToEmbedding : Iso a b -> Embedding a b
isoToEmbedding i = MkEmbedding i.forward i.backward i.leftInverse

public export
embeddingAntisym : (i : Embedding a b) -> (j : Embedding b a) ->
  Pointwise i.embed j.project -> Pointwise i.project j.embed -> Iso a b
embeddingAntisym i j ef pf = MkIso i.embed i.project i.retract
  (\y => trans (cong i.embed (pf y)) (trans (ef (j.embed y)) (j.retract y)))

public export
binaryEmbedding : Embedding Nat Bin
binaryEmbedding = MkEmbedding toBin fromBin fromTo

public export
record Iff (a : Type) (b : Type) where
  constructor MkIff
  to : a -> b
  from : b -> a

public export
iffRefl : Iff a a
iffRefl = MkIff id id

public export
iffSym : Iff a b -> Iff b a
iffSym i = MkIff i.from i.to

public export
iffTrans : Iff a b -> Iff b c -> Iff a c
iffTrans i j = MkIff (compose j.to i.to) (compose i.from j.from)
-- endregion embedding
