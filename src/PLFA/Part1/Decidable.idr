module PLFA.Part1.Decidable

import public PLFA.Part1.Quantifiers

%default total

-- region boolean-evidence
public export
Truth : Bool -> Type
Truth True = ()
Truth False = Void

public export
truthEquality : (b : Bool) -> Truth b -> b = True
truthEquality True u = Refl
truthEquality False v = explode v

public export
equalityTruth : b = True -> Truth b
equalityTruth Refl = ()

public export
leBool : Nat -> Nat -> Bool
leBool Z n = True
leBool (S m) Z = False
leBool (S m) (S n) = leBool m n

public export
boolToLE : (m, n : Nat) -> Truth (leBool m n) -> LE m n
boolToLE Z n u = LZ
boolToLE (S m) Z v = explode v
boolToLE (S m) (S n) p = LS (boolToLE m n p)

public export
leToBool : LE m n -> Truth (leBool m n)
leToBool LZ = ()
leToBool (LS p) = leToBool p
-- endregion boolean-evidence

-- region decisions
public export
noSuccZero : Refutes (LE (S m) Z)
noSuccZero p impossible

public export
decLE : (m, n : Nat) -> Dec (LE m n)
decLE Z n = Yes LZ
decLE (S m) Z = No noSuccZero
decLE (S m) (S n) = case decLE m n of
  Yes p => Yes (LS p)
  No np => No (\(LS p) => np p)

public export
decLT : (m, n : Nat) -> Dec (LT m n)
decLT m n = decLE (S m) n

public export
succNotZero : Refutes (S n = Z)
succNotZero Refl impossible

public export
succInjective : S m = S n -> m = n
succInjective Refl = Refl

public export
decNatEq : (m, n : Nat) -> Dec (m = n)
decNatEq Z Z = Yes Refl
decNatEq Z (S n) = No zeroNotSucc
decNatEq (S m) Z = No succNotZero
decNatEq (S m) (S n) = case decNatEq m n of
  Yes p => Yes (cong S p)
  No np => No (\eq => np (succInjective eq))

public export
decBool : Dec a -> Bool
decBool (Yes p) = True
decBool (No np) = False

public export
toWitness : (d : Dec a) -> Truth (decBool d) -> a
toWitness (Yes p) u = p
toWitness (No np) v = explode v

public export
fromWitness : (d : Dec a) -> a -> Truth (decBool d)
fromWitness (Yes p) q = ()
fromWitness (No np) q = np q

public export
reflectedLE : (m, n : Nat) -> decBool (decLE m n) = leBool m n
reflectedLE Z n = Refl
reflectedLE (S m) Z = Refl
reflectedLE (S m) (S n) with (decLE m n) proof eq
  reflectedLE (S m) (S n) | Yes p = trans (sym (cong decBool eq)) (reflectedLE m n)
  reflectedLE (S m) (S n) | No np = trans (sym (cong decBool eq)) (reflectedLE m n)

public export
decisionExamples : (decBool (decLE 2 4), decBool (decLE 4 2), decBool (decNatEq 3 3)) = (True, False, True)
decisionExamples = Refl
-- endregion decisions

-- region connectives
public export
decAnd : Dec a -> Dec b -> Dec (a, b)
decAnd (Yes x) (Yes y) = Yes (x, y)
decAnd (Yes x) (No ny) = No (\p => ny (snd p))
decAnd (No nx) dy = No (\p => nx (fst p))

public export
decOr : Dec a -> Dec b -> Dec (Either a b)
decOr (Yes x) dy = Yes (Left x)
decOr (No nx) (Yes y) = Yes (Right y)
decOr (No nx) (No ny) = No (sumCase nx ny)

public export
decNot : Dec a -> Dec (Refutes a)
decNot (Yes x) = No (\nx => nx x)
decNot (No nx) = Yes nx

public export
decImplies : Dec a -> Dec b -> Dec (a -> b)
decImplies (No nx) dy = Yes (\x => explode (nx x))
decImplies (Yes x) (Yes y) = Yes (\z => y)
decImplies (Yes x) (No ny) = No (\f => ny (f x))

public export
decIff : Dec a -> Dec b -> Dec (Iff a b)
decIff da db = case decAnd (decImplies da db) (decImplies db da) of
  Yes (f, g) => Yes (MkIff f g)
  No reject => No (\i => reject (i.to, i.from))

public export
boolAnd : Bool -> Bool -> Bool
boolAnd True q = q
boolAnd False q = False

public export
boolOr : Bool -> Bool -> Bool
boolOr True q = True
boolOr False q = q

public export
boolNot : Bool -> Bool
boolNot True = False
boolNot False = True

public export
andErasure : (da : Dec a) -> (db : Dec b) ->
  decBool (decAnd da db) = boolAnd (decBool da) (decBool db)
andErasure (Yes x) (Yes y) = Refl
andErasure (Yes x) (No ny) = Refl
andErasure (No nx) db = Refl

public export
orErasure : (da : Dec a) -> (db : Dec b) ->
  decBool (decOr da db) = boolOr (decBool da) (decBool db)
orErasure (Yes x) db = Refl
orErasure (No nx) (Yes y) = Refl
orErasure (No nx) (No ny) = Refl

public export
notErasure : (da : Dec a) -> decBool (decNot da) = boolNot (decBool da)
notErasure (Yes x) = Refl
notErasure (No nx) = Refl

public export
impliesErasure : (da : Dec a) -> (db : Dec b) ->
  decBool (decImplies da db) = boolOr (boolNot (decBool da)) (decBool db)
impliesErasure (No nx) db = Refl
impliesErasure (Yes x) (Yes y) = Refl
impliesErasure (Yes x) (No ny) = Refl

public export
iffErasure : (da : Dec a) -> (db : Dec b) -> decBool (decIff da db) =
  boolAnd (boolOr (boolNot (decBool da)) (decBool db))
          (boolOr (boolNot (decBool db)) (decBool da))
iffErasure (Yes x) (Yes y) = Refl
iffErasure (Yes x) (No ny) = Refl
iffErasure (No nx) (Yes y) = Refl
iffErasure (No nx) (No ny) = Refl
-- endregion connectives

-- region reflection
public export
minus : (m, n : Nat) -> LE n m -> Nat
minus m Z p = m
minus Z (S n) p impossible
minus (S m) (S n) (LS p) = minus m n p

public export
safeMinus : (m, n : Nat) -> {auto ok : Truth (decBool (decLE n m))} -> Nat
safeMinus m n {ok} = minus m n (toWitness (decLE n m) ok)

public export
safeMinusExample : safeMinus 5 3 = 2
safeMinusExample = Refl

public export
FalseDecision : Dec a -> Type
FalseDecision d = Truth (boolNot (decBool d))

public export
fromFalse : (d : Dec a) -> FalseDecision d -> Refutes a
fromFalse (Yes p) v = explode v
fromFalse (No np) u = np
public export
toFalse : (d : Dec a) -> Refutes a -> FalseDecision d
toFalse (Yes p) np = explode (np p)
toFalse (No np) nq = ()
-- endregion reflection

-- region binary-decisions
public export
decOne : (b : Bin) -> Dec (One b)
decOne Empty = No noEmpty
  where
  noEmpty : One Empty -> Void
  noEmpty p impossible
decOne (B0 b) = case decOne b of
  Yes p => Yes (One0 p)
  No np => No (\(One0 p) => np p)
decOne (B1 Empty) = Yes Leading
decOne (B1 (B0 b)) = case decOne (B0 b) of
  Yes p => Yes (One1 p)
  No np => No (\(One1 p) => np p)
decOne (B1 (B1 b)) = case decOne (B1 b) of
  Yes p => Yes (One1 p)
  No np => No (\(One1 p) => np p)

public export
positiveDecision : (b : Bin) -> (Canonical b -> One b) -> Dec (Canonical b)
positiveDecision b positive = case decOne b of
  Yes p => Yes (CanonPositive p)
  No np => No (\c => np (positive c))

public export
decCanonical : (b : Bin) -> Dec (Canonical b)
decCanonical Empty = positiveDecision Empty (\(CanonPositive p) => p)
decCanonical (B0 Empty) = Yes CanonZero
decCanonical (B0 (B0 b)) = positiveDecision (B0 (B0 b)) (\(CanonPositive p) => p)
decCanonical (B0 (B1 b)) = positiveDecision (B0 (B1 b)) (\(CanonPositive p) => p)
decCanonical (B1 b) = positiveDecision (B1 b) (\(CanonPositive p) => p)

public export
canonicalDecisionExamples :
  (decBool (decCanonical (B0 Empty)), decBool (decCanonical (B0 (B0 Empty))),
   decBool (decCanonical (B0 (B1 Empty)))) = (True, False, True)
canonicalDecisionExamples = Refl
-- endregion binary-decisions
