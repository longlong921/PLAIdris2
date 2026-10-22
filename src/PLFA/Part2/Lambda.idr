module PLFA.Part2.Lambda

import public PLFA.Part2.Typed

%default total

-- region dynamics
public export
data Value : Raw n -> Type where
  VLam  : Value (RLam body)
  VZero : Value RZero
  VSucc : Value t -> Value (RSucc t)

public export
data Step : Raw n -> Raw n -> Type where
  AppL     : Step f f' -> Step (RApp f a) (RApp f' a)
  AppR     : Value f -> Step a a' -> Step (RApp f a) (RApp f a')
  Beta     : Value v -> Step (RApp (RLam b) v) (instantiate b v)
  SuccStep : Step t t' -> Step (RSucc t) (RSucc t')
  CaseStep : Step t t' -> Step (RCase t z s) (RCase t' z s)
  CaseZero : Step (RCase RZero z s) z
  CaseSucc : Value v -> Step (RCase (RSucc v) z s) (instantiate s v)
  Unfold   : Step (RFix b) (instantiate b (RFix b))

public export
data Steps : Raw n -> Raw n -> Type where
  Done : Steps t t
  Next : Step t u -> Steps u v -> Steps t v

public export
appendSteps : Steps t u -> Steps u v -> Steps t v
appendSteps Done q = q
appendSteps (Next p ps) q = Next p (appendSteps ps q)

public export
applicationSteps : Steps f g -> Steps (RApp f a) (RApp g a)
applicationSteps Done = Done
applicationSteps (Next p ps) = Next (AppL p) (applicationSteps ps)
-- endregion dynamics

-- region examples
public export
numeral : Nat -> Raw n
numeral Z = RZero
numeral (S k) = RSucc (numeral k)

public export
numeralValue : (k : Nat) -> Value (numeral {n} k)
numeralValue Z = VZero
numeralValue (S k) = VSucc (numeralValue k)

public export
numeralType : (k : Nat) -> HasType gamma (numeral k) TNat
numeralType Z = TZero
numeralType (S k) = TSucc (numeralType k)

public export
identity : Raw n
identity = RLam (RVar FZ)

public export
identityType : HasType gamma Lambda.identity (Arr a a)
identityType = TLam (TVar FZ)

public export
identityTwo : Step (RApp (identity {n = 0}) (numeral 2)) (numeral 2)
identityTwo = Beta (numeralValue 2)

-- At the successor branch: predecessor, n, m, recursive function.
public export
plus : Raw n
plus = RFix (RLam (RLam
  (RCase (RVar (FS FZ)) (RVar FZ)
    (RSucc (RApp (RApp (RVar (FS (FS (FS FZ))))
                         (RVar FZ)) (RVar (FS FZ)))))))

public export
plusType : HasType gamma Lambda.plus (Arr TNat (Arr TNat TNat))
plusType = TFix (TLam (TLam
  (TCase (TVar (FS FZ)) (TVar FZ)
    (TSucc (TApp (TApp (TVar (FS (FS (FS FZ))))
                         (TVar FZ)) (TVar (FS FZ)))))))

public export
Church : Ty -> Ty
Church a = Arr (Arr a a) (Arr a a)

public export
churchTwo : Raw n
churchTwo = RLam (RLam
  (RApp (RVar (FS FZ)) (RApp (RVar (FS FZ)) (RVar FZ))))

public export
churchTwoType : HasType gamma Lambda.churchTwo (Church a)
churchTwoType = TLam (TLam
  (TApp (TVar (FS FZ)) (TApp (TVar (FS FZ)) (TVar FZ))))
-- endregion examples

-- region solutions
-- Exercise 1: evaluation must enter the argument of a lambda value.
public export
nestedIdentity : Steps
  (RApp (identity {n = 0}) (RApp Lambda.identity (numeral 2))) (numeral 2)
nestedIdentity = Next (AppR VLam identityTwo) (Next identityTwo Done)

-- Exercise 2: shadowing does not hide an outer de Bruijn index.
public export
constant : Raw n
constant = RLam (RLam (RVar (FS FZ)))

public export
constantType : HasType gamma Lambda.constant (Arr a (Arr b a))
constantType = TLam (TLam (TVar (FS FZ)))

-- Exercise 3: a well-scoped term need not be well typed.
public export
zeroApplicationUntypable : HasType [] (RApp RZero RZero) a -> Void
zeroApplicationUntypable (TApp TZero _) impossible
-- endregion solutions

-- region multiplication
public export
multiply : Raw n
multiply = RFix (RLam (RLam
  (RCase (RVar (FS FZ)) RZero
    (RApp (RApp Lambda.plus (RVar (FS FZ)))
      (RApp (RApp (RVar (FS (FS (FS FZ)))) (RVar FZ)) (RVar (FS FZ)))))))

public export
multiplyType : HasType gamma Lambda.multiply (Arr TNat (Arr TNat TNat))
multiplyType = TFix (TLam (TLam
  (TCase (TVar (FS FZ)) TZero
    (TApp (TApp plusType (TVar (FS FZ)))
      (TApp (TApp (TVar (FS (FS (FS FZ)))) (TVar FZ)) (TVar (FS FZ)))))))
-- endregion multiplication
