module PLFA.Part2.Properties

import public PLFA.Part2.Lambda

%default total

-- region structural
public export
liftRenType : {0 gamma : Context n} -> {0 delta : Context m} ->
  {0 a : Ty} -> (rho : Ren n m) ->
  ((i : Fin n) -> index i gamma = index (rho i) delta) ->
  (i : Fin (S n)) ->
  index i (a :: gamma) = index (liftRen rho i) (a :: delta)
liftRenType rho good FZ = Refl
liftRenType rho good (FS i) = good i

public export
renameTyping : {0 gamma : Context n} -> {0 delta : Context m} ->
  (rho : Ren n m) ->
  ((i : Fin n) -> index i gamma = index (rho i) delta) ->
  HasType gamma t a -> HasType delta (rename rho t) a
renameTyping rho good (TVar i) = rewrite good i in TVar (rho i)
renameTyping rho good (TLam p) = TLam (renameTyping (liftRen rho) (liftRenType rho good) p)
renameTyping rho good (TApp f a) = TApp (renameTyping rho good f) (renameTyping rho good a)
renameTyping rho good TZero = TZero
renameTyping rho good (TSucc p) = TSucc (renameTyping rho good p)
renameTyping rho good (TCase t z s) = TCase
  (renameTyping rho good t) (renameTyping rho good z)
  (renameTyping (liftRen rho) (liftRenType rho good) s)
renameTyping rho good (TFix p) = TFix (renameTyping (liftRen rho) (liftRenType rho good) p)

public export
liftSubType : {0 gamma : Context n} -> {0 delta : Context m} ->
  {0 a : Ty} -> (0 sigma : Sub n m) ->
  ((i : Fin n) -> HasType delta (sigma i) (index i gamma)) ->
  (i : Fin (S n)) ->
  HasType (a :: delta) (liftSub sigma i) (index i (a :: gamma))
liftSubType sigma good FZ = TVar FZ
liftSubType sigma good (FS i) = renameTyping FS (\j => Refl) (good i)

public export
substTyping : {0 gamma : Context n} -> {0 delta : Context m} ->
  (0 sigma : Sub n m) ->
  ((i : Fin n) -> HasType delta (sigma i) (index i gamma)) ->
  HasType gamma t a -> HasType delta (subst sigma t) a
substTyping sigma good (TVar i) = good i
substTyping sigma good (TLam p) = TLam (substTyping (liftSub sigma) (liftSubType sigma good) p)
substTyping sigma good (TApp f a) = TApp (substTyping sigma good f) (substTyping sigma good a)
substTyping sigma good TZero = TZero
substTyping sigma good (TSucc p) = TSucc (substTyping sigma good p)
substTyping sigma good (TCase t z s) = TCase
  (substTyping sigma good t) (substTyping sigma good z)
  (substTyping (liftSub sigma) (liftSubType sigma good) s)
substTyping sigma good (TFix p) = TFix (substTyping (liftSub sigma) (liftSubType sigma good) p)

public export
singleType : HasType gamma arg a -> (i : Fin (S n)) ->
  HasType gamma (single arg i) (index i (a :: gamma))
singleType argType FZ = argType
singleType argType (FS i) = TVar i

public export
instantiateTyping : HasType (a :: gamma) body b -> HasType gamma arg a ->
  HasType gamma (instantiate body arg) b
instantiateTyping bodyType argType = substTyping (single _) (singleType argType) bodyType
-- endregion structural

-- region preservation
public export
preservation : HasType gamma t a -> Step t u -> HasType gamma u a
preservation (TApp f a) (AppL s) = TApp (preservation f s) a
preservation (TApp f a) (AppR v s) = TApp f (preservation a s)
preservation (TApp (TLam b) a) (Beta v) = instantiateTyping b a
preservation (TSucc p) (SuccStep s) = TSucc (preservation p s)
preservation (TCase t z s) (CaseStep p) = TCase (preservation t p) z s
preservation (TCase TZero z s) CaseZero = z
preservation (TCase (TSucc v) z s) (CaseSucc value) = instantiateTyping s v
preservation (TFix b) Unfold = instantiateTyping b (TFix b)

public export
preservationMany : HasType gamma t a -> Steps t u -> HasType gamma u a
preservationMany p Done = p
preservationMany p (Next s ss) = preservationMany (preservation p s) ss
-- endregion preservation

-- region progress
public export
data Progress : Raw n -> Type where
  IsValue : Value t -> Progress t
  CanStep : (u : Raw n) -> Step t u -> Progress t

appProgress : (f, arg : Raw 0) -> HasType [] f (Arr a b) ->
  Value f -> Progress arg -> Progress (RApp f arg)
appProgress f arg pf vf (CanStep arg' s) = CanStep _ (AppR vf s)
appProgress (RLam body) arg (TLam pb) vf (IsValue va) = CanStep _ (Beta va)

caseProgress : (t, z : Raw 0) -> (s : Raw 1) ->
  HasType [] t TNat -> Value t -> Progress (RCase t z s)
caseProgress RZero z s TZero v = CanStep z CaseZero
caseProgress (RSucc t) z s (TSucc pt) (VSucc v) = CanStep _ (CaseSucc v)

public export
progress : (t : Raw 0) -> HasType [] t a -> Progress t
progress (RVar i) (TVar i) = absurd i
progress (RLam b) (TLam p) = IsValue VLam
progress (RApp f a) (TApp pf pa) = case progress f pf of
  CanStep f' s => CanStep _ (AppL s)
  IsValue vf => appProgress f a pf vf (progress a pa)
progress RZero TZero = IsValue VZero
progress (RSucc t) (TSucc p) = case progress t p of
  IsValue v => IsValue (VSucc v)
  CanStep u s => CanStep _ (SuccStep s)
progress (RCase t z s) (TCase pt pz ps) = case progress t pt of
  CanStep u p => CanStep _ (CaseStep p)
  IsValue v => caseProgress t z s pt v
progress (RFix b) (TFix p) = CanStep _ Unfold

public export
valueNormal : Value t -> Step t u -> Void
valueNormal VLam p impossible
valueNormal VZero p impossible
valueNormal (VSucc v) (SuccStep p) = valueNormal v p

public export
Normal : {n : Nat} -> Raw n -> Type
Normal t = (u : Raw n) -> Step t u -> Void

public export
normalTypedIsValue : (t : Raw 0) -> HasType [] t a -> Normal t -> Value t
normalTypedIsValue t p normal with (progress t p)
  normalTypedIsValue t p normal | IsValue v = v
  normalTypedIsValue t p normal | CanStep u s = void (normal u s)

public export
safety : (u : Raw 0) -> HasType [] t a -> Steps t u -> Normal u -> Value u
safety u p steps = normalTypedIsValue u (preservationMany p steps)
-- endregion progress

-- region determinism
public export
deterministic : Step t u -> Step t v -> u = v
deterministic (AppL p) (AppL q) = rewrite deterministic p q in Refl
deterministic (AppL p) (AppR v q) = void (valueNormal v p)
deterministic (AppL p) (Beta v) = void (valueNormal VLam p)
deterministic (AppR v p) (AppL q) = void (valueNormal v q)
deterministic (AppR v p) (AppR w q) = rewrite deterministic p q in Refl
deterministic (AppR v p) (Beta w) = void (valueNormal w p)
deterministic (Beta v) (AppL q) = void (valueNormal VLam q)
deterministic (Beta v) (AppR w q) = void (valueNormal v q)
deterministic (Beta v) (Beta w) = Refl
deterministic (SuccStep p) (SuccStep q) = cong RSucc (deterministic p q)
deterministic (CaseStep p) (CaseStep q) = rewrite deterministic p q in Refl
deterministic (CaseStep p) CaseZero = void (valueNormal VZero p)
deterministic (CaseStep p) (CaseSucc v) = void (valueNormal (VSucc v) p)
deterministic CaseZero (CaseStep q) = void (valueNormal VZero q)
deterministic CaseZero CaseZero = Refl
deterministic (CaseSucc v) (CaseStep q) = void (valueNormal (VSucc v) q)
deterministic (CaseSucc v) (CaseSucc w) = Refl
deterministic Unfold Unfold = Refl
-- endregion determinism

-- region evaluator
public export
data Finished : Raw n -> Type where
  OutOfFuel : Finished t
  ReachedValue : Value t -> Finished t

public export
data Evaluation : Raw n -> Type where
  Result : (u : Raw n) -> Steps t u -> Finished u -> Evaluation t

public export
evaluate : Nat -> (t : Raw 0) -> HasType [] t a -> Evaluation t
evaluate Z t p = Result t Done OutOfFuel
evaluate (S fuel) t p with (progress t p)
  evaluate (S fuel) t p | IsValue v = Result t Done (ReachedValue v)
  evaluate (S fuel) t p | CanStep u s with (evaluate fuel u (preservation p s))
    evaluate (S fuel) t p | CanStep u s | Result v ss end = Result v (Next s ss) end
-- endregion evaluator

-- region solutions
-- Exercise 1: general recursion permits divergence even at TNat.
public export
loop : Raw n
loop = RFix (RVar FZ)

public export
loopType : HasType gamma Properties.loop a
loopType {a} {gamma} = TFix {a} (TVar {gamma = a :: gamma} FZ)

public export
loopStep : Step (loop {n}) Properties.loop
loopStep = Unfold

-- Exercise 2: preserve a derivation across an actual evaluation trace.
public export
nestedIdentityType : HasType [] (numeral 2) TNat
nestedIdentityType = preservationMany
  (TApp identityType (TApp identityType (numeralType 2))) nestedIdentity

-- Exercise 3: normality and being a value differ on untyped terms.
public export
stuckNormal : Normal (RApp {n = 0} RZero RZero)
stuckNormal _ (AppL p) = valueNormal VZero p
stuckNormal _ (AppR v p) = valueNormal VZero p

public export
stuckNotValue : Value (RApp {n = 0} RZero RZero) -> Void
stuckNotValue v impossible
-- endregion solutions

-- region computations
public export
naturalValue : HasType gamma t TNat -> Value t -> Nat
naturalValue TZero VZero = Z
naturalValue (TSucc p) (VSucc v) = S (naturalValue p v)

public export
evaluateNatural : Nat -> (t : Raw 0) -> HasType [] t TNat -> Maybe Nat
evaluateNatural fuel t p = case evaluate fuel t p of
  Result u steps OutOfFuel => Nothing
  Result u steps (ReachedValue v) => Just (naturalValue (preservationMany p steps) v)

public export
additionResult : Maybe Nat
additionResult = evaluateNatural 80
  (RApp (RApp Lambda.plus (numeral 2)) (numeral 2))
  (TApp (TApp plusType (numeralType 2)) (numeralType 2))

public export
additionComputed : Properties.additionResult = Just 4
additionComputed = Refl

public export
multiplicationResult : Maybe Nat
multiplicationResult = evaluateNatural 200
  (RApp (RApp Lambda.multiply (numeral 3)) (numeral 2))
  (TApp (TApp multiplyType (numeralType 3)) (numeralType 2))

public export
multiplicationComputed : Properties.multiplicationResult = Just 6
multiplicationComputed = Refl

public export
loopExhausts : evaluateNatural 10 Properties.loop Properties.loopType = Nothing
loopExhausts = Refl
-- endregion computations

-- region expansion
public export
expansionSource : Raw 0
expansionSource = RCase RZero RZero (RApp RZero RZero)

public export
expansionStep : Step Properties.expansionSource RZero
expansionStep = CaseZero

public export
expansionUntypable : HasType [] Properties.expansionSource a -> Void
expansionUntypable (TCase TZero TZero (TApp TZero _)) impossible
-- endregion expansion
