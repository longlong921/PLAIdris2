module PLFA.Part2.DeBruijn

import public PLFA.Part2.Typed

%default total

-- region intrinsic
public export
data Ref : {0 n : Nat} -> (0 gamma : Context n) -> (0 a : Ty) -> Type where
  At : (i : Fin n) -> Ref gamma (index i gamma)

public export
vz : Ref (a :: gamma) a
vz = At FZ

public export
vs : Ref gamma a -> Ref (b :: gamma) a
vs (At i) = At (FS i)

public export
data Term : {0 n : Nat} -> (0 gamma : Context n) -> (0 a : Ty) -> Type where
  Var  : Ref gamma a -> Term gamma a
  Lam  : Term (a :: gamma) b -> Term gamma (Arr a b)
  App  : Term gamma (Arr a b) -> Term gamma a -> Term gamma b
  Zero : Term gamma TNat
  Succ : Term gamma TNat -> Term gamma TNat
  Case : Term gamma TNat -> Term gamma a -> Term (TNat :: gamma) a -> Term gamma a
  Fix  : Term (a :: gamma) a -> Term gamma a
-- endregion intrinsic

-- region renaming
public export
TRen : Context n -> Context m -> Type
TRen gamma delta = {0 ty : Ty} -> Ref gamma ty -> Ref delta ty

public export
extendRen : TRen gamma delta -> TRen (b :: gamma) (b :: delta)
extendRen rho (At FZ) = vz
extendRen rho (At (FS i)) = vs (rho (At i))

public export
renameTerm : TRen gamma delta -> Term gamma a -> Term delta a
renameTerm rho (Var i) = Var (rho i)
renameTerm rho (Lam b) = Lam (renameTerm (extendRen rho) b)
renameTerm rho (App f a) = App (renameTerm rho f) (renameTerm rho a)
renameTerm rho Zero = Zero
renameTerm rho (Succ t) = Succ (renameTerm rho t)
renameTerm rho (Case t z s) = Case (renameTerm rho t) (renameTerm rho z) (renameTerm (extendRen rho) s)
renameTerm rho (Fix b) = Fix (renameTerm (extendRen rho) b)
-- endregion renaming

-- region substitution
public export
TSub : Context n -> Context m -> Type
TSub gamma delta = {0 ty : Ty} -> Ref gamma ty -> Term delta ty

public export
extendSub : TSub gamma delta -> TSub (b :: gamma) (b :: delta)
extendSub sigma (At FZ) = Var vz
extendSub sigma (At (FS i)) = renameTerm vs (sigma (At i))

public export
substTerm : TSub gamma delta -> Term gamma a -> Term delta a
substTerm sigma (Var i) = sigma i
substTerm sigma (Lam b) = Lam (substTerm (extendSub sigma) b)
substTerm sigma (App f a) = App (substTerm sigma f) (substTerm sigma a)
substTerm sigma Zero = Zero
substTerm sigma (Succ t) = Succ (substTerm sigma t)
substTerm sigma (Case t z s) = Case (substTerm sigma t) (substTerm sigma z) (substTerm (extendSub sigma) s)
substTerm sigma (Fix b) = Fix (substTerm (extendSub sigma) b)

public export
replace : Term gamma a -> TSub (a :: gamma) gamma
replace arg (At FZ) = arg
replace arg (At (FS i)) = Var (At i)

public export
instantiateTerm : Term (a :: gamma) b -> Term gamma a -> Term gamma b
instantiateTerm body arg = substTerm (replace arg) body
-- endregion substitution

-- region dynamics
public export
data Value : Term gamma a -> Type where
  IsLam : Value (Lam b)
  IsZero : Value Zero
  IsSucc : Value t -> Value (Succ t)

public export
data Step : Term gamma a -> Term gamma a -> Type where
  SAppL : {0 gamma : Context n} -> {0 a, b : Ty} ->
    {0 f, f' : Term gamma (Arr a b)} -> {0 arg : Term gamma a} ->
    Step f f' -> Step (App f arg) (App f' arg)
  SAppR : {0 gamma : Context n} -> {0 a, b : Ty} ->
    {0 f : Term gamma (Arr a b)} -> {0 arg, arg' : Term gamma a} ->
    Value f -> Step arg arg' -> Step (App f arg) (App f arg')
  SBeta : {0 gamma : Context n} -> {0 a, b : Ty} ->
    {0 body : Term (a :: gamma) b} -> {0 v : Term gamma a} ->
    Value v -> Step (App (Lam body) v) (instantiateTerm body v)
  SSucc : Step t t' -> Step (Succ t) (Succ t')
  SCase : {0 gamma : Context n} -> {0 a : Ty} ->
    {0 t, t' : Term gamma TNat} -> {0 z : Term gamma a} ->
    {0 s : Term (TNat :: gamma) a} ->
    Step t t' -> Step (Case t z s) (Case t' z s)
  SZero : Step (Case Zero z s) z
  SSuc : {0 gamma : Context n} -> {0 a : Ty} ->
    {0 v : Term gamma TNat} -> {0 z : Term gamma a} ->
    {0 s : Term (TNat :: gamma) a} ->
    Value v -> Step (Case (Succ v) z s) (instantiateTerm s v)
  SFix : Step (Fix b) (instantiateTerm b (Fix b))

public export
data Progress : Term gamma a -> Type where
  Val : Value t -> Progress t
  Red : (u : Term gamma a) -> Step t u -> Progress t

public export
appProgress : (f : Term [] (Arr a b)) -> (arg : Term [] a) ->
  Value f -> Progress arg -> Progress (App f arg)
appProgress f arg vf (Red arg' s) = Red _ (SAppR vf s)
appProgress (Lam body) arg vf (Val va) = Red _ (SBeta va)

public export
caseProgress : (t : Term [] TNat) -> (z : Term [] a) ->
  (s : Term [TNat] a) -> Value t -> Progress (Case t z s)
caseProgress Zero z s v = Red z SZero
caseProgress (Succ t) z s (IsSucc v) = Red _ (SSuc v)

public export
progress : (t : Term [] a) -> Progress t
progress (Var (At i)) = absurd i
progress (Lam b) = Val IsLam
progress (App f a) = case progress f of
  Red f' s => Red _ (SAppL s)
  Val vf => appProgress f a vf (progress a)
progress Zero = Val IsZero
progress (Succ t) = case progress t of
  Val v => Val (IsSucc v)
  Red u s => Red _ (SSucc s)
progress (Case t z s) = case progress t of
  Red u p => Red _ (SCase p)
  Val v => caseProgress t z s v
progress (Fix b) = Red _ SFix

public export
data Steps : Term gamma a -> Term gamma a -> Type where
  ReflSteps : Steps t t
  MoreSteps : Step t u -> Steps u v -> Steps t v

public export
data Finished : Term gamma a -> Type where
  Exhausted : Finished t
  Returned : Value t -> Finished t

public export
data Run : Term gamma a -> Type where
  Ran : (u : Term gamma a) -> Steps t u -> Finished u -> Run t

public export
run : Nat -> (t : Term [] a) -> Run t
run Z t = Ran t ReflSteps Exhausted
run (S fuel) t with (progress t)
  run (S fuel) t | Val v = Ran t ReflSteps (Returned v)
  run (S fuel) t | Red u s with (run fuel u)
    run (S fuel) t | Red u s | Ran v ss end = Ran v (MoreSteps s ss) end
-- endregion dynamics

-- region correspondence
public export
indexRef : {0 gamma : Context n} -> (i : Fin n) ->
  Ref gamma (index i gamma)
indexRef = At

public export
elaborate : HasType gamma t a -> Term gamma a
elaborate (TVar i) = Var (indexRef i)
elaborate (TLam b) = Lam (elaborate b)
elaborate (TApp f a) = App (elaborate f) (elaborate a)
elaborate TZero = Zero
elaborate (TSucc t) = Succ (elaborate t)
elaborate (TCase t z s) = Case (elaborate t) (elaborate z) (elaborate s)
elaborate (TFix b) = Fix (elaborate b)
-- endregion correspondence

-- region examples
public export
num : Nat -> Term gamma TNat
num Z = Zero
num (S n) = Succ (num n)

public export
add : Term gamma (Arr TNat (Arr TNat TNat))
add = Fix (Lam (Lam
  (Case (Var (vs DeBruijn.vz)) (Var vz)
    (Succ (App (App (Var (vs (vs (vs DeBruijn.vz)))) (Var vz)) (Var (vs DeBruijn.vz)))))))

public export
multiplication : Term gamma (Arr TNat (Arr TNat TNat))
multiplication = Fix (Lam (Lam
  (Case (Var (vs DeBruijn.vz)) Zero
    (App (App add (Var (vs DeBruijn.vz)))
      (App (App (Var (vs (vs (vs DeBruijn.vz)))) (Var vz)) (Var (vs DeBruijn.vz)))))))

public export
churchTwo : Term gamma (Arr (Arr a a) (Arr a a))
churchTwo = Lam (Lam (App (Var (vs DeBruijn.vz)) (App (Var (vs DeBruijn.vz)) (Var vz))))
-- endregion examples

-- region solutions
-- Exercise 1: capture avoidance underneath a binder.
public export
captureAvoidance : instantiateTerm
  (the (Term (TNat :: [TNat]) (Arr TNat TNat)) (Lam (Var (vs DeBruijn.vz))))
  (Var DeBruijn.vz) = Lam (Var (vs DeBruijn.vz))
captureAvoidance = Refl

-- Exercise 2: closed identity executes in one CBV step.
public export
identityStep : Step (App (Lam (Var DeBruijn.vz)) (num {gamma = []} 2)) (num 2)
identityStep = SBeta (IsSucc (IsSucc IsZero))

-- Exercise 3: values admit no outgoing steps, for any context and type.
public export
valueNormal : Value t -> Step t u -> Void
valueNormal IsLam p impossible
valueNormal IsZero p impossible
valueNormal (IsSucc v) (SSucc p) = valueNormal v p
-- endregion solutions

-- region erasure
public export
forget : {0 gamma : Context n} -> Term gamma a -> Raw n
forget (Var (At i)) = RVar i
forget (Lam b) = RLam (forget b)
forget (App f a) = RApp (forget f) (forget a)
forget Zero = RZero
forget (Succ t) = RSucc (forget t)
forget (Case t z s) = RCase (forget t) (forget z) (forget s)
forget (Fix b) = RFix (forget b)

public export
forgetElaborate : (p : HasType gamma t a) -> forget (elaborate p) = t
forgetElaborate (TVar i) = Refl
forgetElaborate (TLam b) = rewrite forgetElaborate b in Refl
forgetElaborate (TApp f a) = rewrite forgetElaborate f in rewrite forgetElaborate a in Refl
forgetElaborate TZero = Refl
forgetElaborate (TSucc t) = rewrite forgetElaborate t in Refl
forgetElaborate (TCase t z s) = rewrite forgetElaborate t in
  rewrite forgetElaborate z in rewrite forgetElaborate s in Refl
forgetElaborate (TFix b) = rewrite forgetElaborate b in Refl
-- endregion erasure

-- region computations
public export
naturalValue : {0 t : Term gamma TNat} -> Value t -> Nat
naturalValue IsZero = Z
naturalValue (IsSucc v) = S (naturalValue v)

public export
runNatural : Nat -> Term [] TNat -> Maybe Nat
runNatural fuel t = case run fuel t of
  Ran u steps Exhausted => Nothing
  Ran u steps (Returned v) => Just (naturalValue v)

public export
additionResult : Maybe Nat
additionResult = runNatural 80 (App (App add (num 2)) (num 2))

public export
additionComputed : DeBruijn.additionResult = Just 4
additionComputed = Refl

public export
multiplicationResult : Maybe Nat
multiplicationResult = runNatural 200 (App (App multiplication (num 3)) (num 2))

public export
multiplicationComputed : DeBruijn.multiplicationResult = Just 6
multiplicationComputed = Refl
-- endregion computations
