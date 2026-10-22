module PLFA.Part2.More

%default total

-- region syntax
public export
data MTy = NatT | Arrow MTy MTy | PrimT | Product MTy MTy
         | Sum MTy MTy | UnitT | EmptyT | ListT MTy

public export
data Ref : (0 gamma : List MTy) -> (0 a : MTy) -> Type where
  MZ : Ref (a :: gamma) a
  MS : Ref gamma a -> Ref (b :: gamma) a

public export
data Term : (0 gamma : List MTy) -> (0 a : MTy) -> Type where
  MVar : Ref gamma a -> Term gamma a
  MLam : Term (a :: gamma) b -> Term gamma (Arrow a b)
  MApp : Term gamma (Arrow a b) -> Term gamma a -> Term gamma b
  MZero : Term gamma NatT
  MSucc : Term gamma NatT -> Term gamma NatT
  MCase : Term gamma NatT -> Term gamma a -> Term (NatT :: gamma) a -> Term gamma a
  MFix : Term (a :: gamma) a -> Term gamma a
  Lit : Nat -> Term gamma PrimT
  Times : Term gamma PrimT -> Term gamma PrimT -> Term gamma PrimT
  Let : Term gamma a -> Term (a :: gamma) b -> Term gamma b
  Pair : Term gamma a -> Term gamma b -> Term gamma (Product a b)
  Fst : Term gamma (Product a b) -> Term gamma a
  Snd : Term gamma (Product a b) -> Term gamma b
  Split : Term gamma (Product a b) -> Term (b :: a :: gamma) c -> Term gamma c
  InL : Term gamma a -> Term gamma (Sum a b)
  InR : Term gamma b -> Term gamma (Sum a b)
  SumCase : Term gamma (Sum a b) -> Term (a :: gamma) c -> Term (b :: gamma) c -> Term gamma c
  Unit : Term gamma UnitT
  UnitCase : Term gamma UnitT -> Term gamma a -> Term gamma a
  Absurd : Term gamma EmptyT -> Term gamma a
  Nil : Term gamma (ListT a)
  Cons : Term gamma a -> Term gamma (ListT a) -> Term gamma (ListT a)
  ListCase : Term gamma (ListT a) -> Term gamma b ->
             Term (ListT a :: a :: gamma) b -> Term gamma b
-- endregion syntax

-- region structural
public export
Ren : List MTy -> List MTy -> Type
Ren gamma delta = {0 ty : MTy} -> Ref gamma ty -> Ref delta ty

public export
extendRen : Ren gamma delta -> Ren (b :: gamma) (b :: delta)
extendRen rho MZ = MZ
extendRen rho (MS i) = MS (rho i)

public export
rename : Ren gamma delta -> Term gamma a -> Term delta a
rename rho (MVar i) = MVar (rho i)
rename rho (MLam b) = MLam (rename (extendRen rho) b)
rename rho (MApp f a) = MApp (rename rho f) (rename rho a)
rename rho MZero = MZero
rename rho (MSucc t) = MSucc (rename rho t)
rename rho (MCase t z s) = MCase (rename rho t) (rename rho z) (rename (extendRen rho) s)
rename rho (MFix b) = MFix (rename (extendRen rho) b)
rename rho (Lit n) = Lit n
rename rho (Times l r) = Times (rename rho l) (rename rho r)
rename rho (Let t b) = Let (rename rho t) (rename (extendRen rho) b)
rename rho (Pair l r) = Pair (rename rho l) (rename rho r)
rename rho (Fst p) = Fst (rename rho p)
rename rho (Snd p) = Snd (rename rho p)
rename rho (Split p b) = Split (rename rho p) (rename (extendRen (extendRen rho)) b)
rename rho (InL t) = InL (rename rho t)
rename rho (InR t) = InR (rename rho t)
rename rho (SumCase t l r) = SumCase (rename rho t)
  (rename (extendRen rho) l) (rename (extendRen rho) r)
rename rho Unit = Unit
rename rho (UnitCase t b) = UnitCase (rename rho t) (rename rho b)
rename rho (Absurd t) = Absurd (rename rho t)
rename rho Nil = Nil
rename rho (Cons h t) = Cons (rename rho h) (rename rho t)
rename rho (ListCase t n c) = ListCase (rename rho t) (rename rho n)
  (rename (extendRen (extendRen rho)) c)

public export
Sub : List MTy -> List MTy -> Type
Sub gamma delta = {0 ty : MTy} -> Ref gamma ty -> Term delta ty

public export
extendSub : Sub gamma delta -> Sub (b :: gamma) (b :: delta)
extendSub sigma MZ = MVar MZ
extendSub sigma (MS i) = rename MS (sigma i)

public export
subst : Sub gamma delta -> Term gamma a -> Term delta a
subst sigma (MVar i) = sigma i
subst sigma (MLam b) = MLam (subst (extendSub sigma) b)
subst sigma (MApp f a) = MApp (subst sigma f) (subst sigma a)
subst sigma MZero = MZero
subst sigma (MSucc t) = MSucc (subst sigma t)
subst sigma (MCase t z s) = MCase (subst sigma t) (subst sigma z) (subst (extendSub sigma) s)
subst sigma (MFix b) = MFix (subst (extendSub sigma) b)
subst sigma (Lit n) = Lit n
subst sigma (Times l r) = Times (subst sigma l) (subst sigma r)
subst sigma (Let t b) = Let (subst sigma t) (subst (extendSub sigma) b)
subst sigma (Pair l r) = Pair (subst sigma l) (subst sigma r)
subst sigma (Fst p) = Fst (subst sigma p)
subst sigma (Snd p) = Snd (subst sigma p)
subst sigma (Split p b) = Split (subst sigma p) (subst (extendSub (extendSub sigma)) b)
subst sigma (InL t) = InL (subst sigma t)
subst sigma (InR t) = InR (subst sigma t)
subst sigma (SumCase t l r) = SumCase (subst sigma t)
  (subst (extendSub sigma) l) (subst (extendSub sigma) r)
subst sigma Unit = Unit
subst sigma (UnitCase t b) = UnitCase (subst sigma t) (subst sigma b)
subst sigma (Absurd t) = Absurd (subst sigma t)
subst sigma Nil = Nil
subst sigma (Cons h t) = Cons (subst sigma h) (subst sigma t)
subst sigma (ListCase t n c) = ListCase (subst sigma t) (subst sigma n)
  (subst (extendSub (extendSub sigma)) c)

public export
single : Term gamma a -> Sub (a :: gamma) gamma
single arg MZ = arg
single arg (MS i) = MVar i

public export
inst : Term (a :: gamma) b -> Term gamma a -> Term gamma b
inst body arg = subst (single arg) body

public export
double : Term gamma a -> Term gamma b -> Sub (b :: a :: gamma) gamma
double first second MZ = second
double first second (MS MZ) = first
double first second (MS (MS i)) = MVar i

public export
inst2 : Term (b :: a :: gamma) c -> Term gamma a -> Term gamma b -> Term gamma c
inst2 body first second = subst (double first second) body
-- endregion structural

-- region dynamics
public export
data Value : Term gamma a -> Type where
  VLam : Value (MLam b)
  VZero : Value MZero
  VSucc : Value t -> Value (MSucc t)
  VPrim : Value (Lit n)
  VPair : Value l -> Value r -> Value (Pair l r)
  VInL : Value t -> Value (InL t)
  VInR : Value t -> Value (InR t)
  VUnit : Value Unit
  VNil : Value Nil
  VCons : Value h -> Value t -> Value (Cons h t)

public export
data Step : Term gamma a -> Term gamma a -> Type where
  AppL : Step f f' -> Step (MApp f arg) (MApp f' arg)
  AppR : {0 f : Term gamma (Arrow a b)} -> {0 arg, arg' : Term gamma a} ->
    Value f -> Step arg arg' -> Step (MApp f arg) (MApp f arg')
  Beta : {0 body : Term (a :: gamma) b} -> {0 v : Term gamma a} ->
    Value v -> Step (MApp (MLam body) v) (inst body v)
  SuccStep : Step t t' -> Step (MSucc t) (MSucc t')
  CaseStep : Step t t' -> Step (MCase t z s) (MCase t' z s)
  CaseZero : Step (MCase MZero z s) z
  CaseSucc : {0 v : Term gamma NatT} -> {0 z : Term gamma a} ->
    {0 s : Term (NatT :: gamma) a} ->
    Value v -> Step (MCase (MSucc v) z s) (inst s v)
  Unfold : Step (MFix b) (inst b (MFix b))
  TimesL : Step l l' -> Step (Times l r) (Times l' r)
  TimesR : Value l -> Step r r' -> Step (Times l r) (Times l r')
  Multiply : Step (Times (Lit m) (Lit n)) (Lit (m * n))
  LetStep : Step t t' -> Step (Let t b) (Let t' b)
  LetBeta : {0 v : Term gamma a} -> {0 b : Term (a :: gamma) c} ->
    Value v -> Step (Let v b) (inst b v)
  PairL : Step l l' -> Step (Pair l r) (Pair l' r)
  PairR : {0 l : Term gamma a} -> {0 r, r' : Term gamma b} ->
    Value l -> Step r r' -> Step (Pair l r) (Pair l r')
  FstStep : Step p p' -> Step (Fst p) (Fst p')
  SndStep : Step p p' -> Step (Snd p) (Snd p')
  FstBeta : {0 l : Term gamma a} -> {0 r : Term gamma b} ->
    Value l -> Value r -> Step (Fst (Pair l r)) l
  SndBeta : {0 l : Term gamma a} -> {0 r : Term gamma b} ->
    Value l -> Value r -> Step (Snd (Pair l r)) r
  SplitStep : Step p p' -> Step (Split p b) (Split p' b)
  SplitBeta : {0 l : Term gamma a} -> {0 r : Term gamma b} ->
    {0 body : Term (b :: a :: gamma) c} ->
    Value l -> Value r -> Step (Split (Pair l r) body) (inst2 body l r)
  InLStep : Step t t' -> Step (InL t) (InL t')
  InRStep : Step t t' -> Step (InR t) (InR t')
  SumStep : Step t t' -> Step (SumCase t l r) (SumCase t' l r)
  SumLeft : {0 v : Term gamma a} -> {0 l : Term (a :: gamma) c} ->
    {0 r : Term (b :: gamma) c} -> Value v -> Step (SumCase (InL v) l r) (inst l v)
  SumRight : {0 v : Term gamma b} -> {0 l : Term (a :: gamma) c} ->
    {0 r : Term (b :: gamma) c} -> Value v -> Step (SumCase (InR v) l r) (inst r v)
  UnitStep : Step t t' -> Step (UnitCase t b) (UnitCase t' b)
  UnitBeta : Step (UnitCase Unit b) b
  AbsurdStep : Step t t' -> Step (Absurd t) (Absurd t')
  ConsL : Step h h' -> Step (Cons h t) (Cons h' t)
  ConsR : {0 h : Term gamma a} -> {0 t, t' : Term gamma (ListT a)} ->
    Value h -> Step t t' -> Step (Cons h t) (Cons h t')
  ListStep : Step t t' -> Step (ListCase t n c) (ListCase t' n c)
  ListNil : Step (ListCase Nil n c) n
  ListCons : {0 h : Term gamma a} -> {0 t : Term gamma (ListT a)} ->
    {0 n : Term gamma b} -> {0 c : Term (ListT a :: a :: gamma) b} ->
    Value h -> Value t -> Step (ListCase (Cons h t) n c) (inst2 c h t)
-- endregion dynamics

-- region progress
public export
data Progress : Term gamma a -> Type where
  Val : Value t -> Progress t
  Red : (u : Term gamma a) -> Step t u -> Progress t

appReady : (f : Term [] (Arrow a b)) -> (arg : Term [] a) ->
  Value f -> Progress arg -> Progress (MApp f arg)
appReady f arg vf (Red arg' s) = Red _ (AppR vf s)
appReady (MLam b) arg vf (Val va) = Red _ (Beta va)

caseReady : (t : Term [] NatT) -> (z : Term [] a) -> (s : Term [NatT] a) ->
  Value t -> Progress (MCase t z s)
caseReady MZero z s v = Red z CaseZero
caseReady (MSucc t) z s (VSucc v) = Red _ (CaseSucc v)

timesReady : (l, r : Term [] PrimT) -> Value l -> Progress r -> Progress (Times l r)
timesReady l r vl (Red r' s) = Red _ (TimesR vl s)
timesReady (Lit m) (Lit n) vl (Val vr) = Red _ Multiply

pairReady : (l : Term [] a) -> (r : Term [] b) -> Value l -> Progress r -> Progress (Pair l r)
pairReady l r vl (Red r' s) = Red _ (PairR vl s)
pairReady l r vl (Val vr) = Val (VPair vl vr)

fstReady : (p : Term [] (Product a b)) -> Value p -> Progress (Fst p)
fstReady (Pair l r) (VPair vl vr) = Red l (FstBeta vl vr)

sndReady : (p : Term [] (Product a b)) -> Value p -> Progress (Snd p)
sndReady (Pair l r) (VPair vl vr) = Red r (SndBeta vl vr)

splitReady : (p : Term [] (Product a b)) -> (body : Term [b, a] c) ->
  Value p -> Progress (Split p body)
splitReady (Pair l r) body (VPair vl vr) = Red _ (SplitBeta vl vr)

sumReady : (t : Term [] (Sum a b)) -> (l : Term [a] c) -> (r : Term [b] c) ->
  Value t -> Progress (SumCase t l r)
sumReady (InL v) l r (VInL vv) = Red _ (SumLeft vv)
sumReady (InR v) l r (VInR vv) = Red _ (SumRight vv)

unitReady : (t : Term [] UnitT) -> (b : Term [] a) -> Value t -> Progress (UnitCase t b)
unitReady Unit b v = Red b UnitBeta

emptyValue : (t : Term [] EmptyT) -> Value t -> Void
emptyValue t v impossible

consReady : (h : Term [] a) -> (t : Term [] (ListT a)) -> Value h -> Progress t -> Progress (Cons h t)
consReady h t vh (Red t' s) = Red _ (ConsR vh s)
consReady h t vh (Val vt) = Val (VCons vh vt)

listReady : (t : Term [] (ListT a)) -> (n : Term [] b) -> (c : Term [ListT a, a] b) ->
  Value t -> Progress (ListCase t n c)
listReady Nil n c v = Red n ListNil
listReady (Cons h t) n c (VCons vh vt) = Red _ (ListCons vh vt)

public export
progress : (t : Term [] a) -> Progress t
progress (MVar MZ) impossible
progress (MVar (MS i)) impossible
progress (MLam b) = Val VLam
progress (MApp f a) = case progress f of
  Red f' s => Red _ (AppL s)
  Val vf => appReady f a vf (progress a)
progress MZero = Val VZero
progress (MSucc t) = case progress t of
  Red u s => Red _ (SuccStep s)
  Val v => Val (VSucc v)
progress (MCase t z s) = case progress t of
  Red u p => Red _ (CaseStep p)
  Val v => caseReady t z s v
progress (MFix b) = Red _ Unfold
progress (Lit n) = Val VPrim
progress (Times l r) = case progress l of
  Red l' s => Red _ (TimesL s)
  Val vl => timesReady l r vl (progress r)
progress (Let t b) = case progress t of
  Red u s => Red _ (LetStep s)
  Val v => Red _ (LetBeta v)
progress (Pair l r) = case progress l of
  Red l' s => Red _ (PairL s)
  Val vl => pairReady l r vl (progress r)
progress (Fst p) = case progress p of
  Red q s => Red _ (FstStep s)
  Val v => fstReady p v
progress (Snd p) = case progress p of
  Red q s => Red _ (SndStep s)
  Val v => sndReady p v
progress (Split p b) = case progress p of
  Red q s => Red _ (SplitStep s)
  Val v => splitReady p b v
progress (InL t) = case progress t of
  Red u s => Red _ (InLStep s)
  Val v => Val (VInL v)
progress (InR t) = case progress t of
  Red u s => Red _ (InRStep s)
  Val v => Val (VInR v)
progress (SumCase t l r) = case progress t of
  Red u s => Red _ (SumStep s)
  Val v => sumReady t l r v
progress Unit = Val VUnit
progress (UnitCase t b) = case progress t of
  Red u s => Red _ (UnitStep s)
  Val v => unitReady t b v
progress (Absurd t) = case progress t of
  Red u s => Red _ (AbsurdStep s)
  Val v => void (emptyValue t v)
progress Nil = Val VNil
progress (Cons h t) = case progress h of
  Red h' s => Red _ (ConsL s)
  Val vh => consReady h t vh (progress t)
progress (ListCase t n c) = case progress t of
  Red u s => Red _ (ListStep s)
  Val v => listReady t n c v
-- endregion progress

-- region evaluation
public export
data Steps : Term gamma a -> Term gamma a -> Type where
  Done : Steps t t
  Next : Step t u -> Steps u v -> Steps t v

public export
data Finished : Term gamma a -> Type where
  OutOfFuel : Finished t
  Returned : Value t -> Finished t

public export
data Evaluation : Term gamma a -> Type where
  Result : (u : Term gamma a) -> Steps t u -> Finished u -> Evaluation t

public export
evaluate : Nat -> (t : Term [] a) -> Evaluation t
evaluate Z t = Result t Done OutOfFuel
evaluate (S fuel) t with (progress t)
  evaluate (S fuel) t | Val v = Result t Done (Returned v)
  evaluate (S fuel) t | Red u s with (evaluate fuel u)
    evaluate (S fuel) t | Red u s | Result v ss end = Result v (Next s ss) end
-- endregion evaluation

-- region examples
public export
cube : Term gamma (Arrow PrimT PrimT)
cube = MLam (Let (Times (MVar MZ) (MVar MZ))
                (Times (MVar MZ) (MVar (MS MZ))))

public export
lengthList : Term gamma (Arrow (ListT a) NatT)
lengthList = MFix (MLam
  (ListCase (MVar MZ) MZero
    (MSucc (MApp (MVar (MS (MS (MS MZ)))) (MVar MZ)))))

public export
cubeTwo : Steps (MApp (cube {gamma = []}) (Lit 2)) (Lit 8)
cubeTwo = Next (Beta VPrim)
  (Next (LetStep Multiply) (Next (LetBeta VPrim) (Next Multiply Done)))

public export
swapPair : Term gamma (Arrow (Product a b) (Product b a))
swapPair = MLam (Split (MVar MZ) (Pair (MVar MZ) (MVar (MS MZ))))
-- endregion examples

-- region solutions
-- Exercise 1: distinguish the two binders of a product eliminator.
public export
splitOrder : Step
  (Split (Pair (Lit {gamma = []} 3) (Lit 5)) (Times (MVar (MS MZ)) (MVar MZ)))
  (Times (Lit 3) (Lit 5))
splitOrder = SplitBeta VPrim VPrim

-- Exercise 2: the chosen sum branch is instantiated; the other is ignored.
public export
sumChoice : Step
  (SumCase (the (Term [] (Sum PrimT UnitT)) (InL (Lit 7)))
           (Times (MVar MZ) (Lit 2)) (Lit 0))
  (Times (Lit 7) (Lit 2))
sumChoice = SumLeft VPrim

-- Exercise 3: list case replaces head and tail simultaneously.
public export
listHead : Step
  (ListCase (Cons (Lit {gamma = []} 9) Nil) (Lit 0) (MVar (MS MZ)))
  (Lit 9)
listHead = ListCons VPrim VNil
-- endregion solutions

-- region value-normal
public export
valueNormal : Value t -> Step t u -> Void
valueNormal VLam p impossible
valueNormal VZero p impossible
valueNormal (VSucc v) (SuccStep p) = valueNormal v p
valueNormal VPrim p impossible
valueNormal (VPair vl vr) (PairL p) = valueNormal vl p
valueNormal (VPair vl vr) (PairR v p) = valueNormal vr p
valueNormal (VInL v) (InLStep p) = valueNormal v p
valueNormal (VInR v) (InRStep p) = valueNormal v p
valueNormal VUnit p impossible
valueNormal VNil p impossible
valueNormal (VCons vh vt) (ConsL p) = valueNormal vh p
valueNormal (VCons vh vt) (ConsR v p) = valueNormal vt p
-- endregion value-normal

-- region computations
public export
primitiveValue : (t : Term gamma PrimT) -> Value t -> Nat
primitiveValue (Lit k) v = k

public export
runPrimitive : Nat -> Term [] PrimT -> Maybe Nat
runPrimitive fuel t = case evaluate fuel t of
  Result u steps OutOfFuel => Nothing
  Result u steps (Returned v) => Just (primitiveValue u v)

public export
cubeResult : Maybe Nat
cubeResult = runPrimitive 20 (MApp cube (Lit 2))

public export
cubeComputed : More.cubeResult = Just 8
cubeComputed = Refl

public export
unaryValue : {0 t : Term gamma NatT} -> Value t -> Nat
unaryValue VZero = Z
unaryValue (VSucc v) = S (unaryValue v)

public export
runUnary : Nat -> Term [] NatT -> Maybe Nat
runUnary fuel t = case evaluate fuel t of
  Result u steps OutOfFuel => Nothing
  Result u steps (Returned v) => Just (unaryValue v)

public export
lengthResult : Maybe Nat
lengthResult = runUnary 100 (MApp lengthList (Cons (Lit 3) (Cons (Lit 5) Nil)))

public export
lengthComputed : More.lengthResult = Just 2
lengthComputed = Refl
-- endregion computations

-- region empty-loop
public export
emptyLoop : Term [] EmptyT
emptyLoop = MFix (MVar MZ)

public export
emptyLoopStep : Step More.emptyLoop More.emptyLoop
emptyLoopStep = Unfold
-- endregion empty-loop
