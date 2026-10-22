module PLFA.Part2.Bisimulation

import public PLFA.Part2.More

%default total

-- region relation
public export
data Related : Term gamma a -> Term gamma a -> Type where
  RVar : (i : Ref gamma a) -> Related (MVar i) (MVar i)
  RLam : Related b b' -> Related (MLam b) (MLam b')
  RApp : {0 f, f' : Term gamma (Arrow a b)} ->
    {0 arg, arg' : Term gamma a} ->
    Related f f' -> Related arg arg' -> Related (MApp f arg) (MApp f' arg')
  RLet : {0 arg, arg' : Term gamma a} ->
    {0 body, body' : Term (a :: gamma) b} ->
    Related arg arg' -> Related body body' ->
    Related (Let arg body) (MApp (MLam body') arg')

public export
data Fragment : Term gamma a -> Type where
  FVar : (i : Ref gamma a) -> Fragment (MVar i)
  FLam : Fragment b -> Fragment (MLam b)
  FApp : {0 f : Term gamma (Arrow a b)} -> {0 arg : Term gamma a} ->
    Fragment f -> Fragment arg -> Fragment (MApp f arg)
  FLet : {0 arg : Term gamma a} -> {0 b : Term (a :: gamma) c} ->
    Fragment arg -> Fragment b -> Fragment (Let arg b)

public export
compile : Fragment s -> (t : Term gamma a ** Related s t)
compile (FVar i) = (MVar i ** RVar i)
compile (FLam b) = case compile b of
  (t ** related) => (MLam t ** RLam related)
compile (FApp f arg) = case (compile f, compile arg) of
  ((f' ** rf), (arg' ** ra)) => (MApp f' arg' ** RApp rf ra)
compile (FLet arg b) = case (compile arg, compile b) of
  ((arg' ** ra), (b' ** rb)) => (MApp (MLam b') arg' ** RLet ra rb)

public export
relatedFunctional : Related s t -> Related s u -> t = u
relatedFunctional (RVar i) (RVar i) = Refl
relatedFunctional (RLam p) (RLam q) = rewrite relatedFunctional p q in Refl
relatedFunctional (RApp f a) (RApp g b) =
  rewrite relatedFunctional f g in rewrite relatedFunctional a b in Refl
relatedFunctional (RLet a b) (RLet c d) =
  rewrite relatedFunctional a c in rewrite relatedFunctional b d in Refl
-- endregion relation

-- region compatibility
public export
valueForward : Related s t -> Value s -> Value t
valueForward (RVar i) v impossible
valueForward (RLam p) VLam = VLam
valueForward (RApp f a) v impossible
valueForward (RLet a b) v impossible

public export
valueBackward : Related s t -> Value t -> Value s
valueBackward (RVar i) v impossible
valueBackward (RLam p) VLam = VLam
valueBackward (RApp f a) v impossible
valueBackward (RLet a b) v impossible

public export
renameRelated : (rho : Ren gamma delta) -> Related s t ->
  Related (rename rho s) (rename rho t)
renameRelated rho (RVar i) = RVar (rho i)
renameRelated rho (RLam p) = RLam (renameRelated (extendRen rho) p)
renameRelated rho (RApp f a) = RApp (renameRelated rho f) (renameRelated rho a)
renameRelated rho (RLet a b) = RLet (renameRelated rho a) (renameRelated (extendRen rho) b)

public export
extendRelated : {0 sigma, tau : Sub gamma delta} ->
  ({0 ty : MTy} -> (i : Ref gamma ty) -> Related (sigma i) (tau i)) ->
  {0 ty : MTy} -> (i : Ref (b :: gamma) ty) ->
  Related (extendSub sigma i) (extendSub tau i)
extendRelated good MZ = RVar MZ
extendRelated good (MS i) = renameRelated MS (good i)

public export
substRelated : {0 sigma, tau : Sub gamma delta} ->
  ({0 ty : MTy} -> (i : Ref gamma ty) -> Related (sigma i) (tau i)) ->
  Related s t -> Related (subst sigma s) (subst tau t)
substRelated good (RVar i) = good i
substRelated good (RLam p) = RLam (substRelated (extendRelated good) p)
substRelated good (RApp f a) = RApp (substRelated good f) (substRelated good a)
substRelated good (RLet a b) = RLet (substRelated good a) (substRelated (extendRelated good) b)

public export
singleRelated : Related v w -> {0 ty : MTy} -> (i : Ref (a :: gamma) ty) ->
  Related (single v i) (single w i)
singleRelated r MZ = r
singleRelated r (MS i) = RVar i

public export
instRelated : Related body body' -> Related arg arg' ->
  Related (inst body arg) (inst body' arg')
instRelated b a = substRelated (singleRelated a) b
-- endregion compatibility

-- region forward
public export
data ForwardLeg : Term gamma a -> Term gamma a -> Type where
  Forward : {0 target : Term gamma a} ->
    Related result target -> Step start target -> ForwardLeg start result

public export
forward : Related s t -> Step s u -> ForwardLeg t u
forward (RVar i) p impossible
forward (RLam b) p impossible
forward (RApp f a) (AppL p) with (forward f p)
  forward (RApp f a) (AppL p) | Forward rf q = Forward (RApp rf a) (AppL q)
forward (RApp f a) (AppR vf p) with (forward a p)
  forward (RApp f a) (AppR vf p) | Forward ra q =
    Forward (RApp f ra) (AppR (valueForward f vf) q)
forward (RApp (RLam b) a) (Beta va) =
  Forward (instRelated b a) (Beta (valueForward a va))
forward (RLet a b) (LetStep p) with (forward a p)
  forward (RLet a b) (LetStep p) | Forward ra q =
    Forward (RLet ra b) (AppR VLam q)
forward (RLet a b) (LetBeta va) =
  Forward (instRelated b a) (Beta (valueForward a va))
-- endregion forward

-- region backward
public export
data BackwardLeg : Term gamma a -> Term gamma a -> Type where
  Backward : {0 source : Term gamma a} ->
    Related source result -> Step start source -> BackwardLeg start result

public export
backward : Related s t -> Step t u -> BackwardLeg s u
backward (RVar i) p impossible
backward (RLam b) p impossible
backward (RApp f a) (AppL q) with (backward f q)
  backward (RApp f a) (AppL q) | Backward rf p = Backward (RApp rf a) (AppL p)
backward (RApp f a) (AppR vf q) with (backward a q)
  backward (RApp f a) (AppR vf q) | Backward ra p =
    Backward (RApp f ra) (AppR (valueBackward f vf) p)
backward (RApp (RLam b) a) (Beta va) =
  Backward (instRelated b a) (Beta (valueBackward a va))
backward (RLet a b) (AppL q) impossible
backward (RLet a b) (AppR vf q) with (backward a q)
  backward (RLet a b) (AppR vf q) | Backward ra p =
    Backward (RLet ra b) (LetStep p)
backward (RLet a b) (Beta va) =
  Backward (instRelated b a) (LetBeta (valueBackward a va))
-- endregion backward

-- region traces
public export
data ForwardTrace : Term gamma a -> Term gamma a -> Type where
  FTrace : {0 target : Term gamma a} ->
    Related result target -> Steps start target -> ForwardTrace start result

public export
forwardMany : Related s t -> Steps s u -> ForwardTrace t u
forwardMany r Done = FTrace r Done
forwardMany r (Next p ps) with (forward r p)
  forwardMany r (Next p ps) | Forward r' q with (forwardMany r' ps)
    forwardMany r (Next p ps) | Forward r' q | FTrace r'' qs = FTrace r'' (Next q qs)

public export
data BackwardTrace : Term gamma a -> Term gamma a -> Type where
  BTrace : {0 source : Term gamma a} ->
    Related source result -> Steps start source -> BackwardTrace start result

public export
backwardMany : Related s t -> Steps t u -> BackwardTrace s u
backwardMany r Done = BTrace r Done
backwardMany r (Next q qs) with (backward r q)
  backwardMany r (Next q qs) | Backward r' p with (backwardMany r' qs)
    backwardMany r (Next q qs) | Backward r' p | BTrace r'' ps = BTrace r'' (Next p ps)
-- endregion traces

-- region examples
public export
letIdentity : Term [] (Arrow PrimT PrimT)
letIdentity = Let (MLam (MVar MZ)) (MVar MZ)

public export
compiledIdentity : Term [] (Arrow PrimT PrimT)
compiledIdentity = MApp (MLam (MVar MZ)) (MLam (MVar MZ))

public export
exampleRelated : Related Bisimulation.letIdentity Bisimulation.compiledIdentity
exampleRelated = RLet (RLam (RVar MZ)) (RVar MZ)

public export
exampleStep : ForwardLeg Bisimulation.compiledIdentity (MLam (MVar MZ))
exampleStep = forward exampleRelated (LetBeta VLam)
-- endregion examples

-- region solutions
-- Exercise 1: an actual compilation certificate for a nested let.
public export
nestedLet : Term [] (Arrow PrimT PrimT)
nestedLet = Let (MLam (MVar MZ)) (Let (MVar MZ) (MVar MZ))

public export
nestedFragment : Fragment Bisimulation.nestedLet
nestedFragment = FLet (FLam (FVar MZ)) (FLet (FVar MZ) (FVar MZ))

public export
nestedCompilation : (t : Term [] (Arrow PrimT PrimT) ** Related Bisimulation.nestedLet t)
nestedCompilation = compile nestedFragment

-- Exercise 2: the reverse direction transports a target beta step.
public export
reverseExample : BackwardLeg Bisimulation.letIdentity (MLam (MVar MZ))
reverseExample = backward exampleRelated (Beta VLam)

-- Exercise 3: source terms in this fragment can be recovered from a relation.
public export
relatedFragment : Related s t -> Fragment s
relatedFragment (RVar i) = FVar i
relatedFragment (RLam p) = FLam (relatedFragment p)
relatedFragment (RApp f a) = FApp (relatedFragment f) (relatedFragment a)
relatedFragment (RLet a b) = FLet (relatedFragment a) (relatedFragment b)
-- endregion solutions

-- region graph
public export
compiledMatches : (fragment : Fragment s) -> Related s t -> fst (compile fragment) = t
compiledMatches fragment related with (compile fragment)
  compiledMatches fragment related | (compiled ** certificate) = relatedFunctional certificate related
-- endregion graph
