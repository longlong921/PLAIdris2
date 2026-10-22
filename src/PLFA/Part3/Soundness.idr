module PLFA.Part3.Soundness

import public PLFA.Part3.Compositional
import Decidable.Equality

%default total
%unbound_implicits off

-- region substitution-preservation
public export
SubDenote : {m, n : Nat} -> Env n -> (Fin m -> Tm n) -> Env m -> Type
SubDenote delta sigma gamma = (x : Fin m) -> Denote delta (sigma x) (gamma x)

public export
substExtension : {m, n : Nat} -> {a : Value} -> {gamma : Env m} -> {delta : Env n} ->
  (sigma : Fin m -> Tm n) -> SubDenote delta sigma gamma ->
  SubDenote (extendEnv delta a) (liftSub sigma) (extendEnv gamma a)
substExtension sigma related FZ = DVar
substExtension sigma related (FS x) = renamePres FS (\i => infoRefl) (related x)

public export
substPres : {m, n : Nat} -> {gamma : Env m} -> {delta : Env n} ->
  {term : Tm m} -> {v : Value} ->
  (sigma : Fin m -> Tm n) -> SubDenote delta sigma gamma ->
  Denote gamma term v -> Denote delta (subst sigma term) v
substPres sigma related (DVar {x}) = related x
substPres sigma related (DApp fun arg) =
  DApp (substPres sigma related fun) (substPres sigma related arg)
substPres sigma related (DLam body) =
  DLam (substPres (liftSub sigma) (substExtension sigma related) body)
substPres sigma related DBot = DBot
substPres sigma related (DJoin left right) =
  DJoin (substPres sigma related left) (substPres sigma related right)
substPres sigma related (DSub derivation below) =
  DSub (substPres sigma related derivation) below

public export
singleRelated : {n : Nat} -> {a : Value} -> {gamma : Env n} -> {arg : Tm n} ->
  Denote gamma arg a -> SubDenote gamma (single arg) (extendEnv gamma a)
singleRelated derivation FZ = derivation
singleRelated derivation (FS x) = DVar

public export
substitution : {n : Nat} -> {a, b : Value} ->
  {gamma : Env n} -> {body : Tm (S n)} -> {arg : Tm n} ->
  Denote (extendEnv gamma a) body b -> Denote gamma arg a ->
  Denote gamma (beta body arg) b
substitution {arg} body argument = substPres (single arg) (singleRelated argument) body
-- endregion substitution-preservation

-- region preservation
public export
preserve : {n : Nat} -> {gamma : Env n} -> {term, next : Tm n} -> {v : Value} ->
  Denote gamma term v -> Step term next -> Denote gamma next v
preserve (DApp fun arg) step = case step of
  AppLeft inner => DApp (preserve fun inner) arg
  AppRight inner => DApp fun (preserve arg inner)
  Beta => substitution (lambdaInversion fun) arg
preserve (DLam body) (UnderLam step) = DLam (preserve body step)
preserve DBot step = DBot
preserve (DJoin left right) step = DJoin (preserve left step) (preserve right step)
preserve (DSub derivation below) step = DSub (preserve derivation step) below
-- endregion preservation

-- region renaming-reflection
reflectExtension : {m, n : Nat} -> {a : Value} -> {gamma : Env m} -> {delta : Env n} ->
  (rho : Fin m -> Fin n) -> ((x : Fin m) -> Info (delta (rho x)) (gamma x)) ->
  (x : Fin (S m)) ->
  Info (extendEnv delta a (liftRen rho x)) (extendEnv gamma a x)
reflectExtension rho below FZ = infoRefl
reflectExtension rho below (FS x) = below x

public export
renameReflect : {m, n : Nat} -> {v : Value} -> {gamma : Env m} -> {delta : Env n} ->
  (term : Tm m) -> (rho : Fin m -> Fin n) ->
  ((x : Fin m) -> Info (delta (rho x)) (gamma x)) ->
  Denote delta (rename rho term) v -> Denote gamma term v
renameReflect (Var x) rho below derivation = DSub DVar (ITrans (varInv derivation) (below x))
renameReflect (Lam body) rho below (DLam derivation) =
  DLam (renameReflect body (liftRen rho) (reflectExtension rho below) derivation)
renameReflect (Lam body) rho below DBot = DBot
renameReflect (Lam body) rho below (DJoin left right) =
  DJoin (renameReflect (Lam body) rho below left) (renameReflect (Lam body) rho below right)
renameReflect (Lam body) rho below (DSub derivation le) =
  DSub (renameReflect (Lam body) rho below derivation) le
renameReflect (App fun arg) rho below (DApp df da) =
  DApp (renameReflect fun rho below df) (renameReflect arg rho below da)
renameReflect (App fun arg) rho below DBot = DBot
renameReflect (App fun arg) rho below (DJoin left right) =
  DJoin (renameReflect (App fun arg) rho below left) (renameReflect (App fun arg) rho below right)
renameReflect (App fun arg) rho below (DSub derivation le) =
  DSub (renameReflect (App fun arg) rho below derivation) le

public export
renameShiftReflect : {n : Nat} -> {a, v : Value} -> {gamma : Env n} -> (term : Tm n) ->
  Denote (extendEnv gamma a) (rename FS term) v -> Denote gamma term v
renameShiftReflect term derivation = renameReflect term FS (\x => infoRefl) derivation
-- endregion renaming-reflection

-- region finite-demand
public export
oneEnv : {n : Nat} -> (x : Fin n) -> Value -> Env n
oneEnv x value y with (decEq x y)
  oneEnv x value y | Yes eq = value
  oneEnv x value y | No neq = Bottom

oneEnvHere : {n : Nat} -> (x : Fin n) -> (value : Value) -> oneEnv x value x = value
oneEnvHere x value with (decEq x x)
  oneEnvHere x value | Yes eq = Refl
  oneEnvHere x value | No neq = void (neq Refl)

oneEnvRelated : {m, n : Nat} -> {v : Value} -> {delta : Env n} ->
  (sigma : Fin m -> Tm n) -> (x : Fin m) ->
  Denote delta (sigma x) v -> SubDenote delta sigma (oneEnv x v)
oneEnvRelated sigma x derivation y with (decEq x y)
  oneEnvRelated sigma x derivation x | Yes Refl = derivation
  oneEnvRelated sigma x derivation y | No neq = DBot

reflectVariable : {m, n : Nat} -> {v : Value} -> {delta : Env n} -> (sigma : Fin m -> Tm n) ->
  (x : Fin m) -> Denote delta (sigma x) v ->
  (gamma : Env m ** (SubDenote delta sigma gamma, Denote gamma (Var x) v))
reflectVariable {v} sigma x derivation =
  (oneEnv x v ** (oneEnvRelated sigma x derivation,
    rewrite sym (oneEnvHere x v) in DVar))

joinRelated : {m, n : Nat} -> {delta : Env n} -> {sigma : Fin m -> Tm n} ->
  {gamma, theta : Env m} ->
  SubDenote delta sigma gamma -> SubDenote delta sigma theta ->
  SubDenote delta sigma (joinEnv gamma theta)
joinRelated left right x = DJoin (left x) (right x)

splitEnv : {n : Nat} -> (gamma : Env (S n)) ->
  EnvLE gamma (extendEnv (tailEnv gamma) (headEnv gamma))
splitEnv gamma FZ = infoRefl
splitEnv gamma (FS x) = infoRefl

public export
substReflect : {m, n : Nat} -> {v : Value} -> {delta : Env n} ->
  (term : Tm m) -> (sigma : Fin m -> Tm n) ->
  Denote delta (subst sigma term) v ->
  (gamma : Env m ** (SubDenote delta sigma gamma, Denote gamma term v))
substReflect (Var x) sigma derivation = reflectVariable sigma x derivation
substReflect (Lam body) sigma (DLam derivation) =
  let (gamma ** (related, bodyDenote)) = substReflect body (liftSub sigma) derivation
  in (tailEnv gamma **
       (\x => renameShiftReflect (sigma x) (related (FS x)),
        DLam (upEnv (envMono bodyDenote (splitEnv gamma)) (varInv (related FZ)))))
substReflect (Lam body) sigma DBot = (bottomEnv ** (\x => DBot, DBot))
substReflect (Lam body) sigma (DJoin left right) =
  let (gamma ** (leftRelated, leftDenote)) = substReflect (Lam body) sigma left
      (theta ** (rightRelated, rightDenote)) = substReflect (Lam body) sigma right
  in (joinEnv gamma theta ** (joinRelated leftRelated rightRelated,
       DJoin (envMono leftDenote (envJoinLeft gamma theta))
             (envMono rightDenote (envJoinRight gamma theta))))
substReflect (Lam body) sigma (DSub derivation below) =
  let (gamma ** (related, result)) = substReflect (Lam body) sigma derivation
  in (gamma ** (related, DSub result below))
substReflect (App fun arg) sigma (DApp df da) =
  let (gamma ** (funRelated, funDenote)) = substReflect fun sigma df
      (theta ** (argRelated, argDenote)) = substReflect arg sigma da
  in (joinEnv gamma theta ** (joinRelated funRelated argRelated,
       DApp (envMono funDenote (envJoinLeft gamma theta))
            (envMono argDenote (envJoinRight gamma theta))))
substReflect (App fun arg) sigma DBot = (bottomEnv ** (\x => DBot, DBot))
substReflect (App fun arg) sigma (DJoin left right) =
  let (gamma ** (leftRelated, leftDenote)) = substReflect (App fun arg) sigma left
      (theta ** (rightRelated, rightDenote)) = substReflect (App fun arg) sigma right
  in (joinEnv gamma theta ** (joinRelated leftRelated rightRelated,
       DJoin (envMono leftDenote (envJoinLeft gamma theta))
             (envMono rightDenote (envJoinRight gamma theta))))
substReflect (App fun arg) sigma (DSub derivation below) =
  let (gamma ** (related, result)) = substReflect (App fun arg) sigma derivation
  in (gamma ** (related, DSub result below))

singleBelow : {n : Nat} -> {arg : Tm n} -> {delta : Env n} -> (gamma : Env (S n)) ->
  SubDenote delta (single arg) gamma -> EnvLE gamma (extendEnv delta (headEnv gamma))
singleBelow gamma related FZ = infoRefl
singleBelow gamma related (FS x) = varInv (related (FS x))

public export
substitutionReflect : {n : Nat} -> {v : Value} -> {delta : Env n} ->
  (body : Tm (S n)) -> (arg : Tm n) ->
  Denote delta (beta body arg) v ->
  (a : Value ** (Denote delta arg a, Denote (extendEnv delta a) body v))
substitutionReflect body arg derivation =
  let (gamma ** (related, result)) = substReflect body (single arg) derivation
  in (headEnv gamma ** (related FZ, envMono result (singleBelow gamma related)))
-- endregion finite-demand

-- region reflection
public export
reflectBeta : {n : Nat} -> {v : Value} -> {gamma : Env n} ->
  (body : Tm (S n)) -> (arg : Tm n) ->
  Denote gamma (beta body arg) v -> Denote gamma (App (Lam body) arg) v
reflectBeta body arg derivation =
  let (a ** (argument, result)) = substitutionReflect body arg derivation
  in DApp (DLam result) argument

public export
reflect : {n : Nat} -> {gamma : Env n} -> {term, next : Tm n} -> {v : Value} ->
  Step term next -> Denote gamma next v -> Denote gamma term v
reflect (Beta {body} {arg}) derivation = reflectBeta body arg derivation
reflect (AppLeft step) (DApp fun arg) = DApp (reflect step fun) arg
reflect (AppLeft step) DBot = DBot
reflect (AppLeft step) (DJoin left right) =
  DJoin (reflect (AppLeft step) left) (reflect (AppLeft step) right)
reflect (AppLeft step) (DSub derivation below) = DSub (reflect (AppLeft step) derivation) below
reflect (AppRight step) (DApp fun arg) = DApp fun (reflect step arg)
reflect (AppRight step) DBot = DBot
reflect (AppRight step) (DJoin left right) =
  DJoin (reflect (AppRight step) left) (reflect (AppRight step) right)
reflect (AppRight step) (DSub derivation below) = DSub (reflect (AppRight step) derivation) below
reflect (UnderLam step) (DLam body) = DLam (reflect step body)
reflect (UnderLam step) DBot = DBot
reflect (UnderLam step) (DJoin left right) =
  DJoin (reflect (UnderLam step) left) (reflect (UnderLam step) right)
reflect (UnderLam step) (DSub derivation below) = DSub (reflect (UnderLam step) derivation) below
-- endregion reflection

-- region soundness
public export
stepSoundness : {n : Nat} -> {term, next : Tm n} -> Step term next -> SemEq term next
stepSoundness step gamma v = (\d => preserve d step, reflect step)

public export
soundness : {n : Nat} -> {term, result : Tm n} -> Steps term result -> SemEq term result
soundness Done gamma v = (id, id)
soundness (More first rest) gamma v =
  let (forward, backward) = soundness rest gamma v
  in (\d => forward (preserve d first), \d => reflect first (backward d))
-- endregion soundness

-- region exercises
public export
betaMeaning : {n : Nat} -> (body : Tm (S n)) -> (arg : Tm n) ->
  SemEq (App (Lam body) arg) (beta body arg)
betaMeaning body arg = stepSoundness Beta

public export
ignoredArgumentMeaning : {n : Nat} -> (arg : Tm n) ->
  SemEq (App (Lam (Lam (Var FZ))) arg) (Lam (Var FZ))
ignoredArgumentMeaning arg = stepSoundness Beta

public export
underLambdaMeaning : {n : Nat} ->
  SemEq {n} (Lam (App (Lam (Var FZ)) (Var FZ))) (Lam (Var FZ))
underLambdaMeaning = stepSoundness (UnderLam Beta)
-- endregion exercises
