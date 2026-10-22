module PLFA.Part3.Adequacy

import public PLFA.Part3.Soundness
import public PLFA.Part2.ClosureCorrespondence
import PLFA.Appendix.Substitution

%default total
%unbound_implicits off

-- region observation
public export
Converges : Tm 0 -> Type
Converges term = (body : Tm 1 ** Eval term (Lam body))

public export
HasFunction : Tm 0 -> Type
HasFunction term = (a : Value ** (b : Value ** Denote emptyEnv term (Arrow a b)))
-- endregion observation

-- region logical-relation
public export
Realizes : Value -> Tm 0 -> Type
Realizes Bottom term = ()
Realizes (Join a b) term = (Realizes a term, Realizes b term)
Realizes (Arrow a b) term =
  (body : Tm 1 **
    (Eval term (Lam body),
     (arg : Tm 0) -> Realizes a arg -> Realizes b (beta body arg)))

public export
realizesExpansion : (value : Value) -> {term, next : Tm 0} ->
  ((body : Tm 1) -> Eval next (Lam body) -> Eval term (Lam body)) ->
  Realizes value next -> Realizes value term
realizesExpansion Bottom expand related = ()
realizesExpansion (Join a b) expand (left, right) =
  (realizesExpansion a expand left, realizesExpansion b expand right)
realizesExpansion (Arrow a b) expand (body ** (evaluates, function)) =
  (body ** (expand body evaluates, function))

lambdaInjective : {n : Nat} -> {left, right : Tm (S n)} -> Lam left = Lam right -> left = right
lambdaInjective Refl = Refl

public export
realizesDown : {a, b : Value} -> {term : Tm 0} ->
  Info a b -> Realizes b term -> Realizes a term
realizesDown IBot related = ()
realizesDown (IJoinL left right) related =
  (realizesDown left related, realizesDown right related)
realizesDown (IJoinR1 below) (left, right) = realizesDown below left
realizesDown (IJoinR2 below) (left, right) = realizesDown below right
realizesDown (ITrans first second) related =
  realizesDown first (realizesDown second related)
realizesDown (IFun domain codomain) (body ** (evaluates, function)) =
  (body ** (evaluates, \arg, related =>
     realizesDown codomain (function arg (realizesDown domain related))))
realizesDown IDist related = case related of
  ((body ** (leftEval, leftFun)), (other ** (rightEval, rightFun))) =>
    case lambdaInjective (evalDeterministic leftEval rightEval) of
      Refl => (body ** (leftEval, \arg, argument =>
                 (leftFun arg argument, rightFun arg argument)))
-- endregion logical-relation

-- region fundamental
public export
RealizesEnv : {n : Nat} -> Denotational.Env n -> (Fin n -> Tm 0) -> Type
RealizesEnv gamma sigma = (x : Fin n) -> Realizes (gamma x) (sigma x)

realizesExtend : {n : Nat} -> {a : Value} -> {arg : Tm 0} ->
  {gamma : Denotational.Env n} -> {sigma : Fin n -> Tm 0} ->
  RealizesEnv gamma sigma -> Realizes a arg ->
  RealizesEnv (extendEnv gamma a) (cons arg sigma)
realizesExtend related argument FZ = argument
realizesExtend related argument (FS x) = related x

public export
fundamental : {n : Nat} -> {gamma : Denotational.Env n} -> {term : Tm n} -> {value : Value} ->
  (sigma : Fin n -> Tm 0) -> RealizesEnv gamma sigma ->
  Denote gamma term value -> Realizes value (subst sigma term)
fundamental sigma related (DVar {x}) = related x
fundamental sigma related (DApp {m} {b} fun arg) =
  let (body ** (funEval, function)) = fundamental sigma related fun
  in realizesExpansion b (\result, bodyEval => EvalApp funEval bodyEval)
       (function (subst sigma m) (fundamental sigma related arg))
fundamental sigma related (DLam {body} derivation) =
  (subst (liftSub sigma) body ** (EvalLam, \arg, argument =>
    rewrite betaSubst sigma body arg in
      fundamental (cons arg sigma) (realizesExtend related argument) derivation))
fundamental sigma related DBot = ()
fundamental sigma related (DJoin left right) =
  (fundamental sigma related left, fundamental sigma related right)
fundamental sigma related (DSub derivation below) =
  realizesDown below (fundamental sigma related derivation)

emptyRealizes : RealizesEnv emptyEnv Var
emptyRealizes x impossible

public export
closedFundamental : {value : Value} ->
  (term : Tm 0) -> Denote emptyEnv term value -> Realizes value term
closedFundamental term derivation =
  rewrite sym (substId term) in fundamental Var emptyRealizes derivation
-- endregion fundamental

-- region adequacy
public export
functionConverges : {a, b : Value} -> (term : Tm 0) ->
  Denote emptyEnv term (Arrow a b) -> Converges term
functionConverges term derivation =
  let (body ** (evaluates, function)) = closedFundamental term derivation
  in (body ** evaluates)

public export
adequacy : (term : Tm 0) -> (body : Tm 1) -> SemEq term (Lam body) -> Converges term
adequacy term body equal =
  functionConverges term (snd (equal emptyEnv (Arrow Bottom Bottom)) (DLam DBot))

public export
convergesFunction : {term : Tm 0} -> Converges term ->
  Denote emptyEnv term (Arrow Bottom Bottom)
convergesFunction (body ** evaluates) =
  snd (soundness (evalToSteps evaluates) emptyEnv (Arrow Bottom Bottom)) (DLam DBot)

public export
observableAdequacy : (term : Tm 0) ->
  (HasFunction term -> Converges term, Converges term -> HasFunction term)
observableAdequacy term =
  (\(a ** (b ** derivation)) => functionConverges term derivation,
   \converges => (Bottom ** (Bottom ** convergesFunction converges)))

public export
reducesConverges : {term : Tm 0} -> {body : Tm 1} ->
  Steps term (Lam body) -> Converges term
reducesConverges {term} {body} reduction = adequacy term body (soundness reduction)

public export
cbnBetaEquivalent : (term : Tm 0) ->
  ((body : Tm 1 ** Steps term (Lam body)) -> Converges term,
   Converges term -> (body : Tm 1 ** Steps term (Lam body)))
cbnBetaEquivalent term =
  (\(body ** reduction) => reducesConverges reduction,
   \(body ** evaluates) => (body ** evalToSteps evaluates))
-- endregion adequacy

-- region closure-adequacy
public export
ClosureConverges : Tm 0 -> Type
ClosureConverges term =
  (result : Closure ** (ClosEval (Close term Empty) result, ClosureValue result))

public export
convergenceToClosure : {term : Tm 0} -> Converges term -> ClosureConverges term
convergenceToClosure (body ** evaluates) =
  let (result ** (closureEval, equal)) = closedEvalToClos evaluates
  in (result ** (closureEval, closValue closureEval))

public export
closureToConvergence : {term : Tm 0} -> ClosureConverges term -> Converges term
closureToConvergence {term} (result ** (evaluates, shape)) = case shape of
  ClosureLambda {body, env} =>
    (subst (liftSub (reifyEnv env)) body **
      rewrite sym (reifyClosed term) in closToEval evaluates)

public export
functionClosureConverges : {a, b : Value} -> (term : Tm 0) ->
  Denote emptyEnv term (Arrow a b) -> ClosureConverges term
functionClosureConverges term derivation = convergenceToClosure (functionConverges term derivation)

public export
closureAdequacy : (term : Tm 0) -> (body : Tm 1) ->
  SemEq term (Lam body) -> ClosureConverges term
closureAdequacy term body equal = convergenceToClosure (adequacy term body equal)

public export
reduceToClosure : {term : Tm 0} -> {body : Tm 1} ->
  Steps term (Lam body) -> ClosureConverges term
reduceToClosure reduction = convergenceToClosure (reducesConverges reduction)

public export
closureBetaEquivalent : (term : Tm 0) ->
  ((body : Tm 1 ** Steps term (Lam body)) -> ClosureConverges term,
   ClosureConverges term -> (body : Tm 1 ** Steps term (Lam body)))
closureBetaEquivalent term =
  (\(body ** reduction) => reduceToClosure reduction,
   \(result ** (evaluates, shape)) => closedClosToLambda evaluates)

public export
closureObservableAdequacy : (term : Tm 0) ->
  (HasFunction term -> ClosureConverges term, ClosureConverges term -> HasFunction term)
closureObservableAdequacy term =
  (\(a ** (b ** derivation)) => functionClosureConverges term derivation,
   \converges => (Bottom ** (Bottom ** convergesFunction (closureToConvergence converges))))
-- endregion closure-adequacy

-- region exercises
public export
bottomIsNotEnough : Denote emptyEnv (Untyped.omega {n = 0}) Bottom
bottomIsNotEnough = DBot

public export
identityConverges : Converges (Untyped.identity {n = 0})
identityConverges = functionConverges {a = Bottom} {b = Bottom}
  (Untyped.identity {n = 0}) (DLam DBot)

public export
constantIgnoresArgument : (arg : Tm 0) ->
  Converges (App (Lam (Lam (Var FZ))) arg)
constantIgnoresArgument arg =
  functionConverges {a = Bottom} {b = Bottom} (App (Lam (Lam (Var FZ))) arg)
    (DApp (DLam (DLam DBot)) DBot)

public export
equalPreservesConvergence : {left, right : Tm 0} -> SemEq left right ->
  Converges left -> Converges right
equalPreservesConvergence {right} equal converges =
  functionConverges right
    (fst (equal emptyEnv (Arrow Bottom Bottom)) (convergesFunction converges))

public export
omegaHasNoFunction : HasFunction (Untyped.omega {n = 0}) -> Void
omegaHasNoFunction (a ** (b ** derivation)) =
  let (body ** evaluates) = functionConverges (Untyped.omega {n = 0}) derivation
  in omegaNoEval evaluates
-- endregion exercises
