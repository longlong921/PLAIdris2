module PLFA.Part2.BigStep

import public PLFA.Appendix.Substitution

%default total

-- region evaluation
public export
data Eval : Tm n -> Tm n -> Type where
  EvalLam : {body : Tm (S n)} -> Eval (Lam body) (Lam body)
  EvalApp : {fun, arg, value : Tm n} -> {body : Tm (S n)} ->
    Eval fun (Lam body) -> Eval (beta body arg) value -> Eval (App fun arg) value

public export
evalValue : {term, value : Tm n} -> Eval term value ->
  (body : Tm (S n) ** value = Lam body)
evalValue (EvalLam {body}) = (body ** Refl)
evalValue (EvalApp fun body) = evalValue body

public export
evalDeterministic : {term, left, right : Tm n} ->
  Eval term left -> Eval term right -> left = right
evalDeterministic EvalLam EvalLam = Refl
evalDeterministic (EvalApp fun body) (EvalApp fun' body') =
  case evalDeterministic fun fun' of
    Refl => evalDeterministic body body'
-- endregion evaluation

-- region weak-small-step
public export
data HeadStep : Tm n -> Tm n -> Type where
  HeadBeta : {body : Tm (S n)} -> {arg : Tm n} ->
    HeadStep (App (Lam body) arg) (beta body arg)
  HeadApp : {fun, fun', arg : Tm n} ->
    HeadStep fun fun' -> HeadStep (App fun arg) (App fun' arg)

public export
data HeadSteps : Tm n -> Tm n -> Type where
  HeadDone : {term : Tm n} -> HeadSteps term term
  HeadMore : {term, next, final : Tm n} ->
    HeadStep term next -> HeadSteps next final -> HeadSteps term final

public export
headTrans : {l, m, r : Tm n} -> HeadSteps l m -> HeadSteps m r -> HeadSteps l r
headTrans HeadDone rest = rest
headTrans (HeadMore first rest) tail = HeadMore first (headTrans rest tail)

public export
headLeft : {fun, fun', arg : Tm n} ->
  HeadSteps fun fun' -> HeadSteps (App fun arg) (App fun' arg)
headLeft HeadDone = HeadDone
headLeft (HeadMore first rest) = HeadMore (HeadApp first) (headLeft rest)

public export
headIsBeta : {term, next : Tm n} -> HeadStep term next -> Step term next
headIsBeta HeadBeta = Beta
headIsBeta (HeadApp p) = AppLeft (headIsBeta p)

public export
headsAreBetas : {term, next : Tm n} -> HeadSteps term next -> Steps term next
headsAreBetas HeadDone = Done
headsAreBetas (HeadMore p ps) = More (headIsBeta p) (headsAreBetas ps)

public export
lambdaDoesNotStep : HeadStep (Lam body) target -> Void
lambdaDoesNotStep HeadBeta impossible
lambdaDoesNotStep (HeadApp _) impossible

public export
headDeterministic : {source, left, right : Tm n} ->
  HeadStep source left -> HeadStep source right -> left = right
headDeterministic HeadBeta HeadBeta = Refl
headDeterministic HeadBeta (HeadApp p) = void (lambdaDoesNotStep p)
headDeterministic (HeadApp p) HeadBeta = void (lambdaDoesNotStep p)
headDeterministic (HeadApp {arg} p) (HeadApp q) =
  cong (\fun => App fun arg) (headDeterministic p q)
-- endregion weak-small-step

-- region correspondence
public export
evalToHeadSteps : {term, value : Tm n} -> Eval term value -> HeadSteps term value
evalToHeadSteps EvalLam = HeadDone
evalToHeadSteps (EvalApp fun body) =
  headTrans (headLeft (evalToHeadSteps fun)) (HeadMore HeadBeta (evalToHeadSteps body))

public export
evalToSteps : {term, value : Tm n} -> Eval term value -> Steps term value
evalToSteps deriv = headsAreBetas (evalToHeadSteps deriv)

public export
headExpand : {term, next, value : Tm n} ->
  HeadStep term next -> Eval next value -> Eval term value
headExpand HeadBeta rest = EvalApp EvalLam rest
headExpand (HeadApp p) rest =
  case rest of
    EvalApp fun body => EvalApp (headExpand p fun) body

public export
headStepsToEval : {term : Tm n} -> {body : Tm (S n)} ->
  HeadSteps term (Lam body) -> Eval term (Lam body)
headStepsToEval HeadDone = EvalLam
headStepsToEval (HeadMore first rest) = headExpand first (headStepsToEval rest)
-- endregion correspondence

-- region closures
mutual
  public export
  data Closure : Type where
    Close : {0 scope : Nat} -> Tm scope -> Env scope -> Closure

  public export
  data Env : Nat -> Type where
    Empty : Env Z
    Extend : Closure -> Env n -> Env (S n)

public export
lookupEnv : Env n -> Fin n -> Closure
lookupEnv Empty i impossible
lookupEnv (Extend closure env) FZ = closure
lookupEnv (Extend closure env) (FS i) = lookupEnv env i

mutual
  public export
  reify : Closure -> Tm Z
  reify (Close term env) = subst (reifyEnv env) term

  public export
  reifyEnv : Env n -> Fin n -> Tm Z
  reifyEnv Empty i impossible
  reifyEnv (Extend closure env) FZ = reify closure
  reifyEnv (Extend closure env) (FS i) = reifyEnv env i

public export
data ClosEval : Closure -> Closure -> Type where
  ClosVar : {env : Env n} -> {i : Fin n} -> {value : Closure} ->
    ClosEval (lookupEnv env i) value -> ClosEval (Close (Var i) env) value
  ClosLam : {env : Env n} -> {body : Tm (S n)} ->
    ClosEval (Close (Lam body) env) (Close (Lam body) env)
  ClosApp : {env : Env n} -> {delta : Env m} -> {fun, arg : Tm n} ->
    {body : Tm (S m)} -> {value : Closure} ->
    ClosEval (Close fun env) (Close (Lam body) delta) ->
    ClosEval (Close body (Extend (Close arg env) delta)) value ->
    ClosEval (Close (App fun arg) env) value

public export
closDeterministic : {input, left, right : Closure} ->
  ClosEval input left -> ClosEval input right -> left = right
closDeterministic (ClosVar p) (ClosVar q) = closDeterministic p q
closDeterministic ClosLam ClosLam = Refl
closDeterministic (ClosApp fun body) (ClosApp fun' body') =
  case closDeterministic fun fun' of
    Refl => closDeterministic body body'

public export
reifyLookup : (env : Env n) -> (i : Fin n) ->
  reify (lookupEnv env i) = reifyEnv env i
reifyLookup Empty i impossible
reifyLookup (Extend closure env) FZ = Refl
reifyLookup (Extend closure env) (FS i) = reifyLookup env i

reifyCons : (closure : Closure) -> (env : Env n) -> (i : Fin (S n)) ->
  cons (reify closure) (reifyEnv env) i = reifyEnv (Extend closure env) i
reifyCons closure env FZ = Refl
reifyCons closure env (FS i) = Refl

public export
reifyBeta : (body : Tm (S n)) -> (env : Env n) -> (arg : Closure) ->
  beta (subst (liftSub (reifyEnv env)) body) (reify arg) =
  reify (Close body (Extend arg env))
reifyBeta body env arg =
  trans (betaSubst (reifyEnv env) body (reify arg))
    (substExt (cons (reify arg) (reifyEnv env)) (reifyEnv (Extend arg env))
      (reifyCons arg env) body)

public export
closToEval : {input, value : Closure} ->
  ClosEval input value -> Eval (reify input) (reify value)
closToEval (ClosVar {env, i} p) =
  rewrite sym (reifyLookup env i) in closToEval p
closToEval ClosLam = EvalLam
closToEval (ClosApp {delta, body, arg, env} fun bodyEval) =
  EvalApp (closToEval fun)
    (rewrite reifyBeta body delta (Close arg env) in closToEval bodyEval)

public export
closToSteps : {input, value : Closure} ->
  ClosEval input value -> Steps (reify input) (reify value)
closToSteps deriv = evalToSteps (closToEval deriv)

public export
reifyClosed : (term : Tm Z) -> reify (Close term Empty) = term
reifyClosed term =
  trans (substExt (reifyEnv Empty) Var (\i => absurd i) term) (substId term)

public export
closedClosToSteps : {term : Tm Z} -> {value : Closure} ->
  ClosEval (Close term Empty) value -> Steps term (reify value)
closedClosToSteps {term} deriv = rewrite sym (reifyClosed term) in closToSteps deriv

public export
closedClosToLambda : {term : Tm Z} -> {value : Closure} ->
  ClosEval (Close term Empty) value -> (body : Tm 1 ** Steps term (Lam body))
closedClosToLambda deriv = case evalValue (closToEval deriv) of
  (body ** eq) => (body ** rewrite sym eq in closedClosToSteps deriv)
-- endregion closures

-- region fuel
public export
data Neutral : Tm n -> Type where
  NeutralVar : {i : Fin n} -> Neutral (Var i)
  NeutralApp : {fun, arg : Tm n} -> Neutral fun -> Neutral (App fun arg)

public export
data HeadView : Tm n -> Type where
  IsLambda : (body : Tm (S n)) -> HeadView (Lam body)
  IsNeutral : {term : Tm n} -> Neutral term -> HeadView term
  CanStep : {term : Tm n} -> (next : Tm n) -> HeadStep term next -> HeadView term

public export
headView : (term : Tm n) -> HeadView term
headView (Var i) = IsNeutral NeutralVar
headView (Lam body) = IsLambda body
headView (App fun arg) = case headView fun of
  IsLambda body => CanStep (beta body arg) HeadBeta
  IsNeutral neutral => IsNeutral (NeutralApp neutral)
  CanStep next deriv => CanStep (App next arg) (HeadApp deriv)

public export
data RunResult : Tm n -> Type where
  Returned : {term : Tm n} -> (body : Tm (S n)) ->
    HeadSteps term (Lam body) -> RunResult term
  Blocked : {term : Tm n} -> (neutral : Tm n) ->
    HeadSteps term neutral -> Neutral neutral -> RunResult term
  OutOfFuel : {term : Tm n} -> (residual : Tm n) ->
    HeadSteps term residual -> RunResult term

prependRun : {term, next : Tm n} -> HeadStep term next -> RunResult next -> RunResult term
prependRun p (Returned body path) = Returned body (HeadMore p path)
prependRun p (Blocked neutral path nf) = Blocked neutral (HeadMore p path) nf
prependRun p (OutOfFuel residual path) = OutOfFuel residual (HeadMore p path)

public export
run : Nat -> (term : Tm n) -> RunResult term
run Z term = OutOfFuel term HeadDone
run (S fuel) term = case headView term of
  IsLambda body => Returned body HeadDone
  IsNeutral nf => Blocked term HeadDone nf
  CanStep next deriv => prependRun deriv (run fuel next)

public export
data RunStatus = ValueFound | OpenNeutral | BudgetUsed

public export
runStatus : RunResult term -> RunStatus
runStatus (Returned _ _) = ValueFound
runStatus (Blocked _ _ _) = OpenNeutral
runStatus (OutOfFuel _ _) = BudgetUsed
-- endregion fuel

-- region examples
public export
ignoreOmega : Tm n
ignoreOmega = App (Lam (Lam (Var FZ))) Untyped.omega

public export
ignoreOmegaTerminates : Eval (BigStep.ignoreOmega {n}) Untyped.identity
ignoreOmegaTerminates = EvalApp EvalLam EvalLam

public export
omegaNoEval : {value : Tm n} -> Eval (Untyped.omega {n}) value -> Void
omegaNoEval (EvalApp fun body) = case fun of
  EvalLam => omegaNoEval body

public export
fuelIdentity : runStatus (run 3 (App (Untyped.identity {n = 0}) Untyped.identity)) = ValueFound
fuelIdentity = Refl

public export
fuelOmega : runStatus (run 12 (Untyped.omega {n = 0})) = BudgetUsed
fuelOmega = Refl

public export
fuelNeutral : runStatus (run 1 (Var {n = 1} FZ)) = OpenNeutral
fuelNeutral = Refl

public export
lazyCaptureTerminates :
  Eval (App (Untyped.constant {n = 0}) Untyped.omega)
       (Lam (rename FS Untyped.omega))
lazyCaptureTerminates = EvalApp EvalLam EvalLam

public export
closureLazyCapture :
  ClosEval (Close (App Untyped.constant Untyped.omega) Empty)
           (Close (Lam (Var (FS FZ))) (Extend (Close Untyped.omega Empty) Empty))
closureLazyCapture = ClosApp ClosLam ClosLam
-- endregion examples
