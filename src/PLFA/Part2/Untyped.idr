module PLFA.Part2.Untyped

import public Data.Fin
import public Data.Nat

%default total

-- region syntax
public export
data Tm : Nat -> Type where
  Var : Fin n -> Tm n
  Lam : Tm (S n) -> Tm n
  App : Tm n -> Tm n -> Tm n

public export
liftRen : (Fin m -> Fin n) -> Fin (S m) -> Fin (S n)
liftRen rho FZ = FZ
liftRen rho (FS i) = FS (rho i)

public export
rename : (Fin m -> Fin n) -> Tm m -> Tm n
rename rho (Var i) = Var (rho i)
rename rho (Lam body) = Lam (rename (liftRen rho) body)
rename rho (App fun arg) = App (rename rho fun) (rename rho arg)

public export
liftSub : (Fin m -> Tm n) -> Fin (S m) -> Tm (S n)
liftSub sigma FZ = Var FZ
liftSub sigma (FS i) = rename FS (sigma i)

public export
subst : (Fin m -> Tm n) -> Tm m -> Tm n
subst sigma (Var i) = sigma i
subst sigma (Lam body) = Lam (subst (liftSub sigma) body)
subst sigma (App fun arg) = App (subst sigma fun) (subst sigma arg)

public export
single : Tm n -> Fin (S n) -> Tm n
single arg FZ = arg
single arg (FS i) = Var i

public export
beta : Tm (S n) -> Tm n -> Tm n
beta body arg = subst (single arg) body
-- endregion syntax

-- region reduction
public export
data Step : Tm n -> Tm n -> Type where
  Beta : {body : Tm (S n)} -> {arg : Tm n} ->
         Step (App (Lam body) arg) (beta body arg)
  AppLeft : {fun, fun', arg : Tm n} ->
            Step fun fun' -> Step (App fun arg) (App fun' arg)
  AppRight : {fun, arg, arg' : Tm n} ->
             Step arg arg' -> Step (App fun arg) (App fun arg')
  UnderLam : {body, body' : Tm (S n)} ->
             Step body body' -> Step (Lam body) (Lam body')

public export
data Steps : Tm n -> Tm n -> Type where
  Done : {term : Tm n} -> Steps term term
  More : {term, next, final : Tm n} -> Step term next -> Steps next final -> Steps term final

public export
stepsTrans : {l, m, r : Tm n} -> Steps l m -> Steps m r -> Steps l r
stepsTrans Done rest = rest
stepsTrans (More first rest) tail = More first (stepsTrans rest tail)

public export
stepsLam : {body, body' : Tm (S n)} -> Steps body body' -> Steps (Lam body) (Lam body')
stepsLam Done = Done
stepsLam (More first rest) = More (UnderLam first) (stepsLam rest)

public export
stepsLeft : {fun, fun', arg : Tm n} -> Steps fun fun' -> Steps (App fun arg) (App fun' arg)
stepsLeft Done = Done
stepsLeft (More first rest) = More (AppLeft first) (stepsLeft rest)

public export
stepsRight : {fun, arg, arg' : Tm n} -> Steps arg arg' -> Steps (App fun arg) (App fun arg')
stepsRight Done = Done
stepsRight (More first rest) = More (AppRight first) (stepsRight rest)
-- endregion reduction

-- region normalization
mutual
  public export
  data FullNeutral : Tm n -> Type where
    NeutralVariable : {i : Fin n} -> FullNeutral (Var i)
    NeutralApply : {fun, arg : Tm n} ->
      FullNeutral fun -> FullNormal arg -> FullNeutral (App fun arg)

  public export
  data FullNormal : Tm n -> Type where
    NormalNeutral : {term : Tm n} -> FullNeutral term -> FullNormal term
    NormalLambda : {body : Tm (S n)} -> FullNormal body -> FullNormal (Lam body)

public export
data Progress : Tm n -> Type where
  NormalNow : {term : Tm n} -> FullNormal term -> Progress term
  ReduceNext : {term : Tm n} -> (next : Tm n) -> Step term next -> Progress term

public export
progress : (term : Tm n) -> Progress term
progress (Var i) = NormalNow (NormalNeutral NeutralVariable)
progress (Lam body) = case progress body of
  NormalNow normal => NormalNow (NormalLambda normal)
  ReduceNext next step => ReduceNext (Lam next) (UnderLam step)
progress (App (Lam body) arg) = ReduceNext (beta body arg) Beta
progress (App (Var i) arg) = case progress arg of
  NormalNow normal => NormalNow (NormalNeutral (NeutralApply NeutralVariable normal))
  ReduceNext next step => ReduceNext (App (Var i) next) (AppRight step)
progress (App (App f a) arg) = case progress (App f a) of
  ReduceNext next step => ReduceNext (App next arg) (AppLeft step)
  NormalNow normal => case normal of
    NormalNeutral neutral => case progress arg of
      NormalNow argNormal => NormalNow (NormalNeutral (NeutralApply neutral argNormal))
      ReduceNext next step => ReduceNext (App (App f a) next) (AppRight step)

neutralNotLambda : FullNeutral (Lam body) -> Void
neutralNotLambda NeutralVariable impossible
neutralNotLambda (NeutralApply _ _) impossible

mutual
  public export
  fullNormalNoStep : FullNormal term -> Step term target -> Void
  fullNormalNoStep (NormalNeutral neutral) step = fullNeutralNoStep neutral step
  fullNormalNoStep (NormalLambda normal) (UnderLam step) = fullNormalNoStep normal step

  public export
  fullNeutralNoStep : FullNeutral term -> Step term target -> Void
  fullNeutralNoStep NeutralVariable Beta impossible
  fullNeutralNoStep NeutralVariable (AppLeft _) impossible
  fullNeutralNoStep NeutralVariable (AppRight _) impossible
  fullNeutralNoStep NeutralVariable (UnderLam _) impossible
  fullNeutralNoStep (NeutralApply neutral normal) Beta = neutralNotLambda neutral
  fullNeutralNoStep (NeutralApply neutral normal) (AppLeft step) = fullNeutralNoStep neutral step
  fullNeutralNoStep (NeutralApply neutral normal) (AppRight step) = fullNormalNoStep normal step

public export
noStepIsNormal : (term : Tm n) ->
  ((target : Tm n) -> Step term target -> Void) -> FullNormal term
noStepIsNormal term cannot = case progress term of
  NormalNow normal => normal
  ReduceNext next step => void (cannot next step)

public export
stepsLength : Steps source target -> Nat
stepsLength Done = Z
stepsLength (More first rest) = S (stepsLength rest)

public export
data NormalizeResult : Tm n -> Nat -> Type where
  Exhausted : {term : Tm n} -> {fuel : Nat} -> (residual : Tm n) ->
    (path : Steps term residual) -> stepsLength path = fuel -> NormalizeResult term fuel
  Normalized : {term : Tm n} -> {fuel : Nat} -> (normal : Tm n) ->
    (path : Steps term normal) -> LTE (S (stepsLength path)) fuel ->
    FullNormal normal -> NormalizeResult term fuel

public export
normalize : (fuel : Nat) -> (term : Tm n) -> NormalizeResult term fuel
normalize Z term = Exhausted term Done Refl
normalize (S fuel) term = case progress term of
  NormalNow normal => Normalized term Done (LTESucc LTEZero) normal
  ReduceNext next step => case normalize fuel next of
    Exhausted residual path count => Exhausted residual (More step path) (cong S count)
    Normalized normal path bound nf => Normalized normal (More step path) (LTESucc bound) nf

public export
normalResult : {term : Tm n} -> NormalizeResult term fuel -> Tm n
normalResult (Exhausted residual path count) = residual
normalResult (Normalized normal path bound nf) = normal

public export
finishedNormalizing : NormalizeResult term fuel -> Bool
finishedNormalizing (Exhausted _ _ _) = False
finishedNormalizing (Normalized _ _ _ _) = True
-- endregion normalization

-- region encodings
public export
churchBody : Nat -> Tm (S (S n))
churchBody Z = Var FZ
churchBody (S k) = App (Var (FS FZ)) (churchBody k)

public export
church : Nat -> Tm n
church k = Lam (Lam (churchBody k))

public export
churchAdd : Tm n
churchAdd = Lam (Lam (Lam (Lam
  (App (App (Var (FS (FS (FS FZ)))) (Var (FS FZ)))
       (App (App (Var (FS (FS FZ))) (Var (FS FZ))) (Var FZ))))))

public export
scottZero : Tm n
scottZero = Lam (Lam (Var FZ))

public export
scottSucc : Tm n -> Tm n
scottSucc predecessor = App (Lam (Lam (Lam (App (Var (FS FZ)) (Var (FS (FS FZ))))))) predecessor

public export
scott : Nat -> Tm n
scott Z = scottZero
scott (S k) = scottSucc (scott k)

public export
scottCase : Tm n -> Tm n -> Tm (S n) -> Tm n
scottCase scrutinee zeroBranch successorBranch =
  App (App scrutinee (Lam successorBranch)) zeroBranch

public export
fixpoint : Tm (S n) -> Tm n
fixpoint body = App
  (Lam (App (Lam (App (Var (FS FZ)) (App (Var FZ) (Var FZ))))
            (Lam (App (Var (FS FZ)) (App (Var FZ) (Var FZ))))))
  (Lam body)

public export
scottAdd : Tm n
scottAdd = fixpoint $ Lam $ Lam $
  scottCase (Var (FS FZ)) (Var FZ) $
    scottSucc (App (App (Var (FS (FS (FS FZ)))) (Var FZ)) (Var (FS FZ)))

public export
scottMultiply : Tm n
scottMultiply = fixpoint $ Lam $ Lam $
  scottCase (Var (FS FZ)) scottZero $
    App (App scottAdd (Var (FS FZ)))
      (App (App (Var (FS (FS (FS FZ)))) (Var FZ)) (Var (FS FZ)))
-- endregion encodings

-- region examples
public export
identity : Tm n
identity = Lam (Var FZ)

public export
constant : Tm n
constant = Lam (Lam (Var (FS FZ)))

public export
selfApply : Tm n
selfApply = Lam (App (Var FZ) (Var FZ))

public export
omega : Tm n
omega = App selfApply selfApply

public export
identityBeta : (arg : Tm n) -> Step (App Untyped.identity arg) arg
identityBeta arg = Beta

public export
omegaLoops : Step (Untyped.omega {n}) (Untyped.omega {n})
omegaLoops = Beta

public export
underBinder : Step (Lam (App Untyped.identity (Var FZ))) (Lam (Var FZ))
underBinder = UnderLam Beta

public export
captureAvoidance :
  beta (Lam (Var (FS FZ))) (Var {n = 1} FZ) = Lam (Var (FS FZ))
captureAvoidance = Refl

churchBodyNormal : (k : Nat) -> FullNormal (Untyped.churchBody {n} k)
churchBodyNormal Z = NormalNeutral NeutralVariable
churchBodyNormal (S k) = NormalNeutral (NeutralApply NeutralVariable (churchBodyNormal k))

public export
churchNormal : (k : Nat) -> FullNormal (Untyped.church {n} k)
churchNormal k = NormalLambda (NormalLambda (churchBodyNormal k))

public export
churchTwoPlusTwo :
  normalResult (normalize 32 (App (App (Untyped.churchAdd {n = 0}) (church 2)) (church 2))) = church 4
churchTwoPlusTwo = Refl

public export
churchTwoPlusTwoFinishes :
  finishedNormalizing (normalize 32 (App (App (Untyped.churchAdd {n = 0}) (church 2)) (church 2))) = True
churchTwoPlusTwoFinishes = Refl

public export
normalizesUnderLambda :
  normalResult (normalize 2 (Lam (App (Untyped.identity {n = 1}) (Var FZ)))) = Untyped.identity
normalizesUnderLambda = Refl

public export
scottTwoPlusTwo :
  normalResult (normalize 100 (App (App (Untyped.scottAdd {n = 0}) (scott 2)) (scott 2))) =
  normalResult (normalize 100 (scott {n = 0} 4))
scottTwoPlusTwo = Refl

public export
scottTwoTimesTwo :
  normalResult (normalize 200 (App (App (Untyped.scottMultiply {n = 0}) (scott 2)) (scott 2))) =
  normalResult (normalize 200 (scott {n = 0} 4))
scottTwoTimesTwo = Refl

public export
scottArithmeticFinishes :
  (finishedNormalizing (normalize 100 (App (App (Untyped.scottAdd {n = 0}) (scott 2)) (scott 2))),
   finishedNormalizing (normalize 200 (App (App (Untyped.scottMultiply {n = 0}) (scott 2)) (scott 2)))) =
  (True, True)
scottArithmeticFinishes = Refl
-- endregion examples
