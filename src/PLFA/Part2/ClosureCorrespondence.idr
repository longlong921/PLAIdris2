module PLFA.Part2.ClosureCorrespondence

import public PLFA.Part2.ClosureBounds

%default total

-- region closure-values
public export
data ClosureValue : Closure -> Type where
  ClosureLambda : {body : Tm (S n)} -> {env : BigStep.Env n} ->
    ClosureValue (Close (Lam body) env)

public export
closValue : {input, value : Closure} -> ClosEval input value -> ClosureValue value
closValue (ClosVar deriv) = closValue deriv
closValue ClosLam = ClosureLambda
closValue (ClosApp fun body) = closValue body

lambdaInjective : {left, right : Tm (S n)} -> Lam left = Lam right -> left = right
lambdaInjective Refl = Refl
-- endregion closure-values

-- region inverse
mutual
  public export
  boundedToClos : (fuel : Nat) -> (input : Closure) -> {value : Tm 0} ->
    BoundedEval fuel (reify input) value ->
    (result : Closure ** (ClosEval input result, reify result = value))
  boundedToClos Z input deriv = void (zeroBoundImpossible deriv)
  boundedToClos (S fuel) (Close (Var i) env) deriv =
    let (result ** (evaluates, equal)) = boundedEnvToClos (S fuel) env i deriv
    in (result ** (ClosVar evaluates, equal))
  boundedToClos (S fuel) (Close (Lam body) env) BVLam =
    (Close (Lam body) env ** (ClosLam, Refl))
  boundedToClos (S fuel) (Close (App fun arg) env) (BVApp funBound bodyBound) =
    let (funResult ** (funEval, funEqual)) = boundedToClos fuel (Close fun env) funBound
    in case closValue funEval of
      ClosureLambda {body, env = delta} =>
        let (result ** (bodyEval, equal)) =
              boundedToClos fuel (Close body (Extend (Close arg env) delta))
                (rewrite sym (reifyBeta body delta (Close arg env)) in
                   rewrite lambdaInjective funEqual in bodyBound)
        in (result ** (ClosApp funEval bodyEval, equal))

  public export
  boundedEnvToClos : (fuel : Nat) -> (env : BigStep.Env n) -> (i : Fin n) ->
    {value : Tm 0} -> BoundedEval fuel (reifyEnv env i) value ->
    (result : Closure ** (ClosEval (lookupEnv env i) result, reify result = value))
  boundedEnvToClos fuel Empty i deriv impossible
  boundedEnvToClos fuel (Extend closure env) FZ deriv = boundedToClos fuel closure deriv
  boundedEnvToClos fuel (Extend closure env) (FS i) deriv = boundedEnvToClos fuel env i deriv

public export
evalToClos : (input : Closure) -> {value : Tm 0} -> Eval (reify input) value ->
  (result : Closure ** (ClosEval input result, reify result = value))
evalToClos input deriv =
  let (fuel ** bounded) = evalBound deriv
  in boundedToClos fuel input bounded

public export
closedEvalToClos : {term, value : Tm 0} -> Eval term value ->
  (result : Closure ** (ClosEval (Close term Empty) result, reify result = value))
closedEvalToClos {term} deriv =
  evalToClos (Close term Empty) (rewrite reifyClosed term in deriv)
-- endregion inverse
