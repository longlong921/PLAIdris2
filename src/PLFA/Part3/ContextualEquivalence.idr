module PLFA.Part3.ContextualEquivalence

import public PLFA.Part3.Adequacy

%default total
%unbound_implicits off

-- region observations
public export
Terminates : {n : Nat} -> Tm n -> Type
Terminates {n} term = (body : Tm (S n) ** Steps term (Lam body))

public export
ContextuallyEquivalent : {n : Nat} -> Tm n -> Tm n -> Type
ContextuallyEquivalent {n} left right = (context : Ctx n 0) ->
  (Converges (plug context left) -> Converges (plug context right),
   Converges (plug context right) -> Converges (plug context left))

public export
BetaContextuallyEquivalent : {n : Nat} -> Tm n -> Tm n -> Type
BetaContextuallyEquivalent {n} left right = (context : Ctx n 0) ->
  (Terminates (plug context left) -> Terminates (plug context right),
   Terminates (plug context right) -> Terminates (plug context left))
-- endregion observations

-- region replacement
public export
denotEqualConverges : {n : Nat} -> {left, right : Tm n} ->
  SemEq left right -> (context : Ctx n 0) ->
  Converges (plug context left) -> Converges (plug context right)
denotEqualConverges equal context = equalPreservesConvergence (compositionality context equal)

public export
denotEqualTerminates : {n : Nat} -> {left, right : Tm n} ->
  SemEq left right -> (context : Ctx n 0) ->
  Terminates (plug context left) -> Terminates (plug context right)
denotEqualTerminates equal context (body ** reduction) =
  let (result ** evaluates) = denotEqualConverges equal context (reducesConverges reduction)
  in (result ** evalToSteps evaluates)

public export
contextualEquivalence : {n : Nat} -> {left, right : Tm n} ->
  SemEq left right -> ContextuallyEquivalent left right
contextualEquivalence equal context =
  (denotEqualConverges equal context, denotEqualConverges (denEqSym equal) context)

public export
betaContextualEquivalence : {n : Nat} -> {left, right : Tm n} ->
  SemEq left right -> BetaContextuallyEquivalent left right
betaContextualEquivalence equal context =
  (denotEqualTerminates equal context, denotEqualTerminates (denEqSym equal) context)
-- endregion replacement

-- region examples
public export
betaReplacement : {n : Nat} -> (body : Tm (S n)) -> (arg : Tm n) ->
  ContextuallyEquivalent (App (Lam body) arg) (beta body arg)
betaReplacement body arg = contextualEquivalence (betaMeaning body arg)

public export
ignoredArgumentReplacement : (arg : Tm 0) ->
  ContextuallyEquivalent (App (Lam (Lam (Var FZ))) arg) (Lam (Var FZ))
ignoredArgumentReplacement arg = contextualEquivalence (ignoredArgumentMeaning arg)

public export
closingBinder : Ctx 1 0
closingBinder = CLam Hole

public export
openBetaReplacement : ContextuallyEquivalent
  (App (Lam (Var FZ)) (Var {n = 1} FZ)) (Var FZ)
openBetaReplacement = betaReplacement (Var FZ) (Var FZ)

public export
etaExpansion : Tm 0
etaExpansion = Lam (App (rename FS (Untyped.omega {n = 0})) (Var FZ))

public export
etaExpansionConverges : Converges etaExpansion
etaExpansionConverges =
  (App (rename FS (Untyped.omega {n = 0})) (Var FZ) ** EvalLam)
-- endregion examples

-- region exercises
public export
contextualReflexive : {n : Nat} -> {term : Tm n} -> ContextuallyEquivalent term term
contextualReflexive context = (id, id)

public export
contextualSymmetric : {n : Nat} -> {left, right : Tm n} ->
  ContextuallyEquivalent left right -> ContextuallyEquivalent right left
contextualSymmetric equivalent context =
  (snd (equivalent context), fst (equivalent context))

public export
contextualTransitive : {n : Nat} -> {left, middle, right : Tm n} ->
  ContextuallyEquivalent left middle -> ContextuallyEquivalent middle right ->
  ContextuallyEquivalent left right
contextualTransitive first second context =
  (\converges => fst (second context) (fst (first context) converges),
   \converges => snd (first context) (snd (second context) converges))

public export
underBinderReplacement : {n : Nat} ->
  ContextuallyEquivalent {n}
    (Lam (App (Lam (Var FZ)) (Var FZ))) (Lam (Var FZ))
underBinderReplacement = contextualEquivalence underLambdaMeaning

public export
reduceReplacement : {n : Nat} -> {left, right : Tm n} ->
  Steps left right -> ContextuallyEquivalent left right
reduceReplacement reduction = contextualEquivalence (soundness reduction)

public export
etaNotContextual : ContextuallyEquivalent (Untyped.omega {n = 0}) etaExpansion -> Void
etaNotContextual equivalent =
  let (body ** evaluates) = snd (equivalent Hole) etaExpansionConverges
  in omegaNoEval evaluates
-- endregion exercises
