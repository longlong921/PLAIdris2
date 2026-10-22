module PLFA.Part2.ClosureBounds

import public Data.Nat
import public PLFA.Part2.BigStep

%default total
%unbound_implicits off

-- A height bound on an existing finite derivation. This is an induction
-- measure for closure correspondence, not a bound on the object language.
-- region bounded-evaluation
public export
data BoundedEval : {n : Nat} -> Nat -> Tm n -> Tm n -> Type where
  BVLam : {n, fuel : Nat} -> {body : Tm (S n)} ->
          BoundedEval (S fuel) (Lam body) (Lam body)
  BVApp : {n, fuel : Nat} -> {fun, arg, value : Tm n} -> {body : Tm (S n)} ->
          BoundedEval fuel fun (Lam body) ->
          BoundedEval fuel (beta body arg) value ->
          BoundedEval (S fuel) (App fun arg) value

public export
zeroBoundImpossible : {n : Nat} -> {term, value : Tm n} ->
                      BoundedEval Z term value -> Void
zeroBoundImpossible deriv impossible

public export
weakenBound : {n, small, big : Nat} -> {term, value : Tm n} ->
              LTE small big -> BoundedEval small term value ->
              BoundedEval big term value
weakenBound LTEZero deriv = absurd (zeroBoundImpossible deriv)
weakenBound (LTESucc le) BVLam = BVLam
weakenBound (LTESucc le) (BVApp fun body) =
  BVApp (weakenBound le fun) (weakenBound le body)

public export
forgetBound : {n, fuel : Nat} -> {term, value : Tm n} ->
              BoundedEval fuel term value -> Eval term value
forgetBound BVLam = EvalLam
forgetBound (BVApp fun body) = EvalApp (forgetBound fun) (forgetBound body)
-- endregion bounded-evaluation

-- region finite-derivation-bound
boundRefl : (n : Nat) -> LTE n n
boundRefl Z = LTEZero
boundRefl (S n) = LTESucc (boundRefl n)

boundStep : {a, b : Nat} -> LTE a b -> LTE a (S b)
boundStep LTEZero = LTEZero
boundStep (LTESucc p) = LTESucc (boundStep p)

boundAddLeft : (a, b : Nat) -> LTE a (a + b)
boundAddLeft Z b = LTEZero
boundAddLeft (S a) b = LTESucc (boundAddLeft a b)

boundAddRight : (a, b : Nat) -> LTE b (a + b)
boundAddRight Z b = boundRefl b
boundAddRight (S a) b = boundStep (boundAddRight a b)

public export
evalBound : {n : Nat} -> {term, value : Tm n} ->
            Eval term value -> (fuel : Nat ** BoundedEval fuel term value)
evalBound EvalLam = (1 ** BVLam)
evalBound (EvalApp fun body) =
  let (functionFuel ** functionBound) = evalBound fun
      (bodyFuel ** bodyBound) = evalBound body in
  (S (functionFuel + bodyFuel) **
    BVApp (weakenBound (boundAddLeft functionFuel bodyFuel) functionBound)
          (weakenBound (boundAddRight functionFuel bodyFuel) bodyBound))
-- endregion finite-derivation-bound
