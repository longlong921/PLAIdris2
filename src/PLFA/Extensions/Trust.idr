module PLFA.Extensions.Trust

%default total

-- region machine
public export
data Machine = Halt | Spin

public export
data Transition : Machine -> Machine -> Type where
  Again : Transition Spin Spin

public export
data Trace : Nat -> Machine -> Machine -> Type where
  Stop : Trace Z machine machine
  Next : Transition before middle -> Trace n middle after ->
         Trace (S n) before after

public export
spinFor : (fuel : Nat) -> Trace fuel Spin Spin
spinFor Z = Stop
spinFor (S k) = Next Again (spinFor k)
-- endregion machine

-- region observations
public export
data Observation = Finished | OutOfFuel

public export
runFor : Nat -> Machine -> Observation
runFor fuel Halt = Finished
runFor Z Spin = OutOfFuel
runFor (S k) Spin = runFor k Spin

public export
spinExhausts : (fuel : Nat) -> runFor fuel Spin = OutOfFuel
spinExhausts Z = Refl
spinExhausts (S k) = spinExhausts k

public export
haltFinishes : (fuel : Nat) -> runFor fuel Halt = Finished
haltFinishes fuel = Refl
-- endregion observations

-- region exercises
public export
noHaltStep : Transition Halt next -> Void
noHaltStep Again impossible

public export
traceStaysSpin : Trace n Spin target -> target = Spin
traceStaysSpin Stop = Refl
traceStaysSpin (Next Again rest) = traceStaysSpin rest
-- endregion exercises
