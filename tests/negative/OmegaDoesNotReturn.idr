module OmegaDoesNotReturn
import PLFA.Part2.BigStep
%default total
bad : Eval (Untyped.omega {n = 0}) Untyped.identity
bad = EvalLam
