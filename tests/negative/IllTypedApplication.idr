module IllTypedApplication
import PLFA.Part2.Typed
%default total
bad : HasType [] (RApp RZero RZero) TNat
bad = TApp TZero TZero
