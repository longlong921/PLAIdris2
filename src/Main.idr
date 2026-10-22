module Main

import PLFA.Part1.Lists
import PLFA.Part2.Properties
import PLFA.Part2.DeBruijn
import PLFA.Part2.More
import PLFA.Part2.Inference
import PLFA.Part2.BigStep
import PLFA.Extensions.IdrisPrimer
import PLFA.Extensions.QTT
import PLFA.Extensions.Trust
import System

%default total

allUpTo : Nat -> (Nat -> Bool) -> Bool
allUpTo Z predicate = predicate Z
allUpTo (S k) predicate = predicate (S k) && allUpTo k predicate

sameTerm : Tm n -> Tm n -> Bool
sameTerm (Var i) (Var j) = i == j
sameTerm (Lam a) (Lam b) = sameTerm a b
sameTerm (App f a) (App g b) = sameTerm f g && sameTerm a b
sameTerm _ _ = False

normalizesTo : Nat -> Tm n -> Tm n -> Bool
normalizesTo fuel term expected =
  let result = Untyped.normalize fuel term in
  finishedNormalizing result && sameTerm (normalResult result) expected

headReturns : BigStep.RunResult term -> Bool
headReturns (Returned _ _) = True
headReturns _ = False

headExhausts : BigStep.RunResult term -> Bool
headExhausts (OutOfFuel _ _) = True
headExhausts _ = False

machineExhausts : Trust.Observation -> Bool
machineExhausts Trust.OutOfFuel = True
machineExhausts Trust.Finished = False

tests : List (String, Bool)
tests =
  [ ("natural addition", Naturals.add 3 4 == 7)
  , ("natural multiplication", Naturals.mul 3 4 == 12)
  , ("natural exponentiation", Naturals.power 3 4 == 81)
  , ("truncated subtraction", Naturals.monus 3 5 == 0 && Naturals.monus 5 3 == 2)
  , ("binary round trips 0..64", allUpTo 64 (\n => fromBin (toBin n) == n))
  , ("canonical binary decisions 0..64", allUpTo 64 (\n => decBool (decCanonical (toBin n))))
  , ("order reflection 0..12 squared", allUpTo 12 (\m => allUpTo 12 (\n => decBool (decLE m n) == leBool m n)))
  , ("safe subtraction", safeMinus 5 3 == 2)
  , ("append", Lists.append [0, 1, 2] [3, 4] == the (List Nat) [0, 1, 2, 3, 4])
  , ("reverse algorithms agree", Lists.fastReverse [0, 1, 2] == Lists.reverseList (the (List Nat) [0, 1, 2]))
  , ("fold sum", Lists.sumList [1, 2, 3, 4] == 10)
  , ("fold product", Lists.productList [1, 2, 3, 4] == 24)
  , ("extrinsic CBV recursive addition", Properties.additionResult == Just 4)
  , ("extrinsic CBV recursive multiplication", Properties.multiplicationResult == Just 6)
  , ("typed general recursion exhausts finite fuel", Properties.evaluateNatural 10 Properties.loop Properties.loopType == Nothing)
  , ("intrinsic CBV recursive addition", DeBruijn.additionResult == Just 4)
  , ("intrinsic CBV recursive multiplication", DeBruijn.multiplicationResult == Just 6)
  , ("let and primitive cube", More.cubeResult == Just 8)
  , ("object-language recursive list length", More.lengthResult == Just 2)
  , ("bidirectional inference accepts addition", Inference.isYes (Inference.synthesize [] Inference.plusTwoTwo))
  , ("inference to intrinsic evaluation", Inference.inferredResult == Just 4)
  , ("bidirectional inference rejects zero application", not (Inference.isYes (Inference.synthesize [] Inference.badApplication)))
  , ("bidirectional inference rejects false annotation", not (Inference.isYes (Inference.synthesize [] Inference.badAnnotation)))
  , ("CBN identity", headReturns (BigStep.run 3 (App (Untyped.identity {n = 0}) Untyped.identity)))
  , ("CBN ignores divergent unused argument", headReturns (BigStep.run 3 (BigStep.ignoreOmega {n = 0})))
  , ("Omega exhausts finite CBN fuel", headExhausts (BigStep.run 12 (Untyped.omega {n = 0})))
  , ("full normalization enters lambda", normalizesTo 10
       (Lam (App (Untyped.identity {n = 1}) (Var FZ)))
       (Lam (Var FZ)))
  , ("full normalization Church addition", normalizesTo 32
       (App (App (Untyped.churchAdd {n = 0}) (Untyped.church 2)) (Untyped.church 2))
       (Untyped.church 4))
  , ("full normalization recursive Scott addition", normalizesTo 100
       (App (App (Untyped.scottAdd {n = 0}) (Untyped.scott 2)) (Untyped.scott 2))
       (normalResult (normalize 100 (Untyped.scott 4))))
  , ("full normalization recursive Scott multiplication", normalizesTo 200
       (App (App (Untyped.scottMultiply {n = 0}) (Untyped.scott 2)) (Untyped.scott 2))
       (normalResult (normalize 100 (Untyped.scott 4))))
  , ("Omega exhausts finite full-normalization fuel", not (finishedNormalizing (normalize 12 (Untyped.omega {n = 0}))))
  , ("Idris primer vector map", IdrisPrimer.mapVector S [1, 2] == [2, 3])
  , ("QTT erased index, counted spine", QTT.countSpine 3 [4, 5, 6] == 3)
  , ("host totality does not halt object machine", machineExhausts (Trust.runFor 20 Trust.Spin))
  ]

report : List (String, Bool) -> IO Bool
report [] = pure True
report ((name, success) :: rest) = do
  putStrLn ((if success then "PASS " else "FAIL ") ++ name)
  others <- report rest
  pure (success && others)

main : IO Builtin.Unit
main = do
  success <- report tests
  if success then putStrLn "ALL EXAMPLES PASSED"
             else exitFailure
