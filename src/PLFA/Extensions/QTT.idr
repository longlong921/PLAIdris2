module PLFA.Extensions.QTT

import public Data.Vect

%default total

-- region erasure
public export
storedLength : {n : Nat} -> Vect n a -> Nat
storedLength {n} xs = n

public export
countSpine : (0 n : Nat) -> Vect n a -> Nat
countSpine Z [] = Z
countSpine (S k) (_ :: xs) = S (countSpine k xs)

public export
countCorrect : (xs : Vect n a) -> countSpine n xs = n
countCorrect [] = Refl
countCorrect (_ :: xs) = cong S (countCorrect xs)
-- endregion erasure

-- region linear
public export
linearIdentity : (1 x : a) -> a
linearIdentity x = x

public export
data LinearPair : Type -> Type -> Type where
  PairOnce : (1 x : a) -> (1 y : b) -> LinearPair a b

public export
swapOnce : (1 pair : LinearPair a b) -> LinearPair b a
swapOnce (PairOnce x y) = PairOnce y x

public export
mapOnce : (1 f : (1 x : a) -> b) -> (1 x : a) -> b
mapOnce f x = f x
-- endregion linear

-- region exercises
public export
countThree : countSpine 3 [4, 5, 6] = 3
countThree = Refl

public export
swapOnceTwice : (p : LinearPair a b) -> swapOnce (swapOnce p) = p
swapOnceTwice (PairOnce x y) = Refl
-- endregion exercises
