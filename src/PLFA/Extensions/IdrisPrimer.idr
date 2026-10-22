module PLFA.Extensions.IdrisPrimer

import public Data.Vect

%default total

-- region definitions
public export
twice : Nat -> Nat
twice Z = Z
twice (S k) = S (S (twice k))

public export
mapVector : (a -> b) -> Vect n a -> Vect n b
mapVector f [] = []
mapVector f (x :: xs) = f x :: mapVector f xs

public export
swapPair : (a, b) -> (b, a)
swapPair (x, y) = (y, x)
-- endregion definitions

-- region proofs
public export
twiceThree : twice 3 = 6
twiceThree = Refl

public export
mapIdentity : (xs : Vect n a) -> mapVector (\x => x) xs = xs
mapIdentity [] = Refl
mapIdentity (x :: xs) = cong (x ::) (mapIdentity xs)

public export
swapTwice : (p : (a, b)) -> swapPair (swapPair p) = p
swapTwice (x, y) = Refl
-- endregion proofs

-- region exercises
public export
mapCompose : (f : b -> c) -> (g : a -> b) -> (xs : Vect n a) ->
  mapVector f (mapVector g xs) = mapVector (\x => f (g x)) xs
mapCompose f g [] = Refl
mapCompose f g (x :: xs) = cong (f (g x) ::) (mapCompose f g xs)

public export
twiceSuccessor : (n : Nat) -> twice (S n) = S (S (twice n))
twiceSuccessor n = Refl
-- endregion exercises
