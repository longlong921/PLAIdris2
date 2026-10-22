module PLFA.Part1.Induction

import public PLFA.Part1.Naturals

%default total

-- region addition
public export
addAssoc : (m, n, p : Nat) -> add (add m n) p = add m (add n p)
addAssoc Z n p = Refl
addAssoc (S m) n p = cong S (addAssoc m n p)

public export
addZeroRight : (m : Nat) -> add m Z = m
addZeroRight Z = Refl
addZeroRight (S m) = cong S (addZeroRight m)

public export
addSuccRight : (m, n : Nat) -> add m (S n) = S (add m n)
addSuccRight Z n = Refl
addSuccRight (S m) n = cong S (addSuccRight m n)

public export
addComm : (m, n : Nat) -> add m n = add n m
addComm Z n = sym (addZeroRight n)
addComm (S m) n = trans (cong S (addComm m n)) (sym (addSuccRight n m))

public export
addSwap : (m, n, p : Nat) -> add m (add n p) = add n (add m p)
addSwap m n p = trans (sym (addAssoc m n p))
  (trans (cong (\x => add x p) (addComm m n)) (addAssoc n m p))

public export
addRearrange : (m, n, p, q : Nat) ->
  add (add m n) (add p q) = add (add m (add n p)) q
addRearrange m n p q = trans (addAssoc m n (add p q))
  (trans (cong (add m) (sym (addAssoc n p q))) (sym (addAssoc m (add n p) q)))
-- endregion addition

-- region multiplication
public export
mulZeroRight : (m : Nat) -> mul m 0 = 0
mulZeroRight Z = Refl
mulZeroRight (S m) = mulZeroRight m

public export
mulSuccRight : (m, n : Nat) -> mul m (S n) = add m (mul m n)
mulSuccRight Z n = Refl
mulSuccRight (S m) n = cong S
  (trans (cong (add n) (mulSuccRight m n)) (addSwap n m (mul m n)))

public export
mulComm : (m, n : Nat) -> mul m n = mul n m
mulComm Z n = sym (mulZeroRight n)
mulComm (S m) n = trans (cong (add n) (mulComm m n)) (sym (mulSuccRight n m))

public export
mulDistrib : (m, n, p : Nat) -> mul (add m n) p = add (mul m p) (mul n p)
mulDistrib Z n p = Refl
mulDistrib (S m) n p = trans (cong (add p) (mulDistrib m n p))
  (sym (addAssoc p (mul m p) (mul n p)))

public export
mulDistribRight : (m, n, p : Nat) -> mul m (add n p) = add (mul m n) (mul m p)
mulDistribRight m n p = trans (mulComm m (add n p))
  (trans (mulDistrib n p m)
    (trans (cong (\x => add x (mul p m)) (mulComm n m))
           (cong (add (mul m n)) (mulComm p m))))

public export
mulAssoc : (m, n, p : Nat) -> mul (mul m n) p = mul m (mul n p)
mulAssoc Z n p = Refl
mulAssoc (S m) n p = trans (mulDistrib n (mul m n) p)
  (cong (add (mul n p)) (mulAssoc m n p))

public export
mulOneRight : (m : Nat) -> mul m 1 = m
mulOneRight m = trans (mulComm m 1) (addZeroRight m)

public export
mulSwap : (m, n, p : Nat) -> mul m (mul n p) = mul n (mul m p)
mulSwap m n p = trans (sym (mulAssoc m n p))
  (trans (cong (\x => mul x p) (mulComm m n)) (mulAssoc n m p))
-- endregion multiplication

-- region powers-monus
public export
powerAdd : (m, n, p : Nat) -> power m (add n p) = mul (power m n) (power m p)
powerAdd m Z p = sym (addZeroRight (power m p))
powerAdd m (S n) p = trans (cong (mul m) (powerAdd m n p))
  (sym (mulAssoc m (power m n) (power m p)))

public export
powerMul : (m, n, p : Nat) -> power m (mul n p) = power (power m n) p
powerMul m n Z = rewrite mulZeroRight n in Refl
powerMul m n (S p) = rewrite mulSuccRight n p in
  trans (powerAdd m n (mul n p)) (cong (mul (power m n)) (powerMul m n p))

public export
powerProduct : (m, n, p : Nat) -> power (mul m n) p = mul (power m p) (power n p)
powerProduct m n Z = Refl
powerProduct m n (S p) =
  trans (cong (mul (mul m n)) (powerProduct m n p))
  (trans (mulAssoc m n (mul (power m p) (power n p)))
  (trans (cong (mul m) (mulSwap n (power m p) (power n p)))
         (sym (mulAssoc m (power m p) (mul n (power n p))))))

public export
zeroMonus : (n : Nat) -> monus 0 n = 0
zeroMonus Z = Refl
zeroMonus (S n) = Refl

public export
monusAdd : (m, n, p : Nat) -> monus (monus m n) p = monus m (add n p)
monusAdd m Z p = Refl
monusAdd Z (S n) p = zeroMonus p
monusAdd (S m) (S n) p = monusAdd m n p
-- endregion powers-monus

-- region binary-laws
public export
doubleSucc : (n : Nat) -> add (S n) (S n) = S (S (add n n))
doubleSucc n = cong S (addSuccRight n n)

public export
fromInc : (b : Bin) -> fromBin (inc b) = S (fromBin b)
fromInc Empty = Refl
fromInc (B0 b) = Refl
fromInc (B1 b) = rewrite fromInc b in doubleSucc (fromBin b)

public export
fromTo : (n : Nat) -> fromBin (toBin n) = n
fromTo Z = Refl
fromTo (S n) = trans (fromInc (toBin n)) (cong S (fromTo n))

public export
normalizeValue : (b : Bin) -> fromBin (normalize b) = fromBin b
normalizeValue b = fromTo (fromBin b)

public export
normalizeIdempotent : (b : Bin) -> normalize (normalize b) = normalize b
normalizeIdempotent b = cong toBin (fromTo (fromBin b))

public export
notRawRoundTrip : toBin (fromBin Empty) = Empty -> Void
notRawRoundTrip Refl impossible
-- endregion binary-laws
