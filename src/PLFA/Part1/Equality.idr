module PLFA.Part1.Equality

import public PLFA.Part1.Relations

%default total

-- region equality
public export
eqSym : x = y -> y = x
eqSym Refl = Refl

public export
eqTrans : x = y -> y = z -> x = z
eqTrans Refl q = q

public export
eqCong : (f : a -> b) -> x = y -> f x = f y
eqCong f Refl = Refl

public export
eqCong2 : (f : a -> b -> c) -> x = y -> u = v -> f x u = f y v
eqCong2 f Refl Refl = Refl

public export
applicationCong : {f, g : a -> b} -> f = g -> (x : a) -> f x = g x
applicationCong Refl x = Refl

public export
transport : (p : a -> Type) -> x = y -> p x -> p y
transport p Refl px = px
-- endregion equality

-- region reasoning
public export
step : (x : a) -> {y, z : a} -> x = y -> y = z -> x = z
step x = eqTrans

public export
finish : (x : a) -> x = x
finish x = Refl

public export
evenComm : (m, n : Nat) -> Even (add m n) -> Even (add n m)
evenComm m n = transport Even (addComm m n)

public export
evenCommRewrite : (m, n : Nat) -> Even (add m n) -> Even (add n m)
evenCommRewrite m n p = rewrite sym (addComm m n) in p

public export
leChain : (m : Nat) -> {n, p : Nat} -> LE m n -> LE n p -> LE m p
leChain m = leTrans

public export
calculation : (m, n : Nat) -> add m (S n) = add (S n) m
calculation m n = step (add m (S n))
  (addSuccRight m n)
  (step (S (add m n)) (cong S (addComm m n)) (finish (S (add n m))))
-- endregion reasoning

-- region leibniz
public export
Leibniz : (a : Type) -> a -> a -> Type
Leibniz a x y = (p : a -> Type) -> p x -> p y

public export
leibnizRefl : Leibniz a x x
leibnizRefl p px = px

public export
leibnizTrans : Leibniz a x y -> Leibniz a y z -> Leibniz a x z
leibnizTrans xy yz p px = yz p (xy p px)

public export
equalityToLeibniz : x = y -> Leibniz a x y
equalityToLeibniz Refl p px = px

public export
leibnizToEquality : {x, y : a} -> Leibniz a x y -> x = y
leibnizToEquality {x} xy = xy (\z => x = z) Refl

public export
leibnizSym : {x, y : a} -> Leibniz a x y -> Leibniz a y x
leibnizSym xy = equalityToLeibniz (sym (leibnizToEquality xy))
-- endregion leibniz
