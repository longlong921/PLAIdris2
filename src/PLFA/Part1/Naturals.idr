module PLFA.Part1.Naturals

%default total

-- region arithmetic
public export
add : Nat -> Nat -> Nat
add Z n = n
add (S m) n = S (add m n)

public export
mul : Nat -> Nat -> Nat
mul Z n = Z
mul (S m) n = add n (mul m n)

public export
power : Nat -> Nat -> Nat
power m Z = 1
power m (S n) = mul m (power m n)

public export
monus : Nat -> Nat -> Nat
monus m Z = m
monus Z (S n) = Z
monus (S m) (S n) = monus m n
-- endregion arithmetic

-- region examples
public export
seven : Nat
seven = S (S (S (S (S (S (S Z))))))

public export
addExample : add 3 4 = 7
addExample = Refl

public export
mulExample : mul 3 4 = 12
mulExample = Refl

public export
powerExample : power 3 4 = 81
powerExample = Refl

public export
monusExample : (monus 3 5, monus 5 3) = (0, 2)
monusExample = Refl
-- endregion examples

-- region binary
public export
data Bin = Empty | B0 Bin | B1 Bin

public export
inc : Bin -> Bin
inc Empty = B1 Empty
inc (B0 b) = B1 b
inc (B1 b) = B0 (inc b)

public export
toBin : Nat -> Bin
toBin Z = B0 Empty
toBin (S n) = inc (toBin n)

public export
fromBin : Bin -> Nat
fromBin Empty = Z
fromBin (B0 b) = add (fromBin b) (fromBin b)
fromBin (B1 b) = S (add (fromBin b) (fromBin b))

public export
normalize : Bin -> Bin
normalize b = toBin (fromBin b)

public export
binaryExamples :
  (toBin 0, toBin 1, toBin 2, toBin 3, toBin 4) =
  (B0 Empty, B1 Empty, B0 (B1 Empty), B1 (B1 Empty), B0 (B0 (B1 Empty)))
binaryExamples = Refl

public export
binaryValues :
  (fromBin (B0 Empty), fromBin (B1 Empty),
   fromBin (B0 (B1 Empty)), fromBin (B1 (B1 Empty)),
   fromBin (B0 (B0 (B1 Empty)))) = (0, 1, 2, 3, 4)
binaryValues = Refl

public export
carryExample : inc (B1 (B1 (B0 (B1 Empty)))) = B0 (B0 (B1 (B1 Empty)))
carryExample = Refl
-- endregion binary
