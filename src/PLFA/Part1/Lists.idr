module PLFA.Part1.Lists

import public PLFA.Part1.Decidable

%default total

-- region append
public export
append : List a -> List a -> List a
append [] ys = ys
append (x :: xs) ys = x :: append xs ys

public export
appendAssoc : (xs, ys, zs : List a) -> append (append xs ys) zs = append xs (append ys zs)
appendAssoc [] ys zs = Refl
appendAssoc (x :: xs) ys zs = cong (x ::) (appendAssoc xs ys zs)

public export
appendRightNil : (xs : List a) -> append xs [] = xs
appendRightNil [] = Refl
appendRightNil (x :: xs) = cong (x ::) (appendRightNil xs)

public export
size : List a -> Nat
size [] = 0
size (x :: xs) = S (size xs)

public export
sizeAppend : (xs, ys : List a) -> size (append xs ys) = add (size xs) (size ys)
sizeAppend [] ys = Refl
sizeAppend (x :: xs) ys = cong S (sizeAppend xs ys)

public export
appendExample : append [0, 1, 2] [3, 4] = the (List Nat) [0, 1, 2, 3, 4]
appendExample = Refl
-- endregion append

-- region reverse
public export
reverseList : List a -> List a
reverseList [] = []
reverseList (x :: xs) = append (reverseList xs) [x]

public export
reverseAppend : (xs, ys : List a) ->
  reverseList (append xs ys) = append (reverseList ys) (reverseList xs)
reverseAppend [] ys = sym (appendRightNil (reverseList ys))
reverseAppend (x :: xs) ys = trans (cong (\zs => append zs [x]) (reverseAppend xs ys))
  (appendAssoc (reverseList ys) (reverseList xs) [x])

public export
reverseInvolutive : (xs : List a) -> reverseList (reverseList xs) = xs
reverseInvolutive [] = Refl
reverseInvolutive (x :: xs) = trans (reverseAppend (reverseList xs) [x])
  (cong (x ::) (reverseInvolutive xs))

public export
shunt : List a -> List a -> List a
shunt [] ys = ys
shunt (x :: xs) ys = shunt xs (x :: ys)

public export
shuntCorrect : (xs, ys : List a) -> shunt xs ys = append (reverseList xs) ys
shuntCorrect [] ys = Refl
shuntCorrect (x :: xs) ys = trans (shuntCorrect xs (x :: ys))
  (sym (appendAssoc (reverseList xs) [x] ys))

public export
fastReverse : List a -> List a
fastReverse xs = shunt xs []

public export
reversesAgree : (xs : List a) -> fastReverse xs = reverseList xs
reversesAgree xs = trans (shuntCorrect xs []) (appendRightNil (reverseList xs))

public export
reverseExample : fastReverse [0, 1, 2] = the (List Nat) [2, 1, 0]
reverseExample = Refl
-- endregion reverse

-- region map-fold
public export
mapList : (a -> b) -> List a -> List b
mapList f [] = []
mapList f (x :: xs) = f x :: mapList f xs

public export
mapCompose : (f : a -> b) -> (g : b -> c) -> (xs : List a) ->
  mapList (compose g f) xs = mapList g (mapList f xs)
mapCompose f g [] = Refl
mapCompose f g (x :: xs) = cong (g (f x) ::) (mapCompose f g xs)

public export
mapAppend : (f : a -> b) -> (xs, ys : List a) ->
  mapList f (append xs ys) = append (mapList f xs) (mapList f ys)
mapAppend f [] ys = Refl
mapAppend f (x :: xs) ys = cong (f x ::) (mapAppend f xs ys)

public export
foldRight : (a -> b -> b) -> b -> List a -> b
foldRight f z [] = z
foldRight f z (x :: xs) = f x (foldRight f z xs)

public export
sumList : List Nat -> Nat
sumList = foldRight add 0

public export
productList : List Nat -> Nat
productList = foldRight mul 1

public export
foldAppend : (f : a -> b -> b) -> (z : b) -> (xs, ys : List a) ->
  foldRight f z (append xs ys) = foldRight f (foldRight f z ys) xs
foldAppend f z [] ys = Refl
foldAppend f z (x :: xs) ys = cong (f x) (foldAppend f z xs ys)

public export
foldCons : (xs : List a) -> foldRight (::) [] xs = xs
foldCons [] = Refl
foldCons (x :: xs) = cong (x ::) (foldCons xs)

public export
mapAsFold : (f : a -> b) -> (xs : List a) ->
  mapList f xs = foldRight (\x, ys => f x :: ys) [] xs
mapAsFold f [] = Refl
mapAsFold f (x :: xs) = cong (f x ::) (mapAsFold f xs)

public export
foldExamples : (sumList [1, 2, 3, 4], productList [1, 2, 3, 4]) = (10, 24)
foldExamples = Refl
-- endregion map-fold

-- region trees
public export
data Tree a b = Leaf a | Node (Tree a b) b (Tree a b)

public export
mapTree : (a -> c) -> (b -> d) -> Tree a b -> Tree c d
mapTree f g (Leaf x) = Leaf (f x)
mapTree f g (Node l x r) = Node (mapTree f g l) (g x) (mapTree f g r)

public export
foldTree : (a -> c) -> (c -> b -> c -> c) -> Tree a b -> c
foldTree leaf node (Leaf x) = leaf x
foldTree leaf node (Node l x r) = node (foldTree leaf node l) x (foldTree leaf node r)

public export
mapTreeAsFold : (f : a -> c) -> (g : b -> d) -> (t : Tree a b) ->
  mapTree f g t = foldTree (\x => Leaf (f x)) (\l, x, r => Node l (g x) r) t
mapTreeAsFold f g (Leaf x) = Refl
mapTreeAsFold f g (Node l x r) =
  rewrite mapTreeAsFold f g l in rewrite mapTreeAsFold f g r in Refl
-- endregion trees

-- region monoids
public export
record MonoidLaw (a : Type) (op : a -> a -> a) (unit : a) where
  constructor MkMonoidLaw
  associative : (x, y, z : a) -> op (op x y) z = op x (op y z)
  identityLeft : (x : a) -> op unit x = x
  identityRight : (x : a) -> op x unit = x

public export
additionMonoid : MonoidLaw Nat PLFA.Part1.Naturals.add 0
additionMonoid = MkMonoidLaw addAssoc (\x => Refl) addZeroRight

public export
multiplicationMonoid : MonoidLaw Nat PLFA.Part1.Naturals.mul 1
multiplicationMonoid = MkMonoidLaw mulAssoc addZeroRight mulOneRight

public export
appendMonoid : MonoidLaw (List a) PLFA.Part1.Lists.append []
appendMonoid = MkMonoidLaw appendAssoc (\xs => Refl) appendRightNil

public export
foldMonoid : (op : a -> a -> a) -> (unit : a) -> MonoidLaw a op unit ->
  (xs : List a) -> (y : a) -> foldRight op y xs = op (foldRight op unit xs) y
foldMonoid op unit law [] y = sym (law.identityLeft y)
foldMonoid op unit law (x :: xs) y = trans (cong (op x) (foldMonoid op unit law xs y))
  (sym (law.associative x (foldRight op unit xs) y))

public export
foldMonoidAppend : (op : a -> a -> a) -> (unit : a) -> MonoidLaw a op unit ->
  (xs, ys : List a) -> foldRight op unit (append xs ys) =
  op (foldRight op unit xs) (foldRight op unit ys)
foldMonoidAppend op unit law xs ys = trans (foldAppend op unit xs ys)
  (foldMonoid op unit law xs (foldRight op unit ys))

public export
foldLeft : (b -> a -> b) -> b -> List a -> b
foldLeft f z [] = z
foldLeft f z (x :: xs) = foldLeft f (f z x) xs

public export
foldLeftInvariant : (op : a -> a -> a) -> (unit : a) -> MonoidLaw a op unit ->
  (xs : List a) -> (acc : a) -> foldLeft op acc xs = op acc (foldRight op unit xs)
foldLeftInvariant op unit law [] acc = sym (law.identityRight acc)
foldLeftInvariant op unit law (x :: xs) acc =
  trans (foldLeftInvariant op unit law xs (op acc x))
        (law.associative acc x (foldRight op unit xs))

public export
foldDirectionsAgree : (op : a -> a -> a) -> (unit : a) -> MonoidLaw a op unit ->
  (xs : List a) -> foldRight op unit xs = foldLeft op unit xs
foldDirectionsAgree op unit law xs = sym
  (trans (foldLeftInvariant op unit law xs unit) (law.identityLeft (foldRight op unit xs)))

public export
downFrom : Nat -> List Nat
downFrom Z = []
downFrom (S n) = n :: downFrom n

public export
doubleAdd : (a, b : Nat) -> add (add a b) (add a b) = add a (add a (add b b))
doubleAdd a b = trans (addAssoc a b (add a b)) (cong (add a) (addSwap b a b))

public export
sumDownFrom : (n : Nat) ->
  add (sumList (downFrom n)) (sumList (downFrom n)) = mul n (monus n 1)
sumDownFrom Z = Refl
sumDownFrom (S Z) = Refl
sumDownFrom (S (S k)) = trans (doubleAdd (S k) (sumList (downFrom (S k))))
  (cong (\z => add (S k) (add (S k) z))
    (trans (sumDownFrom (S k)) (mulComm (S k) k)))
public export
sumDownFromTimes : (n : Nat) -> mul (sumList (downFrom n)) 2 = mul n (monus n 1)
sumDownFromTimes n = trans (mulComm (sumList (downFrom n)) 2)
  (trans (cong (add (sumList (downFrom n))) (addZeroRight (sumList (downFrom n))))
         (sumDownFrom n))
-- endregion monoids

-- region predicates
public export
data All : (a -> Type) -> List a -> Type where
  AllNil : {0 p : a -> Type} -> All p []
  AllCons : {0 p : a -> Type} -> {0 x : a} -> {0 xs : List a} -> p x -> All p xs -> All p (x :: xs)

public export
data Any : (a -> Type) -> List a -> Type where
  Here : {0 p : a -> Type} -> {0 x : a} -> {0 xs : List a} -> p x -> Any p (x :: xs)
  There : {0 p : a -> Type} -> {0 x : a} -> {0 xs : List a} -> Any p xs -> Any p (x :: xs)

public export
Member : a -> List a -> Type
Member x xs = Any (\y => x = y) xs

public export
allExample : All (\n => LE n 2) [0, 1, 2]
allExample = AllCons LZ (AllCons (LS LZ) (AllCons (LS (LS LZ)) AllNil))

public export
firstZero : Member (the Nat 0) [0, 1, 0, 2]
firstZero = Here Refl

public export
secondZero : Member (the Nat 0) [0, 1, 0, 2]
secondZero = There (There (Here Refl))

public export
threeAbsent : Refutes (Member (the Nat 3) [0, 1, 0, 2])
threeAbsent (Here Refl) impossible
threeAbsent (There (Here Refl)) impossible
threeAbsent (There (There (Here Refl))) impossible
threeAbsent (There (There (There (Here Refl)))) impossible
threeAbsent (There (There (There (There p)))) impossible
-- endregion predicates

-- region quantified-laws
public export
allAppendTo : {p : a -> Type} -> (xs, ys : List a) -> All p (append xs ys) -> (All p xs, All p ys)
allAppendTo [] ys ps = (AllNil, ps)
allAppendTo (x :: xs) ys (AllCons px ps) =
  case allAppendTo xs ys ps of (left, right) => (AllCons px left, right)

public export
allAppendFrom : {p : a -> Type} -> All p xs -> All p ys -> All p (append xs ys)
allAppendFrom AllNil qs = qs
allAppendFrom (AllCons px ps) qs = AllCons px (allAppendFrom ps qs)

public export
allAppendIff : {p : a -> Type} -> (xs, ys : List a) -> Iff (All p (append xs ys)) (All p xs, All p ys)
allAppendIff xs ys = MkIff (allAppendTo xs ys) (\(ps, qs) => allAppendFrom ps qs)

public export
allAppendLeft : {p : a -> Type} -> (xs, ys : List a) -> (ps : All p (append xs ys)) ->
  allAppendFrom (fst (allAppendTo xs ys ps)) (snd (allAppendTo xs ys ps)) = ps
allAppendLeft [] ys ps = Refl
allAppendLeft (x :: xs) ys (AllCons px ps) with (allAppendTo xs ys ps) proof eq
  allAppendLeft (x :: xs) ys (AllCons px ps) | (left, right) =
    cong (AllCons px) (transport (\pair => allAppendFrom (fst pair) (snd pair) = ps) eq (allAppendLeft xs ys ps))

public export
allAppendRight : {p : a -> Type} -> (xs, ys : List a) -> (ps : All p xs) -> (qs : All p ys) ->
  allAppendTo xs ys (allAppendFrom ps qs) = (ps, qs)
allAppendRight [] ys AllNil qs = Refl
allAppendRight (x :: xs) ys (AllCons px ps) qs =
  rewrite allAppendRight xs ys ps qs in Refl

public export
allAppendIso : {p : a -> Type} -> (xs, ys : List a) -> Iso (All p (append xs ys)) (All p xs, All p ys)
allAppendIso xs ys = MkIso (allAppendTo xs ys) (\pair => allAppendFrom (fst pair) (snd pair))
  (allAppendLeft xs ys) (\(ps, qs) => allAppendRight xs ys ps qs)

public export
anyAppendTo : {p : a -> Type} -> (xs, ys : List a) -> Any p (append xs ys) -> Either (Any p xs) (Any p ys)
anyAppendTo [] ys ps = Right ps
anyAppendTo (x :: xs) ys (Here px) = Left (Here px)
anyAppendTo (x :: xs) ys (There ps) = case anyAppendTo xs ys ps of
  Left left => Left (There left)
  Right right => Right right

public export
anyAppendLeft : {p : a -> Type} -> Any p xs -> Any p (append xs ys)
anyAppendLeft (Here px) = Here px
anyAppendLeft (There ps) = There (anyAppendLeft ps)

public export
anyAppendRight : {p : a -> Type} -> (xs : List a) -> Any p ys -> Any p (append xs ys)
anyAppendRight [] ps = ps
anyAppendRight (x :: xs) ps = There (anyAppendRight xs ps)

public export
anyAppendIff : {p : a -> Type} -> (xs, ys : List a) -> Iff (Any p (append xs ys)) (Either (Any p xs) (Any p ys))
anyAppendIff xs ys = MkIff (anyAppendTo xs ys) (sumCase anyAppendLeft (anyAppendRight xs))

public export
notAnyToAll : {p : a -> Type} -> (xs : List a) -> Refutes (Any p xs) -> All (\x => Refutes (p x)) xs
notAnyToAll [] reject = AllNil
notAnyToAll (x :: xs) reject = AllCons (\px => reject (Here px))
  (notAnyToAll xs (\ps => reject (There ps)))

public export
allToNotAny : {p : a -> Type} -> All (\x => Refutes (p x)) xs -> Refutes (Any p xs)
allToNotAny (AllCons nx nxs) (Here px) = nx px
allToNotAny (AllCons nx nxs) (There ps) = allToNotAny nxs ps

public export
notAnyIff : {p : a -> Type} -> (xs : List a) -> Iff (Refutes (Any p xs)) (All (\x => Refutes (p x)) xs)
notAnyIff xs = MkIff (notAnyToAll xs) allToNotAny

public export
allToForall : {p : a -> Type} -> All p xs -> (x : a) -> Member x xs -> p x
allToForall (AllCons px ps) x (Here Refl) = px
allToForall (AllCons px ps) x (There member) = allToForall ps x member

public export
forallToAll : {p : a -> Type} -> (xs : List a) -> ((x : a) -> Member x xs -> p x) -> All p xs
forallToAll [] f = AllNil
forallToAll (x :: xs) f = AllCons (f x (Here Refl))
  (forallToAll xs (\y, member => f y (There member)))

public export
allForall : {p : a -> Type} -> (xs : List a) -> Iff (All p xs) ((x : a) -> Member x xs -> p x)
allForall xs = MkIff allToForall (forallToAll xs)

public export
shiftWitness : {p : a -> Type} -> (head : a) ->
  (w : (x : a ** (Member x xs, p x))) -> (x : a ** (Member x (head :: xs), p x))
shiftWitness head (x ** (at, px)) = (x ** (There at, px))

public export
anyToExists : {p : a -> Type} -> (xs : List a) -> Any p xs -> (x : a ** (Member x xs, p x))
anyToExists (x :: xs) (Here px) = (x ** (Here Refl, px))
anyToExists (x :: xs) (There ps) = shiftWitness x (anyToExists xs ps)

public export
existsToAny : {p : a -> Type} -> (x : a ** (Member x xs, p x)) -> Any p xs
existsToAny (x ** (Here Refl, px)) = Here px
existsToAny (x ** (There member, px)) = There (existsToAny (x ** (member, px)))

public export
anyExists : {p : a -> Type} -> (xs : List a) -> Iff (Any p xs) (x : a ** (Member x xs, p x))
anyExists xs = MkIff (anyToExists xs) existsToAny
public export
allForallLeft : {p : a -> Type} -> (xs : List a) -> (ps : All p xs) ->
  forallToAll xs (allToForall ps) = ps
allForallLeft [] AllNil = Refl
allForallLeft (x :: xs) (AllCons px ps) = cong (AllCons px) (allForallLeft xs ps)

public export
allForallPointwise : {p : a -> Type} -> (xs : List a) ->
  (f : (x : a) -> Member x xs -> p x) -> (x : a) -> (member : Member x xs) ->
  allToForall (forallToAll xs f) x member = f x member
allForallPointwise (x :: xs) f x (Here Refl) = Refl
allForallPointwise (y :: xs) f x (There member) =
  allForallPointwise xs (\z, at => f z (There at)) x member

public export
anyExistsLeft : {p : a -> Type} -> (xs : List a) -> (ps : Any p xs) ->
  existsToAny (anyToExists xs ps) = ps
anyExistsLeft (x :: xs) (Here px) = Refl
anyExistsLeft (x :: xs) (There ps) with (anyToExists xs ps) proof eq
  anyExistsLeft (x :: xs) (There ps) | (y ** (member, py)) =
    cong There (transport (\w => existsToAny w = ps) eq (anyExistsLeft xs ps))

public export
anyExistsRight : {p : a -> Type} -> (xs : List a) ->
  (w : (x : a ** (Member x xs, p x))) -> anyToExists xs (existsToAny w) = w
anyExistsRight [] (x ** (member, px)) impossible
anyExistsRight (x :: xs) (x ** (Here Refl, px)) = Refl
anyExistsRight (x :: xs) (y ** (There member, py)) =
  cong (shiftWitness x) (anyExistsRight xs (y ** (member, py)))

public export
anyExistsIso : {p : a -> Type} -> (xs : List a) -> Iso (Any p xs) (x : a ** (Member x xs, p x))
anyExistsIso xs = MkIso (anyToExists xs) existsToAny (anyExistsLeft xs) (anyExistsRight xs)
-- endregion quantified-laws

-- region decidable-split
public export
allBool : (a -> Bool) -> List a -> Bool
allBool p [] = True
allBool p (x :: xs) = boolAnd (p x) (allBool p xs)

public export
decAll : {p : a -> Type} -> ((x : a) -> Dec (p x)) -> (xs : List a) -> Dec (All p xs)
decAll decide [] = Yes AllNil
decAll decide (x :: xs) = case decide x of
  No nx => No (\(AllCons px ps) => nx px)
  Yes px => case decAll decide xs of
    Yes ps => Yes (AllCons px ps)
    No nxs => No (\(AllCons qx ps) => nxs ps)

public export
decAny : {p : a -> Type} -> ((x : a) -> Dec (p x)) -> (xs : List a) -> Dec (Any p xs)
decAny decide [] = No empty
  where
  empty : Any p [] -> Void
  empty ps impossible
decAny decide (x :: xs) = case decide x of
  Yes px => Yes (Here px)
  No nx => case decAny decide xs of
    Yes ps => Yes (There ps)
    No nxs => No (reject nx nxs)
  where
  reject : Refutes (p x) -> Refutes (Any p xs) -> Refutes (Any p (x :: xs))
  reject nx nxs (Here px) = nx px
  reject nx nxs (There ps) = nxs ps

public export
data Merge : List a -> List a -> List a -> Type where
  MergeNil : Merge [] [] []
  MergeLeft : Merge xs ys zs -> Merge (x :: xs) ys (x :: zs)
  MergeRight : Merge xs ys zs -> Merge xs (y :: ys) (y :: zs)

public export
split : {p : a -> Type} -> ((x : a) -> Dec (p x)) -> (zs : List a) ->
  (xs : List a ** (ys : List a ** (Merge xs ys zs, (All p xs, All (\x => Refutes (p x)) ys))))
split decide [] = ([] ** ([] ** (MergeNil, (AllNil, AllNil))))
split decide (z :: zs) = case split decide zs of
  (xs ** (ys ** (merged, (positive, negative)))) => case decide z of
    Yes pz => (z :: xs ** (ys ** (MergeLeft merged, (AllCons pz positive, negative))))
    No nz => (xs ** (z :: ys ** (MergeRight merged, (positive, AllCons nz negative))))

public export
mergeExample : Merge [1, 4] [2, 3] (the (List Nat) [1, 2, 3, 4])
mergeExample = MergeLeft (MergeRight (MergeRight (MergeLeft MergeNil)))
-- endregion decidable-split
