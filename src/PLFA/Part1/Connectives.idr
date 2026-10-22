module PLFA.Part1.Connectives

import public PLFA.Part1.Isomorphism

%default total

-- region products
public export
pairEta : (p : (a, b)) -> (fst p, snd p) = p
pairEta (x, y) = Refl

public export
productComm : Iso (a, b) (b, a)
productComm = MkIso (\(x, y) => (y, x)) (\(y, x) => (x, y))
  (\(x, y) => Refl) (\(y, x) => Refl)

public export
productAssoc : Iso ((a, b), c) (a, (b, c))
productAssoc = MkIso (\((x, y), z) => (x, (y, z)))
  (\(x, (y, z)) => ((x, y), z))
  (\((x, y), z) => Refl) (\(x, (y, z)) => Refl)

public export
iffProduct : Iso (Iff a b) (a -> b, b -> a)
iffProduct = MkIso (\i => (i.to, i.from)) (\(f, g) => MkIff f g)
  (\(MkIff f g) => Refl) (\(f, g) => Refl)

public export
unitLeft : Iso ((), a) a
unitLeft = MkIso snd (\x => ((), x)) (\((), x) => Refl) (\x => Refl)

public export
unitRight : Iso (a, ()) a
unitRight = isoTrans productComm unitLeft
-- endregion products

-- region sums
public export
sumCase : (a -> c) -> (b -> c) -> Either a b -> c
sumCase f g (Left x) = f x
sumCase f g (Right y) = g y

public export
sumEta : (s : Either a b) -> sumCase Left Right s = s
sumEta (Left x) = Refl
sumEta (Right y) = Refl

public export
sumUnique : (h : Either a b -> c) -> (s : Either a b) ->
  sumCase (\x => h (Left x)) (\y => h (Right y)) s = h s
sumUnique h (Left x) = Refl
sumUnique h (Right y) = Refl

public export
sumComm : Iso (Either a b) (Either b a)
sumComm = MkIso (sumCase Right Left) (sumCase Right Left) round round
  where
  round : (s : Either x y) -> sumCase Right Left (sumCase Right Left s) = s
  round (Left x) = Refl
  round (Right y) = Refl

public export
sumAssocTo : Either (Either a b) c -> Either a (Either b c)
sumAssocTo (Left (Left x)) = Left x
sumAssocTo (Left (Right y)) = Right (Left y)
sumAssocTo (Right z) = Right (Right z)

public export
sumAssocFrom : Either a (Either b c) -> Either (Either a b) c
sumAssocFrom (Left x) = Left (Left x)
sumAssocFrom (Right (Left y)) = Left (Right y)
sumAssocFrom (Right (Right z)) = Right z

public export
sumAssoc : Iso (Either (Either a b) c) (Either a (Either b c))
sumAssoc = MkIso sumAssocTo sumAssocFrom left right
  where
  left : (s : Either (Either a b) c) -> sumAssocFrom (sumAssocTo s) = s
  left (Left (Left x)) = Refl
  left (Left (Right y)) = Refl
  left (Right z) = Refl
  right : (s : Either a (Either b c)) -> sumAssocTo (sumAssocFrom s) = s
  right (Left x) = Refl
  right (Right (Left y)) = Refl
  right (Right (Right z)) = Refl

public export
explode : Void -> a
explode v impossible

public export
emptyLeft : Iso (Either Void a) a
emptyLeft = MkIso (sumCase explode id) Right left (\x => Refl)
  where
  left : (s : Either Void a) -> Right (sumCase PLFA.Part1.Connectives.explode Prelude.id s) = s
  left (Left v) = explode v
  left (Right x) = Refl

public export
emptyRight : Iso (Either a Void) a
emptyRight = isoTrans sumComm emptyLeft
-- endregion sums

-- region functions
public export
curryPair : ((a, b) -> c) -> a -> b -> c
curryPair f x y = f (x, y)

public export
uncurryPair : (a -> b -> c) -> (a, b) -> c
uncurryPair f (x, y) = f x y

public export
currying : Iff (a -> b -> c) ((a, b) -> c)
currying = MkIff uncurryPair curryPair

public export
curryRound : (f : a -> b -> c) -> (x : a) -> (y : b) ->
  curryPair (uncurryPair f) x y = f x y
curryRound f x y = Refl

public export
uncurryRound : (f : (a, b) -> c) -> (p : (a, b)) ->
  uncurryPair (curryPair f) p = f p
uncurryRound f (x, y) = Refl

public export
functionSum : Iff (Either a b -> c) (a -> c, b -> c)
functionSum = MkIff (\h => (\x => h (Left x), \y => h (Right y)))
  (\(f, g) => sumCase f g)

public export
functionSumRound : (h : Either a b -> c) -> (s : Either a b) ->
  sumCase (\x => h (Left x)) (\y => h (Right y)) s = h s
functionSumRound = sumUnique

public export
functionProduct : Iff (a -> (b, c)) (a -> b, a -> c)
functionProduct = MkIff (\h => (\x => fst (h x), \x => snd (h x)))
  (\(f, g), x => (f x, g x))

public export
functionProductRound : (h : a -> (b, c)) -> (x : a) ->
  (fst (h x), snd (h x)) = h x
functionProductRound h x = pairEta (h x)
public export
functionSumHandlers : (f : a -> c) -> (g : b -> c) -> (x : a) -> (y : b) ->
  (sumCase f g (Left x), sumCase f g (Right y)) = (f x, g y)
functionSumHandlers f g x y = Refl

public export
functionProductHandlers : (f : a -> b) -> (g : a -> c) -> (x : a) ->
  (fst (f x, g x), snd (f x, g x)) = (f x, g x)
functionProductHandlers f g x = Refl
-- endregion functions

-- region distribution
public export
distribute : (Either a b, c) -> Either (a, c) (b, c)
distribute (Left x, z) = Left (x, z)
distribute (Right y, z) = Right (y, z)

public export
factor : Either (a, c) (b, c) -> (Either a b, c)
factor (Left (x, z)) = (Left x, z)
factor (Right (y, z)) = (Right y, z)

public export
productSum : Iso (Either a b, c) (Either (a, c) (b, c))
productSum = MkIso distribute factor left right
  where
  left : (p : (Either a b, c)) -> factor (distribute p) = p
  left (Left x, z) = Refl
  left (Right y, z) = Refl
  right : (s : Either (a, c) (b, c)) -> distribute (factor s) = s
  right (Left (x, z)) = Refl
  right (Right (y, z)) = Refl

public export
sumProductTo : Either (a, b) c -> (Either a c, Either b c)
sumProductTo (Left (x, y)) = (Left x, Left y)
sumProductTo (Right z) = (Right z, Right z)

public export
sumProductFrom : (Either a c, Either b c) -> Either (a, b) c
sumProductFrom (Left x, Left y) = Left (x, y)
sumProductFrom (Left x, Right z) = Right z
sumProductFrom (Right z, s) = Right z

public export
sumProduct : Embedding (Either (a, b) c) (Either a c, Either b c)
sumProduct = MkEmbedding sumProductTo sumProductFrom left
  where
  left : (s : Either (a, b) c) -> sumProductFrom (sumProductTo s) = s
  left (Left (x, y)) = Refl
  left (Right z) = Refl

public export
weakDistribution : (Either a b, c) -> Either a (b, c)
weakDistribution (Left x, z) = Left x
weakDistribution (Right y, z) = Right (y, z)

public export
disjunctToConjunct : Either (a, b) (c, d) -> (Either a c, Either b d)
disjunctToConjunct (Left (x, y)) = (Left x, Left y)
disjunctToConjunct (Right (z, w)) = (Right z, Right w)

public export
noGeneralConverse : ((Either () Void, Either Void ()) -> Either ((), Void) (Void, ())) -> Void
noGeneralConverse f = case f (Left (), Right ()) of
  Left (u, v) => v
  Right (v, u) => v
-- endregion distribution
