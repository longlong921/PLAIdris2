module PLFA.Part3.Denotational

import public Data.Fin
import Data.Vect
import public PLFA.Part2.Untyped

%default total
%unbound_implicits off

-- Adapted from PLFA, commit 1c39b1e82caa4283274e64ba58c3bc3c9ab781eb.
-- Philip Wadler, Wen Kokke, Jeremy G. Siek; CC BY 4.0.

-- region information
public export
data Value = Bottom | Arrow Value Value | Join Value Value

public export
data Info : Value -> Value -> Type where
  IBot : {v : Value} -> Info Bottom v
  IJoinL : {a, b, c : Value} ->
           Info a c -> Info b c -> Info (Join a b) c
  IJoinR1 : {a, b, c : Value} -> Info a b -> Info a (Join b c)
  IJoinR2 : {a, b, c : Value} -> Info a c -> Info a (Join b c)
  ITrans : {a, b, c : Value} -> Info a b -> Info b c -> Info a c
  IFun : {a, b, a', b' : Value} ->
         Info a' a -> Info b b' -> Info (Arrow a b) (Arrow a' b')
  IDist : {a, b, c : Value} ->
          Info (Arrow a (Join b c)) (Join (Arrow a b) (Arrow a c))

public export
infoRefl : {v : Value} -> Info v v
infoRefl {v = Bottom} = IBot
infoRefl {v = Arrow a b} = IFun infoRefl infoRefl
infoRefl {v = Join a b} = IJoinL (IJoinR1 infoRefl) (IJoinR2 infoRefl)

public export
joinMono : {a, b, c, d : Value} ->
           Info a c -> Info b d -> Info (Join a b) (Join c d)
joinMono p q = IJoinL (IJoinR1 p) (IJoinR2 q)

public export
mixedDist : {a, b, c, d : Value} ->
            Info (Arrow (Join a c) (Join b d))
                 (Join (Arrow a b) (Arrow c d))
mixedDist = ITrans IDist
              (joinMono (IFun (IJoinR1 infoRefl) infoRefl)
                        (IFun (IJoinR2 infoRefl) infoRefl))

public export
joinLeft : {a, b, c : Value} -> Info (Join a b) c -> Info a c
joinLeft p = ITrans (IJoinR1 infoRefl) p

public export
joinRight : {a, b, c : Value} -> Info (Join a b) c -> Info b c
joinRight p = ITrans (IJoinR2 infoRefl) p

public export
joinCommute : {a, b : Value} -> Info (Join a b) (Join b a)
joinCommute = IJoinL (IJoinR2 infoRefl) (IJoinR1 infoRefl)

public export
joinIdempotent : {a : Value} -> Info (Join a a) a
joinIdempotent = IJoinL infoRefl infoRefl
-- endregion information

-- region environments
public export
Env : Nat -> Type
Env n = Fin n -> Value

public export
emptyEnv : Env 0
emptyEnv x impossible

public export
extendEnv : {n : Nat} -> Env n -> Value -> Env (S n)
extendEnv g v FZ = v
extendEnv g v (FS x) = g x

public export
headEnv : {n : Nat} -> Env (S n) -> Value
headEnv g = g FZ

public export
tailEnv : {n : Nat} -> Env (S n) -> Env n
tailEnv g x = g (FS x)

public export
envEta : {n : Nat} -> (g : Env (S n)) -> (x : Fin (S n)) ->
         g x = extendEnv (tailEnv g) (headEnv g) x
envEta g FZ = Refl
envEta g (FS x) = Refl

public export
EnvLE : {n : Nat} -> Env n -> Env n -> Type
EnvLE g d = (x : Fin n) -> Info (g x) (d x)

public export
bottomEnv : {n : Nat} -> Env n
bottomEnv x = Bottom

public export
joinEnv : {n : Nat} -> Env n -> Env n -> Env n
joinEnv g d x = Join (g x) (d x)

public export
envRefl : {n : Nat} -> {g : Env n} -> EnvLE g g
envRefl x = infoRefl

public export
envJoinLeft : {n : Nat} -> (g, d : Env n) -> EnvLE g (joinEnv g d)
envJoinLeft g d x = IJoinR1 infoRefl

public export
envJoinRight : {n : Nat} -> (g, d : Env n) -> EnvLE d (joinEnv g d)
envJoinRight g d x = IJoinR2 infoRefl

public export
extendMono : {n : Nat} -> {g, d : Env n} -> {a, b : Value} ->
             EnvLE g d -> Info a b -> EnvLE (extendEnv g a) (extendEnv d b)
extendMono le p FZ = p
extendMono le p (FS x) = le x
-- endregion environments

-- region judgment
public export
data Denote : {n : Nat} -> Env n -> Tm n -> Value -> Type where
  DVar : {n : Nat} -> {g : Env n} -> {x : Fin n} ->
         Denote g (Var x) (g x)
  DApp : {n : Nat} -> {g : Env n} -> {l, m : Tm n} -> {a, b : Value} ->
         Denote g l (Arrow a b) -> Denote g m a -> Denote g (App l m) b
  DLam : {n : Nat} -> {g : Env n} -> {body : Tm (S n)} -> {a, b : Value} ->
         Denote (extendEnv g a) body b -> Denote g (Lam body) (Arrow a b)
  DBot : {n : Nat} -> {g : Env n} -> {m : Tm n} -> Denote g m Bottom
  DJoin : {n : Nat} -> {g : Env n} -> {m : Tm n} -> {a, b : Value} ->
          Denote g m a -> Denote g m b -> Denote g m (Join a b)
  DSub : {n : Nat} -> {g : Env n} -> {m : Tm n} -> {a, b : Value} ->
         Denote g m a -> Info b a -> Denote g m b

public export
envMono : {n : Nat} -> {g, d : Env n} -> {m : Tm n} -> {v : Value} ->
          Denote g m v -> EnvLE g d -> Denote d m v
envMono (DVar {x}) le = DSub DVar (le x)
envMono (DApp f a) le = DApp (envMono f le) (envMono a le)
envMono (DLam body) le = DLam (envMono body (extendMono le infoRefl))
envMono DBot le = DBot
envMono (DJoin p q) le = DJoin (envMono p le) (envMono q le)
envMono (DSub p lt) le = DSub (envMono p le) lt

public export
upEnv : {n : Nat} -> {g : Env n} -> {m : Tm (S n)} -> {v, a, b : Value} ->
        Denote (extendEnv g a) m v -> Info a b -> Denote (extendEnv g b) m v
upEnv p le = envMono p (extendMono envRefl le)

public export
applyLarger : {n : Nat} -> {g : Env n} -> {l, m : Tm n} -> {a, b, c : Value} ->
              Denote g l (Arrow a c) -> Denote g m b -> Info a b ->
              Denote g (App l m) c
applyLarger f arg le = DApp f (DSub arg le)
-- endregion judgment

-- region renaming
public export
renameEnvLift : {m, n : Nat} -> {g : Env m} -> {d : Env n} -> {v : Value} ->
  (rho : Fin m -> Fin n) -> ((x : Fin m) -> Info (g x) (d (rho x))) ->
  (x : Fin (S m)) ->
  Info (extendEnv g v x) (extendEnv d v (liftRen rho x))
renameEnvLift rho le FZ = infoRefl
renameEnvLift rho le (FS x) = le x

public export
renamePres : {m, n : Nat} -> {g : Env m} -> {d : Env n} ->
  {tm : Tm m} -> {v : Value} ->
  (rho : Fin m -> Fin n) -> ((x : Fin m) -> Info (g x) (d (rho x))) ->
  Denote g tm v -> Denote d (rename rho tm) v
renamePres rho le (DVar {x}) = DSub DVar (le x)
renamePres rho le (DApp f a) = DApp (renamePres rho le f) (renamePres rho le a)
renamePres rho le (DLam body) =
  DLam (renamePres (liftRen rho) (renameEnvLift rho le) body)
renamePres rho le DBot = DBot
renamePres rho le (DJoin p q) = DJoin (renamePres rho le p) (renamePres rho le q)
renamePres rho le (DSub p lt) = DSub (renamePres rho le p) lt
-- endregion renaming

-- region equality
public export
Denotation : Nat -> Type
Denotation n = Env n -> Value -> Type

public export
meaning : {n : Nat} -> Tm n -> Denotation n
meaning m g v = Denote g m v

public export
DenEq : {n : Nat} -> Denotation n -> Denotation n -> Type
DenEq d e = (g : Env n) -> (v : Value) -> (d g v -> e g v, e g v -> d g v)

public export
SemEq : {n : Nat} -> Tm n -> Tm n -> Type
SemEq m k = DenEq (meaning m) (meaning k)

public export
denEqRefl : {n : Nat} -> {d : Denotation n} -> DenEq d d
denEqRefl g v = (\p => p, \p => p)

public export
denEqSym : {n : Nat} -> {d, e : Denotation n} -> DenEq d e -> DenEq e d
denEqSym eq g v = (snd (eq g v), fst (eq g v))

public export
denEqTrans : {n : Nat} -> {d, e, f : Denotation n} ->
             DenEq d e -> DenEq e f -> DenEq d f
denEqTrans de ef g v = (\p => fst (ef g v) (fst (de g v) p),
                       \p => snd (de g v) (snd (ef g v) p))
-- endregion equality

-- region examples
public export
identityTerm : Tm 0
identityTerm = Lam (Var FZ)

public export
selfTerm : Tm 0
selfTerm = Lam (App (Var FZ) (Var FZ))

public export
omegaTerm : Tm 0
omegaTerm = App selfTerm selfTerm

public export
identityMeaning : {a : Value} -> Denote emptyEnv identityTerm (Arrow a a)
identityMeaning = DLam DVar

public export
identityTable : Denote emptyEnv identityTerm
                  (Join (Arrow Bottom Bottom)
                        (Arrow (Arrow Bottom Bottom) (Arrow Bottom Bottom)))
identityTable = DJoin identityMeaning identityMeaning

public export
identitySelf : {a : Value} ->
               Denote emptyEnv (App identityTerm identityTerm) (Arrow a a)
identitySelf = DApp identityMeaning identityMeaning

public export
selfMeaning : {a, b : Value} ->
              Denote emptyEnv selfTerm (Arrow (Join (Arrow a b) a) b)
selfMeaning = DLam (DApp (DSub DVar (IJoinR1 infoRefl))
                         (DSub DVar (IJoinR2 infoRefl)))

public export
omegaBottom : Denote emptyEnv omegaTerm Bottom
omegaBottom = DApp selfMeaning (DJoin (DLam DBot) DBot)

public export
churchTwo : Tm 0
churchTwo = Lam (Lam (App (Var (FS FZ)) (App (Var (FS FZ)) (Var FZ))))

public export
churchTwoMeaning : {a, b, c : Value} ->
  Denote emptyEnv churchTwo (Arrow (Join (Arrow a b) (Arrow b c)) (Arrow a c))
churchTwoMeaning = DLam (DLam
  (DApp (DSub DVar (IJoinR2 infoRefl))
        (DApp (DSub DVar (IJoinR1 infoRefl)) DVar)))
-- endregion examples

-- region membership
public export
data Member : Value -> Value -> Type where
  MBottom : Member Bottom Bottom
  MArrow : {a, b : Value} -> Member (Arrow a b) (Arrow a b)
  MLeft : {a, b, c : Value} -> Member a b -> Member a (Join b c)
  MRight : {a, b, c : Value} -> Member a c -> Member a (Join b c)

public export
Included : Value -> Value -> Type
Included u v = {entry : Value} -> Member entry u -> Member entry v

public export
memberInfo : {u, v : Value} -> Member u v -> Info u v
memberInfo MBottom = IBot
memberInfo MArrow = infoRefl
memberInfo (MLeft p) = IJoinR1 (memberInfo p)
memberInfo (MRight p) = IJoinR2 (memberInfo p)

public export
includedInfo : {u, v : Value} -> Included u v -> Info u v
includedInfo {u = Bottom} inc = IBot
includedInfo {u = Arrow a b} inc = memberInfo (inc MArrow)
includedInfo {u = Join a b} inc =
  IJoinL (includedInfo (\p => inc (MLeft p)))
         (includedInfo (\p => inc (MRight p)))

public export
data AllFuns : Value -> Type where
  FArrow : {a, b : Value} -> AllFuns (Arrow a b)
  FJoin : {a, b : Value} -> AllFuns a -> AllFuns b -> AllFuns (Join a b)

public export
someFunction : {v : Value} -> AllFuns v ->
               (a : Value ** (b : Value ** Member (Arrow a b) v))
someFunction (FArrow {a} {b}) = (a ** (b ** MArrow))
someFunction (FJoin l r) =
  let (a ** (b ** p)) = someFunction l in (a ** (b ** MLeft p))

public export
joinDomain : Value -> Value
joinDomain Bottom = Bottom
joinDomain (Arrow a b) = a
joinDomain (Join a b) = Join (joinDomain a) (joinDomain b)

public export
joinCodomain : Value -> Value
joinCodomain Bottom = Bottom
joinCodomain (Arrow a b) = b
joinCodomain (Join a b) = Join (joinCodomain a) (joinCodomain b)

public export
domainMember : {a, b, v : Value} ->
               Member (Arrow a b) v -> Included a (joinDomain v)
domainMember MArrow p = p
domainMember (MLeft m) p = MLeft (domainMember m p)
domainMember (MRight m) p = MRight (domainMember m p)

public export
bottomNotArrowMember : {a, b : Value} -> Member Bottom (Arrow a b) -> Void
bottomNotArrowMember p impossible

public export
codomainIncluded : {u, a, b : Value} ->
                   Included u (Arrow a b) -> Included (joinCodomain u) b
codomainIncluded {u = Bottom} inc p = absurd (bottomNotArrowMember (inc MBottom))
codomainIncluded {u = Arrow c d} inc p with (inc MArrow)
  _ | MArrow = p
codomainIncluded {u = Join c d} inc (MLeft p) =
  codomainIncluded (\q => inc (MLeft q)) p
codomainIncluded {u = Join c d} inc (MRight p) =
  codomainIncluded (\q => inc (MRight q)) p
-- endregion membership

-- region factorization
public export
record Factor (whole : Value) (selected : Value) (a : Value) (b : Value) where
  constructor MkFactor
  functions : AllFuns selected
  inclusion : Included selected whole
  domainBound : Info (joinDomain selected) a
  codomainBound : Info b (joinCodomain selected)

public export
mergeFactors : {whole, p, q, a, b, c, d : Value} ->
  Factor whole p a b -> Factor whole q c d ->
  Factor whole (Join p q) (Join a c) (Join b d)
mergeFactors (MkFactor fp ip dp cp) (MkFactor fq iq dq cq) =
  MkFactor (FJoin fp fq) (\mem => case mem of
    MLeft x => ip x
    MRight x => iq x) (joinMono dp dq) (joinMono cp cq)

public export
factorAcross : {selected, mid, whole : Value} ->
  AllFuns selected -> Included selected mid ->
  ({a, b : Value} -> Member (Arrow a b) mid ->
     (s : Value ** Factor whole s a b)) ->
  (s : Value ** Factor whole s (joinDomain selected) (joinCodomain selected))
factorAcross FArrow inc ih = ih (inc MArrow)
factorAcross (FJoin fp fq) inc ih =
  let (p ** factp) = factorAcross fp (\x => inc (MLeft x)) ih
      (q ** factq) = factorAcross fq (\x => inc (MRight x)) ih in
  (Join p q ** mergeFactors factp factq)

public export
subInv : {u, v : Value} -> Info u v -> {a, b : Value} ->
  Member (Arrow a b) u -> (selected : Value ** Factor v selected a b)
subInv IBot mem impossible
subInv (IJoinL p q) (MLeft mem) = subInv p mem
subInv (IJoinL p q) (MRight mem) = subInv q mem
subInv (IJoinR1 p) mem =
  let (s ** MkFactor fs inc dom cod) = subInv p mem in
  (s ** MkFactor fs (\x => MLeft (inc x)) dom cod)
subInv (IJoinR2 p) mem =
  let (s ** MkFactor fs inc dom cod) = subInv p mem in
  (s ** MkFactor fs (\x => MRight (inc x)) dom cod)
subInv (ITrans p q) mem =
  let (s ** MkFactor fs inc dom cod) = subInv p mem
      (t ** MkFactor ft inc' dom' cod') = factorAcross fs inc (subInv q) in
  (t ** MkFactor ft inc' (ITrans dom' dom) (ITrans cod cod'))
subInv (IFun {a'} {b'} p q) MArrow =
  (Arrow a' b' ** MkFactor FArrow (\x => x) p q)
subInv (IDist {a = x} {b = y} {c = z}) mem =
  case mem of
    MArrow => (Join (Arrow x y) (Arrow x z) **
      MkFactor (FJoin FArrow FArrow) (\entry => entry) joinIdempotent infoRefl)

public export
functionFactor : {a, b, v : Value} -> Info (Arrow a b) v ->
                 (selected : Value ** Factor v selected a b)
functionFactor p = subInv p MArrow

public export
functionMemberBound : {whole, selected, a, b, c, d : Value} ->
  Factor whole selected a b -> Member (Arrow c d) selected -> Info c a
functionMemberBound (MkFactor fs inc dom cod) mem =
  ITrans (includedInfo (domainMember mem)) dom

public export
arrowInversion : {a, b, c, d : Value} ->
                 Info (Arrow a b) (Arrow c d) -> (Info c a, Info b d)
arrowInversion lt =
  let (s ** fact@(MkFactor fs inc dom cod)) = functionFactor lt
      (e ** (f ** mem)) = someFunction fs in
  case inc mem of
    MArrow => (functionMemberBound fact mem,
               ITrans cod (includedInfo (codomainIncluded inc)))

public export
arrowNotBottom : {a, b : Value} -> Info (Arrow a b) Bottom -> Void
arrowNotBottom lt =
  let (s ** MkFactor fs inc dom cod) = functionFactor lt
      (e ** (f ** mem)) = someFunction fs in
  case inc mem of {}
-- endregion factorization

-- region church-paths
public export
iterateTerm : Nat -> Tm 2
iterateTerm Z = Var FZ
iterateTerm (S k) = App (Var (FS FZ)) (iterateTerm k)

public export
church : Nat -> Tm 0
church k = Lam (Lam (iterateTerm k))

public export
pathTable : (k : Nat) -> Vect (S k) Value -> Value
pathTable Z (a :: []) = Bottom
pathTable (S k) (a :: b :: rest) = Join (Arrow b a) (pathTable k (b :: rest))

public export
pathStart : {k : Nat} -> Vect (S k) Value -> Value
pathStart {k = Z} (a :: []) = a
pathStart {k = S k} (a :: b :: rest) = pathStart (b :: rest)

public export
pathEnd : {k : Nat} -> Vect (S k) Value -> Value
pathEnd (a :: rest) = a

public export
pathEnv : (k : Nat) -> Vect (S k) Value -> Env 2
pathEnv k path = extendEnv (extendEnv emptyEnv (pathTable k path)) (pathStart path)

public export
pathEnvGrow : {k : Nat} -> (a, b : Value) -> (rest : Vect k Value) ->
  EnvLE (pathEnv k (b :: rest)) (pathEnv (S k) (a :: b :: rest))
pathEnvGrow a b rest FZ = infoRefl
pathEnvGrow a b rest (FS FZ) = IJoinR2 infoRefl
pathEnvGrow a b rest (FS (FS x)) impossible

public export
iterateMeaning : (k : Nat) -> (path : Vect (S k) Value) ->
  Denote (pathEnv k path) (iterateTerm k) (pathEnd path)
iterateMeaning Z (a :: []) = DVar
iterateMeaning (S k) (a :: b :: rest) =
  DApp (DSub DVar (IJoinR1 infoRefl))
       (envMono (iterateMeaning k (b :: rest)) (pathEnvGrow a b rest))

public export
churchMeaning : (k : Nat) -> (path : Vect (S k) Value) ->
  Denote emptyEnv (Denotational.church k) (Arrow (pathTable k path) (Arrow (pathStart path) (pathEnd path)))
churchMeaning k path = DLam (DLam (iterateMeaning k path))
-- endregion church-paths

-- region addition
public export
churchPlus : Tm 0
churchPlus = Lam (Lam (Lam (Lam
  (App (App (Var (FS (FS (FS FZ)))) (Var (FS FZ)))
       (App (App (Var (FS (FS FZ))) (Var (FS FZ))) (Var FZ))))))

public export
churchPlusMeaning : {f, a, b, c : Value} ->
  Denote emptyEnv churchPlus
    (Arrow (Arrow f (Arrow b c))
      (Arrow (Arrow f (Arrow a b)) (Arrow f (Arrow a c))))
churchPlusMeaning = DLam (DLam (DLam (DLam
  (DApp (DApp DVar DVar) (DApp (DApp DVar DVar) DVar)))))
-- endregion addition
