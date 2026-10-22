module PLFA.Part2.Inference

import public PLFA.Part2.DeBruijn

%default total

-- region syntax
mutual
  public export
  data SynthTerm : Nat -> Type where
    SVariable : Fin n -> SynthTerm n
    SApply : SynthTerm n -> CheckTerm n -> SynthTerm n
    Annotate : CheckTerm n -> Ty -> SynthTerm n

  public export
  data CheckTerm : Nat -> Type where
    CLambda : CheckTerm (S n) -> CheckTerm n
    CZero : CheckTerm n
    CSucc : CheckTerm n -> CheckTerm n
    CCase : SynthTerm n -> CheckTerm n -> CheckTerm (S n) -> CheckTerm n
    CFix : CheckTerm (S n) -> CheckTerm n
    Embed : SynthTerm n -> CheckTerm n
-- endregion syntax

-- region judgements
mutual
  public export
  data Synth : (0 gamma : Context n) -> (0 t : SynthTerm n) -> (0 a : Ty) -> Type where
    SyVar : (i : Fin n) -> Synth gamma (SVariable i) (index i gamma)
    SyApp : {a : Ty} -> {0 gamma : Context n} -> {0 b : Ty} ->
      {0 f : SynthTerm n} -> {0 arg : CheckTerm n} ->
      Synth gamma f (Arr a b) -> Check gamma arg a -> Synth gamma (SApply f arg) b
    SyAnn : Check gamma t a -> Synth gamma (Annotate t a) a

  public export
  data Check : (0 gamma : Context n) -> (0 t : CheckTerm n) -> (0 a : Ty) -> Type where
    ChLam : Check (a :: gamma) b c -> Check gamma (CLambda b) (Arr a c)
    ChZero : Check gamma CZero TNat
    ChSucc : Check gamma t TNat -> Check gamma (CSucc t) TNat
    ChCase : {0 gamma : Context n} -> {0 a : Ty} ->
      {0 t : SynthTerm n} -> {0 z : CheckTerm n} -> {0 s : CheckTerm (S n)} ->
      Synth gamma t TNat -> Check gamma z a -> Check (TNat :: gamma) s a ->
      Check gamma (CCase t z s) a
    ChFix : Check (a :: gamma) b a -> Check gamma (CFix b) a
    ChEmbed : {a : Ty} -> {0 gamma : Context n} -> {0 t : SynthTerm n} -> {0 b : Ty} ->
      Synth gamma t a -> a = b -> Check gamma (Embed t) b
-- endregion judgements

-- region equality
public export
natNotArrow : TNat = Arr a b -> Void
natNotArrow Refl impossible

public export
arrowNotNat : Arr a b = TNat -> Void
arrowNotNat Refl impossible

public export
arrDomain : Arr a b = Arr c d -> a = c
arrDomain Refl = Refl

public export
arrCodomain : Arr a b = Arr c d -> b = d
arrCodomain Refl = Refl

public export
typeEqual : (a, b : Ty) -> Dec (a = b)
typeEqual TNat TNat = Yes Refl
typeEqual TNat (Arr a b) = No natNotArrow
typeEqual (Arr a b) TNat = No arrowNotNat
typeEqual (Arr a b) (Arr c d) = case typeEqual a c of
  No different => No (\eq => different (arrDomain eq))
  Yes Refl => case typeEqual b d of
    No different => No (\eq => different (arrCodomain eq))
    Yes Refl => Yes Refl

public export
synthUnique : Synth gamma t a -> Synth gamma t b -> a = b
synthUnique (SyVar i) (SyVar i) = Refl
synthUnique (SyApp f a) (SyApp g b) = arrCodomain (synthUnique f g)
synthUnique (SyAnn p) (SyAnn q) = Refl

public export
convertCheck : a = b -> Check gamma t a -> Check gamma t b
convertCheck Refl p = p

lambdaNotNat : Check gamma (CLambda t) TNat -> Void
lambdaNotNat (ChLam p) impossible

zeroNotArrow : Check gamma CZero (Arr a b) -> Void
zeroNotArrow ChZero impossible

succNotArrow : Check gamma (CSucc t) (Arr a b) -> Void
succNotArrow (ChSucc p) impossible
-- endregion equality

-- region decision
mutual
  public export
  synthesize : (gamma : Context n) -> (t : SynthTerm n) ->
    Dec (a : Ty ** Synth gamma t a)
  synthesize gamma (SVariable i) = Yes (index i gamma ** SyVar i)
  synthesize gamma (Annotate t a) = case check gamma t a of
    Yes p => Yes (a ** SyAnn p)
    No bad => No (\(_ ** SyAnn p) => bad p)
  synthesize gamma (SApply f arg) = case synthesize gamma f of
    No bad => No (\(b ** SyApp {a} pf pa) => bad (Arr a b ** pf))
    Yes (TNat ** pf) => No (\(_ ** SyApp qf qa) => natNotArrow (synthUnique pf qf))
    Yes (Arr a b ** pf) => case check gamma arg a of
      Yes pa => Yes (b ** SyApp pf pa)
      No bad => No (\(_ ** SyApp qf qa) =>
        bad (convertCheck (sym (arrDomain (synthUnique pf qf))) qa))

  public export
  check : (gamma : Context n) -> (t : CheckTerm n) -> (a : Ty) -> Dec (Check gamma t a)
  check gamma (CLambda b) TNat = No lambdaNotNat
  check gamma (CLambda b) (Arr a c) = case check (a :: gamma) b c of
    Yes p => Yes (ChLam p)
    No bad => No (\(ChLam p) => bad p)
  check gamma CZero TNat = Yes ChZero
  check gamma CZero (Arr a b) = No zeroNotArrow
  check gamma (CSucc t) TNat = case check gamma t TNat of
    Yes p => Yes (ChSucc p)
    No bad => No (\(ChSucc p) => bad p)
  check gamma (CSucc t) (Arr a b) = No succNotArrow
  check gamma (CCase t z s) a = case synthesize gamma t of
    No bad => No (\(ChCase pt pz ps) => bad (TNat ** pt))
    Yes (Arr b c ** pt) => No (\(ChCase qt qz qs) => arrowNotNat (synthUnique pt qt))
    Yes (TNat ** pt) => case check gamma z a of
      No bad => No (\(ChCase qt qz qs) => bad qz)
      Yes pz => case check (TNat :: gamma) s a of
        No bad => No (\(ChCase qt qz qs) => bad qs)
        Yes ps => Yes (ChCase pt pz ps)
  check gamma (CFix b) a = case check (a :: gamma) b a of
    Yes p => Yes (ChFix p)
    No bad => No (\(ChFix p) => bad p)
  check gamma (Embed t) a = case synthesize gamma t of
    No bad => No (\(ChEmbed {a = b} p eq) => bad (b ** p))
    Yes (b ** p) => case typeEqual b a of
      Yes Refl => Yes (ChEmbed p Refl)
      No different => No (\(ChEmbed q eq) => different (trans (synthUnique p q) eq))
-- endregion decision

-- region soundness
mutual
  public export
  eraseSynth : SynthTerm n -> Raw n
  eraseSynth (SVariable i) = RVar i
  eraseSynth (SApply f a) = RApp (eraseSynth f) (eraseCheck a)
  eraseSynth (Annotate t a) = eraseCheck t

  public export
  eraseCheck : CheckTerm n -> Raw n
  eraseCheck (CLambda b) = RLam (eraseCheck b)
  eraseCheck CZero = RZero
  eraseCheck (CSucc t) = RSucc (eraseCheck t)
  eraseCheck (CCase t z s) = RCase (eraseSynth t) (eraseCheck z) (eraseCheck s)
  eraseCheck (CFix b) = RFix (eraseCheck b)
  eraseCheck (Embed t) = eraseSynth t

mutual
  public export
  synthSound : Synth gamma t a -> HasType gamma (eraseSynth t) a
  synthSound (SyVar i) = TVar i
  synthSound (SyApp f a) = TApp (synthSound f) (checkSound a)
  synthSound (SyAnn p) = checkSound p

  public export
  checkSound : Check gamma t a -> HasType gamma (eraseCheck t) a
  checkSound (ChLam b) = TLam (checkSound b)
  checkSound ChZero = TZero
  checkSound (ChSucc t) = TSucc (checkSound t)
  checkSound (ChCase t z s) = TCase (synthSound t) (checkSound z) (checkSound s)
  checkSound (ChFix b) = TFix (checkSound b)
  checkSound (ChEmbed p Refl) = synthSound p

public export
elaborateSynth : Synth gamma t a -> Term gamma a
elaborateSynth p = elaborate (synthSound p)

public export
elaborateCheck : Check gamma t a -> Term gamma a
elaborateCheck p = elaborate (checkSound p)

public export
synthErasure : (p : Synth gamma t a) -> forget (elaborateSynth p) = eraseSynth t
synthErasure p = forgetElaborate (synthSound p)

public export
checkErasure : (p : Check gamma t a) -> forget (elaborateCheck p) = eraseCheck t
checkErasure p = forgetElaborate (checkSound p)
-- endregion soundness

-- region examples
public export
two : CheckTerm n
two = CSucc (CSucc CZero)

public export
identity : CheckTerm n
identity = CLambda (Embed (SVariable FZ))

public export
identityTwo : SynthTerm 0
identityTwo = SApply (Annotate Inference.identity (Arr TNat TNat)) Inference.two

public export
identityTwoDerivation : Synth [] Inference.identityTwo TNat
identityTwoDerivation = SyApp (SyAnn (ChLam (ChEmbed (SyVar FZ) Refl)))
  (ChSucc (ChSucc ChZero))

public export
plus : SynthTerm n
plus = Annotate
  (CFix (CLambda (CLambda
    (CCase (SVariable (FS FZ)) (Embed (SVariable FZ))
      (CSucc (Embed (SApply
        (SApply (SVariable (FS (FS (FS FZ)))) (Embed (SVariable FZ)))
        (Embed (SVariable (FS FZ))))))))))
  (Arr TNat (Arr TNat TNat))

public export
plusTwoTwo : SynthTerm 0
plusTwoTwo = SApply (SApply Inference.plus Inference.two) Inference.two

public export
isYes : Dec p -> Bool
isYes (Yes _) = True
isYes (No _) = False

public export
plusAccepted : isYes (synthesize [] Inference.plusTwoTwo) = True
plusAccepted = Refl
-- endregion examples

-- region solutions
-- Exercise 1: a lambda checks against an arrow; no global principal type is required.
public export
identityAt : (a : Ty) -> Check gamma Inference.identity (Arr a a)
identityAt a = ChLam (ChEmbed {a} (SyVar FZ) Refl)

-- Exercise 2: reject applying a number, with a proof excluding every result type.
public export
badApplication : SynthTerm 0
badApplication = SApply (Annotate CZero TNat) CZero

public export
badApplicationImpossible : (a : Ty ** Synth [] Inference.badApplication a) -> Void
badApplicationImpossible (_ ** SyApp (SyAnn ChZero) _) impossible

public export
badRejected : isYes (synthesize [] Inference.badApplication) = False
badRejected = Refl

-- Exercise 3: annotations can make an otherwise typable erased term fail checking.
public export
badAnnotation : SynthTerm 0
badAnnotation = Annotate CZero (Arr TNat TNat)

public export
annotationRejected : isYes (synthesize [] Inference.badAnnotation) = False
annotationRejected = Refl

public export
erasureStillTyped : HasType [] (eraseSynth Inference.badAnnotation) TNat
erasureStillTyped = TZero
-- endregion solutions

-- region completeness
public export
synthesizeComplete : (gamma : Context n) -> (t : SynthTerm n) ->
  (a : Ty) -> Synth gamma t a -> isYes (synthesize gamma t) = True
synthesizeComplete gamma t a p with (synthesize gamma t)
  synthesizeComplete gamma t a p | Yes answer = Refl
  synthesizeComplete gamma t a p | No bad = void (bad (a ** p))

public export
checkComplete : (gamma : Context n) -> (t : CheckTerm n) ->
  (a : Ty) -> Check gamma t a -> isYes (check gamma t a) = True
checkComplete gamma t a p with (check gamma t a)
  checkComplete gamma t a p | Yes answer = Refl
  checkComplete gamma t a p | No bad = void (bad p)
-- endregion completeness

-- region execution
public export
inferredTerm : Maybe (Term [] TNat)
inferredTerm = case synthesize [] Inference.plusTwoTwo of
  No bad => Nothing
  Yes (TNat ** derivation) => Just (elaborateSynth derivation)
  Yes (Arr a b ** derivation) => Nothing

public export
inferredTermCorrect : Inference.inferredTerm =
  Just (App (App DeBruijn.add (num 2)) (num 2))
inferredTermCorrect = Refl

public export
inferredResult : Maybe Nat
inferredResult = maybe Nothing (runNatural 100) Inference.inferredTerm

public export
inferredComputed : Inference.inferredResult = Just 4
inferredComputed = trans (cong (maybe Nothing (runNatural 100)) inferredTermCorrect) Refl
-- endregion execution
