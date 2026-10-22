module PLFA.Part3.Compositional

import public PLFA.Part3.Denotational

%default total
%unbound_implicits off

-- Adapted from PLFA, commit 1c39b1e82caa4283274e64ba58c3bc3c9ab781eb.
-- Philip Wadler, Wen Kokke, Jeremy G. Siek; CC BY 4.0.

-- region lambda-equation
public export
FunDen : {n : Nat} -> Denotation (S n) -> Denotation n
FunDen d g Bottom = ()
FunDen d g (Arrow a b) = d (extendEnv g a) b
FunDen d g (Join a b) = (FunDen d g a, FunDen d g b)

public export
funDown : {n : Nat} -> {body : Tm (S n)} -> {g : Env n} -> {a, b : Value} ->
          FunDen (meaning body) g b -> Info a b -> FunDen (meaning body) g a
funDown d IBot = ()
funDown d (IJoinL p q) = (funDown d p, funDown d q)
funDown (l, r) (IJoinR1 p) = funDown l p
funDown (l, r) (IJoinR2 p) = funDown r p
funDown d (ITrans p q) = funDown (funDown d q) p
funDown d (IFun p q) = DSub (upEnv d p) q
funDown (p, q) IDist = DJoin p q

public export
lambdaForward : {n : Nat} -> {body : Tm (S n)} -> {g : Env n} -> {v : Value} ->
                Denote g (Lam body) v -> FunDen (meaning body) g v
lambdaForward (DLam body) = body
lambdaForward DBot = ()
lambdaForward (DJoin p q) = (lambdaForward p, lambdaForward q)
lambdaForward (DSub p lt) = funDown (lambdaForward p) lt

public export
lambdaBackward : {n : Nat} -> {body : Tm (S n)} -> {g : Env n} -> {v : Value} ->
                 FunDen (meaning body) g v -> Denote g (Lam body) v
lambdaBackward {v = Bottom} p = DBot
lambdaBackward {v = Arrow a b} p = DLam p
lambdaBackward {v = Join a b} (p, q) = DJoin (lambdaBackward p) (lambdaBackward q)

public export
lambdaInversion : {n : Nat} -> {body : Tm (S n)} -> {g : Env n} -> {a, b : Value} ->
                  Denote g (Lam body) (Arrow a b) -> Denote (extendEnv g a) body b
lambdaInversion d = lambdaForward d

public export
lamEquation : {n : Nat} -> {body : Tm (S n)} ->
              DenEq (meaning (Lam body)) (FunDen (meaning body))
lamEquation g v = (lambdaForward, lambdaBackward)
-- endregion lambda-equation

-- region application-equation
public export
AppDen : {n : Nat} -> Denotation n -> Denotation n -> Denotation n
AppDen d e g w = Either (Info w Bottom)
                       (a : Value ** (d g (Arrow a w), e g a))

public export
applicationInversion : {n : Nat} -> {g : Env n} -> {l, m : Tm n} -> {v : Value} ->
  Denote g (App l m) v -> AppDen (meaning l) (meaning m) g v
applicationInversion (DApp {a} f arg) = Right (a ** (f, arg))
applicationInversion DBot = Left IBot
applicationInversion (DJoin p q) with (applicationInversion p, applicationInversion q)
  _ | (Left lp, Left lq) = Left (IJoinL lp lq)
  _ | (Left lp, Right (a ** (f, arg))) =
      Right (a ** (DSub f (IFun infoRefl (IJoinL (ITrans lp IBot) infoRefl)), arg))
  _ | (Right (a ** (f, arg)), Left lq) =
      Right (a ** (DSub f (IFun infoRefl (IJoinL infoRefl (ITrans lq IBot))), arg))
  _ | (Right (a ** (f, arg)), Right (b ** (f', arg'))) =
      Right (Join a b ** (DSub (DJoin f f') mixedDist, DJoin arg arg'))
applicationInversion (DSub p lt) with (applicationInversion p)
  _ | Left le = Left (ITrans lt le)
  _ | Right (a ** (f, arg)) = Right (a ** (DSub f (IFun infoRefl lt), arg))

public export
applicationBackward : {n : Nat} -> {g : Env n} -> {l, m : Tm n} -> {v : Value} ->
  AppDen (meaning l) (meaning m) g v -> Denote g (App l m) v
applicationBackward (Left lt) = DSub DBot lt
applicationBackward (Right (a ** (f, arg))) = DApp f arg

public export
appEquation : {n : Nat} -> {l, m : Tm n} ->
              DenEq (meaning (App l m)) (AppDen (meaning l) (meaning m))
appEquation g v = (applicationInversion, applicationBackward)

public export
varInv : {n : Nat} -> {g : Env n} -> {x : Fin n} -> {v : Value} ->
         Denote g (Var x) v -> Info v (g x)
varInv DVar = infoRefl
varInv DBot = IBot
varInv (DJoin p q) = IJoinL (varInv p) (varInv q)
varInv (DSub p lt) = ITrans lt (varInv p)

public export
varEquation : {n : Nat} -> {x : Fin n} ->
              DenEq (meaning (Var x)) (\g, v => Info v (g x))
varEquation g v = (varInv, \lt => DSub DVar lt)
-- endregion application-equation

-- region congruence
public export
funMap : {n : Nat} -> {d, e : Denotation (S n)} ->
         ((g : Env (S n)) -> (v : Value) -> d g v -> e g v) ->
         (g : Env n) -> (v : Value) -> FunDen d g v -> FunDen e g v
funMap f g Bottom p = ()
funMap f g (Arrow a b) p = f (extendEnv g a) b p
funMap f g (Join a b) (p, q) = (funMap f g a p, funMap f g b q)

public export
funCong : {n : Nat} -> {d, e : Denotation (S n)} ->
          DenEq d e -> DenEq (FunDen d) (FunDen e)
funCong eq g v = (funMap (\g', v' => fst (eq g' v')) g v,
                  funMap (\g', v' => snd (eq g' v')) g v)

public export
appMap : {n : Nat} -> {d, d', e, e' : Denotation n} ->
  ((g : Env n) -> (v : Value) -> d g v -> d' g v) ->
  ((g : Env n) -> (v : Value) -> e g v -> e' g v) ->
  (g : Env n) -> (v : Value) -> AppDen d e g v -> AppDen d' e' g v
appMap fd fe g v (Left lt) = Left lt
appMap fd fe g v (Right (a ** (f, arg))) = Right (a ** (fd g (Arrow a v) f, fe g a arg))

public export
appDenCong : {n : Nat} -> {d, d', e, e' : Denotation n} ->
             DenEq d d' -> DenEq e e' -> DenEq (AppDen d e) (AppDen d' e')
appDenCong df de g v =
  (appMap (\g', v' => fst (df g' v')) (\g', v' => fst (de g' v')) g v,
   appMap (\g', v' => snd (df g' v')) (\g', v' => snd (de g' v')) g v)

public export
lamCong : {n : Nat} -> {m, k : Tm (S n)} -> SemEq m k -> SemEq (Lam m) (Lam k)
lamCong eq = denEqTrans lamEquation (denEqTrans (funCong eq) (denEqSym lamEquation))

public export
appCong : {n : Nat} -> {l, l', m, m' : Tm n} ->
          SemEq l l' -> SemEq m m' -> SemEq (App l m) (App l' m')
appCong eqf eqa =
  denEqTrans appEquation (denEqTrans (appDenCong eqf eqa) (denEqSym appEquation))
-- endregion congruence

-- region contexts
public export
data Ctx : Nat -> Nat -> Type where
  Hole : {n : Nat} -> Ctx n n
  CLam : {m, n : Nat} -> Ctx m (S n) -> Ctx m n
  CAppLeft : {m, n : Nat} -> Ctx m n -> Tm n -> Ctx m n
  CAppRight : {m, n : Nat} -> Tm n -> Ctx m n -> Ctx m n

public export
plug : {m, n : Nat} -> Ctx m n -> Tm m -> Tm n
plug Hole tm = tm
plug (CLam c) tm = Lam (plug c tm)
plug (CAppLeft c arg) tm = App (plug c tm) arg
plug (CAppRight fun c) tm = App fun (plug c tm)

public export
compositionality : {m, n : Nat} -> {l, r : Tm m} ->
                   (c : Ctx m n) -> SemEq l r -> SemEq (plug c l) (plug c r)
compositionality Hole eq = eq
compositionality (CLam c) eq = lamCong (compositionality c eq)
compositionality (CAppLeft c arg) eq = appCong (compositionality c eq) denEqRefl
compositionality (CAppRight fun c) eq = appCong denEqRefl (compositionality c eq)
-- endregion contexts

-- region structural
public export
structural : {n : Nat} -> Tm n -> Denotation n
structural (Var x) g v = Info v (g x)
structural (Lam body) g v = FunDen (structural body) g v
structural (App f arg) g v = AppDen (structural f) (structural arg) g v

public export
structuralCorrect : {n : Nat} -> (tm : Tm n) -> DenEq (meaning tm) (structural tm)
structuralCorrect (Var x) = varEquation
structuralCorrect (Lam body) = denEqTrans lamEquation (funCong (structuralCorrect body))
structuralCorrect (App f arg) =
  denEqTrans appEquation (appDenCong (structuralCorrect f) (structuralCorrect arg))
-- endregion structural

-- region exercises
public export
doubleApplication : Ctx 0 0
doubleApplication = CAppLeft (CAppRight identityTerm Hole) identityTerm

public export
identityContextExample :
  plug (CAppRight identityTerm Hole) identityTerm = App identityTerm identityTerm
identityContextExample = Refl

public export
replaceUnderBinder : {n : Nat} -> {l, r : Tm (S n)} ->
  SemEq l r -> SemEq (Lam (App l (Var FZ))) (Lam (App r (Var FZ)))
replaceUnderBinder eq = compositionality (CLam (CAppLeft Hole (Var FZ))) eq

public export
joinFunctionOutputs : {n : Nat} -> {g : Env n} -> {m : Tm n} -> {a, b, c : Value} ->
  Denote g m (Arrow a b) -> Denote g m (Arrow a c) ->
  Denote g m (Arrow a (Join b c))
joinFunctionOutputs p q = DSub (DJoin p q) IDist
-- endregion exercises
