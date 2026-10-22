module PLFA.Part2.Confluence

import public PLFA.Appendix.Substitution

%default total

-- region parallel
public export
data Par : Tm n -> Tm n -> Type where
  PVar : {i : Fin n} -> Par (Var i) (Var i)
  PLam : {body, body' : Tm (S n)} -> Par body body' -> Par (Lam body) (Lam body')
  PApp : {fun, fun', arg, arg' : Tm n} -> Par fun fun' -> Par arg arg' -> Par (App fun arg) (App fun' arg')
  PBeta : {body, body' : Tm (S n)} -> {arg, arg' : Tm n} -> Par body body' -> Par arg arg' ->
          Par (App (Lam body) arg) (beta body' arg')

public export
parRefl : (term : Tm n) -> Par term term
parRefl (Var i) = PVar
parRefl (Lam body) = PLam (parRefl body)
parRefl (App fun arg) = PApp (parRefl fun) (parRefl arg)

public export
data Pars : Tm n -> Tm n -> Type where
  PDone : {term : Tm n} -> Pars term term
  PMore : {term, next, final : Tm n} -> Par term next -> Pars next final -> Pars term final

public export
parsTrans : {l, m, r : Tm n} -> Pars l m -> Pars m r -> Pars l r
parsTrans PDone rest = rest
parsTrans (PMore first rest) tail = PMore first (parsTrans rest tail)
-- endregion parallel

-- region preservation
public export
parRename : (rho : Fin m -> Fin n) -> {source, target : Tm m} ->
  Par source target -> Par (rename rho source) (rename rho target)
parRename rho PVar = PVar
parRename rho (PLam p) = PLam (parRename (liftRen rho) p)
parRename rho (PApp p q) = PApp (parRename rho p) (parRename rho q)
parRename rho (PBeta {body', arg'} p q) =
  rewrite renameBeta rho body' arg' in
    PBeta (parRename (liftRen rho) p) (parRename rho q)

public export
parLift : (sigma, tau : Fin m -> Tm n) ->
  ((i : Fin m) -> Par (sigma i) (tau i)) ->
  (i : Fin (S m)) -> Par (liftSub sigma i) (liftSub tau i)
parLift sigma tau rel FZ = PVar
parLift sigma tau rel (FS i) = parRename FS (rel i)

public export
parSubst : (sigma, tau : Fin m -> Tm n) ->
  ((i : Fin m) -> Par (sigma i) (tau i)) ->
  {source, target : Tm m} -> Par source target ->
  Par (subst sigma source) (subst tau target)
parSubst sigma tau rel (PVar {i}) = rel i
parSubst sigma tau rel (PLam p) =
  PLam (parSubst (liftSub sigma) (liftSub tau) (parLift sigma tau rel) p)
parSubst sigma tau rel (PApp p q) =
  PApp (parSubst sigma tau rel p) (parSubst sigma tau rel q)
parSubst sigma tau rel (PBeta {body', arg'} p q) =
  rewrite substBeta tau body' arg' in
    PBeta (parSubst (liftSub sigma) (liftSub tau) (parLift sigma tau rel) p)
          (parSubst sigma tau rel q)

parSingle : {arg, arg' : Tm n} -> Par arg arg' ->
  (i : Fin (S n)) -> Par (single arg i) (single arg' i)
parSingle p FZ = p
parSingle p (FS i) = PVar

public export
parBeta : {body, body' : Tm (S n)} -> {arg, arg' : Tm n} ->
  Par body body' -> Par arg arg' -> Par (beta body arg) (beta body' arg')
parBeta {arg, arg'} p q = parSubst (single arg) (single arg') (parSingle q) p
-- endregion preservation

-- region triangle
public export
develop : Tm n -> Tm n
develop (Var i) = Var i
develop (Lam body) = Lam (develop body)
develop (App (Lam body) arg) = beta (develop body) (develop arg)
develop (App (Var i) arg) = App (Var i) (develop arg)
develop (App (App fun arg) other) =
  App (develop (App fun arg)) (develop other)

public export
parTriangle : {source, target : Tm n} ->
  Par source target -> Par target (develop source)
parTriangle {source = Var i} PVar = PVar
parTriangle {source = Lam body} (PLam p) = PLam (parTriangle p)
parTriangle {source = App (Lam body) arg} (PBeta p q) = parBeta (parTriangle p) (parTriangle q)
parTriangle {source = App (Lam body) arg} (PApp p q) =
  case p of
    PLam r => PBeta (parTriangle r) (parTriangle q)
parTriangle {source = App (Var i) arg} (PApp p q) = PApp (parTriangle p) (parTriangle q)
parTriangle {source = App (App fun arg) other} (PApp p q) = PApp (parTriangle p) (parTriangle q)

public export
parDiamond : {source, left, right : Tm n} ->
  Par source left -> Par source right ->
  (meet : Tm n ** (Par left meet, Par right meet))
parDiamond {source} p q = (develop source ** (parTriangle p, parTriangle q))
-- endregion triangle

-- region correspondence
public export
stepPar : {source, target : Tm n} -> Step source target -> Par source target
stepPar (Beta {body, arg}) = PBeta (parRefl body) (parRefl arg)
stepPar (AppLeft {arg} p) = PApp (stepPar p) (parRefl arg)
stepPar (AppRight {fun} p) = PApp (parRefl fun) (stepPar p)
stepPar (UnderLam p) = PLam (stepPar p)

public export
stepsPars : {source, target : Tm n} -> Steps source target -> Pars source target
stepsPars Done = PDone
stepsPars (More p ps) = PMore (stepPar p) (stepsPars ps)

public export
parSteps : {source, target : Tm n} -> Par source target -> Steps source target
parSteps PVar = Done
parSteps (PLam p) = stepsLam (parSteps p)
parSteps (PApp p q) = stepsTrans (stepsLeft (parSteps p)) (stepsRight (parSteps q))
parSteps (PBeta p q) =
  stepsTrans (stepsLeft (stepsLam (parSteps p)))
    (stepsTrans (stepsRight (parSteps q)) (More Beta Done))

public export
parsSteps : {source, target : Tm n} -> Pars source target -> Steps source target
parsSteps PDone = Done
parsSteps (PMore p ps) = stepsTrans (parSteps p) (parsSteps ps)
-- endregion correspondence

-- region confluence
public export
strip : {source, left, right : Tm n} ->
  Par source left -> Pars source right ->
  (meet : Tm n ** (Pars left meet, Par right meet))
strip {left} p PDone = (left ** (PDone, p))
strip p (PMore q qs) =
  let (corner ** (fromLeft, fromNext)) = parDiamond p q
      (meet ** (rest, fromRight)) = strip fromNext qs
  in (meet ** (PMore fromLeft rest, fromRight))

public export
parsConfluent : {source, left, right : Tm n} ->
  Pars source left -> Pars source right ->
  (meet : Tm n ** (Pars left meet, Pars right meet))
parsConfluent {right} PDone qs = (right ** (qs, PDone))
parsConfluent (PMore p ps) qs =
  let (corner ** (toCorner, fromRight)) = strip p qs
      (meet ** (fromLeft, rest)) = parsConfluent ps toCorner
  in (meet ** (fromLeft, PMore fromRight rest))

public export
confluence : {source, left, right : Tm n} ->
  Steps source left -> Steps source right ->
  (meet : Tm n ** (Steps left meet, Steps right meet))
confluence ps qs =
  let (meet ** (leftPath, rightPath)) = parsConfluent (stepsPars ps) (stepsPars qs)
  in (meet ** (parsSteps leftPath, parsSteps rightPath))

public export
data Convertible : Tm n -> Tm n -> Type where
  ConvRefl : Convertible term term
  ConvForward : {middle : Tm n} -> Step left middle -> Convertible middle right -> Convertible left right
  ConvBackward : {middle : Tm n} -> Step middle left -> Convertible middle right -> Convertible left right

public export
churchRosser : {left, right : Tm n} -> Convertible left right ->
  (meet : Tm n ** (Steps left meet, Steps right meet))
churchRosser {left} ConvRefl = (left ** (Done, Done))
churchRosser (ConvForward p rest) =
  let (meet ** (leftPath, rightPath)) = churchRosser rest
  in (meet ** (More p leftPath, rightPath))
churchRosser (ConvBackward p rest) =
  let (corner ** (middlePath, rightPath)) = churchRosser rest
      (meet ** (leftPath, cornerPath)) = confluence (More p Done) middlePath
  in (meet ** (leftPath, stepsTrans rightPath cornerPath))

public export
Normal : {n : Nat} -> Tm n -> Type
Normal term = (target : Tm n) -> Step term target -> Void

public export
normalPath : {n : Nat} -> {source, target : Tm n} -> Normal source -> Steps source target -> source = target
normalPath normal Done = Refl
normalPath normal (More {next} first rest) = void (normal next first)

public export
normalUnique : {n : Nat} -> {source, left, right : Tm n} ->
  Steps source left -> Steps source right -> Normal left -> Normal right -> left = right
normalUnique ps qs leftNormal rightNormal =
  let (meet ** (leftPath, rightPath)) = confluence ps qs
  in trans (normalPath leftNormal leftPath) (sym (normalPath rightNormal rightPath))
-- endregion confluence

-- region exercises
public export
duplicateJoin : (arg, result : Tm n) -> Par arg result ->
  Par (App arg arg) (App result result)
duplicateJoin arg result p = PApp p p

public export
identityParallel : (arg : Tm n) -> Par (App Untyped.identity arg) arg
identityParallel arg = PBeta PVar (parRefl arg)

public export
duplicatingRedex : Tm 1
duplicatingRedex = App Untyped.selfApply (App Untyped.identity (Var FZ))

public export
duplicateOuterFirst :
  Steps Confluence.duplicatingRedex (App (Var FZ) (Var FZ))
duplicateOuterFirst = More Beta (More (AppLeft Beta) (More (AppRight Beta) Done))

public export
duplicateInnerFirst :
  Steps Confluence.duplicatingRedex (App (Var FZ) (Var FZ))
duplicateInnerFirst = More (AppRight Beta) (More Beta Done)
-- endregion exercises
