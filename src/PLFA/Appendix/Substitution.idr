module PLFA.Appendix.Substitution

import public PLFA.Part2.Untyped

%default total

-- region extensionality
public export
liftRenExt : (rho, tau : Fin m -> Fin n) ->
  ((i : Fin m) -> rho i = tau i) ->
  (i : Fin (S m)) -> liftRen rho i = liftRen tau i
liftRenExt rho tau eq FZ = Refl
liftRenExt rho tau eq (FS i) = cong FS (eq i)

public export
renameExt : (rho, tau : Fin m -> Fin n) ->
  ((i : Fin m) -> rho i = tau i) ->
  (term : Tm m) -> rename rho term = rename tau term
renameExt rho tau eq (Var i) = cong Var (eq i)
renameExt rho tau eq (Lam body) =
  cong Lam (renameExt (liftRen rho) (liftRen tau) (liftRenExt rho tau eq) body)
renameExt rho tau eq (App fun arg) =
  cong2 App (renameExt rho tau eq fun) (renameExt rho tau eq arg)

public export
liftSubExt : (sigma, tau : Fin m -> Tm n) ->
  ((i : Fin m) -> sigma i = tau i) ->
  (i : Fin (S m)) -> liftSub sigma i = liftSub tau i
liftSubExt sigma tau eq FZ = Refl
liftSubExt sigma tau eq (FS i) = cong (rename FS) (eq i)

public export
substExt : (sigma, tau : Fin m -> Tm n) ->
  ((i : Fin m) -> sigma i = tau i) ->
  (term : Tm m) -> subst sigma term = subst tau term
substExt sigma tau eq (Var i) = eq i
substExt sigma tau eq (Lam body) =
  cong Lam (substExt (liftSub sigma) (liftSub tau) (liftSubExt sigma tau eq) body)
substExt sigma tau eq (App fun arg) =
  cong2 App (substExt sigma tau eq fun) (substExt sigma tau eq arg)
-- endregion extensionality

-- region renaming
liftRenIdentity : (i : Fin (S n)) -> liftRen Prelude.id i = i
liftRenIdentity FZ = Refl
liftRenIdentity (FS i) = Refl

public export
renameId : (term : Tm n) -> rename Prelude.id term = term
renameId (Var i) = Refl
renameId (Lam body) = cong Lam
  (trans (renameExt (liftRen Prelude.id) id liftRenIdentity body) (renameId body))
renameId (App fun arg) = cong2 App (renameId fun) (renameId arg)

liftRenComposition : (rho : Fin n -> Fin p) -> (tau : Fin m -> Fin n) ->
  (i : Fin (S m)) ->
  liftRen rho (liftRen tau i) = liftRen (\j => rho (tau j)) i
liftRenComposition rho tau FZ = Refl
liftRenComposition rho tau (FS i) = Refl

public export
renameComp : (rho : Fin n -> Fin p) -> (tau : Fin m -> Fin n) ->
  (term : Tm m) ->
  rename rho (rename tau term) = rename (\i => rho (tau i)) term
renameComp rho tau (Var i) = Refl
renameComp rho tau (Lam body) = cong Lam
  (trans (renameComp (liftRen rho) (liftRen tau) body)
    (renameExt (\i => liftRen rho (liftRen tau i))
      (liftRen (\i => rho (tau i))) (liftRenComposition rho tau) body))
renameComp rho tau (App fun arg) =
  cong2 App (renameComp rho tau fun) (renameComp rho tau arg)
-- endregion renaming

-- region mixed-laws
liftSubRenaming : (sigma : Fin n -> Tm p) -> (rho : Fin m -> Fin n) ->
  (i : Fin (S m)) ->
  liftSub sigma (liftRen rho i) = liftSub (\j => sigma (rho j)) i
liftSubRenaming sigma rho FZ = Refl
liftSubRenaming sigma rho (FS i) = Refl

public export
substRename : (sigma : Fin n -> Tm p) -> (rho : Fin m -> Fin n) ->
  (term : Tm m) ->
  subst sigma (rename rho term) = subst (\i => sigma (rho i)) term
substRename sigma rho (Var i) = Refl
substRename sigma rho (Lam body) = cong Lam
  (trans (substRename (liftSub sigma) (liftRen rho) body)
    (substExt (\i => liftSub sigma (liftRen rho i))
      (liftSub (\i => sigma (rho i))) (liftSubRenaming sigma rho) body))
substRename sigma rho (App fun arg) =
  cong2 App (substRename sigma rho fun) (substRename sigma rho arg)

liftRenameSub : (rho : Fin n -> Fin p) -> (sigma : Fin m -> Tm n) ->
  (i : Fin (S m)) ->
  rename (liftRen rho) (liftSub sigma i) =
  liftSub (\j => rename rho (sigma j)) i
liftRenameSub rho sigma FZ = Refl
liftRenameSub rho sigma (FS i) =
  trans (renameComp (liftRen rho) FS (sigma i))
    (sym (renameComp FS rho (sigma i)))

public export
renameSubst : (rho : Fin n -> Fin p) -> (sigma : Fin m -> Tm n) ->
  (term : Tm m) ->
  rename rho (subst sigma term) = subst (\i => rename rho (sigma i)) term
renameSubst rho sigma (Var i) = Refl
renameSubst rho sigma (Lam body) = cong Lam
  (trans (renameSubst (liftRen rho) (liftSub sigma) body)
    (substExt (\i => rename (liftRen rho) (liftSub sigma i))
      (liftSub (\i => rename rho (sigma i))) (liftRenameSub rho sigma) body))
renameSubst rho sigma (App fun arg) =
  cong2 App (renameSubst rho sigma fun) (renameSubst rho sigma arg)
-- endregion mixed-laws

-- region substitution-laws
liftSubIdentity : (i : Fin (S n)) -> liftSub Var i = Var i
liftSubIdentity FZ = Refl
liftSubIdentity (FS i) = Refl

public export
substId : (term : Tm n) -> subst Var term = term
substId (Var i) = Refl
substId (Lam body) = cong Lam
  (trans (substExt (liftSub Var) Var liftSubIdentity body) (substId body))
substId (App fun arg) = cong2 App (substId fun) (substId arg)

liftSubComposition : (sigma : Fin n -> Tm p) -> (tau : Fin m -> Tm n) ->
  (i : Fin (S m)) ->
  subst (liftSub sigma) (liftSub tau i) =
  liftSub (\j => subst sigma (tau j)) i
liftSubComposition sigma tau FZ = Refl
liftSubComposition sigma tau (FS i) =
  trans (substRename (liftSub sigma) FS (tau i))
    (sym (renameSubst FS sigma (tau i)))

public export
substComp : (sigma : Fin n -> Tm p) -> (tau : Fin m -> Tm n) ->
  (term : Tm m) ->
  subst sigma (subst tau term) = subst (\i => subst sigma (tau i)) term
substComp sigma tau (Var i) = Refl
substComp sigma tau (Lam body) = cong Lam
  (trans (substComp (liftSub sigma) (liftSub tau) body)
    (substExt (\i => subst (liftSub sigma) (liftSub tau i))
      (liftSub (\i => subst sigma (tau i))) (liftSubComposition sigma tau) body))
substComp sigma tau (App fun arg) =
  cong2 App (substComp sigma tau fun) (substComp sigma tau arg)

public export
cancelShift : (arg : Tm n) -> (term : Tm n) ->
  subst (single arg) (rename FS term) = term
cancelShift arg term = trans (substRename (single arg) FS term) (substId term)

renameSingle : (rho : Fin m -> Fin n) -> (arg : Tm m) ->
  (i : Fin (S m)) ->
  rename rho (single arg i) = single (rename rho arg) (liftRen rho i)
renameSingle rho arg FZ = Refl
renameSingle rho arg (FS i) = Refl

public export
renameBeta : (rho : Fin m -> Fin n) -> (body : Tm (S m)) -> (arg : Tm m) ->
  rename rho (beta body arg) = beta (rename (liftRen rho) body) (rename rho arg)
renameBeta rho body arg =
  trans (renameSubst rho (single arg) body)
    (trans (substExt (\i => rename rho (single arg i))
      (\i => single (rename rho arg) (liftRen rho i)) (renameSingle rho arg) body)
      (sym (substRename (single (rename rho arg)) (liftRen rho) body)))

substSingle : (sigma : Fin m -> Tm n) -> (arg : Tm m) ->
  (i : Fin (S m)) ->
  subst sigma (single arg i) = subst (single (subst sigma arg)) (liftSub sigma i)
substSingle sigma arg FZ = Refl
substSingle sigma arg (FS i) = sym (cancelShift (subst sigma arg) (sigma i))

public export
substBeta : (sigma : Fin m -> Tm n) -> (body : Tm (S m)) -> (arg : Tm m) ->
  subst sigma (beta body arg) = beta (subst (liftSub sigma) body) (subst sigma arg)
substBeta sigma body arg =
  trans (substComp sigma (single arg) body)
    (trans (substExt (\i => subst sigma (single arg i))
      (\i => subst (single (subst sigma arg)) (liftSub sigma i))
      (substSingle sigma arg) body)
      (sym (substComp (single (subst sigma arg)) (liftSub sigma) body)))

public export
cons : Tm n -> (Fin m -> Tm n) -> Fin (S m) -> Tm n
cons arg sigma FZ = arg
cons arg sigma (FS i) = sigma i

singleLift : (sigma : Fin m -> Tm n) -> (arg : Tm n) ->
  (i : Fin (S m)) -> subst (single arg) (liftSub sigma i) = cons arg sigma i
singleLift sigma arg FZ = Refl
singleLift sigma arg (FS i) = cancelShift arg (sigma i)

public export
betaSubst : (sigma : Fin m -> Tm n) -> (body : Tm (S m)) -> (arg : Tm n) ->
  beta (subst (liftSub sigma) body) arg = subst (cons arg sigma) body
betaSubst sigma body arg =
  trans (substComp (single arg) (liftSub sigma) body)
    (substExt (\i => subst (single arg) (liftSub sigma i))
      (cons arg sigma) (singleLift sigma arg) body)
-- endregion substitution-laws

-- region exercises
public export
renamingAsSubstitution : (rho : Fin m -> Fin n) -> (term : Tm m) ->
  rename rho term = subst (\i => Var (rho i)) term
renamingAsSubstitution rho term =
  trans (sym (substId (rename rho term))) (substRename Var rho term)

public export
unusedBinder : (arg, term : Tm n) -> beta (rename FS term) arg = term
unusedBinder = cancelShift
-- endregion exercises
