module PLFA.Part2.Typed

import public Data.Fin
import public Data.Vect

%default total

-- region types
public export
data Ty = TNat | Arr Ty Ty

public export
Context : Nat -> Type
Context n = Vect n Ty

-- Variables are scoped, but types remain an external judgement.
public export
data Raw : Nat -> Type where
  RVar  : Fin n -> Raw n
  RLam  : Raw (S n) -> Raw n
  RApp  : Raw n -> Raw n -> Raw n
  RZero : Raw n
  RSucc : Raw n -> Raw n
  RCase : Raw n -> Raw n -> Raw (S n) -> Raw n
  RFix  : Raw (S n) -> Raw n
-- endregion types

-- region maps
public export
Ren : Nat -> Nat -> Type
Ren n m = Fin n -> Fin m

public export
liftRen : Ren n m -> Ren (S n) (S m)
liftRen rho FZ = FZ
liftRen rho (FS i) = FS (rho i)

public export
rename : Ren n m -> Raw n -> Raw m
rename rho (RVar i) = RVar (rho i)
rename rho (RLam body) = RLam (rename (liftRen rho) body)
rename rho (RApp fun arg) = RApp (rename rho fun) (rename rho arg)
rename rho RZero = RZero
rename rho (RSucc t) = RSucc (rename rho t)
rename rho (RCase t z s) =
  RCase (rename rho t) (rename rho z) (rename (liftRen rho) s)
rename rho (RFix body) = RFix (rename (liftRen rho) body)

public export
Sub : Nat -> Nat -> Type
Sub n m = Fin n -> Raw m

public export
liftSub : Sub n m -> Sub (S n) (S m)
liftSub sigma FZ = RVar FZ
liftSub sigma (FS i) = rename FS (sigma i)

public export
subst : Sub n m -> Raw n -> Raw m
subst sigma (RVar i) = sigma i
subst sigma (RLam body) = RLam (subst (liftSub sigma) body)
subst sigma (RApp fun arg) = RApp (subst sigma fun) (subst sigma arg)
subst sigma RZero = RZero
subst sigma (RSucc t) = RSucc (subst sigma t)
subst sigma (RCase t z s) =
  RCase (subst sigma t) (subst sigma z) (subst (liftSub sigma) s)
subst sigma (RFix body) = RFix (subst (liftSub sigma) body)

public export
single : Raw n -> Sub (S n) n
single arg FZ = arg
single arg (FS i) = RVar i

public export
instantiate : Raw (S n) -> Raw n -> Raw n
instantiate body arg = subst (single arg) body
-- endregion maps

-- region typing
public export
data HasType : Context n -> Raw n -> Ty -> Type where
  TVar  : (i : Fin n) -> HasType gamma (RVar i) (index i gamma)
  TLam  : HasType (a :: gamma) body b ->
          HasType gamma (RLam body) (Arr a b)
  TApp  : HasType gamma fun (Arr a b) -> HasType gamma arg a ->
          HasType gamma (RApp fun arg) b
  TZero : HasType gamma RZero TNat
  TSucc : HasType gamma t TNat -> HasType gamma (RSucc t) TNat
  TCase : HasType gamma t TNat -> HasType gamma z a ->
          HasType (TNat :: gamma) s a -> HasType gamma (RCase t z s) a
  TFix  : HasType (a :: gamma) body a -> HasType gamma (RFix body) a
-- endregion typing
