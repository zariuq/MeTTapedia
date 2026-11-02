import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# Extending typed simultaneous substitutions

A substitution into an extended source context consists of the image of its
new variable and the old substitution. Instantiating a lifted substitution is
exactly this extension, including below further binders.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {gamma delta : Ctx Base} {domain result : Ty Base}

def Subst.cons (head : Term Const delta domain) (tail : Subst Const gamma delta) :
    Subst Const (domain :: gamma) delta
  | _, .vz => head
  | _, .vs index => tail index

theorem Subst.lift_comp_eq {later : Ctx Base} (tau : Subst Const delta later)
    (sigma : Subst Const gamma delta) :
    (Subst.comp (Subst.lift (σ := domain) tau) (Subst.lift sigma) : Subst Const (domain :: gamma) (domain :: later)) =
      (Subst.lift (σ := domain) (Subst.comp tau sigma) : Subst Const (domain :: gamma) (domain :: later)) := by
  funext type index
  exact (Subst.lift_comp_apply tau sigma index).symm

theorem Subst.single_lift_eq_cons (argument : Term Const delta domain) (sigma : Subst Const gamma delta) :
    (Subst.comp (Subst.single argument) (Subst.lift (σ := domain) sigma) : Subst Const (domain :: gamma) delta) =
      (Subst.cons argument sigma : Subst Const (domain :: gamma) delta) := by
  funext type index
  cases index with
  | vz => rfl
  | vs prior => exact instantiate_weaken argument (sigma prior)

/-- A finite typed assignment stores each variable image once. -/
inductive Subst.Table (Const : Ty Base → Type v) (target : Ctx Base) : Ctx Base → Type (max u v) where
  | nil : Subst.Table Const target []
  | cons {source : Ctx Base} {type : Ty Base} (term : Term Const target type)
      (rest : Subst.Table Const target source) : Subst.Table Const target (type :: source)

namespace Subst.Table

def lookup : {source : Ctx Base} → Subst.Table Const delta source → Subst Const source delta
  | _, .nil, _, index => nomatch index
  | _, .cons term _, _, .vz => term
  | _, .cons _ rest, _, .vs index => rest.lookup index

def ofSubst : {source : Ctx Base} → Subst Const source delta → Subst.Table Const delta source
  | [], _ => .nil
  | _ :: _, substitution => .cons (substitution .vz) (ofSubst (fun index => substitution (.vs index)))

theorem lookup_ofSubst (substitution : Subst Const gamma delta) :
    ((ofSubst substitution).lookup : Subst Const gamma delta) = (substitution : Subst Const gamma delta) := by
  induction gamma with
  | nil => funext type index; cases index
  | cons type context ih =>
      funext result index
      cases index with
      | vz => rfl
      | vs prior => exact congrFun (congrFun (ih (fun index => substitution (.vs index))) result) prior

end Subst.Table

theorem instantiate_subst_lift (argument : Term Const delta domain)
    (theta : Subst Const gamma delta) (body : Term Const (domain :: gamma) result) :
    instantiate argument (subst (Subst.lift theta) body) = subst (Subst.cons argument theta) body := by
  rw [instantiate, subst_comp]
  apply subst_ext
  intro type index
  cases index with
  | vz => rfl
  | vs index =>
      change instantiate argument (weaken (theta index)) = theta index
      exact instantiate_weaken argument (theta index)

#print axioms instantiate_subst_lift

end Mettapedia.Logic.HOL
