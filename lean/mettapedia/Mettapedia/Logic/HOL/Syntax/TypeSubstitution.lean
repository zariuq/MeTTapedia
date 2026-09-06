import Mettapedia.Logic.HOL.Syntax.Subst

/-!
# Type substitution in intrinsic HOL syntax

A base type may be interpreted by a compound type. Such a substitution acts
on contexts and terms when constants are assigned symbols at their translated
types. This is the syntactic component of a type-derived interpretation; it
does not supply a reduct of arbitrary Henkin models.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u u' u'' v v'

variable {Base : Type u} {Base' : Type u'} {Base'' : Type u''}

namespace Ty

/-- Substitute simple types for base-type symbols. -/
def substitute (σ : Base → Ty Base') : Ty Base → Ty Base'
  | .prop => .prop
  | .base b => σ b
  | .arr a b => .arr (substitute σ a) (substitute σ b)

@[simp] theorem substitute_base (σ : Base → Ty Base') (b : Base) :
    substitute σ (.base b) = σ b := rfl

@[simp] theorem substitute_prop (σ : Base → Ty Base') :
    substitute σ .prop = .prop := rfl

@[simp] theorem substitute_arr (σ : Base → Ty Base') (a b : Ty Base) :
    substitute σ (.arr a b) = .arr (substitute σ a) (substitute σ b) := rfl

@[simp] theorem substitute_id (a : Ty Base) : substitute Ty.base a = a := by
  induction a <;> simp_all [substitute]

/-- Successive type instantiations compose by substituting in their images. -/
theorem substitute_comp (σ : Base → Ty Base') (τ : Base' → Ty Base'') (a : Ty Base) :
    substitute τ (substitute σ a) = substitute (fun b => substitute τ (σ b)) a := by
  induction a <;> simp_all [substitute]

end Ty

namespace Var

/-- Retype a context position without changing its de Bruijn index. -/
def mapTypes (σ : Base → Ty Base') :
    {Γ : Ctx Base} → {a : Ty Base} → Var Γ a →
      Var (Γ.map (Ty.substitute σ)) (Ty.substitute σ a)
  | _, _, .vz => .vz
  | _, _, .vs x => .vs (mapTypes σ x)

end Var

variable {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}

/-- Retype all variable, constant, and binder occurrences in a HOL term. -/
def mapTypes (σ : Base → Ty Base')
    (constants : ∀ {a}, Const a → Const' (Ty.substitute σ a)) :
    {Γ : Ctx Base} → {a : Ty Base} → Term Const Γ a →
      Term Const' (Γ.map (Ty.substitute σ)) (Ty.substitute σ a)
  | _, _, .var x => .var (x.mapTypes σ)
  | _, _, .const c => .const (constants c)
  | _, _, .app f t => .app (mapTypes σ constants f) (mapTypes σ constants t)
  | _, _, .lam t => .lam (mapTypes σ constants t)
  | _, _, .top => .top
  | _, _, .bot => .bot
  | _, _, .and p q => .and (mapTypes σ constants p) (mapTypes σ constants q)
  | _, _, .or p q => .or (mapTypes σ constants p) (mapTypes σ constants q)
  | _, _, .imp p q => .imp (mapTypes σ constants p) (mapTypes σ constants q)
  | _, _, .not p => .not (mapTypes σ constants p)
  | _, _, .eq t s => .eq (mapTypes σ constants t) (mapTypes σ constants s)
  | _, _, .all p => .all (mapTypes σ constants p)
  | _, _, .ex p => .ex (mapTypes σ constants p)

variable (σ : Base → Ty Base')
  (constants : ∀ {a}, Const a → Const' (Ty.substitute σ a))
  {Γ Δ : Ctx Base} {a b : Ty Base}

/-- Type instantiation commutes with compatible context renamings. -/
theorem mapTypes_rename (ρ : Rename Base Γ Δ)
    (ρ' : Rename Base' (Γ.map (Ty.substitute σ)) (Δ.map (Ty.substitute σ)))
    (compatible : ∀ {a} (x : Var Γ a), (ρ x).mapTypes σ = ρ' (x.mapTypes σ))
    (t : Term Const Γ a) :
    mapTypes σ constants (rename ρ t) = rename ρ' (mapTypes σ constants t) := by
  induction t generalizing Δ with
  | var x => simp [rename, mapTypes, compatible]
  | const _ => rfl
  | app f t ihf iht => simp [rename, mapTypes, ihf ρ ρ' compatible, iht ρ ρ' compatible]
  | lam t ih =>
      apply congrArg Term.lam
      apply ih (Rename.lift ρ) (Rename.lift ρ')
      intro a x
      cases x with
      | vz => rfl
      | vs x => simp [Rename.lift, Var.mapTypes, compatible]
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [rename, mapTypes, ihp ρ ρ' compatible, ihq ρ ρ' compatible]
  | or p q ihp ihq => simp [rename, mapTypes, ihp ρ ρ' compatible, ihq ρ ρ' compatible]
  | imp p q ihp ihq => simp [rename, mapTypes, ihp ρ ρ' compatible, ihq ρ ρ' compatible]
  | not p ih => simp [rename, mapTypes, ih ρ ρ' compatible]
  | eq t s iht ihs => simp [rename, mapTypes, iht ρ ρ' compatible, ihs ρ ρ' compatible]
  | all p ih =>
      apply congrArg Term.all
      apply ih (Rename.lift ρ) (Rename.lift ρ')
      intro a x
      cases x with
      | vz => rfl
      | vs x => simp [Rename.lift, Var.mapTypes, compatible]
  | ex p ih =>
      apply congrArg Term.ex
      apply ih (Rename.lift ρ) (Rename.lift ρ')
      intro a x
      cases x with
      | vz => rfl
      | vs x => simp [Rename.lift, Var.mapTypes, compatible]

@[simp] theorem mapTypes_weaken (t : Term Const Γ a) :
    mapTypes σ constants (weaken (σ := b) t) =
      weaken (σ := Ty.substitute σ b) (mapTypes σ constants t) :=
  mapTypes_rename σ constants Rename.weaken Rename.weaken (by intro a x; rfl) t

/-- Compatible simultaneous substitutions remain compatible in a binder. -/
private theorem mapTypes_lift_compatible (θ : Subst Const Γ Δ)
    (θ' : Subst Const' (Γ.map (Ty.substitute σ)) (Δ.map (Ty.substitute σ)))
    (compatible : ∀ {a} (x : Var Γ a), mapTypes σ constants (θ x) = θ' (x.mapTypes σ))
    {a b : Ty Base} (x : Var (b :: Γ) a) :
    mapTypes σ constants (Subst.lift θ x) =
      Subst.lift θ' (x.mapTypes σ) := by
  cases x with
  | vz => rfl
  | vs x =>
      change mapTypes σ constants (weaken (θ x)) = weaken (θ' (x.mapTypes σ))
      rw [mapTypes_weaken, compatible]

/-- Retyping commutes with term substitution whenever the variable images
commute. No injectivity of the type substitution is assumed. -/
theorem mapTypes_subst (θ : Subst Const Γ Δ)
    (θ' : Subst Const' (Γ.map (Ty.substitute σ)) (Δ.map (Ty.substitute σ)))
    (compatible : ∀ {a} (x : Var Γ a), mapTypes σ constants (θ x) = θ' (x.mapTypes σ))
    (t : Term Const Γ a) :
    mapTypes σ constants (subst θ t) = subst θ' (mapTypes σ constants t) := by
  induction t generalizing Δ with
  | var x => exact compatible x
  | const _ => rfl
  | app f t ihf iht => simp [subst, mapTypes, ihf θ θ' compatible, iht θ θ' compatible]
  | lam t ih =>
      exact congrArg Term.lam
        (ih (Subst.lift θ) (Subst.lift θ') (mapTypes_lift_compatible σ constants θ θ' compatible))
  | top => rfl
  | bot => rfl
  | and p q ihp ihq => simp [subst, mapTypes, ihp θ θ' compatible, ihq θ θ' compatible]
  | or p q ihp ihq => simp [subst, mapTypes, ihp θ θ' compatible, ihq θ θ' compatible]
  | imp p q ihp ihq => simp [subst, mapTypes, ihp θ θ' compatible, ihq θ θ' compatible]
  | not p ih => simp [subst, mapTypes, ih θ θ' compatible]
  | eq t s iht ihs => simp [subst, mapTypes, iht θ θ' compatible, ihs θ θ' compatible]
  | all p ih =>
      exact congrArg Term.all
        (ih (Subst.lift θ) (Subst.lift θ') (mapTypes_lift_compatible σ constants θ θ' compatible))
  | ex p ih =>
      exact congrArg Term.ex
        (ih (Subst.lift θ) (Subst.lift θ') (mapTypes_lift_compatible σ constants θ θ' compatible))

@[simp] theorem mapTypes_instantiate (t : Term Const Γ b) (s : Term Const (b :: Γ) a) :
    mapTypes σ constants (instantiate t s) =
      instantiate (mapTypes σ constants t) (mapTypes σ constants s) := by
  apply mapTypes_subst
  intro a x
  cases x <;> rfl

#print axioms Ty.substitute_comp
#print axioms mapTypes_rename
#print axioms mapTypes_subst
#print axioms mapTypes_instantiate

end Mettapedia.Logic.HOL
