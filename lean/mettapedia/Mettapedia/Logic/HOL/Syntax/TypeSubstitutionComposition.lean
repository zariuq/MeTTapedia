import Mettapedia.Logic.HOL.Syntax.TypeSubstitution
import Mettapedia.Logic.HOL.Syntax.ConstMap

/-!+# Coherence of type-derived interpretations

Successive interpretations agree with their composite on intrinsically typed
terms. Heterogeneous equality records the propositional equalities of translated
contexts and types; it does not identify different source types.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u u' u'' v v' v''

variable {Base : Type u} {Base' : Type u'} {Base'' : Type u''}

namespace Ctx

@[simp] theorem map_substitute_id (Γ : Ctx Base) :
    Γ.map (Ty.substitute Ty.base) = Γ := by
  induction Γ <;> simp_all

theorem map_substitute_comp (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (Γ : Ctx Base) :
    (Γ.map (Ty.substitute σ)).map (Ty.substitute τ) =
      Γ.map (Ty.substitute (fun b => Ty.substitute τ (σ b))) := by
  induction Γ <;> simp_all [Ty.substitute_comp]

end Ctx

namespace Var

theorem mapTypes_id {Γ : Ctx Base} {a : Ty Base} (x : Var Γ a) :
    HEq (x.mapTypes Ty.base) x := by
  induction x with
  | vz => simp only [mapTypes]; congr 1 <;> simp
  | vs x ih =>
      simp only [mapTypes]
      congr 1 <;> simp

theorem mapTypes_comp (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    {Γ : Ctx Base} {a : Ty Base} (x : Var Γ a) :
    HEq ((x.mapTypes σ).mapTypes τ)
      (x.mapTypes (fun b => Ty.substitute τ (σ b))) := by
  induction x with
  | vz => simp only [mapTypes]; congr 1 <;> simp [Ty.substitute_comp]
  | vs x ih =>
      simp only [mapTypes]
      congr 1 <;> simp [Ty.substitute_comp]

end Var

variable {Const : Ty Base → Type v} {Const' : Ty Base' → Type v'}
  {Const'' : Ty Base'' → Type v''}

/-- Constant-only translation is the identity type interpretation. -/
theorem mapTypes_base {Other : Ty Base → Type v'}
    (constants : ∀ {a}, Const a → Other a)
    {Γ : Ctx Base} {a : Ty Base} (t : Term Const Γ a) :
    HEq (mapTypes (Const' := Other) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ constants c) t)
      (mapConst constants t) := by
  induction t <;> simp only [mapTypes, mapConst] <;> congr 1 <;>
    simp_all [Var.mapTypes_id, eqRec_heq]

/-- The constant-only sentence map is recovered literally. -/
theorem mapTypes_base_closed {Other : Ty Base → Type v'}
    (constants : ∀ {a}, Const a → Other a) (φ : ClosedFormula Const) :
    mapTypes (Const' := Other) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ constants c) φ =
      mapConst constants φ := eq_of_heq (mapTypes_base constants φ)

/-- The identity interpretation retains the complete intrinsic term. -/
theorem mapTypes_id {Γ : Ctx Base} {a : Ty Base} (t : Term Const Γ a) :
    HEq (mapTypes (Const' := Const) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ c) t) t := by
  simpa only [mapConst_id] using mapTypes_base (Other := Const) (fun c => c) t

/-- Constant symbols compose at the propositionally equal composite type. -/
def composeTypeConstants (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (first : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (second : ∀ {a}, Const' a → Const'' (Ty.substitute τ a))
    {a : Ty Base} (c : Const a) :
    Const'' (Ty.substitute (fun b => Ty.substitute τ (σ b)) a) :=
  Ty.substitute_comp σ τ a ▸ second (first c)

/-- Successive type-derived interpretations agree with their composite, on
open terms as well as closed formulas. -/
theorem mapTypes_comp (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (first : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (second : ∀ {a}, Const' a → Const'' (Ty.substitute τ a))
    {Γ : Ctx Base} {a : Ty Base} (t : Term Const Γ a) :
    HEq (mapTypes τ second (mapTypes σ first t))
      (mapTypes (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) t) := by
  induction t <;> simp only [mapTypes] <;> congr 1 <;>
    simp_all [Ty.substitute_comp, Var.mapTypes_comp, composeTypeConstants]
  exact (eqRec_heq _ _).symm

/-- Closed formulas have identical target indices, so the composition law is
ordinary equality rather than heterogeneous equality. -/
theorem mapTypes_comp_closed (σ : Base → Ty Base') (τ : Base' → Ty Base'')
    (first : ∀ {a}, Const a → Const' (Ty.substitute σ a))
    (second : ∀ {a}, Const' a → Const'' (Ty.substitute τ a))
    (φ : ClosedFormula Const) :
    mapTypes τ second (mapTypes σ first φ) =
      mapTypes (fun b => Ty.substitute τ (σ b))
        (composeTypeConstants σ τ first second) φ :=
  eq_of_heq (mapTypes_comp σ τ first second φ)

@[simp] theorem mapTypes_id_closed (φ : ClosedFormula Const) :
    mapTypes (Const' := Const) Ty.base
      (fun {a} c => (Ty.substitute_id a).symm ▸ c) φ = φ :=
  eq_of_heq (mapTypes_id φ)

#print axioms mapTypes_id
#print axioms mapTypes_comp

end Mettapedia.Logic.HOL
