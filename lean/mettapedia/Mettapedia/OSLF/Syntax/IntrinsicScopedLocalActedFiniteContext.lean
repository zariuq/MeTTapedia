import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFree
import Mettapedia.OSLF.Syntax.IndexedRuleFiniteListSkeleton
import Mettapedia.TypeTheory.IndexedPolynomialFreeMapInjective

/-!
# Finite contexts of rule-local, substitution-closed events

Each listed event variable has an exact original judgment. Arrows interpret
its uses naturally across contextual substitutions, then extend uniquely to
all local-rule firing trees. Composition is induced by model-map composition.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext

open CategoryTheory
open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalJudgmentCategory
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree
open Mettapedia.OSLF.Binding.IndexedRuleFiniteListSkeleton
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalEventOrbit
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
open Mettapedia.TypeTheory

variable {S : Signature}
variable (R : List (LocalRule S))
variable (A : BindingCloneAlgebra.Algebra.{0} S)

/-- Finite ordered event positions over the selected local-rule polynomial. -/
structure Context where
  listed : ListContext (rules R A)

/-- A seed is an enumerated event variable at its original judgment. -/
def seeds (Γ : Context R A) (sort : S.Srt)
    (state : State A sort) : Type :=
  (toContext (rules R A) Γ.listed).slots (state.asJudgment A)

/-- The old exact-judgment variable is the same original event generator
used through the identity substitution arrow. -/
noncomputable def exactHole (Γ : Context R A)
    {judgment : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A}
    (slot : (toContext (rules R A) Γ.listed).slots judgment) :
    Holes A (seeds R A Γ) judgment :=
  Orbit.unit A (seeds R A Γ)
    ((State.as_of A judgment).symm ▸ slot)

theorem exactHole_injective (Γ : Context R A)
    (judgment : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) :
    Function.Injective (exactHole R A Γ (judgment := judgment)) := by
  intro first second same
  unfold exactHole at same
  have castEq :
      ((State.as_of A judgment).symm ▸ first) =
        ((State.as_of A judgment).symm ▸ second) := by
    cases same
    rfl
  exact eq_of_heq
    ((heq_transport (State.as_of A judgment).symm first).symm.trans
      ((heq_of_eq castEq).trans
        (heq_transport (State.as_of A judgment).symm second)))

/-- Embedding exact-position rule trees leaves both authored rule nodes and
the identity of each original event position intact. -/
noncomputable def embedExact (Γ : Context R A)
    (judgment : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) :
    IndexedRuleFiniteContexts.Term (rules R A)
      (toContext (rules R A) Γ.listed) judgment →
      Tree R A (seeds R A Γ) judgment :=
  IndexedPolynomial.Free.map (rules R A)
    (fun _ _ slot => exactHole R A Γ slot) () judgment

theorem embedExact_injective (Γ : Context R A)
    (judgment : Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial.Judgment A) :
    Function.Injective (embedExact R A Γ judgment) :=
  IndexedPolynomial.Free.map_injective (rules R A)
    (fun _ _ slot => exactHole R A Γ slot)
    (fun _ index => exactHole_injective R A Γ index)
    () judgment

/-- An arrow interprets every use of each target event variable and commutes
with substitution of its ordinary variables. -/
abbrev Hom (Γ Δ : Context R A) : Type :=
  NaturalAssignment R A (seeds R A Δ)
    (freeModel R A (seeds R A Γ))

/-- The universal fold identifies context arrows with maps of the associated
free substitution-operational models. -/
noncomputable def homEquiv (Γ Δ : Context R A) :
    Hom R A Γ Δ ≃
      SubstitutionModel.Hom R A
        (freeModel R A (seeds R A Δ))
        (freeModel R A (seeds R A Γ)) :=
  freeModelUniversal R A (seeds R A Δ)
    (freeModel R A (seeds R A Γ))

noncomputable def asModelHom {Γ Δ : Context R A}
    (f : Hom R A Γ Δ) :
    SubstitutionModel.Hom R A
      (freeModel R A (seeds R A Δ))
      (freeModel R A (seeds R A Γ)) :=
  (homEquiv R A Γ Δ) f

noncomputable def Hom.id (Γ : Context R A) : Hom R A Γ Γ :=
  (homEquiv R A Γ Γ).symm
    (SubstitutionModel.Hom.id R A (freeModel R A (seeds R A Γ)))

noncomputable def Hom.comp {Γ Δ Θ : Context R A}
    (first : Hom R A Γ Δ) (second : Hom R A Δ Θ) :
    Hom R A Γ Θ :=
  (homEquiv R A Γ Θ).symm
    (SubstitutionModel.Hom.comp R A
      (asModelHom R A second) (asModelHom R A first))

theorem asModelHom_id (Γ : Context R A) :
    asModelHom R A (Hom.id R A Γ) =
      SubstitutionModel.Hom.id R A (freeModel R A (seeds R A Γ)) :=
  (homEquiv R A Γ Γ).apply_symm_apply _

theorem asModelHom_comp {Γ Δ Θ : Context R A}
    (first : Hom R A Γ Δ) (second : Hom R A Δ Θ) :
    asModelHom R A (Hom.comp R A first second) =
      SubstitutionModel.Hom.comp R A
        (asModelHom R A second) (asModelHom R A first) :=
  (homEquiv R A Γ Θ).apply_symm_apply _

/-- Finite event contexts form a category whose arrows preserve both rule
constructors and substitution of individual firing evidence. -/
noncomputable instance : Category (Context R A) where
  Hom := Hom R A
  id := Hom.id R A
  comp := Hom.comp R A
  id_comp := by
    intro Γ Δ f
    apply (homEquiv R A Γ Δ).injective
    change asModelHom R A (Hom.comp R A (Hom.id R A Γ) f) =
      asModelHom R A f
    rw [asModelHom_comp, asModelHom_id]
    exact SubstitutionModel.Hom.comp_id R A (asModelHom R A f)
  comp_id := by
    intro Γ Δ f
    apply (homEquiv R A Γ Δ).injective
    change asModelHom R A (Hom.comp R A f (Hom.id R A Δ)) =
      asModelHom R A f
    rw [asModelHom_comp, asModelHom_id]
    exact SubstitutionModel.Hom.id_comp R A (asModelHom R A f)
  assoc := by
    intro Γ Δ Θ Ψ first second third
    apply (homEquiv R A Γ Ψ).injective
    change asModelHom R A
        (Hom.comp R A (Hom.comp R A first second) third) =
      asModelHom R A (Hom.comp R A first
        (Hom.comp R A second third))
    rw [asModelHom_comp, asModelHom_comp,
      asModelHom_comp, asModelHom_comp]
    exact (SubstitutionModel.Hom.assoc R A
      (asModelHom R A third) (asModelHom R A second)
      (asModelHom R A first)).symm

/-- The finite event-context category embeds fully and faithfully into
free rule-local substitution models with arrows reversed. -/
noncomputable def intoModels :
    Context R A ⥤ (SubstitutionModel R A)ᵒᵖ where
  obj Γ := Opposite.op (freeModel R A (seeds R A Γ))
  map f := Quiver.Hom.op (asModelHom R A f)
  map_id Γ := by
    apply Quiver.Hom.unop_inj
    exact asModelHom_id R A Γ
  map_comp first second := by
    apply Quiver.Hom.unop_inj
    exact asModelHom_comp R A first second

instance intoModels_full : (intoModels R A).Full where
  map_surjective := by
    intro Γ Δ mapped
    refine ⟨(homEquiv R A Γ Δ).symm mapped.unop, ?_⟩
    apply Quiver.Hom.unop_inj
    exact (homEquiv R A Γ Δ).apply_symm_apply mapped.unop

instance intoModels_faithful : (intoModels R A).Faithful where
  map_injective := by
    intro Γ Δ first second same
    apply (homEquiv R A Γ Δ).injective
    exact congrArg Quiver.Hom.unop same

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext
