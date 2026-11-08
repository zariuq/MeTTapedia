import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentConstraints

/-!
# Eliminating a dependent telescope definition

The newest variable may be assigned a term of the preceding context. The
assignment is applied to every remaining endpoint and its type, after which
bounded conversion search revisits the whole worklist. Every solution of the
original definition and residual problem factors through this operation;
every resulting solution reconstructs one. No arbitrary solution is selected.

This rule handles a definition at the end of a telescope. General dependent
pruning and contextual pattern inversion are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstraints

open CategoryTheory Interface Interface.Dependent
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

theorem models_pointwise {Γ Δ : Context rules} {σ τ : Δ ⟶ Γ}
    (same : ∀ term : Entry Γ, Entry.Convertible (term.reindex σ) (term.reindex τ))
    (problem : EquationStore (Entry Γ)) :
    (frames rules).Models σ problem ↔ (frames rules).Models τ problem := by
  constructor
  · intro solved equation member
    exact Entry.Convertible.trans (Entry.Convertible.symm (same equation.1))
      (Entry.Convertible.trans (solved equation member) (same equation.2))
  · intro solved equation member
    exact Entry.Convertible.trans (same equation.1)
      (Entry.Convertible.trans (solved equation member) (Entry.Convertible.symm (same equation.2)))

/-- Elimination retains all solutions, modulo conversion of their action
on the original context; the remaining equations may depend on the variable. -/
theorem definition_models_iff {Γ Δ : Context rules} {A : TypeOver Γ}
    (value : Term Γ A) (problem : EquationStore (Entry (extend Γ A)))
    (σ : Δ ⟶ extend Γ A) :
    (frames rules).Models σ (definition Γ value :: problem) ↔
      ∃ τ : Δ ⟶ Γ,
        (frames rules).Models τ ((frames rules).applyStore (instantiate Γ value) problem) ∧
        ∀ term : Entry (extend Γ A),
          Entry.Convertible (term.reindex σ) (term.reindex (τ ≫ instantiate Γ value)) := by
  constructor
  · intro solved
    have defined : (frames rules).Models σ [definition Γ value] :=
      Frames.models_of_subset
        (fun _ member => List.mem_cons.mpr (.inl (List.mem_singleton.mp member))) solved
    obtain ⟨τ, factor⟩ := (definition_principal Γ value).factors Δ σ defined
    refine ⟨τ, ?_, factor⟩
    apply (Frames.models_applyStore (X := frames rules) (instantiate Γ value) τ problem).mpr
    exact (models_pointwise factor problem).mp
      (Frames.models_of_subset (fun _ member => List.mem_cons_of_mem _ member) solved)
  · rintro ⟨τ, residual, factor⟩
    apply (models_pointwise factor _).mpr
    have defined := Frames.models_comp (X := frames rules) (definition_principal Γ value).sound τ
    have rest := (Frames.models_applyStore (X := frames rules) (instantiate Γ value) τ problem).mp residual
    intro equation member
    rcases List.mem_cons.mp member with rfl | member
    · exact defined _ (List.mem_singleton_self _)
    · exact rest equation member

/-- Principality composes through the actual dependent elimination rule. -/
theorem principal_definition_residual {Γ M : Context rules} {A : TypeOver Γ}
    (value : Term Γ A) (problem : EquationStore (Entry (extend Γ A)))
    {answer : M ⟶ Γ}
    (principal : (frames rules).Principal
      ((frames rules).applyStore (instantiate Γ value) problem) answer) :
    (frames rules).Principal (definition Γ value :: problem) (answer ≫ instantiate Γ value) where
  sound := (definition_models_iff value problem _).mpr
    ⟨answer, principal.sound, fun term => Entry.Convertible.refl _⟩
  factors := by
    intro Δ σ solved
    obtain ⟨τ, residual, factor⟩ := (definition_models_iff value problem σ).mp solved
    obtain ⟨ρ, through⟩ := principal.factors Δ τ residual
    refine ⟨ρ, fun term => ?_⟩
    have carried := through (term.reindex (instantiate Γ value))
    change Entry.Convertible
      ((term.reindex (instantiate Γ value)).reindex τ)
      ((term.reindex (instantiate Γ value)).reindex (ρ ≫ answer)) at carried
    rw [← Entry.reindex_comp, ← Entry.reindex_comp] at carried
    rw [Category.assoc] at carried
    exact Entry.Convertible.trans (factor term) carried

variable [DecidableEq Head] [DecidableRel rules.headEq]
variable (decoder : StructuralConversionCode.RootDecoder rules.computation)
variable (findRoot : {n : Nat} → Tm Head n → Option (decoder.Code n))

def eliminateDefinition (fuel : Nat) {Γ : Context rules} {A : TypeOver Γ}
    (value : Term Γ A) (work : Worklist (extend Γ A)) : Worklist Γ :=
  scan decoder findRoot fuel (work.reindex (instantiate Γ value)).store

theorem eliminateDefinition_models_iff (fuel : Nat) {Γ Δ : Context rules} {A : TypeOver Γ}
    (value : Term Γ A) (work : Worklist (extend Γ A)) (σ : Δ ⟶ extend Γ A) :
    (frames rules).Models σ (definition Γ value :: work.store) ↔
      ∃ τ : Δ ⟶ Γ,
        (frames rules).Models τ (eliminateDefinition decoder findRoot fuel value work).store ∧
        ∀ term : Entry (extend Γ A),
          Entry.Convertible (term.reindex σ) (term.reindex (τ ≫ instantiate Γ value)) := by
  rw [definition_models_iff value work.store σ]
  apply exists_congr
  intro τ
  apply and_congr_left
  intro _
  dsimp only [eliminateDefinition]
  rw [scan_models, work.reindex_store]

theorem eliminateDefinition_solvable_iff (fuel : Nat) {Γ : Context rules} {A : TypeOver Γ}
    (value : Term Γ A) (work : Worklist (extend Γ A)) :
    (frames rules).Solvable (definition Γ value :: work.store) ↔
      (frames rules).Solvable (eliminateDefinition decoder findRoot fuel value work).store := by
  constructor
  · rintro ⟨Δ, σ, solved⟩
    obtain ⟨τ, residual, _⟩ :=
      (eliminateDefinition_models_iff decoder findRoot fuel value work σ).mp solved
    exact ⟨Δ, τ, residual⟩
  · rintro ⟨Δ, τ, residual⟩
    refine ⟨Δ, τ ≫ instantiate Γ value,
      (eliminateDefinition_models_iff decoder findRoot fuel value work _).mpr ?_⟩
    exact ⟨τ, residual, fun term => Entry.Convertible.refl _⟩

/-- Guards transport through elimination when their readout respects
conversion of solutions. This premise is explicit: arbitrary syntax-sensitive
observers need not respect the solver's factorization. -/
theorem eliminateDefinition_entails_iff (fuel : Nat) {Γ : Context rules} {A : TypeOver Γ}
    (value : Term Γ A) (work : Worklist (extend Γ A))
    (observation : (Δ : Context rules) → (Δ ⟶ extend Γ A) → Prop)
    (respects : ∀ (Δ : Context rules) (σ τ : Δ ⟶ extend Γ A),
      (∀ term : Entry (extend Γ A), Entry.Convertible (term.reindex σ) (term.reindex τ)) →
        (observation Δ σ ↔ observation Δ τ)) :
    (frames rules).Entails (definition Γ value :: work.store) observation ↔
      (frames rules).Entails (eliminateDefinition decoder findRoot fuel value work).store
        (fun Δ τ => observation Δ (τ ≫ instantiate Γ value)) := by
  constructor
  · intro asked Δ τ residual
    apply asked Δ (τ ≫ instantiate Γ value)
    exact (eliminateDefinition_models_iff decoder findRoot fuel value work _).mpr
      ⟨τ, residual, fun term => Entry.Convertible.refl _⟩
  · intro asked Δ σ solved
    obtain ⟨τ, residual, factor⟩ :=
      (eliminateDefinition_models_iff decoder findRoot fuel value work σ).mp solved
    exact (respects Δ σ (τ ≫ instantiate Γ value) factor).mpr (asked Δ τ residual)

end ContextualDependentConstraints
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
