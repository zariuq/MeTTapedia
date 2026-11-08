import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.DependentFrames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch

/-!
# Conversion-checked worklists at dependent frames

An equation retains separately formed endpoint types. A bounded search may
certify their conversion and expose a homogeneous obligation, or certify both
type and term conversion and discharge it. Otherwise the equation remains
pending. Failure to find a conversion is never a refutation.

The worklist uses the dependent frame instance's equations and models. Every
pass preserves exactly the solutions in every future frame, including after
typed substitution. This is the conversion and postponement part of a solver;
it does not claim general pattern completeness or decide inhabitation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentConstraints

open CategoryTheory Interface Interface.Dependent
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open FormationSensitiveContextual

variable {Head : Type} {rules : Rules Head}

/-- An active equation has checked convertible endpoint types. -/
structure Ready (Γ : Context rules) where
  equation : Equation (Entry Γ)
  types : Conv rules.headEq equation.1.type.code equation.2.type.code rules.computation

/-- The right endpoint really can be checked at the left endpoint's type.
This uses conversion and retained formation, not equality of raw type codes. -/
def Ready.right {Γ : Context rules} (ready : Ready Γ) : Term Γ ready.equation.1.type :=
  ⟨ready.equation.2.term.code,
    .conv ready.equation.2.term.typed ready.equation.1.type.formed
      ready.equation.1.type.universeWitness (.symm _ _ ready.types)⟩

def Ready.reindex {Γ Δ : Context rules} (ready : Ready Γ) (σ : Δ ⟶ Γ) : Ready Δ :=
  ⟨(ready.equation.1.reindex σ, ready.equation.2.reindex σ),
    Conv.substitute σ.substitution ready.types⟩

structure Worklist (Γ : Context rules) where
  active : List (Ready Γ)
  pending : EquationStore (Entry Γ)

def Worklist.store {Γ : Context rules} (work : Worklist Γ) : EquationStore (Entry Γ) :=
  work.active.map Ready.equation ++ work.pending

def Worklist.reindex {Γ Δ : Context rules} (work : Worklist Γ) (σ : Δ ⟶ Γ) : Worklist Δ :=
  ⟨work.active.map (fun ready => ready.reindex σ), (frames rules).applyStore σ work.pending⟩

theorem Worklist.reindex_store {Γ Δ : Context rules} (work : Worklist Γ) (σ : Δ ⟶ Γ) :
    (work.reindex σ).store = (frames rules).applyStore σ work.store := by
  simp only [Worklist.reindex, Worklist.store, Frames.applyStore,
    List.map_append, List.map_map]
  rfl

theorem Worklist.models_reindex {Γ Δ Θ : Context rules} (work : Worklist Γ)
    (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (frames rules).Models τ (work.reindex σ).store ↔
      (frames rules).Models (τ ≫ σ) work.store := by
  rw [work.reindex_store]
  exact Frames.models_applyStore (X := frames rules) σ τ work.store

/-- These outcomes retain successful conversion evidence. Pending is a
search outcome, with no claim that the equation is insoluble. -/
inductive Inspection {Γ : Context rules} (equation : Equation (Entry Γ)) where
  | solved (converted : Entry.Convertible equation.1 equation.2)
  | ready (types : Conv rules.headEq equation.1.type.code equation.2.type.code rules.computation)
  | pending

variable [DecidableEq Head] [DecidableRel rules.headEq]
variable (decoder : StructuralConversionCode.RootDecoder rules.computation)
variable (findRoot : {n : Nat} → Tm Head n → Option (decoder.Code n))

def inspect (fuel : Nat) {Γ : Context rules} (equation : Equation (Entry Γ)) : Inspection equation :=
  match checkedTypes : StructuralConversionSearch.compare decoder findRoot
      (headEq := rules.headEq) fuel equation.1.type.code equation.2.type.code with
  | none => .pending
  | some types =>
      let typeConversion := StructuralConversionSearch.compare_sound decoder findRoot
        fuel _ _ types checkedTypes
      match checkedTerms : StructuralConversionSearch.compare decoder findRoot
          (headEq := rules.headEq) fuel equation.1.term.code equation.2.term.code with
      | none => .ready typeConversion
      | some terms => .solved ⟨typeConversion,
          StructuralConversionSearch.compare_sound decoder findRoot fuel _ _ terms checkedTerms⟩

/-- Scan every equation once; neither a pending equation nor an active one
is discarded unless both of its conversions have been checked. -/
def scan (fuel : Nat) {Γ : Context rules} : EquationStore (Entry Γ) → Worklist Γ
  | [] => ⟨[], []⟩
  | equation :: rest =>
      let next := scan fuel rest
      match inspect decoder findRoot fuel equation with
      | .solved _ => next
      | .ready types => ⟨⟨equation, types⟩ :: next.active, next.pending⟩
      | .pending => ⟨next.active, equation :: next.pending⟩

omit [DecidableEq Head] [DecidableRel rules.headEq] in
private theorem models_cons {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    (equation : Equation (Entry Γ)) (rest : EquationStore (Entry Γ)) :
    (frames rules).Models σ (equation :: rest) ↔
      (frames rules).Solves σ equation ∧ (frames rules).Models σ rest := by
  simp only [Frames.Models, List.mem_cons, forall_eq_or_imp]

/-- Exact solution preservation, not merely preservation of one chosen
answer. Successful certificates remain valid at every later typed frame. -/
theorem scan_models (fuel : Nat) {Γ Δ : Context rules} (σ : Δ ⟶ Γ)
    (problem : EquationStore (Entry Γ)) :
    (frames rules).Models σ (scan decoder findRoot fuel problem).store ↔
      (frames rules).Models σ problem := by
  induction problem with
  | nil => simp [scan, Worklist.store]
  | cons equation rest ih =>
      simp only [scan]
      cases outcome : inspect decoder findRoot fuel equation with
      | solved converted =>
          rw [models_cons]
          exact ⟨fun solved => ⟨(frames rules).preserves σ converted, ih.mp solved⟩,
            fun solved => ih.mpr solved.2⟩
      | ready types =>
          change (frames rules).Models σ (equation :: (scan decoder findRoot fuel rest).store) ↔ _
          rw [models_cons, models_cons]
          exact and_congr_right (fun _ => ih)
      | pending =>
          change (frames rules).Models σ
            ((scan decoder findRoot fuel rest).active.map Ready.equation ++
              equation :: (scan decoder findRoot fuel rest).pending) ↔ _
          change (frames rules).Models σ
            ((scan decoder findRoot fuel rest).active.map Ready.equation ++
              (scan decoder findRoot fuel rest).pending) ↔ _ at ih
          rw [Frames.models_append] at ih
          rw [Frames.models_append, models_cons, models_cons]
          tauto

theorem scan_solvable_iff (fuel : Nat) {Γ : Context rules}
    (problem : EquationStore (Entry Γ)) :
    (frames rules).Solvable (scan decoder findRoot fuel problem).store ↔
      (frames rules).Solvable problem :=
  Frames.Equivalent.solvable_iff (fun _ σ => scan_models decoder findRoot fuel σ problem)

theorem scan_entails_iff (fuel : Nat) {Γ : Context rules}
    (problem : EquationStore (Entry Γ))
    (observation : (Δ : Context rules) → (Δ ⟶ Γ) → Prop) :
    (frames rules).Entails (scan decoder findRoot fuel problem).store observation ↔
      (frames rules).Entails problem observation :=
  Frames.Equivalent.entails_iff (X := frames rules)
    (fun _ σ => scan_models decoder findRoot fuel σ problem) observation

/-- An exhausted equation queue certifies a principal identity answer for
the scanned problem. Unsolved queues make no such claim. -/
theorem scan_empty_principal (fuel : Nat) {Γ : Context rules}
    (problem : EquationStore (Entry Γ))
    (finished : (scan decoder findRoot fuel problem).store = []) :
    (frames rules).Principal problem (𝟙 Γ) where
  sound := (scan_models decoder findRoot fuel (𝟙 Γ) problem).mp (by
    rw [finished]
    exact Frames.models_nil _)
  factors := by
    intro Δ σ _
    refine ⟨σ, fun term => ?_⟩
    change Entry.Convertible (term.reindex σ) (term.reindex (σ ≫ 𝟙 Γ))
    rw [Category.comp_id]
    exact Entry.Convertible.refl _

/-- Reattempting a suspended problem after a typed tell preserves precisely
the original solutions that factor through that tell. -/
theorem scan_reindexed_models (fuel : Nat) {Γ Δ Θ : Context rules}
    (work : Worklist Γ) (σ : Δ ⟶ Γ) (τ : Θ ⟶ Δ) :
    (frames rules).Models τ (scan decoder findRoot fuel (work.reindex σ).store).store ↔
      (frames rules).Models (τ ≫ σ) work.store :=
  (scan_models decoder findRoot fuel τ _).trans (work.models_reindex σ τ)

end ContextualDependentConstraints
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
