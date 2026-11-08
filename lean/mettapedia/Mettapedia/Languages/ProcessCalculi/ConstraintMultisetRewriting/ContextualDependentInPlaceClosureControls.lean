import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentSpineEtaControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualDependentInPlaceClosure

/-!
# In-place answers leave `Stratified` under the last family

* **The witness under the last family** (`flexOnly`, budget 16): the first round on
  `ContextualDependentInPlaceClosure.witnessStore` solves `X` in place, to a residual outside `Stratified`, inside the
  corrected class `StratifiedShort`, and solvable (`witness_first_round_last`). The store commits
  (`witness_committed_last`); a committed run certifies solvability (`solvable_of_commit`), and an update keeps it
  (`Update.solvable_iff`).
* **A store where the in-place answer would leave `Stratified`, but the family avoids it**: over
  `A : U0, X : U0, F : X, H : X`, the store `[X ≐ Π A A, F ≐ H]` is in the fragment (`placed_in_fragment`). Solving `X`
  first would declare `F, H : Π A A` with bare occurrences, outside `Stratified`. The family solves the newest
  metavariable first (`H := F`, `placed_newest_first`) and commits (`placed_committed`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace ContextualDependentInPlaceClosure.Controls

open CategoryTheory
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentWorklist ContextualDependentDynamicFragment ContextualDependentUpdate
open ContextualDependentClosure
open ContextualDependentSpineEta.Controls ContextualDependentPatternFiring.Controls ContextualDependentInPlaceClosure

/-- A committed run certifies that its store is solvable. -/
theorem solvable_of_commit {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    {outcome : Outcome setting.levels original} (committed : outcome.readout = .commit) :
    (frames setting.levels).Solvable original := by
  cases outcome with
  | solved state finished =>
      have empty : (frames setting.levels).Models (𝟙 state.target) state.remaining := by
        rw [finished]
        intro _ member
        cases member
      have solved := state.sound state.target (𝟙 state.target) empty
      rw [Category.id_comp] at solved
      exact ⟨state.target, state.answer, solved⟩
  | refuted _ => cases committed
  | stuck _ => cases committed
  | cutoff _ => cases committed

/-- The first round's residual leaves `Stratified` for the corrected class. -/
noncomputable def leavesStratified {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)} :
    Outcome setting.levels original → Bool
  | .cutoff state => headOutside state.remaining && singleShort state.remaining
  | _ => false

theorem first_round_of_check {Γ : Context setting.R} {original : EquationStore (TotalTerm Γ)}
    (committed : (run flexOnly original 8).readout = .commit) (check : leavesStratified (run flexOnly original 1) = true) :
    ∃ state : Update setting.levels original, run flexOnly original 1 = .cutoff state ∧
      ¬ Stratified setting.levels state.remaining ∧ StratifiedShort setting.levels state.remaining ∧
      (frames setting.levels).Solvable state.remaining := by
  generalize ran : run flexOnly original 1 = outcome at check
  cases outcome with
  | cutoff state =>
      simp only [leavesStratified, Bool.and_eq_true] at check
      exact ⟨state, rfl, not_stratified_of_headOutside check.1, stratifiedShort_of_singleShort check.2,
        state.solvable_iff.mp (solvable_of_commit committed)⟩
  | solved _ _ => cases check
  | refuted _ => cases check
  | stuck _ => cases check

theorem witness_committed_last : (run flexOnly witnessStore 8).readout = .commit := by decide +kernel

/-- **The witness under the last family**: its first round solves `X` in place, to a solvable residual outside
`Stratified` and inside `StratifiedShort`. -/
theorem witness_first_round_last :
    ∃ state : Update setting.levels witnessStore, run flexOnly witnessStore 1 = .cutoff state ∧
      ¬ Stratified setting.levels state.remaining ∧ StratifiedShort setting.levels state.remaining ∧
      (frames setting.levels).Solvable state.remaining :=
  first_round_of_check witness_committed_last (by decide +kernel)

/-- `X`, over `A, X`. -/
def typeX : TypeOver withX := formIn withX (.var 0) (by decide +kernel)

/-- `A : U0, X : U0, F : X`. -/
abbrev withXF := extend withX typeX

/-- `X`, over `A, X, F`. -/
def typeXF : TypeOver withXF := formIn withXF (.var 1) (by decide +kernel)

/-- `A : U0, X : U0, F : X, H : X`. -/
abbrev withXFH := extend withXF typeXF

def universeXFH : TypeOver withXFH := formIn withXFH (.head (.sort Tower.zero)) (by decide +kernel)

/-- `X`, over `A, X, F, H`. -/
def typeXFH : TypeOver withXFH := formIn withXFH (.var 2) (by decide +kernel)

/-- `X ≐ Π A A`. -/
def placedFirst : Equation (TotalTerm withXFH) :=
  (termIn withXFH universeXFH (.var 2) (by decide +kernel),
    termIn withXFH universeXFH (.pi (.var 3) (.var 4)) (by decide +kernel))

/-- `F ≐ H` at `X`. -/
def placedSecond : Equation (TotalTerm withXFH) :=
  (termIn withXFH typeXFH (.var 1) (by decide +kernel), termIn withXFH typeXFH (.var 0) (by decide +kernel))

/-- `[X ≐ Π A A, F ≐ H]`. -/
def placedStore : EquationStore (TotalTerm withXFH) := [placedFirst, placedSecond]

theorem placedFirst_in_fragment : InFragment placedFirst := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl placedFirst.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

theorem placedSecond_in_fragment : InFragment placedSecond := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact IsType.refl placedSecond.1.1.isType
  · exact (ContextualDependentNormalizing.normal_iff_step_none rfl _).mpr (by decide +kernel)
  · decide +kernel
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)
  · exact ContextualDependentDynamicFragment.Controls.side_by_normalizer 64 (by decide +kernel) (by decide +kernel)
      (by decide +kernel)

/-- **The store is in the dynamic pattern fragment.** -/
theorem placed_in_fragment : InFragmentStore placedStore := by
  intro equation member
  rcases List.mem_cons.mp member with same | later
  · rw [same]
    exact placedFirst_in_fragment
  · rw [List.mem_singleton.mp later]
    exact placedSecond_in_fragment

theorem placed_committed : (run flexOnly placedStore 8).readout = .commit := by decide +kernel

/-- The first round's residual is one equation over three declarations, whose left side is the variable at index 1. -/
noncomputable def newestFirst : Bool :=
  match run flexOnly placedStore 1 with
  | .cutoff state =>
      match state.remaining with
      | [equation] => decide ((⟨_, equation.1.2.code⟩ : Σ n, Tower.Tm n) = ⟨3, .var 1⟩)
      | _ => false
  | _ => false

/-- **The first round solves the newest metavariable, not `X`**: `H := F` by the pattern rule, leaving `X ≐ Π A A` over
`A, X, F` (`X` is the variable at index 1). The in-place answer for `X` that would leave `Stratified` is not the step the
family takes; the next round solves `X` with no equation left. -/
theorem placed_newest_first : newestFirst = true := by decide +kernel

end ContextualDependentInPlaceClosure.Controls
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
