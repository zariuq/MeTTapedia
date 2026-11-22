import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.PhasesInitial
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.TreeFibre.InPlaceAuditControls

/-!
# Controls: initial solutions beyond telescopes of universe families

The base is the tree's in-place solver driven by its rank, keeping a solved run only when its answer covers its frame
(`coverBase`): its answers are then epimorphisms on terms. Stores over telescopes that are not of universe families
(`y : X`, with `X` an unknown) are decided in phases from it, and their answers are initial solutions.

* **The reordering store** (`X ≐ Π (_ : Z). Z` over `X : U1, y : X, Z : U0`): the base alone does not decide it
  (`re_base_alone`); two phases through an exchange of declarations do (`re_phases`), and its answer is the initial
  solution (`re_initial`): the exchange keeps the answer an epimorphism.
* **The dd store and the met store** have initial solutions too (`dd_initial`, `met_initial`).
* **Where this route stops**: the cooperation store, decided in phases from bases with principal answers
  (`ThroughPhasesControls.coop_principal`), is not decided from covering bases (`coop_not_covered`): its glb join keeps
  an unknown declared again at another type, so the answer does not cover its frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace TreeFibre

namespace InitialControls

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta ContextualDependentUpdate ContextualDependentWorklist
open ContextualDependentPatternFiring.Controls

/-- **The covering base**: the in-place solver driven by its rank, a solved run kept only when its answer covers its
frame. -/
def coverBase {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) : Option (Decided problem) :=
  Decided.ofRankCover ContextualDependentInPlace.Controls.inPlaceOnly problem

theorem coverBase_epi {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) (d : Decided problem)
    (found : coverBase problem = some d) : d.Epi :=
  ofRankCover_epi _ problem d found

/-- **Deciding in phases from the covering base.** -/
abbrev coverPhases (fuel depth : Nat) {Θ : Context setting.R} (problem : EquationStore (TotalTerm Θ)) :=
  phases (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer coverBase fuel depth problem

/-- A decision in phases from the covering base that solved the store gives its initial solution. -/
theorem initial_of_cover {Θ : Context setting.R} {problem : EquationStore (TotalTerm Θ)} {fuel depth : Nat}
    (solved : Controls.decidedKind (coverPhases fuel depth problem) = 1) :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Θ), InitialSolution (frames setting.levels) problem answer := by
  have epi := phases_epi (S := setting) TowerModel.facts TowerModel.roots TowerModel.heads TowerModel.algebra
    ContextualDependentInversion.Controls.declarations_formed ExecutableTowerChoices.choices
    ContextualDependentInversion.Controls.reducer coverBase coverBase_epi fuel depth problem
  generalize found : coverPhases fuel depth problem = decision at solved epi
  rcases decision with _ | ⟨update, finished⟩ | absent
  · simp [Controls.decidedKind] at solved
  · exact ⟨update.target, update.answer, Decided.initial_of_epi (finished := finished) (epi _ found)⟩
  · simp [Controls.decidedKind] at solved

/-! ## The reordering store: through an exchange -/

/-- **The base alone does not decide it.** -/
theorem re_base_alone : Controls.decidedKind (coverBase Controls.reStore) = 0 := by decide +kernel

/-- **Two phases through an exchange do.** -/
theorem re_phases : Controls.decidedKind (coverPhases 6 2 Controls.reStore) = 1 := by decide +kernel

/-- **Its answer is the initial solution**, over a telescope that is not of universe families. -/
theorem re_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Controls.ctxRe),
      InitialSolution (frames setting.levels) Controls.reStore answer :=
  initial_of_cover re_phases

/-! ## The dd store and the met store -/

theorem dd_phases : Controls.decidedKind (coverPhases 6 1 Controls.ddStore) = 1 := by decide +kernel

theorem dd_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Controls.ctxDd),
      InitialSolution (frames setting.levels) Controls.ddStore answer :=
  initial_of_cover dd_phases

theorem met_phases : Controls.decidedKind (coverPhases 6 2 Controls.metStore) = 1 := by decide +kernel

theorem met_initial :
    ∃ (Δ : Context setting.R) (answer : Δ ⟶ Controls.ctxMet),
      InitialSolution (frames setting.levels) Controls.metStore answer :=
  initial_of_cover met_phases

/-! ## Where this route stops -/

/-- **The cooperation store is not decided from covering bases**: its glb join declares an unknown again. -/
theorem coop_not_covered : Controls.decidedKind (coverPhases 6 2 Controls.coopStore) = 0 := by decide +kernel

end InitialControls

end TreeFibre

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
