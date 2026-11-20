import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences.UsedUp
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Locality

/-!
# The candidate reads the present rows only through the regions of its firing

`RuleSyntax/Locality` proves that the step of a program reads the present rows only through the
regions of a firing: its taken, read and made identities and the rows that a solution of its
information equates with one of its query patterns (`RuleSyntax.OutsideRegions`).

The same holds of the candidate, for every code system and every firing, with rule queries,
installs, removals and publications:

* **`RFiring.admits_of_outsideRegions`**: a firing admitted at a state is admitted after any change
  of the present rows outside the regions of the firing read in the present step (`RFiring.base`)
  that keeps its opening fresh. The rule queries, the installs, the removals and the publications
  read no row: they read the rule occurrences held and the firing's information.

Over first-order atoms, for the firing of `UsedUp.onceFiring`: adding the row `5`, which is outside
its regions, keeps it admitted (`RowLocality.row_outside_admitted`); removing the row it takes
refuses it (`RowLocality.row_inside_refused`).

This is locality in the rows. Which rule occurrences a firing reads (the one it uses, those of the
zones its rule queries name, those it removes) is not stated here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)

section General

universe uO uT uH uE uOcc uR uC uZ

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {O : Type uOcc} {R : Type uR} {C : Type uC} {Z : Type uZ}
  {E : Extensions.{uO, uH, uE} Hom} {codes : Codes Tm C Z}

/-- The state with other present rows, holding the same rules. -/
def RState.withPresent (s : RState Tm O R C Z) (W : Finset O) : RState Tm O R C Z :=
  ⟨s.toState.withPresent W, s.rules, s.held⟩

/-- A firing, at the state with other present rows. -/
def RFiring.atPresent {s : RState Tm O R C Z} (f : RFiring O R E codes s) (W : Finset O) :
    RFiring O R E codes (s.withPresent W) :=
  ⟨f.use, f.ext, f.opening, f.selection, f.seen, f.madeRules, f.installed, f.removedRules,
    f.published⟩

variable (X : Frames Tm Hom) [DecidableEq O] {s : RState Tm O R C Z}

/-- **Locality in the rows.** A firing admitted at a state is admitted after any change of the
present rows outside the regions of the firing read in the present step that keeps its opening
fresh. -/
theorem RFiring.admits_of_outsideRegions (f : RFiring O R E codes s) {ambient : Set C}
    {W : Finset O} (admitted : f.Admits X ambient)
    (outside : OutsideRegions X s.toState W f.base) (fresh : (f.atPresent W).Fresh X) :
    (f.atPresent W).Admits X ambient := by
  obtain ⟨⟨-, rows, shapes⟩, enabled, solvable, asks⟩ := admitted
  refine ⟨⟨fresh, rows, ?_⟩, (enabled_iff_of_outsideRegions outside).mp enabled, solvable, ?_⟩
  · exact ⟨shapes.available, shapes.arguments, shapes.installed, shapes.madeNodup,
      shapes.madeLength, shapes.madeNew, shapes.removed, shapes.removedNodup, shapes.removedHeld,
      shapes.published⟩
  · intro b σ solved
    have solved' : X.Models σ (f.information X) := solved
    have holds := asks b σ solved'
    have solvedBase : X.Models σ (f.base.information X s.toState) :=
      fun e member => solved' e (List.mem_append_left _ member)
    exact ⟨(holds_iff_of_outsideRegions outside solvedBase).mp holds.1, holds.2.1, holds.2.2.1,
      holds.2.2.2.1, holds.2.2.2.2⟩

end General

#print axioms RFiring.admits_of_outsideRegions

namespace RowLocality

open Mettapedia.Logic.LP
open Examples (Tm X E c)
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.Controls
  (atoms action)

/-- Adding the row `5` is a change outside the regions of the firing that takes row `0` and makes
row `1`. -/
theorem outside_five :
    OutsideRegions X UsedUp.factState.toState {0, 5} UsedUp.onceFiring.base where
  touched := by
    rintro o (taken | read | made)
    · obtain rfl := List.mem_singleton.mp taken
      decide
    · exact absurd read List.not_mem_nil
    · obtain rfl := List.mem_singleton.mp made
      decide
  queries := fun _ _ _ _ member => absurd member List.not_mem_nil

/-- The opening is fresh at the state with the added row: the rule has no unknowns. -/
theorem fresh_five : (UsedUp.onceFiring.atPresent {0, 5}).Fresh X := by
  apply fresh_of_ground action
  intro t member σ
  have terms : (UsedUp.onceFiring.atPresent {0, 5}).spec.terms = Exec.onceRule.terms :=
    Spec.terms_of_plain (Spec.plain_ofRule Exec.onceRule)
  rw [terms] at member
  have inside : t ∈ Exec.onceRule.terms := member
  simp [Exec.onceRule, Rule.terms] at inside
  rcases inside with rfl | rfl <;> rfl

/-- **A row added outside the regions keeps the firing admitted.** -/
theorem row_outside_admitted :
    (UsedUp.onceFiring.atPresent {0, 5}).Admits X (∅ : Set (Rule Tm)) :=
  UsedUp.onceFiring.admits_of_outsideRegions X UsedUp.once_admitted outside_five fresh_five

/-- **Control: removing the row the firing takes refuses it.** -/
theorem row_inside_refused :
    ¬ (UsedUp.onceFiring.atPresent ∅).Admits X (∅ : Set (Rule Tm)) := by
  intro admitted
  have inside : (0 : ℕ) ∈ (∅ : Finset ℕ) :=
    admitted.2.1.taken_subset (List.mem_toFinset.mpr (List.mem_singleton_self 0))
  exact absurd inside (Finset.notMem_empty 0)

#print axioms outside_five
#print axioms row_outside_admitted
#print axioms row_inside_refused

end RowLocality

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.RuleOccurrences
