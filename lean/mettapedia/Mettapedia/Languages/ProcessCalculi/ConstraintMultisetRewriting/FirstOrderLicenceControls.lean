import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.FirstOrderLicence
import Mettapedia.Logic.LP.GroundingSeparation

/-!
# Controls for the first-order CMR solver licence

Profile: one occurrence-bag store, ambient rules, finite first-order terms.
Both ask timings can use the checker at their chosen problem; the controls
do not change the existing after-tells one-match judgment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence.Controls

open Mettapedia.Logic.LP

abbrev signature : LPSignature where
  constants := Nat
  vars := Nat
  relationSymbols := Empty
  relationArity := Empty.elim
  functionSymbols := Unit
  functionArity := fun _ => 1

def x : Term signature := .var 0
def y : Term signature := .var 1
def c (n : Nat) : Term signature := .const n
def successor (term : Term signature) : Term signature := .app () (fun _ => term)
def baseline : Subst signature := Subst.id signature
def unresolvedRows (o : Nat) : Term signature := if o = 0 then y else c 7
def duplicates (_ : Nat) : Term signature := c 4

theorem empty_accepted : unifyTotal ([] : EquationStore (Term signature)) = some baseline := by
  cbv

theorem equality_is_not_merely_unifiability :
    check baseline unresolvedRows {0} (.equal x (c 4)) = false ∧
      (unifyTotal [(x, c 4)]).isSome = true := by cbv

theorem unresolved_absence_is_not_certain :
    check baseline unresolvedRows {0} (.predicate .none (c 4)) = false := by cbv

theorem unrelated_constant_is_certainly_absent :
    check baseline (fun _ : Nat => c 7) {0} (.predicate .none (c 4)) = true := by cbv

theorem possible_extra_row_blocks_a_count :
    check baseline unresolvedRows {0} (.count (c 4) 0) = false := by cbv

theorem duplicate_occurrences_count_twice :
    check baseline duplicates {0, 1} (.count (c 4) 2) = true ∧
      check baseline duplicates {0, 1} (.count (c 4) 1) = false := by cbv

theorem undetermined_collect_is_rejected : collect baseline unresolvedRows {0} (c 4) ∅ = false := by cbv

theorem determined_collect_retains_occurrences :
    collect baseline duplicates {0, 1} (c 4) {0, 1} = true := by cbv

theorem occurs_check_refuses_cycle : unifyTotal [(x, successor x)] = none := by cbv

theorem false_does_not_mean_refuted_everywhere :
    check baseline duplicates ∅ (.equal x (c 4)) = false ∧
      (Check.equal x (c 4)).Holds (FirstOrder.action signature)
        (Subst.single 0 (c 4)) duplicates ∅ := by
  constructor
  · cbv
  · rfl

def impossible : EquationStore (Term signature) := [(c 0, c 1)]

theorem impossible_information_is_refused : unifyTotal impossible = none := by cbv

theorem impossible_information_entails_every_check (condition : Check (Term signature)) :
    (FirstOrder.action signature).Entails impossible
      (fun assignment => condition.Holds (FirstOrder.action signature) assignment duplicates ∅) := by
  intro assignment solved
  have equality := solved (c 0, c 1) (List.mem_singleton_self _)
  change (Term.const (σ := signature) 0) = Term.const (σ := signature) 1 at equality
  cases equality

/-- The ground-only separation boundary is an existing theorem, not a
restriction of the all-substitution licence. -/
theorem one_ground_value_boundary :
    (Term.var () : Term GroundingSeparationControls.single) ≠ Term.const () ∧
      ∀ grounding : Grounding GroundingSeparationControls.single,
        grounding.groundTerm (.var ()) = grounding.groundTerm (.const ()) :=
  GroundingSeparationControls.variable_and_constant_not_separated

abbrev twoValues := GroundingSeparationControls.pair
def twoRows (b : Bool) : Term twoValues := .const b

/-- Two distinct ground values do not make the exact-count characterization
valid for a different, ground-only quantifier. -/
theorem ground_only_constant_count (grounding : Grounding twoValues) :
    (Check.count (.var ()) 1).Holds (FirstOrder.action twoValues)
      grounding.toSubst twoRows Finset.univ := by
  classical
  cases value : grounding () with
  | const b =>
    cases b <;> simp [Check.Holds, Check.matches, FirstOrder.action, twoRows,
      Grounding.toSubst, Subst.applyTerm, GroundTerm.toTerm, value,
      Finset.filter_insert, Finset.filter_singleton]
  | app symbol arguments => cases symbol

theorem unresolved_substitution_separates_ground_count :
    ¬ (Check.count (.var ()) 1).Holds (FirstOrder.action twoValues)
      (Subst.id twoValues) twoRows Finset.univ := by
  classical
  simp [Check.Holds, Check.matches, FirstOrder.action, twoRows, Subst.applyTerm, Subst.id]

namespace ActualAdmission

open RuleSyntax
open OneFrame (Terms frames ext)

def badRule : Rule (Terms (Term signature)) := ⟨PUnit.unit, ⟨[], [], impossible, [], []⟩, []⟩
def badProgram : Program (Terms (Term signature)) := {badRule}
def emptyState : State (Terms (Term signature)) Nat := ⟨PUnit.unit, [], ∅, fun _ => c 0⟩
def badFiring : Firing Nat (ext (FirstOrder.action signature)) badProgram emptyState.frame :=
  ⟨badRule, rfl, PUnit.unit, baseline, ⟨[], [], []⟩, []⟩

theorem contradictory_tells_refuse_firing :
    ¬ badFiring.Admits (frames (FirstOrder.action signature)) emptyState := by
  apply RuleSyntax.FirstOrderLicence.unsolvable_refuses
  change unifyTotal impossible = none
  exact impossible_information_is_refused

end ActualAdmission

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderLicence.Controls
