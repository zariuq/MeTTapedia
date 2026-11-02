import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.GuardCutFamilies
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConjunctiveControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFamilies

/-!
# One schematic row at two instances cannot have one fixed ordinary label

The positive side uses the existing scoped row/query semantics. The negative
side uses the original ordinary selection problem and the exact common-model
field of the guarded cut-family profile. This is a separator, not a new step
semantics or a contextual extension of that profile.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReadCutSeparation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveControls
  (queries locals captures Pattern p patternA patternB independentPatterns schemaRows)

abbrev ordinaryAction := ContextualFamilies.action (ContextualConjunctiveQueries.queryFamily queries captures) [] ()

def readRule : RuleInstance Pattern := ⟨[], independentPatterns, [], [], []⟩
def selection : Selection Nat := ⟨[], [7, 7], []⟩
def before : Configuration Pattern Nat := ⟨[], {7}⟩
def label (row : Pattern) : Nat → Pattern := fun _ => row

theorem fixed_problem (row : Pattern) : selection.problem (label row) readRule before =
    [(p patternA, row), (p patternB, row)] := rfl

theorem the_two_ground_patterns_are_distinct : p patternA ≠ p patternB := by
  intro same
  have arguments := eq_of_heq (Term.op.inj same).2
  have first := (Args.cons.inj arguments).1
  have sizes := congrArg termSize first
  change 1 = 3 at sizes
  omega

theorem no_fixed_ordinary_label_can_supply_both_reads (row : Pattern) :
    ¬ ordinaryAction.Consistent (selection.problem (label row) readRule before) := by
  rintro ⟨candidate, solved⟩
  rw [fixed_problem] at solved
  have first := solved (p patternA, row) (by simp)
  have second := solved (p patternB, row) (by simp)
  change instantiate candidate (p patternA) = instantiate candidate row at first
  change instantiate candidate (p patternB) = instantiate candidate row at second
  have firstFixed : instantiate candidate (p patternA) = p patternA := by rfl
  have secondFixed : instantiate candidate (p patternB) = p patternB := by rfl
  rw [firstFixed] at first
  rw [secondFixed] at second
  exact the_two_ground_patterns_are_distinct (first.trans second.symm)

theorem the_original_ordinary_selection_is_invalid (row : Pattern) :
    ¬ selection.Valid ordinaryAction (label row) readRule before :=
  fun valid => no_fixed_ordinary_label_can_supply_both_reads row valid.consistent

theorem no_fixed_label_guard_cut_conditions (row : Pattern)
    (candidate : Assignment (ContextualConjunctiveQueries.queryFamily queries captures)
      (ContextualConjunctiveQueries.queryFamily queries captures)) :
    ¬ GuardCutSequentialization.Conditions ordinaryAction candidate (label row) before
      (fun _ : Fin 1 => (readRule, selection)) := by
  intro conditions
  exact no_fixed_ordinary_label_can_supply_both_reads row ⟨candidate, conditions.connections 0⟩

/-- One physical row remains one physical row, while its two private uses
instantiate independently under the existing contextual query semantics. -/
theorem fresh_per_use_schema_succeeds_while_every_fixed_label_fails :
    ContextualConjunctiveQueries.Matches queries locals captures (generator captures)
      independentPatterns schemaRows (fun _ => 7) ∧
      (∀ row : Pattern, ¬ selection.Valid ordinaryAction (label row) readRule before) :=
  ⟨ContextualConjunctiveControls.one_schema_row_may_be_read_at_two_independent_instances,
    the_original_ordinary_selection_is_invalid⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualReadCutSeparation
