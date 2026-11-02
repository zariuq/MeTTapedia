import Mettapedia.Languages.CHR.Refinement

/-! Ground source controls for occurrences, propagation history, refined
head order, literal identity and Prolog integer arithmetic. These do not
substitute for the source-to-native controller correspondence. -/

set_option autoImplicit false

namespace Mettapedia.Languages.CHR.Controls

def signal : Head := ⟨"signal", [.var 0]⟩
def published : Head := ⟨"published", [.var 0]⟩
def publishRule : Rule := ⟨"publish", [signal], [], [], [.tell published]⟩
def program : Program := ⟨[⟨"signal", 1⟩, ⟨"published", 1⟩], [publishRule]⟩

def environment : Environment := [(0, .integer 7)]
def constraint : Constraint := ⟨"signal", [.integer 7]⟩
def first : Occurrence := ⟨0, constraint⟩
def second : Occurrence := ⟨1, constraint⟩
def state : State := ⟨[.scan 0 0], [first], [], 1, .running⟩
def selection : Selection := ⟨[first], [], []⟩
def committed : State := commit state publishRule 0 environment selection 0 0 []

theorem selected : selection.Matches publishRule environment state.store := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.Perm.refl _
  · decide +kernel
  · exact .cons (by simp [Head.instantiate, Term.instantiate, lookup, environment, signal, first, constraint]) .nil
  · exact .nil
  · decide +kernel
  · intro binding member
    have same : binding = (0, Value.integer 7) := List.mem_singleton.mp member
    subst binding
    simp [Rule.variables, Rule.heads, Head.variables, Term.variables, publishRule, signal]

theorem publish_step : Step program state committed := by
  apply Step.fire state 0 0 [] ⟨0, 0⟩ publishRule environment selection
  · rfl
  · rfl
  · decide +kernel
  · rfl
  · exact selected
  · exact ⟨first, rfl, rfl⟩
  · intro _
    exact List.not_mem_nil
  · rfl

theorem same_occurrences_cannot_publish_twice : ¬ selection.Fresh publishRule 0 committed.history :=
  propagation_cannot_replay state publishRule 0 environment selection 0 0 [] rfl

theorem equal_new_constraint_has_different_key :
    selection.key 0 ≠ (Selection.mk [second] [] []).key 0 := by
  decide +kernel

theorem new_equal_occurrence_is_fresh : (Selection.mk [second] [] []).Fresh publishRule 0 committed.history := by
  intro _
  decide +kernel

theorem one_occurrence_cannot_fill_two_heads :
    ¬ (Selection.mk [first] [first] []).Matches
      ⟨"consume", [signal], [signal], [], []⟩ environment [first] := by
  intro matched
  have unique := matched.2.1
  change List.Pairwise (fun first second : Nat => first ≠ second) [0, 0] at unique
  simp at unique

theorem duplicate_cleanup_visits_removed_first :
    occurrences ⟨[⟨"signal", 1⟩], [Rule.mk "dedup" [signal] [signal] [] []]⟩ = [⟨0, 1⟩, ⟨0, 0⟩] := by
  decide +kernel

theorem body_precedes_parked_active :
    committed.tasks = [.goals environment [.tell published], .scan 0 0] := by
  simp [committed, commit, selection, publishRule]

theorem empty_environment_is_not_identical_evidence :
    (Guard.identical (.var 0) (.var 1)).eval [] = .error (.uninstantiated (.var 0)) := by
  simp [Guard.eval, Term.instantiate, lookup]

theorem signed_arithmetic :
    IntOperator.quotient.eval (-7) 3 = .ok (-2) ∧
    IntOperator.remainder.eval (-7) 3 = .ok (-1) ∧
    IntOperator.modulo.eval (-7) 3 = .ok 2 ∧
    IntOperator.modulo.eval 7 (-3) = .ok (-2) ∧
    IntOperator.modulo.eval (-7) (-3) = .ok (-1) := by decide +kernel

theorem division_by_zero_is_a_fault :
    IntOperator.modulo.eval 1 0 = .error .divisionByZero := by decide +kernel

#print axioms publish_step
#print axioms one_occurrence_cannot_fill_two_heads
#print axioms signed_arithmetic

end Mettapedia.Languages.CHR.Controls
