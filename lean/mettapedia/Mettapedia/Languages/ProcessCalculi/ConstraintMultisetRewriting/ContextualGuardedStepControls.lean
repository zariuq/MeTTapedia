import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardConsumption

/-!
# Actual guarded firings retain conditions beyond a closed output

A reflexive guard is admitted. A capture-equality guard cannot manufacture
the binding it asks for, even when the output no longer mentions the capture.
The same guard fires when the incoming equation store already supplies that
binding. A schema-count guard uses its all-future local-instantiation ask.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep.Controls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Logic.LP (ScopedVar)
open ContextualActivatedStep
open ContextualGuardMatching
open ContextualGuardSemantics
open ContextualSelectionViews.Controls (base locals captures raw active RawTerm ActiveTerm atom pair p
  rawA rawB privateVariable universalRow sharedValue)

abbrev CapturedTerm := Term (signature base captures) [] ()
abbrev A := ContextualFamilies.action active [] ()
def occupied : Finset Nat := {0, 2, 7}
def selection : Selection Nat := ⟨[], [], [99]⟩
def rows (_ : Nat) : ContextualStoredRows.Row locals captures [] () := .schema universalRow
def bare : Configuration CapturedTerm Nat := ⟨[], {7}⟩
def bound : Configuration CapturedTerm Nat := ⟨[(sharedValue, atom captures)], {7}⟩
def outputs (_ : Nat) : ActiveTerm := atom active

def trueRule : RuleInstance RawTerm := ⟨[], [], [], [.equal rawA rawA], [rawA]⟩
def equalityRule : RuleInstance RawTerm :=
  ⟨[], [], [], [.equal (generator raw (.inr 0)) rawA], [rawA]⟩
def countRule : RuleInstance RawTerm := ⟨[], [], [], [.count (p rawA) 1], [rawA]⟩

def activeA : Assignment active active
  | .inl _ => atom active
  | .inr _ => atom active

theorem a_true_nonempty_guard_has_an_actual_firing :
    Valid locals captures occupied selection trueRule rows bare outputs := by
  refine { take_distinct := by decide
           output_distinct := by decide
           take_length := rfl
           read_length := rfl
           outputs := rfl
           occurrences := by decide
           solvable := ?_
           checks := ?_ }
  swap
  · exact ContextualFrameUnifier.solvable_of_consistent ⟨generator active, A.models_nil _⟩
  · intro check member
    have only : check = .equal (atom active) (atom active) := List.mem_singleton.mp member
    subst check
    exact Ask.equal_refl locals _ _ _ _

theorem guards_do_not_add_the_equations_they_ask_for :
    problem locals captures occupied selection equalityRule rows bare = [] := rfl

theorem an_unjustified_equality_guard_refuses_even_with_a_closed_output :
    ¬ Valid locals captures occupied selection equalityRule rows bare outputs := by
  intro valid
  have ask := valid.checks (.equal (generator active (.inr 0)) (atom active)) (List.mem_singleton_self _)
  have same := ask (ScopedVar Nat ⊕ Nat) active (generator active)
    (fun _ member => False.elim (List.not_mem_nil member))
  change generator active (.inr 0) = atom active at same
  have heads := (Term.op.inj same).1
  cases heads

theorem the_incoming_binding_remains_in_the_problem :
    problem locals captures occupied selection equalityRule rows bound =
      [(generator active (.inr 0), atom active)] := by with_unfolding_all rfl

theorem an_existing_binding_justifies_the_same_guard :
    Valid locals captures occupied selection equalityRule rows bound outputs := by
  refine { take_distinct := by decide
           output_distinct := by decide
           take_length := rfl
           read_length := rfl
           outputs := rfl
           occurrences := by decide
           solvable := ?_
           checks := ?_ }
  swap
  · apply ContextualFrameUnifier.solvable_of_consistent
    refine ⟨activeA, ?_⟩
    change A.Models activeA [(generator active (.inr 0), atom active)]
    exact (A.models_cons activeA _ _).mpr ⟨by with_unfolding_all rfl, A.models_nil _⟩
  · intro check member
    have only : check = .equal (generator active (.inr 0)) (atom active) := List.mem_singleton.mp member
    subst check
    exact Ask.equal_of_mem locals _ _ _ _ _ (List.mem_singleton_self _)

theorem the_justified_guard_emits_its_closed_result :
    Step locals captures occupied equalityRule rows bound outputs
      (result locals captures occupied selection equalityRule rows bound)
      (resultRows locals captures selection outputs rows)
      (ContextualActivationScopes.after occupied selection) :=
  ⟨selection, (valid_iff_factors locals captures _ _ _ _ _ _).mp
    an_existing_binding_justifies_the_same_guard, rfl, rfl, rfl⟩

theorem the_condition_is_retained_although_its_variable_is_absent_from_output :
    (prepared locals captures occupied selection equalityRule rows).rule.checks =
        [.equal (generator active (.inr 0)) (atom active)] ∧
      (prepared locals captures occupied selection equalityRule rows).rule.produce = [atom active] := by
  constructor <;> with_unfolding_all rfl

theorem the_schematic_count_guard_asks_over_every_future_model :
    Ask locals (problem locals captures occupied selection countRule rows bare)
      (guardRows locals captures rows) bare.present (.count (p (atom active)) 1) := by
  intro Next next candidate _
  have matched : Matches locals candidate (instantiate candidate (p (atom active)))
      ((guardRows locals captures rows) 7) := by
    let extension := Extension.withLocals locals next
    let localBodies : Assignment locals extension.declarations := fun _ => atom extension.declarations
    refine ⟨extension, localBodies, ?_⟩
    with_unfolding_all rfl
  exact (congrArg Finset.card
    (region_singleton locals candidate (guardRows locals captures rows) (p (atom active)) 7 matched)).trans
    (by decide : ({7} : Finset Nat).card = 1)

theorem the_schematic_count_guard_has_an_actual_firing :
    Valid locals captures occupied selection countRule rows bare outputs := by
  refine { take_distinct := by decide
           output_distinct := by decide
           take_length := rfl
           read_length := rfl
           outputs := rfl
           occurrences := by decide
           solvable := ?_
           checks := ?_ }
  swap
  · exact ContextualFrameUnifier.solvable_of_consistent ⟨generator active, A.models_nil _⟩
  · intro check member
    have only : check = .count (p (atom active)) 1 := List.mem_singleton.mp member
    subst check
    exact the_schematic_count_guard_asks_over_every_future_model

def takeRule : RuleInstance RawTerm := ⟨[p rawA], [], [], [], []⟩
def takeSelection : Selection Nat := ⟨[7], [], []⟩
def takeProblem := problem locals captures occupied takeSelection takeRule rows bare
def takeAfter := result locals captures occupied takeSelection takeRule rows bare
def takeAfterRows := resultRows locals captures takeSelection outputs rows
def takeScope := ContextualActivationScopes.scopeAt occupied
  (ContextualActivationScopes.takePort takeSelection ⟨0, by decide⟩)

theorem the_actual_take_problem_retains_its_selected_equation :
    (p (atom active), ContextualFreshening.termAt locals captures takeScope
      (ContextualStoredRows.asTemplate locals captures (rows 7))) ∈ takeProblem :=
  List.mem_singleton_self _

theorem the_matching_schema_is_consumed_by_an_actual_firing :
    Valid locals captures occupied takeSelection takeRule rows bare outputs := by
  refine { take_distinct := by decide
           output_distinct := by decide
           take_length := rfl
           read_length := rfl
           outputs := rfl
           occurrences := by decide
           solvable := ?_
           checks := ?_ }
  swap
  · apply ContextualFrameUnifier.solvable_of_consistent
    refine ⟨activeA, ?_⟩
    change A.Models activeA
      [(p (atom active), p (generator active (.inl (ScopedVar.at 9 0))))]
    exact (A.models_cons activeA _ _).mpr ⟨by with_unfolding_all rfl, A.models_nil _⟩
  · intro check member
    exact False.elim (List.not_mem_nil member)

theorem the_guard_after_that_consumption_is_exactly_its_prior_count_condition :
    Ask locals takeProblem takeAfterRows takeAfter.present (.absent (p (atom active))) ↔
      Ask locals takeProblem (guardRows locals captures rows) bare.present (.count (p (atom active)) 1) := by
  have transported := ContextualGuardConsumption.ask_after_erase_iff_exact_count locals captures
    takeProblem rows bare.present (p (atom active)) 7 takeScope (by decide)
    the_actual_take_problem_retains_its_selected_equation
  exact transported

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep.Controls
