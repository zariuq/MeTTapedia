import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedTensorProofs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Controls

/-!
# Unordered connection controls over actual physical CMR selections

Independent occurrences can execute in either order, including two uses of
an equal raw rule. A backwards-listed chain is genuinely sorted before it
runs. Missing suppliers, nonexclusive consumers, a self-cycle and a two-event
cycle are distinguished; graph ordering alone never manufactures resources.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedConnectionControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConstraintMultisetRewriting.Controls
open ConditionalComposite
open UnorderedOccurrenceConnections

def stepRule (input output : Nat) : RuleInstance (Term signature) :=
  ⟨[.const input], [], [], [], [.const output]⟩

def independent (index : Fin 2) : LinearConnectionLayout.Event (Term signature) Nat :=
  if index.val = 0 then (stepRule 0 1, ⟨[0], [], [2]⟩) else (stepRule 0 1, ⟨[1], [], [3]⟩)

def independentLabel (occurrence : Nat) : Term signature := if occurrence < 2 then .const 0 else .const 1
def independentBefore : Configuration (Term signature) Nat := ⟨[], {0, 1}⟩
def independentProgram : Set (RuleInstance (Term signature)) := {stepRule 0 1}

theorem independent_conditions :
    Conditions A independentProgram (Subst.id signature) independentLabel independentBefore independent := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_, A.models_nil _, ?_⟩
  · intro index
    fin_cases index <;> exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · intro index
    fin_cases index <;> exact ⟨rfl, rfl⟩
  · intro index
    fin_cases index <;> exact Set.mem_singleton _
  · intro index occurrence consumed
    fin_cases index
    · have same : occurrence = 0 := by simpa [independent] using consumed
      subst occurrence
      exact Or.inl (by decide)
    · have same : occurrence = 1 := by simpa [independent] using consumed
      subst occurrence
      exact Or.inl (by decide)
  · intro index equation member
    fin_cases index <;>
      have same : equation = (Term.const (σ := signature) 0, .const 0) := by
        simpa [independent, stepRule, addedEquations, Selection.equations, independentLabel] using member
    all_goals subst equation; rfl

theorem independent_order_is_computed : order? independent = some [0, 1] := by decide

theorem equal_rules_remain_separate_event_occurrences :
    (independent 0).1 = (independent 1).1 ∧ (0 : Fin 2) ≠ 1 ∧ (roster independent).length = 2 :=
  ⟨rfl, by decide, rfl⟩

theorem independent_occurrences_execute_in_both_orders :
    ConditionalSchedule.Executable A independentLabel independentBefore ([0, 1].map independent) ∧
      ConditionalSchedule.Executable A independentLabel independentBefore ([1, 0].map independent) := by
  have first := order?_spec independent independent_order_is_computed
  have reverseRespects : (catalogue independent).Respects [1, 0] := ⟨by decide, by decide, by decide⟩
  have reverseCovers : ∀ index : Fin 2, index ∈ ([1, 0] : List (Fin 2)) := by intro index; fin_cases index <;> decide
  exact ⟨(independent_conditions.executes_enumeration first.1 first.2).1,
    (independent_conditions.executes_enumeration reverseRespects reverseCovers).1⟩

theorem independent_exact_residual_is_two_distinct_equal_valued_outputs :
    (ConditionalSchedule.follow independentLabel independentBefore ([0, 1].map independent)).present = {2, 3} := by
  have spec := order?_spec independent independent_order_is_computed
  have result := (independent_conditions.executes_enumeration spec.1 spec.2).2.2
  exact result.trans (by decide)

def chain (index : Fin 2) : LinearConnectionLayout.Event (Term signature) Nat :=
  if index.val = 0 then (stepRule 1 2, ⟨[2], [], [3]⟩) else (stepRule 0 1, ⟨[0], [], [2]⟩)

def chainLabel : Nat → Term signature
  | 0 => .const 0
  | 2 => .const 1
  | _ => .const 2

def chainBefore : Configuration (Term signature) Nat := ⟨[], {0}⟩
def chainProgram : Set (RuleInstance (Term signature)) := {stepRule 1 2, stepRule 0 1}

theorem chain_conditions : Conditions A chainProgram (Subst.id signature) chainLabel chainBefore chain := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_, A.models_nil _, ?_⟩
  · intro index
    fin_cases index <;> exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · intro index
    fin_cases index <;> exact ⟨rfl, rfl⟩
  · intro index
    fin_cases index
    · exact Or.inl rfl
    · exact Or.inr (Set.mem_singleton _)
  · intro index occurrence consumed
    fin_cases index
    · have same : occurrence = 2 := by simpa [chain] using consumed
      subst occurrence
      exact Or.inr ⟨1, by decide⟩
    · have same : occurrence = 0 := by simpa [chain] using consumed
      subst occurrence
      exact Or.inl (by decide)
  · intro index equation member
    fin_cases index
    · have same : equation = (Term.const (σ := signature) 1, .const 1) := by
        simpa [chain, stepRule, addedEquations, Selection.equations, chainLabel] using member
      subst equation
      rfl
    · have same : equation = (Term.const (σ := signature) 0, .const 0) := by
        simpa [chain, stepRule, addedEquations, Selection.equations, chainLabel] using member
      subst equation
      rfl

theorem the_backwards_listed_chain_is_actually_sorted : order? chain = some [1, 0] := by decide

theorem the_original_roster_cannot_execute : ¬ ConditionalSchedule.Executable A chainLabel chainBefore (roster chain) := by
  intro executes
  have absent : 2 ∉ chainBefore.present := by decide
  exact absent (executes.1.occurrences.taken_subset (by decide))

theorem the_computed_chain_executes_and_retains_the_correct_boundary :
    ConditionalSchedule.Executable A chainLabel chainBefore ([1, 0].map chain) ∧
      (ConditionalSchedule.follow chainLabel chainBefore ([1, 0].map chain)).present = {3} := by
  have spec := order?_spec chain the_backwards_listed_chain_is_actually_sorted
  have result := chain_conditions.executes_enumeration spec.1 spec.2
  exact ⟨result.1, result.2.2.trans (by decide)⟩

def missing (_ : Fin 1) : LinearConnectionLayout.Event (Term signature) Nat := (stepRule 0 1, ⟨[7], [], [8]⟩)
def emptyBefore : Configuration (Term signature) Nat := ⟨[], ∅⟩
def missingLabel (identity : Nat) : Term signature := if identity = 7 then .const 0 else .const 1
def groundLabel (identity : Nat) : Term signature := .const identity

theorem missing_supplier_has_no_graph_cycle : order? missing = some [0] := by decide

theorem missing_supplier_ports_are_otherwise_formed_and_solved :
    (ShapeTest.ofSelection (missing 0).1 (missing 0).2).Holds missingLabel ∧
      A.Models (Subst.id signature) (addedEquations missingLabel (missing 0).1 (missing 0).2) := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl⟩, ?_⟩
  intro equation member
  have same : equation = (Term.const (σ := signature) 0, .const 0) := by
    simpa [missing, stepRule, addedEquations, Selection.equations, missingLabel] using member
  subst equation
  rfl

theorem topological_success_does_not_invent_a_missing_supplier
    (program : Set (RuleInstance (Term signature))) (assignment : Subst signature) :
    ¬ Certificate A program assignment missingLabel emptyBefore missing := by
  intro certificate
  have funded := certificate.conditions.funded 0 7 (by decide)
  rcases funded with initial | ⟨producer, made⟩
  · exact (by decide : 7 ∉ emptyBefore.present) initial
  · fin_cases producer
    exact (by decide : 7 ∉ (missing 0).2.made) made

def conflictingConsumers (index : Fin 2) : LinearConnectionLayout.Event (Term signature) Nat :=
  if index.val = 0 then (stepRule 0 1, ⟨[0], [], [2]⟩) else (stepRule 0 1, ⟨[0], [], [3]⟩)

theorem nonexclusive_consumers_are_not_just_an_ordering_problem :
    order? conflictingConsumers = some [0, 1] ∧
      ∀ program assignment, ¬ Certificate A program assignment independentLabel ⟨[], {0}⟩ conflictingConsumers := by
  refine ⟨by decide, ?_⟩
  intro program assignment certificate
  have distinct := certificate.conditions.consumed_distinct
  exact (by decide : ¬ ([0, 0] : List Nat).Nodup) distinct

def selfCycle (_ : Fin 1) : LinearConnectionLayout.Event (Term signature) Nat := (stepRule 0 0, ⟨[0], [], [0]⟩)

theorem self_cycle_has_an_independent_closed_path : Relation.TransGen (Edge selfCycle) 0 0 := .single (by decide)
theorem self_cycle_is_refused : order? selfCycle = none := by decide

def twoCycle (index : Fin 2) : LinearConnectionLayout.Event (Term signature) Nat :=
  if index.val = 0 then (stepRule 1 0, ⟨[1], [], [0]⟩) else (stepRule 0 1, ⟨[0], [], [1]⟩)

theorem two_cycle_has_an_independent_closed_path : Relation.TransGen (Edge twoCycle) 0 0 :=
  Relation.TransGen.tail (Relation.TransGen.single (by decide : Edge twoCycle 0 1)) (by decide : Edge twoCycle 1 0)

theorem two_cycle_is_refused : order? twoCycle = none := by decide

theorem self_cycle_has_all_unordered_port_conditions :
    Conditions A Set.univ (Subst.id signature) groundLabel emptyBefore selfCycle := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_, A.models_nil _, ?_⟩
  · intro index
    fin_cases index
    exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · intro _
    exact ⟨rfl, rfl⟩
  · intro _
    exact Set.mem_univ _
  · intro _ occurrence consumed
    have same : occurrence = 0 := by simpa [selfCycle] using consumed
    subst occurrence
    exact Or.inr ⟨0, by decide⟩
  · intro _ equation member
    have same : equation = (Term.const (σ := signature) 0, .const 0) := by
      simpa [selfCycle, stepRule, addedEquations, Selection.equations, groundLabel] using member
    subst equation
    rfl

theorem two_cycle_has_all_unordered_port_conditions :
    Conditions A Set.univ (Subst.id signature) groundLabel emptyBefore twoCycle := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_, A.models_nil _, ?_⟩
  · intro index
    fin_cases index <;> exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · intro index
    fin_cases index <;> exact ⟨rfl, rfl⟩
  · intro _
    exact Set.mem_univ _
  · intro index occurrence consumed
    fin_cases index
    · have same : occurrence = 1 := by simpa [twoCycle] using consumed
      subst occurrence
      exact Or.inr ⟨1, by decide⟩
    · have same : occurrence = 0 := by simpa [twoCycle] using consumed
      subst occurrence
      exact Or.inr ⟨0, by decide⟩
  · intro index equation member
    fin_cases index
    · have same : equation = (Term.const (σ := signature) 1, .const 1) := by
        simpa [twoCycle, stepRule, addedEquations, Selection.equations, groundLabel] using member
      subst equation
      rfl
    · have same : equation = (Term.const (σ := signature) 0, .const 0) := by
        simpa [twoCycle, stepRule, addedEquations, Selection.equations, groundLabel] using member
      subst equation
      rfl

theorem neither_cycle_has_any_actual_indexed_execution :
    (¬ ∃ order : List (Fin 1), order.Perm (List.finRange 1) ∧
      ConditionalSchedule.Executable A groundLabel emptyBefore (order.map selfCycle)) ∧
      ¬ ∃ order : List (Fin 2), order.Perm (List.finRange 2) ∧
        ConditionalSchedule.Executable A groundLabel emptyBefore (order.map twoCycle) :=
  ⟨fun execution => (self_cycle_has_all_unordered_port_conditions.acyclic_iff_executable_enumeration.mpr execution)
      0 self_cycle_has_an_independent_closed_path,
    fun execution => (two_cycle_has_all_unordered_port_conditions.acyclic_iff_executable_enumeration.mpr execution)
      0 two_cycle_has_an_independent_closed_path⟩

theorem neither_closed_cycle_has_a_source_certificate
    (program : Set (RuleInstance (Term signature))) (assignment : Subst signature) :
    (¬ Certificate A program assignment groundLabel emptyBefore selfCycle) ∧
      ¬ Certificate A program assignment groundLabel emptyBefore twoCycle :=
  ⟨fun certificate => certificate.acyclic 0 self_cycle_has_an_independent_closed_path,
    fun certificate => certificate.acyclic 0 two_cycle_has_an_independent_closed_path⟩

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnorderedConnectionControls
