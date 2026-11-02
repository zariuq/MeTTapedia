import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LinearConnectionCompleteness

/-!
# One installed rule, two actual fresh uses and one shared solution

The same source schema consumes two different ground inputs at two activation
scopes. Its raw outputs contain the appropriate local variable and the same
captured variable. A scoped solution constructs an actual physical layout,
then a logical proof retaining both original schema/scope receipts.

Reusing one scope forces the two different inputs equal and is rejected.
An absent successful activation or installed schema cannot supply a receipt.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivationControls

open Mettapedia.Logic.LP
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ConditionalComposite
open FirstOrderHornActivations
open LinearConnectionLayout

abbrev base := ScopedSolutionGluing.base
abbrev Source := SourceTerm base Nat Nat
abbrev Opened := OpenedTerm base Nat Nat
abbrev action := FirstOrder.action (base.withVars (ScopedVar Nat ⊕ Nat))

def f {Variables : Type} (term : Term (base.withVars Variables)) : Term (base.withVars Variables) :=
  .app () (fun _ => term)

def schema : RuleInstance Source := ⟨[.var (.inl 0)], [], [], [], [f (.var (.inl 0)), .var (.inr 0)]⟩
def installed : Set (RuleInstance Source) := {schema}
def concreteProgram : Set (RuleInstance Opened) := {rule | ∃ scope, rule = ScopedVariables.ruleAt scope schema}

def pickFirst : Selection Nat := ⟨[0], [], [2, 3]⟩
def pickSecond : Selection Nat := ⟨[1], [], [4, 5]⟩

def selected (firstScope secondScope : Nat) : List (ActivatedHornProofs.Selected (O := Nat) activate installed) :=
  [(origin installed schema (Set.mem_singleton _) firstScope, pickFirst),
   (origin installed schema (Set.mem_singleton _) secondScope, pickSecond)]

def events (firstScope secondScope : Nat) : List (Event Opened Nat) :=
  (selected firstScope secondScope).map (ActivatedHornProofs.ordinary activate installed)

def labelAt (firstScope secondScope : Nat) : Nat → Opened
  | 0 => .const 0
  | 1 => .const 1
  | 2 => f (.var (.inl (ScopedVar.at firstScope 0)))
  | 3 => .var (.inr 0)
  | 4 => f (.var (.inl (ScopedVar.at secondScope 0)))
  | _ => .var (.inr 0)

def before : Configuration Opened Nat := ⟨[], {0, 1, 6}⟩

theorem the_same_schema_is_opened_at_two_scopes :
    (selected 0 1).map (fun event => event.1.schema) = [schema, schema] ∧
      (selected 0 1).map (fun event => event.1.inputs) = [0, 1] := ⟨rfl, rfl⟩

theorem caller_capture_is_shared_in_both_outputs_and_the_residual :
    labelAt 0 1 3 = labelAt 0 1 5 ∧ labelAt 0 1 5 = labelAt 0 1 6 := ⟨rfl, rfl⟩

def groundSchema : RuleInstance Source := ⟨[.const 0], [], [], [], [.const 1]⟩
def groundInstalled : Set (RuleInstance Source) := {groundSchema}

/-- A concrete rule alone cannot recover its actual activation origin. -/
theorem equal_concrete_rules_can_have_distinct_activation_receipts :
    (origin groundInstalled groundSchema (Set.mem_singleton _) 0).rule =
        (origin groundInstalled groundSchema (Set.mem_singleton _) 1).rule ∧
      origin groundInstalled groundSchema (Set.mem_singleton _) 0 ≠
        origin groundInstalled groundSchema (Set.mem_singleton _) 1 := by
  refine ⟨rfl, ?_⟩
  intro same
  have impossible := congrArg ActivatedHornProofs.Origin.inputs same
  change (0 : Nat) = 1 at impossible
  cases impossible

theorem certificate_from_scoped_solution (assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat)))
    (solves : ∀ use : Fin 2, ScopedSolutionGluing.Solves assignment use.val (ScopedSolutionGluing.twoUses use)) :
    Certificate action concreteProgram assignment (labelAt 0 1) before (events 0 1) := by
  refine ⟨?_, ?_, ?_, by decide, by decide, by decide, ?_, action.models_nil assignment, ?_⟩
  · intro event member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨by decide, by decide, rfl, rfl, rfl⟩
    · have same := List.mem_singleton.mp later
      subst event
      exact ⟨by decide, by decide, rfl, rfl, rfl⟩
  · intro event member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨rfl, rfl⟩
    · have same := List.mem_singleton.mp later
      subst event
      exact ⟨rfl, rfl⟩
  · intro event member
    rcases List.mem_cons.mp member with rfl | later
    · exact ⟨0, rfl⟩
    · have same := List.mem_singleton.mp later
      subst event
      exact ⟨1, rfl⟩
  · intro earlier event later decomposition
    have member : event ∈ events 0 1 := by rw [decomposition]; simp
    rcases List.mem_cons.mp member with rfl | second
    · exact Finset.Subset.trans (by decide) Finset.subset_union_left
    · have same := List.mem_singleton.mp second
      subst event
      exact Finset.Subset.trans (by decide) Finset.subset_union_left
  · intro event member equation inConnections
    rcases List.mem_cons.mp member with rfl | later
    · have same : equation = (ScopedVariables.termAt 0 ScopedSolutionGluing.X,
          ScopedVariables.termAt 0 (ScopedSolutionGluing.constant 0)) := by
        simpa [events, selected, origin, ActivatedHornProofs.ordinary, addedEquations,
          ScopedVariables.ruleAt, RuleInstance.map, schema, pickFirst, Selection.equations,
          labelAt, ScopedSolutionGluing.X, ScopedSolutionGluing.constant,
          ScopedVariables.termAt, ScopedVariables.variableAt, Term.renameVars] using inConnections
      subst equation
      exact solves 0 (ScopedSolutionGluing.X, ScopedSolutionGluing.constant 0) (by simp [ScopedSolutionGluing.twoUses])
    · have same := List.mem_singleton.mp later
      subst event
      have sameEquation : equation = (ScopedVariables.termAt 1 ScopedSolutionGluing.X,
          ScopedVariables.termAt 1 (ScopedSolutionGluing.constant 1)) := by
        simpa [events, selected, origin, ActivatedHornProofs.ordinary, addedEquations,
          ScopedVariables.ruleAt, RuleInstance.map, schema, pickSecond, Selection.equations,
          labelAt, ScopedSolutionGluing.X, ScopedSolutionGluing.constant,
          ScopedVariables.termAt, ScopedVariables.variableAt, Term.renameVars] using inConnections
      subst equation
      exact solves 1 (ScopedSolutionGluing.X, ScopedSolutionGluing.constant 1) (by simp [ScopedSolutionGluing.twoUses])

/-- The existing gluing witness runs through the real CMR and logical proof
owners. The proof records two uses of the same installed schema at scopes 0
and 1, with one assignment for the complete final constraints and frame. -/
theorem one_schema_has_two_actual_fresh_logical_uses :
    ∃ assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat)),
      ∃ proof : ActivatedHornProofs.Proof action activate installed assignment
          (labels (PositiveResourceProjection.realized action assignment (labelAt 0 1)) before.present)
          (labels (PositiveResourceProjection.realized action assignment (labelAt 0 1))
            (ConditionalSchedule.follow (labelAt 0 1) before (events 0 1)).present),
        proof.uses.map (fun entry => (ActivatedHornProofs.originOf action activate installed assignment entry).inputs) = [0, 1] := by
  classical
  obtain ⟨assignment, solves⟩ := ScopedSolutionGluing.distinct_scopes_glue
  have layout := certificate_from_scoped_solution assignment solves
  have run := layout.executes
  obtain ⟨proof, origins⟩ := ActivatedHornProofs.proof_of_schedule action activate installed assignment
    (labelAt 0 1) rfl (selected 0 1) before run.1 layout.pure run.2
  refine ⟨assignment, proof, ?_⟩
  have scopes := congrArg (List.map fun actual : ActivatedHornProofs.Origin activate installed => actual.inputs) origins
  simp only [List.map_map, selected, List.map_cons, List.map_nil, origin] at scopes
  simp only [Function.comp_def] at scopes
  exact scopes

theorem the_actual_fresh_uses_keep_the_complete_physical_boundary
    (assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat)))
    (solves : ∀ use : Fin 2, ScopedSolutionGluing.Solves assignment use.val (ScopedSolutionGluing.twoUses use)) :
    (ConditionalSchedule.follow (labelAt 0 1) before (events 0 1)).present = {2, 3, 4, 5, 6} := by
  rw [(certificate_from_scoped_solution assignment solves).final_rows]
  decide

theorem reusing_one_scope_cannot_match_the_two_inputs
    (assignment : Subst (base.withVars (ScopedVar Nat ⊕ Nat))) :
    ¬ Certificate action concreteProgram assignment (labelAt 7 7) before (events 7 7) := by
  intro layout
  have zero : assignment.applyTerm (.var (.inl (ScopedVar.at 7 0))) = .const 0 := by
    have solved := layout.connections (ScopedVariables.ruleAt 7 schema, pickFirst) (List.mem_cons_self ..)
    change action.Solves assignment (.var (.inl (ScopedVar.at 7 0)), .const 0)
    exact solved _ (by simp [addedEquations, ScopedVariables.ruleAt, RuleInstance.map, schema, pickFirst,
      Selection.equations, labelAt, ScopedVariables.termAt, ScopedVariables.variableAt, Term.renameVars])
  have one : assignment.applyTerm (.var (.inl (ScopedVar.at 7 0))) = .const 1 := by
    have solved := layout.connections (ScopedVariables.ruleAt 7 schema, pickSecond)
      (List.mem_cons_of_mem _ (List.mem_singleton_self _))
    change action.Solves assignment (.var (.inl (ScopedVar.at 7 0)), .const 1)
    exact solved _ (by simp [addedEquations, ScopedVariables.ruleAt, RuleInstance.map, schema, pickSecond,
      Selection.equations, labelAt, ScopedVariables.termAt, ScopedVariables.variableAt, Term.renameVars])
  have impossible : (Term.const (σ := base.withVars (ScopedVar Nat ⊕ Nat)) 0) = .const 1 := zero.symm.trans one
  cases impossible

theorem a_failed_activation_has_no_origin
    (installedSchemas : Set (RuleInstance Source)) :
    ¬ Nonempty (ActivatedHornProofs.Origin (fun (_ : RuleInstance Source) (_ : Nat) =>
      (none : Option (RuleInstance Opened))) installedSchemas) := by
  rintro ⟨actual⟩
  cases actual.computed

theorem an_uninstalled_schema_has_no_origin :
    ¬ Nonempty (ActivatedHornProofs.Origin (activate (signature := base) (Local := Nat) (Shared := Nat))
      (∅ : Set (RuleInstance Source))) := by
  rintro ⟨actual⟩
  exact actual.member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivationControls
