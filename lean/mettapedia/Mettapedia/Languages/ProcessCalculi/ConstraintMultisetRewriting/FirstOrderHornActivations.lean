import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ActivatedHornProofs
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ScopedSolutionGluing
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrder

/-!
# Per-use first-order rule activation and actual connection equations

The existing `ScopedVariables.ruleAt` is the activation function. Installed
schema and activation scope remain in every logical-use receipt. For shared
stored rows whose labels are unchanged by local freshening, the actual
activated port equations are exactly the source port equations renamed once
into the use's scope. The existing scoped-solution gluing theorem therefore
applies to those actual activation obligations.

This is first-order rule activation over shared rows. Independently opened
stored-schema views, contextual binders, scope allocation and publication
authority are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivations

open Mettapedia.Logic.LP
open ConditionalComposite

variable {signature : LPSignature} {Local Shared O : Type}

abbrev SourceTerm (signature : LPSignature) (Local Shared : Type) :=
  Term (signature.withVars (Local ⊕ Shared))

abbrev OpenedTerm (signature : LPSignature) (Local Shared : Type) :=
  Term (signature.withVars (ScopedVar Local ⊕ Shared))

def activate (schema : RuleInstance (SourceTerm signature Local Shared)) (scope : Nat) :
    Option (RuleInstance (OpenedTerm signature Local Shared)) :=
  some (ScopedVariables.ruleAt scope schema)

def origin (installed : Set (RuleInstance (SourceTerm signature Local Shared)))
    (schema : RuleInstance (SourceTerm signature Local Shared)) (member : schema ∈ installed) (scope : Nat) :
    ActivatedHornProofs.Origin activate installed :=
  ⟨schema, member, scope, ScopedVariables.ruleAt scope schema, rfl⟩

theorem computed_rule (installed : Set (RuleInstance (SourceTerm signature Local Shared)))
    (actual : ActivatedHornProofs.Origin activate installed) :
    actual.rule = ScopedVariables.ruleAt actual.inputs actual.schema :=
  (Option.some.inj actual.computed).symm

/-- Shared labels do not open new local variables on each use. This explicit
condition excludes stored schemas, which have a different per-port view. -/
def SharedLabels (sourceLabel : O → SourceTerm signature Local Shared)
    (openedLabel : O → OpenedTerm signature Local Shared) (scope : Nat) (selected : List O) : Prop :=
  ∀ occurrence ∈ selected, ScopedVariables.termAt scope (sourceLabel occurrence) = openedLabel occurrence

theorem rename_port_equations (sourceLabel : O → SourceTerm signature Local Shared)
    (openedLabel : O → OpenedTerm signature Local Shared)
    (scope : Nat) : ∀ (patterns : List (SourceTerm signature Local Shared)) (selected : List O),
      SharedLabels sourceLabel openedLabel scope selected →
      (Selection.equations sourceLabel patterns selected).map
          (fun pair => (ScopedVariables.termAt scope pair.1, ScopedVariables.termAt scope pair.2)) =
        Selection.equations openedLabel (patterns.map (ScopedVariables.termAt scope)) selected
  | [], _, _ => rfl
  | _ :: _, [], _ => rfl
  | pattern :: patterns, occurrence :: selected, isShared => by
      simp only [Selection.equations, List.zipWith_cons_cons, List.map_cons]
      rw [isShared occurrence (List.mem_cons_self ..)]
      exact congrArg (List.cons _) (rename_port_equations sourceLabel openedLabel scope patterns selected
        (fun item member => isShared item (List.mem_cons_of_mem _ member)))

theorem rename_connection_equations (sourceLabel : O → SourceTerm signature Local Shared)
    (openedLabel : O → OpenedTerm signature Local Shared)
    (scope : Nat) (schema : RuleInstance (SourceTerm signature Local Shared)) (selected : Selection O)
    (isShared : SharedLabels sourceLabel openedLabel scope (selected.taken ++ selected.read)) :
    (addedEquations sourceLabel schema selected).map
        (fun pair => (ScopedVariables.termAt scope pair.1, ScopedVariables.termAt scope pair.2)) =
      addedEquations openedLabel (ScopedVariables.ruleAt scope schema) selected := by
  simp only [addedEquations, List.map_append, ScopedVariables.ruleAt, RuleInstance.map]
  rw [rename_port_equations sourceLabel openedLabel scope _ _
      (fun item member => isShared item (List.mem_append_left _ member)),
    rename_port_equations sourceLabel openedLabel scope _ _
      (fun item member => isShared item (List.mem_append_right _ member))]

theorem models_actual_connections_iff (sourceLabel : O → SourceTerm signature Local Shared)
    (openedLabel : O → OpenedTerm signature Local Shared)
    (scope : Nat) (schema : RuleInstance (SourceTerm signature Local Shared)) (selected : Selection O)
    (isShared : SharedLabels sourceLabel openedLabel scope (selected.taken ++ selected.read))
    (assignment : Subst (signature.withVars (ScopedVar Local ⊕ Shared))) :
    (FirstOrder.action (signature.withVars (ScopedVar Local ⊕ Shared))).Models assignment
        (addedEquations openedLabel (ScopedVariables.ruleAt scope schema) selected) ↔
      ScopedSolutionGluing.Solves assignment scope (addedEquations sourceLabel schema selected) := by
  rw [← rename_connection_equations sourceLabel openedLabel scope schema selected isShared]
  simp only [SubstitutionAction.Models, List.forall_mem_map, SubstitutionAction.Solves,
    FirstOrder.action, ScopedSolutionGluing.Solves]

variable [DecidableEq Local] [DecidableEq Shared]

/-- A genuine per-use theorem about the actual activated rule obligations:
fresh scopes permit one global solution exactly when per-use solutions agree
on the captured caller variables. Individual consistency alone is weaker. -/
theorem actual_connection_solutions_glue {n : Nat} (scopeOf : Fin n → Nat)
    (fresh : Function.Injective scopeOf)
    (schemas : Fin n → RuleInstance (SourceTerm signature Local Shared))
    (selected : Fin n → Selection O)
    (sourceLabel : O → SourceTerm signature Local Shared)
    (openedLabel : O → OpenedTerm signature Local Shared)
    (isShared : ∀ use, SharedLabels sourceLabel openedLabel (scopeOf use) ((selected use).taken ++ (selected use).read)) :
    (∃ assignment : Subst (signature.withVars (ScopedVar Local ⊕ Shared)), ∀ use,
      (FirstOrder.action (signature.withVars (ScopedVar Local ⊕ Shared))).Models assignment
        (addedEquations openedLabel (ScopedVariables.ruleAt (scopeOf use) (schemas use)) (selected use))) ↔
      ∃ family : Fin n → Subst (signature.withVars (ScopedVar Local ⊕ Shared)),
        (∀ use, (FirstOrder.action (signature.withVars (ScopedVar Local ⊕ Shared))).Models (family use)
          (addedEquations openedLabel (ScopedVariables.ruleAt (scopeOf use) (schemas use)) (selected use))) ∧
        ∀ first second (shared : Shared), family first (.inr shared) = family second (.inr shared) := by
  simp only [models_actual_connections_iff sourceLabel openedLabel _ _ _ (isShared _)]
  exact ScopedSolutionGluing.glue scopeOf fresh (fun use => addedEquations sourceLabel (schemas use) (selected use))

theorem distinct_rule_uses_only_share_captures {firstScope secondScope : Nat}
    (different : firstScope ≠ secondScope)
    (first second : SourceTerm signature Local Shared) (name : ScopedVar Local ⊕ Shared)
    (inFirst : name ∈ (ScopedVariables.termAt firstScope first).freeVars)
    (inSecond : name ∈ (ScopedVariables.termAt secondScope second).freeVars) :
    ∃ shared, name = .inr shared :=
  ScopedVariables.different_activations_only_share_captures different first second name inFirst inSecond

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.FirstOrderHornActivations
