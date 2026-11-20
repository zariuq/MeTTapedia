import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationSyntax
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationAlgebra
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationBoundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationWorlds
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationRuleMetadata
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegrationInteraction
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.LiveObservationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.QuantifierControls

/-!
# Positive executions and boundaries of the binding integration

These controls retain the distinction between application failure and
unification refutation, between occurrence views and set support, and between
semantic admission and a budgeted procedure's verdict. The concrete binding
application uses the integration's physical graft and checked readback.

The guard and AC controls use their actual, explicitly selected step
instances. They do not choose a default timing, quotient, or firing grain.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)
open Mettapedia.OSLF.MeTTaIL.RuleBinding (instantiateValue?)
open Mettapedia.GSLT.LanguageDef

/-- A dependency can cross a nested binder without escaping its declared
context. An actually out-of-scope argument is rejected by the same source
application whose physical implementation was compared above. -/
theorem nested_application_and_escape_boundary :
    (Pattern.lambda (some "renamed") (.apply "pair" [.bvar 1, .bvar 2])).isWellScopedAt 2 = true ∧
      instantiateValue? RuleBindingABT.Controls.value 1 1 [.bvar 2] = none :=
  ⟨Syntax.Controls.nested_result_is_scoped, Syntax.Controls.escaped_argument_does_not_apply⟩

namespace PatternBoundary

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualBinding.Controls
open ContextualPatternBinding.Controls

/-- Reordering distinct dependencies is supported. Repetition is not an
invertible dependency renaming; it is not declared globally inconsistent. -/
theorem reordered_spine_and_repeated_boundary :
    ContextualPatternBinding.solve? fId swap inverseSwap (rename (S := extended) swap body) =
        some (ContextualBinding.answer fId body) ∧
      ¬ Nonempty (Strengthener (S := extended) repeated) :=
  ⟨swapped_parameters_compute_the_principal_answer, repeated_parameters_have_no_inverse⟩

/-- This actual structural recovery procedure declines a flexible equation
that still has a solution. Its decline cannot be promoted to a refutation. -/
theorem declined_binding_still_has_a_solution :
    ContextualPatternBinding.solve? nullaryId emptySpine inverseEmpty flexibleRight = none ∧
      (ContextualFamilies.action declaration [()] ()).Consistent
        [(rename (S := extended) emptySpine (generator declaration nullaryId), flexibleRight)] :=
  ⟨symbolic_right_side_is_not_structurally_recovered,
    unrecovered_flex_flex_equation_is_still_consistent⟩

end PatternBoundary

namespace Occurrences

open SchematicRows.LiveObservations
open SchematicRows.LiveObservations.Controls

/-- The same set of payloads can have different live occurrence views.
Keeping only support therefore does not preserve this observer. -/
theorem equal_support_different_live_views :
    oneOccurrence.label '' (oneOccurrence.present : Set Nat) =
        twoOccurrences.label '' (twoOccurrences.present : Set Nat) ∧
      observe oneOccurrence ≠ observe twoOccurrences := by
  constructor
  · ext row
    simp [oneOccurrence, twoOccurrences]
  · exact duplicate_payloads_keep_occurrences

/-- Knowledge is another observed coordinate; erasing it is a separate
quotient, not a consequence of dead-slot erasure. -/
theorem retained_knowledge_changes_the_live_view :
    observe oneOccurrence ≠ observe withKnowledge := knowledge_not_erased

end Occurrences

namespace Activation

open Mettapedia.OSLF.Binding.ContextualFamily
open Rows.Example

/-- Both readouts belong to one model of the actual final knowledge. The
independent local values and the common captured value are observed together. -/
theorem repeated_uses_have_independent_locals_and_shared_capture :
    (Interface.Frames.contextual signature).Models finalPoint secondResult.knowledge ∧
      instantiateObservation finalPoint (secondResult.label 0) = observe (closedBody 7 0) ∧
      instantiateObservation finalPoint (secondResult.label 1) = observe (closedBody 7 1) ∧
      finalPoint (.inl (.inr true)) ≠ finalPoint (.inr true) ∧
      ¬ ∃ point : Assignment secondResult.frame.arity target.arity,
        (Interface.Frames.contextual signature).Models point secondResult.knowledge ∧
          point (.inl (.inl ())) = atom 7 ∧ point (.inr false) = atom 8 :=
  ⟨finalPoint_models, actual_outputs_at_common_model.1, actual_outputs_at_common_model.2,
    actual_local_values_differ, captured_value_cannot_change⟩

end Activation

namespace CountedEvents

open Worlds.Example
open Rows.Example (initial secondResult)

/-- An actual two-event execution retains both authored choices even when
one-step action and endpoint observers cannot distinguish their origins. -/
theorem execution_and_origin_observers_are_distinct :
    (policy program).last repeatedEvents = secondResult.toState ∧
      firstChoice ≠ otherOrigin ∧
      (policy program).action initial firstChoice = (policy program).action initial otherOrigin ∧
      (policy program).next initial firstChoice = (policy program).next initial otherOrigin :=
  ⟨repeated_events_are_actual, distinct_origins_same_successor⟩

end CountedEvents

namespace SharedKnowledge

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily
open Rows.Example (signature ambient target)

def constant (frame : Interface.Frames.Frame signature) (value : Nat) :
    Term (ContextualFamily.signature signature frame.arity) [] () :=
  .op (.inl (.atom value)) .nil

def captured : Contextual.Terms signature ambient :=
  observe (generator ambient.arity ())

/-- Both worlds use this name only locally until an operation explicitly
identifies their interfaces. Concatenation is that shared-interface case. -/
abbrev world (value : Nat) : State (Contextual.Terms signature) Nat :=
  ⟨ambient, [(captured, observe (constant ambient value))], ∅, fun _ => captured⟩

theorem separately_solvable (value : Nat) :
    (Interface.Frames.contextual signature).Solvable (world value).knowledge := by
  refine ⟨target, (fun _ => constant target value), ?_⟩
  intro equation member
  obtain rfl := List.mem_singleton.mp member
  rfl

/-- Local consistency is insufficient when an operation combines information
while retaining the same captured declaration on both sides. -/
theorem explicit_sharing_requires_joint_compatibility :
    (Interface.Frames.contextual signature).Solvable (world 0).knowledge ∧
      (Interface.Frames.contextual signature).Solvable (world 1).knowledge ∧
      ¬ (Interface.Frames.contextual signature).Solvable
        ((world 0).knowledge ++ (world 1).knowledge) := by
  refine ⟨separately_solvable 0, separately_solvable 1, ?_⟩
  rintro ⟨future, point, model⟩
  have zero := model (captured, observe (constant ambient 0)) (by simp [world])
  have one := model (captured, observe (constant ambient 1)) (by simp [world])
  have equal : (constant future 0) = constant future 1 :=
    observe_injective (zero.symm.trans one)
  cases equal

end SharedKnowledge

namespace Timing

open JointFirings.AskTimingControls
open StepWeb

/-- A tell-free consuming rule supplies a positive instance of the timing
transport, using the actual admitted occurrence selection. -/
theorem tell_free_consumption_has_both_timings :
    Examples.consumeFiring.AdmitsBeforeTells Examples.X Examples.tokenState ∧
      (step Examples.X Nat Examples.E Examples.demo).Admits
        (s := Examples.tokenState) Examples.consumeFiring := by
  exact ⟨(oneMatch_beforeTells_iff_of_no_tells
    Examples.consumeFiring rfl).mpr Examples.consume_admitted, Examples.consume_admitted⟩

/-- A real self-telling firing distinguishes the two guard timings. -/
theorem tells_cannot_silently_change_the_guard_timing :
    (step X Nat E selfProgram).toStep.Admits (s := emptyState) selfFiring ∧
      ¬ (beforeTells (step X Nat E selfProgram).toStep (oneMatch X Nat E selfProgram)).Admits
        (s := emptyState) selfFiring :=
  StepWeb.AskTimingControls.oneMatch_strict

end Timing

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.BindingIntegration.Controls
