import Mettapedia.Languages.MeTTa.HE.Spec.Eval
import Mettapedia.Languages.MeTTa.HE.Spec.Match.Completeness

/-!
# Source frames earned by annotated contextual unification

An existing local unifier trace supplies a normal reached presentation. Its
own presented model earns an independent source match and conjunction with
the incoming record. This constructs the reached Frame without assuming a
model of the desired source output. A supported but unassigned variable may
be bound to closed data while updating older contextual values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.ContextualUnificationFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed Spec.Eval.Steps
open Spec.Type.Presentation Spec.Type.RuntimeRefinement Spec.Type.Presentation.BindingTheory
open Spec.Bindings.ScopeObservation Spec.Bindings.ScopeObservation.ModelTransport Spec.Match.SolutionTheory

theorem frame_of_unification (policy : Policy) (before : Frame) (left right : Entry.Value)
    (environment : Entry.Value.Environment)
    (trace : Entry.Value.UnifyRel policy.rebuilding before.environment left right environment) :
    ∃ after : Frame, after.environment = environment ∧
      UnifyCandidateRel left.erase right.erase before.bindings after.bindings := by
  let valuation := Theory.presentedValuation (Entry.Value.eraseEnvironment environment)
  have normal := trace.output_normal before.certified.normal
  have model := Theory.normal_presentedValuation_satisfied normal
  have reached := (trace.solutions before.certified.normal valuation).mp model
  have incoming : TypeBindingSatisfied valuation before.bindings := (before.certified.theory valuation).mp reached.1
  have modelEquation : HEAtomEquationSatisfied (fun name => encodeModelAtom (valuation name)) left.erase right.erase := by
    unfold HEAtomEquationSatisfied
    rw [←encodeModelAtom_applyTypeValuation, ←encodeModelAtom_applyTypeValuation]
    exact congrArg encodeModelAtom reached.2
  obtain ⟨matched, matching, matchedModel⟩ := Spec.Match.Completeness.exists_specMatch_of_solution modelEquation
  have merged := LogicalMergeRel.append_of_common_model
    ⟨valuation, (specTypeBindingSatisfied_iff_heBindingSatisfied_translated valuation matched).mpr matchedModel, incoming⟩
  let output : Bindings := ⟨matched.assignments ++ before.bindings.assignments, matched.equalities ++ before.bindings.equalities⟩
  have selected : UnifyCandidateRel left.erase right.erase before.bindings output := ⟨matched, matching, merged⟩
  exact ⟨⟨output, environment, trace.certifies before.certified selected⟩, rfl, selected⟩

theorem closed_read (policy : Policy) (before : Frame) (value : Entry.Value)
    (closed : TypeSubst.typeVars value.erase = []) : before.read policy value = value := by
  apply Entry.Value.substitute_variable_free
  intro name occurs
  have present := Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
  simp only [closed, List.not_mem_nil] at present

theorem bind_fixed_trace (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fixed : before.read policy (.var name) = .var name) (closed : TypeSubst.typeVars value.erase = []) :
    Entry.Value.UnifyRel policy.rebuilding before.environment value (.var name)
      (Entry.Value.bind policy.rebuilding before.environment name value) := by
  have resolve : Entry.Value.resolve before.environment name = .var name := by
    simpa only [Frame.read, Entry.Value.substitute] using fixed
  have valueFixed := closed_read policy before value closed
  have nonvariable : ∀ key, value.erase ≠ .var key := by
    intro key same
    rw [same] at closed
    simp [TypeSubst.typeVars] at closed
  apply Entry.Value.UnifyRel.ordinary
  have unchanged : Entry.Value.substitute policy.rebuilding (Entry.Value.resolve before.environment) value = value := valueFixed
  rw [unchanged]
  simp only [Entry.Value.substitute, resolve]
  exact .bindRight nonvariable (by simp [closed])

theorem bind_fixed (policy : Policy) (before : Frame) (name : String) (value : Entry.Value)
    (fixed : before.read policy (.var name) = .var name) (closed : TypeSubst.typeVars value.erase = []) :
    ∃ after : Frame,
      after.environment = Entry.Value.bind policy.rebuilding before.environment name value ∧
      UnifyCandidateRel value.erase (.var name) before.bindings after.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding before.environment value (.var name) after.environment := by
  have trace := bind_fixed_trace policy before name value fixed closed
  obtain ⟨after, environment, selected⟩ := frame_of_unification policy before value (.var name) _ trace
  refine ⟨after, environment, ?_, ?_⟩
  · simpa only [Entry.Value.erase] using selected
  · simpa only [environment] using trace

end Mettapedia.Languages.MeTTa.HE.ContextualUnificationFrame
