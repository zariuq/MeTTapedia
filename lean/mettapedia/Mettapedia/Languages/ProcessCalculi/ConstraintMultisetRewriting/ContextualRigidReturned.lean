import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidActivation

/-!
# Actual completed contextual returns reflect rigid occurrence firings

The input is the concrete returned worklist update, its literal run equation
and empty residual, through the existing `FromRun` record. Completion reflects
every prior, take, read and told equation through the structural encoding.
No executable-completeness axiom, fuel-success convention or abstract
existence-of-a-solution predicate replaces that returned result.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidActivation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualFrameUpdate

universe uT uU uO uA
variable {S : Signature} {T : Type uT} {U : Type uU} {O : Type uO} {A : Type uA}
  {Local Shared : Type} (locals : Local → MetaArity S) (captures : Shared → MetaArity S)
  {Γ : Ctx S} {sort : S.Srt} (encode : T → Term S Γ sort)

theorem completed_equations (injective : Function.Injective encode)
    (occupied : Finset Nat) (selection : Selection O) (original : RuleInstance T)
    (label : O → T) (state : Configuration T O)
    (extra : EquationStore (Term (signature S captures) Γ sort))
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures occupied selection
        (rule locals captures encode original) (rows locals captures encode label) (withFrame captures encode extra state))))
    (empty : update.remaining = []) :
    ∀ equation ∈ selection.problem label original state, equation.1 = equation.2 := by
  have modeled := (ContextualResidual.models_observeProblem update.answer _).mp (update.completed empty)
  intro equation member
  have encodedMember :
      (into encode (ContextualActivatedStep.target locals captures) equation.1,
        into encode (ContextualActivatedStep.target locals captures) equation.2) ∈
      ContextualActivatedStep.problem locals captures occupied selection
        (rule locals captures encode original) (rows locals captures encode label) (withFrame captures encode extra state) := by
    rw [problem_withFrame, problem]
    exact List.mem_append_right _ (List.mem_map.mpr ⟨equation, member, rfl⟩)
  have solved := modeled _ encodedMember
  change instantiate update.answer (into encode (ContextualActivatedStep.target locals captures) equation.1) =
    instantiate update.answer (into encode (ContextualActivatedStep.target locals captures) equation.2) at solved
  unfold into at solved
  rw [Rigid.instantiate_include, Rigid.instantiate_include] at solved
  exact injective (Rigid.include_injective update.declaration _ _ solved)

theorem ordinary_valid_of_returned [DecidableEq O] [DecidableEq Local] [DecidableEq Shared]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (injective : Function.Injective encode) (ordinary : SubstitutionAction U A) (readback : T → U)
    {fuel : Nat} {occupied : Finset Nat} {selection : Selection O}
    {original : RuleInstance T} (free : original.checks = [])
    {label : O → T} {state : Configuration T O}
    {extra : EquationStore (Term (signature S captures) Γ sort)}
    (update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures occupied selection
        (rule locals captures encode original) (rows locals captures encode label) (withFrame captures encode extra state))))
    (returned : ContextualTransportedActivation.FromRun locals captures fuel occupied selection
      (rule locals captures encode original) (rows locals captures encode label) (withFrame captures encode extra state)
      (outputs locals captures encode label) update) :
    selection.Valid ordinary (readback ∘ label) (original.map readback)
      (OccurrenceRelabeling.configuration readback state) := by
  let admitted := returned.valid.admitted
  have equationsSame := completed_equations locals captures encode injective occupied selection original label state
    extra update returned.empty
  have outputCodes := admitted.outputs
  rw [prepared_rule] at outputCodes
  have sourceOutputs : selection.made.map label = original.produce := by
    apply (List.map_inj_right (f := into encode (ContextualActivatedStep.target locals captures))
      (fun first second same => injective
        (Rigid.include_injective (ContextualActivatedStep.target locals captures) _ _ same))).mp
    simpa only [List.map_map, Function.comp_def, outputs, RuleInstance.map] using outputCodes
  refine ⟨admitted.take_distinct, admitted.output_distinct, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [rule, RuleInstance.map, List.length_map] using admitted.take_length
  · simpa only [rule, RuleInstance.map, List.length_map] using admitted.read_length
  · simpa only [RuleInstance.map, List.map_map, Function.comp_def] using congrArg (List.map readback) sourceOutputs
  · refine ⟨admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
      admitted.occurrences.apart, admitted.occurrences.fresh, ?_⟩
    intro query member
    cases member
  · refine ⟨ordinary.identity, ?_⟩
    rw [OccurrenceRelabeling.problem]
    intro equation member
    obtain ⟨prior, present, rfl⟩ := List.mem_map.mp member
    rw [equationsSame prior present]
    exact ordinary.equivalence.refl _
  · intro check member
    simp only [RuleInstance.map, free, List.map_nil] at member
    cases member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualRigidActivation
