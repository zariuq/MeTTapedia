import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFactorization
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationNaturality
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPreparationExtensions

/-!
# Reusable contextual firing interfaces retain every instance guard

The reusable structural part is formation and physical resource admission.
Capture substitution transports every prepared port and original guard; it
does not infer the uninstantiated guard from one successful instance.
At each use, consistency and every retained check must hold in that use's
problem and row world. The theorem does not construct an anti-unifier or
authorize installation of an arbitrary logical rule.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedPromotion

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualActivatedStep ContextualInteractionFactors ContextualViewNaturality

variable {S : Signature} {Local Shared Next O : Type} [DecidableEq O]
  (locals : Local → MetaArity S) {captures : Shared → MetaArity S} {next : Next → MetaArity S}
  (change : Assignment captures next) (occupied : Finset Nat) (selection : Selection O)
  {Γ : Ctx S} {sort : S.Srt}
  (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
  (rows : O → ContextualStoredRows.Row locals captures Γ sort)
  (before : Configuration (Term (signature S captures) Γ sort) O)
  (outputs : O → Term (signature S (target locals captures)) Γ sort)

omit [DecidableEq O] in
theorem formation_map
    (formed : Formation locals captures occupied selection rule rows outputs) :
    Formation locals next occupied selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
      (fun occurrence => (rows occurrence).map locals change)
      (fun occurrence => instantiate (activeLift locals change) (outputs occurrence)) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [RuleInstance.map, List.length_map] using formed.take_length
  · simpa only [RuleInstance.map, List.length_map] using formed.read_length
  · have produced := congrArg RuleInstance.produce
      (ContextualPreparationNaturality.prepared_rule_transport locals change occupied selection rule rows)
    change ((prepared locals captures occupied selection rule rows).rule.produce).map
      (instantiate (activeLift locals change)) = _ at produced
    rw [← produced, ← formed.outputs, List.map_map]
    rfl

/-- Structural reuse is exact only when the retained information obligations
are discharged for this instance. Source output agreement remains a premise. -/
theorem instance_valid_iff_information
    (formed : Formation locals captures occupied selection rule rows outputs)
    (resources : Resources selection before.present) :
    ContextualGuardedStep.Valid locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)
        (ContextualTransportedActivation.configurationMap change before)
        (fun occurrence => instantiate (activeLift locals change) (outputs occurrence)) ↔
      Information locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)
        (ContextualTransportedActivation.configurationMap change before) := by
  rw [ContextualGuardedStep.valid_iff_factors]
  exact ⟨fun admitted => admitted.information,
    fun information => ⟨formation_map locals change occupied selection rule rows outputs formed,
      resources, information⟩⟩

omit [DecidableEq O] in
/-- Existing all-future guard evidence is preserved by a compatible instance.
Consistency is checked separately because substitution may restrict solutions. -/
theorem information_map
    (information : Information locals captures occupied selection rule rows before)
    (compatible : ContextualFrameUnifier.Solvable
      (problem locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)
        (ContextualTransportedActivation.configurationMap change before))) :
    Information locals next occupied selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
      (fun occurrence => (rows occurrence).map locals change)
      (ContextualTransportedActivation.configurationMap change before) := by
  refine ⟨compatible, ?_⟩
  intro check member
  have retained := congrArg RuleInstance.checks
    (ContextualPreparationNaturality.prepared_rule_transport locals change occupied selection rule rows)
  change ((prepared locals captures occupied selection rule rows).rule.checks).map
    (Check.map (instantiate (activeLift locals change))) = _ at retained
  rw [← retained] at member
  obtain ⟨original, originalMember, rfl⟩ := List.mem_map.mp member
  exact ContextualPreparationNaturality.ask_forward locals change occupied selection rule rows before original
    (information.checks original originalMember)

theorem valid_instance
    (valid : ContextualGuardedStep.Valid locals captures occupied selection rule rows before outputs)
    (compatible : ContextualFrameUnifier.Solvable
      (problem locals next occupied selection
        (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
        (fun occurrence => (rows occurrence).map locals change)
        (ContextualTransportedActivation.configurationMap change before))) :
    ContextualGuardedStep.Valid locals next occupied selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
      (fun occurrence => (rows occurrence).map locals change)
      (ContextualTransportedActivation.configurationMap change before)
      (fun occurrence => instantiate (activeLift locals change) (outputs occurrence)) := by
  have admitted := (ContextualGuardedStep.valid_iff_factors locals captures occupied selection rule rows before outputs).mp valid
  exact (instance_valid_iff_information locals change occupied selection rule rows before outputs
    admitted.formation admitted.resources).mpr
      (information_map locals change occupied selection rule rows before admitted.information compatible)

omit [DecidableEq O] in
/-- Each original guard remains at the same list position after instantiation. -/
theorem instance_retains_guard_list :
    (prepared locals next occupied selection
      (rule.map (instantiate (ContextualStoredRows.liftCaptures locals change)))
      (fun occurrence => (rows occurrence).map locals change)).rule.checks =
    ((prepared locals captures occupied selection rule rows).rule.checks).map
      (Check.map (instantiate (activeLift locals change))) := by
  exact (congrArg RuleInstance.checks
    (ContextualPreparationNaturality.prepared_rule_transport locals change occupied selection rule rows)).symm

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedPromotion
