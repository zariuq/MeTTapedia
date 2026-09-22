import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceActivationPolicyBoundary
import Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary

/-!
# Activation-policy specimen for quotation/choice views

The selected inert and triggered operational views satisfy source residency.
Their explicit-trigger embeddings preserve the positive choice step and
negative inert case.  Neither acquires an implicit communication step.
-/


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceActivationPolicyCanary

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionChoiceNormalFormBoundary
open SpaceOperationalViewBoundary
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceActivationPolicyBoundary

open Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceOperationalViewCanary

theorem inert_residentSound : ResidentSound inert := by
  intro store occurrence next receipt step
  change False at step
  exact step.elim

theorem triggered_residentSound : ResidentSound triggered := by
  intro store occurrence next receipt step
  rw [step.1]
  simp [triggered, rewriteTriggeredView]

def inertPolicy := ofOperationalView inert inert_residentSound
def triggeredPolicy := ofOperationalView triggered triggered_residentSound

theorem triggered_choice_requested_can_fire :
    triggeredPolicy.CanFire initialStore (.requested () choiceDemo) := by
  exact (canFire_requested_iff triggered triggered_residentSound
    initialStore choiceDemo).2 triggered_choice_can_fire

theorem inert_choice_requested_cannot_fire :
    ¬ inertPolicy.CanFire initialStore (.requested () choiceDemo) := by
  intro fires
  exact inert_choice_cannot_fire
    ((canFire_requested_iff inert inert_residentSound
      initialStore choiceDemo).1 fires)

theorem triggered_view_has_no_implicit_rho_step :
    ¬ triggeredPolicy.CanFire initialStore
      (.communication choiceDemo choiceDemo) :=
  no_communication_fire triggered triggered_residentSound
    initialStore choiceDemo choiceDemo


#print axioms triggered_choice_requested_can_fire
#print axioms inert_choice_requested_cannot_fire
#print axioms triggered_view_has_no_implicit_rho_step

end Mettapedia.Languages.MeTTa.PrimeCandidates.SpaceActivationPolicyCanary
