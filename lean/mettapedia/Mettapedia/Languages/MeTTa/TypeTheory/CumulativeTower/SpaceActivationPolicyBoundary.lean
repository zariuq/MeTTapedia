import Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.SpaceOperationalViewBoundary

/-!
# Prime operational views as explicit-trigger capability fragments

The earlier `OperationalView` interface selects one resident occurrence as the
putative source of a step.  This module embeds such a view into the generic
activation-capability theory as the explicit-trigger fragment.

The embedding exposes one additional proof obligation: a transition must
actually originate at a resident occurrence.  The original narrow interface
did not place that law in its record, so the bridge requires it explicitly.
Both Prime canary views satisfy the law.  Their embedded policies have no
rho-style communication transitions; that capability must be joined as a
separate authored fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace SpaceActivationPolicyBoundary

open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.OSLF.MeTTaIL.Syntax
open ReductionChoiceNormalFormBoundary
open SpaceOperationalViewBoundary

universe uStore uObservation uReceipt

/-- The missing source-residency law required to interpret a narrow
`OperationalView` as a sound activation policy. -/
def ResidentSound
    {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (view : OperationalView language Store Observation Receipt) : Prop :=
  ∀ {store occurrence next receipt},
    view.step store occurrence next receipt →
      view.resident store occurrence

/-- Embed an operational view as a unary explicit-trigger fragment.  A `Unit`
trigger means only that the triggering event carries no additional payload. -/
def ofOperationalView
    {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (view : OperationalView language Store Observation Receipt)
    (residentSound : ResidentSound view) :
    Policy Store Pattern Unit Observation Receipt where
  resident := view.resident
  enabled store cause :=
    match cause with
    | .requested _ occurrence =>
        OperationalView.CanFire view store occurrence
    | .communication _sender _receiver => False
  step store cause next receipt :=
    match cause with
    | .requested _ occurrence => view.step store occurrence next receipt
    | .communication _sender _receiver => False
  step_enabled := by
    intro store cause next receipt step
    cases cause with
    | requested trigger occurrence => exact ⟨next, receipt, step⟩
    | communication sender receiver => exact step.elim
  enabled_supported := by
    intro store cause enabled
    cases cause with
    | requested trigger occurrence =>
        obtain ⟨next, receipt, step⟩ := enabled
        exact residentSound step
    | communication sender receiver => exact enabled.elim
  observe := view.observe

theorem canFire_requested_iff
    {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (view : OperationalView language Store Observation Receipt)
    (residentSound : ResidentSound view)
    (store : Store) (occurrence : Pattern) :
    (ofOperationalView view residentSound).CanFire store
        (.requested () occurrence) ↔
      OperationalView.CanFire view store occurrence :=
  Iff.rfl

/-- A unary operational view cannot silently acquire binary communication. -/
theorem no_communication_fire
    {language : LanguageDef} {Store : Type uStore}
    {Observation : Type uObservation} {Receipt : Type uReceipt}
    (view : OperationalView language Store Observation Receipt)
    (residentSound : ResidentSound view)
    (store : Store) (sender receiver : Pattern) :
    ¬ (ofOperationalView view residentSound).CanFire store
        (.communication sender receiver) := by
  rintro ⟨next, receipt, step⟩
  exact step

namespace PrimeCanary

open SpaceOperationalViewBoundary.PrimeCanary

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

end PrimeCanary

#print axioms canFire_requested_iff
#print axioms no_communication_fire
#print axioms PrimeCanary.triggered_choice_requested_can_fire
#print axioms PrimeCanary.inert_choice_requested_cannot_fire
#print axioms PrimeCanary.triggered_view_has_no_implicit_rho_step

end SpaceActivationPolicyBoundary
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
