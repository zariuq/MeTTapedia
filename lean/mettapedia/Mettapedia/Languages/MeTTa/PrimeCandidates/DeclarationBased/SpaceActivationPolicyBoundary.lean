import Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SpaceOperationalViewBoundary

/-!
# Operational views as explicit-trigger capability fragments

A narrow operational view selects one resident occurrence as the proposed
source of a transition.  It embeds into activation-capability theory once
every transition is proved to originate at a resident occurrence.

The embedding preserves exactly the requested firing relation.  It grants
no binary communication transitions; communication must be supplied as a
separate authored capability.
-/


set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
namespace SpaceActivationPolicyBoundary

open Mettapedia.GSLT.Dynamics.SpaceActivationPolicy
open Mettapedia.OSLF.MeTTaIL.Syntax
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

#print axioms canFire_requested_iff
#print axioms no_communication_fire

end SpaceActivationPolicyBoundary
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
