import Mettapedia.GSLT.Dynamics.CompositeObservationDiscipline
import Mettapedia.GSLT.Dynamics.ObservationPolicyFactorization

/-!
# Policies over composite observation disciplines

Parallel composition of observation disciplines retains both witness and
value coordinates on common collection success.  Supported component policies
therefore pair into a supported joint policy on that synchronized container.
Conversely, adding an observation axis that is constant on the relevant
collision cannot repair information already erased by another axis.
-/

namespace Mettapedia.GSLT.Dynamics

open Mettapedia.Algebra

universe uLeftEvent uRightEvent uLeftContainer uRightContainer
  uLeftValue uRightValue uLeftDecision uRightDecision

namespace ObservationDiscipline

/-- Supported policies compose across the parallel product of two
observation disciplines.  Their witness containers, values, and decisions
remain separate product coordinates. -/
theorem parallelComposite_supportsPolicy
    {LeftEvent : Type uLeftEvent} {RightEvent : Type uRightEvent}
    (left :
      ObservationDiscipline.{uLeftEvent, uLeftContainer, uLeftValue} LeftEvent)
    (right :
      ObservationDiscipline.{uRightEvent, uRightContainer, uRightValue} RightEvent)
    (leftPolicy : left.collection.Container -> LeftDecision)
    (rightPolicy : right.collection.Container -> RightDecision)
    (leftSupported : left.SupportsPolicy leftPolicy)
    (rightSupported : right.SupportsPolicy rightPolicy) :
    (parallelComposite left right).SupportsPolicy
      (fun containers =>
        (leftPolicy containers.1, rightPolicy containers.2)) := by
  obtain ⟨leftObserved, leftRecovers⟩ := leftSupported
  obtain ⟨rightObserved, rightRecovers⟩ := rightSupported
  refine ⟨fun values =>
      (leftObserved values.1, rightObserved values.2),
    fun containers => ?_⟩
  exact Prod.ext (leftRecovers containers.1) (rightRecovers containers.2)

end ObservationDiscipline

/-! ## Positive and negative controls -/

namespace CompositePolicyCanary

def unitCost : Unit -> WorkSpan :=
  fun _ => ⟨1, 1⟩

def workOnly : ObservationDiscipline Unit :=
  WorkSpanObservation.workOnly unitCost

/-- A total constant observation axis. -/
def constant : ObservationDiscipline Unit where
  collection :=
    { Container := Unit
      collect := fun _ => some () }
  Value := Unit
  readout := id

def leftWorkPolicy (value : WorkSpan) : Bool :=
  decide (2 ≤ value.work)

def rightConstantPolicy (_ : Unit) : Bool :=
  true

def leftSpanPolicy (containers : WorkSpan × Unit) : Bool :=
  decide (2 ≤ containers.1.span)

theorem constant_supports_rightPolicy :
    constant.SupportsPolicy rightConstantPolicy := by
  exact ⟨rightConstantPolicy, fun _ => rfl⟩

/-- The product observer supports the product of its independently supported
component policies. -/
theorem composite_supports_componentPolicies :
    (ObservationDiscipline.parallelComposite workOnly constant).SupportsPolicy
      (fun containers =>
        (leftWorkPolicy containers.1, rightConstantPolicy containers.2)) := by
  apply ObservationDiscipline.parallelComposite_supportsPolicy
  · exact WorkSpanPolicyCanary.workOnly_supports_workAtLeastTwo
  · exact constant_supports_rightPolicy

/-- Adding a constant observation coordinate cannot repair the lost span
distinction of work-only observation. -/
theorem constant_axis_does_not_repair_spanPolicy :
    ¬ (ObservationDiscipline.parallelComposite workOnly constant
      ).SupportsPolicy leftSpanPolicy := by
  apply ObservationDiscipline.not_supportsPolicy_of_collision
      (ObservationDiscipline.parallelComposite workOnly constant)
      leftSpanPolicy
      (first := ((⟨2, 1⟩ : WorkSpan), ()))
      (second := ((⟨2, 2⟩ : WorkSpan), ()))
  · rfl
  · decide

end CompositePolicyCanary

#print axioms ObservationDiscipline.parallelComposite_supportsPolicy
#print axioms CompositePolicyCanary.composite_supports_componentPolicies
#print axioms CompositePolicyCanary.constant_axis_does_not_repair_spanPolicy

end Mettapedia.GSLT.Dynamics
