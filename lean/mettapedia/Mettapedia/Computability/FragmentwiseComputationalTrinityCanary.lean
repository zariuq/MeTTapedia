import Mettapedia.Computability.FragmentwiseComputationalTrinity
import Mettapedia.Computability.ObservationCarrierTrinity

/-!
# Canaries for fragmentwise computational-trinity pressure

The positive example selects the first-bit fragment consistently across the
program, logic, and spatial faces of the existing comparison.  The negative
examples show that no constraint imported from an extensional target can
recover a source distinction already erased by its interpretation: neither a
hidden program bit nor answer-stream order can be reconstructed in this way.
-/

namespace Mettapedia.Computability.FragmentwiseComputationalTrinityCanary

open CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open Mettapedia.Computability.FragmentwiseComputationalTrinity

namespace FirstBit

open ComputationalTrinity.FirstBitObservation

private def here : Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- The operational fragment whose visible first bit is false. -/
def programFirstFalse : Constraint comparison.program where
  holds _ program := program.1 = false
  map_closed := by
    intro source target substitution program admitted
    change program.1 = false
    exact admitted

/-- The corresponding logical fragment. -/
def logicFalse : Constraint comparison.logic where
  holds _ proposition := proposition = false
  map_closed := by
    intro source target substitution proposition admitted
    change proposition = false
    exact admitted

/-- The corresponding spatial fragment. -/
def spaceFalse : Constraint comparison.space where
  holds _ point := point = false
  map_closed := by
    intro source target substitution point admitted
    change point = false
    exact admitted

/-- A coherent local fragment exists without asserting that the complete
three faces are exact or final. -/
def fragmentwise :
    ComputationalTrinity.FragmentwiseComparison comparison where
  programFragment := programFirstFalse
  logicFragment := logicFalse
  spaceFragment := spaceFalse
  programLogicCompatible := by
    intro context logicalElement represented
    rcases represented with ⟨program, admitted, rfl⟩
    exact admitted
  logicSpaceCompatible := by
    intro context spatialElement represented
    rcases represented with ⟨logicalElement, admitted, rfl⟩
    exact admitted

/-- The local program fragment is carried directly into the selected spatial
fragment by the generic coherence theorem. -/
theorem local_program_space_compatible :
    (fragmentwise.programFragment.pushforward
      comparison.programToSpace).Entails fragmentwise.spaceFragment :=
  fragmentwise.programSpaceCompatible

/-- Pulling the spatial requirement back accepts every program whose visible
first bit is false, regardless of its hidden second bit. -/
theorem spatial_pressure_accepts_hidden_true :
    (spaceFalse.pullback comparison.programToSpace).holds
      here (false, true) := by
  rfl

/-- A genuinely intensional program constraint selects the hidden bit. -/
def programSecondFalse : Constraint comparison.program where
  holds _ program := program.2 = false
  map_closed := by
    intro source target substitution program admitted
    change program.2 = false
    exact admitted

/-- The visible first-bit fragment is already extensional for the direct
observation, so saturation changes nothing. -/
theorem programFirstFalse_fibreClosed :
    programFirstFalse.FibreClosed comparison.programToSpace := by
  intro context left right sameImage leftAdmitted
  change right.1 = false
  change left.1 = false at leftAdmitted
  change left.1 = right.1 at sameImage
  exact sameImage.symm.trans leftAdmitted

theorem programFirstFalse_saturation_exact :
    programFirstFalse.Equivalent
      (programFirstFalse.saturate comparison.programToSpace) :=
  (Constraint.equivalent_saturate_iff_fibreClosed
    comparison.programToSpace programFirstFalse).2
      programFirstFalse_fibreClosed

/-- The hidden-bit fragment is not extensional for the first-bit
observation.  Its saturation necessarily admits more programs. -/
theorem programSecondFalse_not_fibreClosed :
    ¬ programSecondFalse.FibreClosed comparison.programToSpace := by
  intro fibreClosed
  have admitted := fibreClosed here (false, false) (false, true) rfl rfl
  change true = false at admitted
  cases admitted

/-- No spatial requirement can recover the hidden second bit after the
first-bit interpretation has erased it. -/
theorem no_spatial_constraint_recovers_hidden_bit
    (spatialRequirement : Constraint comparison.space) :
    ¬ programSecondFalse.Equivalent
      (spatialRequirement.pullback comparison.programToSpace) := by
  apply Constraint.not_equivalent_pullback_of_separates_fibre
    comparison.programToSpace programSecondFalse spatialRequirement
      (context := here) (left := (false, false)) (right := (false, true))
  · rfl
  · rfl
  · change ¬(true = false)
    decide

/-- Direct and logic-mediated inverse pressure agree for this concrete
comparison, without choosing one route as semantic authority. -/
theorem direct_and_mediated_pressure_agree :
    (spaceFalse.pullback comparison.logicToSpace |>.pullback
      comparison.programToLogic).Equivalent
        (spaceFalse.pullback comparison.programToSpace) :=
  ComputationalTrinity.FragmentwiseComparison.spacePressureCoherent
    comparison spaceFalse

end FirstBit

namespace Observation

open Mettapedia.Computability.ObservationCarrierTrinity

private def here : Contextᵒᵖ :=
  Opposite.op (Discrete.mk PUnit.unit)

/-- An order-sensitive operational requirement. -/
def exactAnswerOrder : Constraint comparison.program where
  holds _ answers := answers = [true, false]
  map_closed := by
    intro source target substitution answers admitted
    change answers = [true, false]
    exact admitted

/-- Exact answer order is not closed under the stream-to-set observation. -/
theorem exactAnswerOrder_not_fibreClosed :
    ¬ exactAnswerOrder.FibreClosed comparison.programToSpace := by
  intro fibreClosed
  have rejected := fibreClosed here [true, false] [false, true]
    (by
      show ([true, false] : List Bool).toFinset =
        ([false, true] : List Bool).toFinset
      decide)
    rfl
  change ([false, true] : List Bool) = [true, false] at rejected
  have unequal : ([false, true] : List Bool) ≠ [true, false] := by
    decide
  exact unequal rejected

/-- No set-level requirement can recover stream order after order has been
forgotten. -/
theorem no_set_constraint_recovers_answer_order
    (setRequirement : Constraint comparison.space) :
    ¬ exactAnswerOrder.Equivalent
      (setRequirement.pullback comparison.programToSpace) := by
  apply Constraint.not_equivalent_pullback_of_separates_fibre
    comparison.programToSpace exactAnswerOrder setRequirement
      (context := here) (left := [true, false]) (right := [false, true])
  · show ([true, false] : List Bool).toFinset =
      ([false, true] : List Bool).toFinset
    decide
  · rfl
  · change ¬([false, true] : List Bool) = [true, false]
    decide

/-- A multiplicity-sensitive bag requirement. -/
def doubleTrue : Constraint comparison.logic where
  holds _ answers := answers = ({true, true} : Multiset Bool)
  map_closed := by
    intro source target substitution answers admitted
    change answers = ({true, true} : Multiset Bool)
    exact admitted

/-- Multiplicity is not closed under the bag-to-set observation. -/
theorem doubleTrue_not_fibreClosed :
    ¬ doubleTrue.FibreClosed comparison.logicToSpace := by
  intro fibreClosed
  have rejected := fibreClosed here
    ({true, true} : Multiset Bool) ({true} : Multiset Bool)
    (by
      show ({true, true} : Multiset Bool).toFinset =
        ({true} : Multiset Bool).toFinset
      decide)
    rfl
  change ({true} : Multiset Bool) = ({true, true} : Multiset Bool) at rejected
  have unequal : ({true} : Multiset Bool) ≠ ({true, true} : Multiset Bool) := by
    decide
  exact unequal rejected

/-- No set-level requirement can recover occurrence multiplicity after the
bag-to-set projection. -/
theorem no_set_constraint_recovers_multiplicity
    (setRequirement : Constraint comparison.space) :
    ¬ doubleTrue.Equivalent
      (setRequirement.pullback comparison.logicToSpace) := by
  apply Constraint.not_equivalent_pullback_of_separates_fibre
    comparison.logicToSpace doubleTrue setRequirement
      (context := here) (left := ({true, true} : Multiset Bool))
      (right := ({true} : Multiset Bool))
  · show ({true, true} : Multiset Bool).toFinset =
      ({true} : Multiset Bool).toFinset
    decide
  · rfl
  · change ¬({true} : Multiset Bool) = ({true, true} : Multiset Bool)
    decide

end Observation

#print axioms FirstBit.local_program_space_compatible
#print axioms FirstBit.programFirstFalse_saturation_exact
#print axioms FirstBit.programSecondFalse_not_fibreClosed
#print axioms FirstBit.no_spatial_constraint_recovers_hidden_bit
#print axioms FirstBit.direct_and_mediated_pressure_agree
#print axioms Observation.no_set_constraint_recovers_answer_order
#print axioms Observation.no_set_constraint_recovers_multiplicity
#print axioms Observation.exactAnswerOrder_not_fibreClosed
#print axioms Observation.doubleTrue_not_fibreClosed

end Mettapedia.Computability.FragmentwiseComputationalTrinityCanary
