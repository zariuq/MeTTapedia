import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunAdmissionJoin
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.HOLRunControls

/-! # The same loaded admission predicate accepts and refuses whole runs -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunAdmissionControls

open Mettapedia.Languages.OpenTheory
open Step.Evaluation.Controls HOLRunControls

variable (input : HOLRunAdmissionJoin.Input)
  (other : TypeFamilySemantics.OperatorFamilies.{0}) (prior : TypeFamilySemantics.Assignment.{0})

theorem accepts_branches (label : Bool) :
    (input.operations.signature.pathValue (input.model alternatives.effectCore other prior)
      (input.admittedValue alternatives.effectCore other prior alternatives.eventAdmission)
      (encodedWord input.toInput other (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior) label)
      ((input.runCoding alternatives.effectCore other prior).states.symm (some []))
      ((input.runCoding alternatives.effectCore other prior).states.symm (some [(true, false)]))).down := by
  rw [input.admittedValue_eq_step alternatives.effectCore other prior alternatives.eventAdmission]
  exact loaded_accepts_each_branch input.toInput other
    (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior) label

theorem refuses_branches (label : Bool) (target) :
    ¬ (input.operations.signature.pathValue (input.model alternatives.effectCore other prior)
      (input.admittedValue alternatives.effectCore other prior (fun _ _ => False))
      (encodedWord input.toInput other (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior) label)
      ((input.runCoding alternatives.effectCore other prior).states.symm (some []))
      ((input.runCoding alternatives.effectCore other prior).states.symm target)).down := by
  rw [input.admittedValue_eq_step alternatives.effectCore other prior (fun _ _ => False)]
  exact loaded_refuses_each_branch input.toInput other
    (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior) label target

theorem distinct_branches :
    encodedWord input.toInput other (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior) true ≠
      encodedWord input.toInput other (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior) false :=
  encoded_words_distinct input.toInput other (HOLRunAdmissionJoin.Input.admissionPrior alternatives.effectCore prior)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.HOLRunAdmissionControls
