import Mettapedia.GSLT.Core.SemanticImplementation

/-!
# Faithful implementations under a change of host representation

An equivalent host carrier preserves the existing implementation's state
faithfulness, step soundness, and equation-class completeness. This is a
mathematical change of representation, not a claim that arbitrary physical
materials realize the supplied transition relation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.IndexedOperational.OperationalImplementation

open Mettapedia.GSLT

universe uTheory uHost uNewHost

variable {theory : GSLT.{uTheory}}

/-- Transport an independently justified implementation through a host-state
equivalence. The transported step relation retains both operational laws. -/
def recode (implementation : OperationalImplementation.{uHost, uTheory} theory)
    {NewState : Type uNewHost} (encoding : NewState ≃ implementation.State) :
    OperationalImplementation.{uNewHost, uTheory} theory where
  State := NewState
  encode state := implementation.encode (encoding state)
  encode_injective := implementation.encode_injective.comp encoding.injective
  step first second := implementation.step (encoding first) (encoding second)
  sound := implementation.sound
  complete := by
    intro source target step
    obtain ⟨next, advances, equivalent⟩ := implementation.complete step
    refine ⟨encoding.symm next, ?_, ?_⟩
    · simpa using advances
    · simpa using equivalent

/-- A recoded host has exactly the original transitions under its equivalence. -/
theorem recode_step_iff
    (implementation : OperationalImplementation.{uHost, uTheory} theory)
    {NewState : Type uNewHost} (encoding : NewState ≃ implementation.State)
    (first second : NewState) :
    (implementation.recode encoding).step first second ↔
      implementation.step (encoding first) (encoding second) := Iff.rfl

/-- The independently proved implementation criterion remains valid after
recoding, including reflection of target steps rather than only simulation. -/
theorem recode_semanticStep_iff
    (implementation : OperationalImplementation.{uHost, uTheory} theory)
    {NewState : Type uNewHost} (encoding : NewState ≃ implementation.State)
    (source : NewState) (target : theory.Term) :
    theory.Step (implementation.encode (encoding source)) target ↔
      ∃ next : NewState, implementation.step (encoding source) (encoding next) ∧
        theory.Equiv (implementation.encode (encoding next)) target :=
  (implementation.recode encoding).semanticStep_iff_exists_implementationStep source target

#print axioms recode
#print axioms recode_semanticStep_iff

end Mettapedia.GSLT.IndexedOperational.OperationalImplementation
