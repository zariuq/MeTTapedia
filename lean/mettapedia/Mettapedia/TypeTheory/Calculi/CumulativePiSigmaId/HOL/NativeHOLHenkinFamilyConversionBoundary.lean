import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLHenkinFamilySemantics

/-!
# Arbitrary semantic recoding does not establish unique native denotation

The ordinary-family realization relation permits an arbitrary pointwise
equivalence in its conversion constructor.  Even with an unchanged context,
native variable and result family, this can change an observable Boolean.
Thus forward realization through a specified codec is not reflection,
denotation uniqueness, or native execution adequacy.

This counterexample uses an inhabited two-element fibre and retains the
different sections.  It neither refutes a source HOL theorem nor adds a
conversion rule to the native checker.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler.HenkinFamilySemantics.ConversionBoundary

open Mettapedia.Logic FormationSensitiveHOLInterface

universe u v

def booleanContext : SemanticContext.{u + 1} 1 where
  Environment := PUnit
  family := fun _ _ => ULift.{u + 1, 0} Bool
  projection := fun _ _ => ULift.up false

def falseSection : Section (booleanContext.{u}.family 0) := fun _ => ULift.up false

def trueSection : Section (booleanContext.{u}.family 0) := fun _ => ULift.up true

def booleanNegation : Equiv.Perm (ULift.{u + 1, 0} Bool) where
  toFun value := ULift.up (!value.down)
  invFun value := ULift.up (!value.down)
  left_inv value := by cases value with | up value => cases value <;> rfl
  right_inv value := by cases value with | up value => cases value <;> rfl

variable {Base : Type u} {Const : HOL.Ty Base → Type v}

theorem variable_realizes_false
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const) :
    Denotes signature model booleanContext (.var 0)
      (booleanContext.family 0) falseSection := .var booleanContext 0

theorem variable_recodes_to_true
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const) :
    Denotes signature model booleanContext (.var 0)
      (booleanContext.family 0) trueSection := by
  have converted := Denotes.convert (variable_realizes_false signature model)
    (fun _ => booleanNegation)
  apply converted.change_value
  funext environment
  rfl

theorem sections_distinct : falseSection.{u} ≠ trueSection := by
  intro equal
  have values := congrArg (fun value => (value PUnit.unit).down) equal
  exact Bool.false_ne_true values

/-- The present conversion relation fails value uniqueness for the same
variable and expected family, in every ambient logical signature/model. -/
theorem arbitrary_conversion_not_unique
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, u + 1} Base Const) :
    ∃ first second : Section (booleanContext.{u}.family 0),
      Denotes signature model booleanContext (.var 0)
        (booleanContext.family 0) first ∧
      Denotes signature model booleanContext (.var 0)
        (booleanContext.family 0) second ∧ first ≠ second :=
  ⟨falseSection, trueSection, variable_realizes_false signature model,
    variable_recodes_to_true signature model, sections_distinct⟩

#print axioms arbitrary_conversion_not_unique

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLNativeGenericProofCompiler.HenkinFamilySemantics.ConversionBoundary
