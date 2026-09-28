import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Models.ZFSetReplaySubstitution

/-!
# Replay interpretation agreement on structural expressions and their instances

Successful assemblies of a supported structural expression have the same
value, even when their displayed types and supplied certificates differ.
The actual certificate-substitution and instantiation algorithms preserve
that agreement when they use the same supplied image certificates. Images
may contain lambdas and projections; the resulting expression need not be
in the structural fragment.

These comparisons retain exact assembly receipts. They do not compare
arbitrary certificates selected after erasure or establish unrestricted
certificate independence on arbitrary environments.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace ZFSetReplayInterpretation

open StructuralTypingReplay

universe u
variable {Head : Type} {ConversionCode OtherCode : Nat → Type} {n m : Nat}
variable (heads : Head → ZFSet.{u}) (constants : DeclName → ZFSet.{u})

/-- Structural interpretation pins the value of every successful assembly
on its supported fragment. Equality of displayed types is unnecessary. -/
theorem assemble_supported_values
    {subject firstType secondType : Tm Head n}
    {first : Code Head ConversionCode n} {second : Code Head OtherCode n}
    {a b : Meaning.{u} n}
    (supported : ZFSetTypeExpressionInterpretation.supported subject = true)
    (atFirst : assemble heads constants first subject firstType = some a)
    (atSecond : assemble heads constants second subject secondType = some b) :
    a.value = b.value := by
  funext env
  exact
    (agrees_with_type_expressions heads constants first subject firstType a
      supported atFirst env).trans
      (agrees_with_type_expressions heads constants second subject secondType b
        supported atSecond env).symm

variable (renameConversion : {n m : Nat} → Ren n m → ConversionCode n → ConversionCode m)
variable (substituteConversion : {n m : Nat} → Sub Head n m → ConversionCode n → ConversionCode m)
variable (R : Rules Head) [DecidableEq Head]
variable [∀ h u, Decidable (R.headTyping h u)] [∀ h, Decidable (R.isUniverse h)]
variable [∀ u v w, Decidable (R.join u v w)] [∀ u v, Decidable (R.cumulative u v)]
variable (conversionCheck : {n : Nat} → ConversionCode n → Tm Head n → Tm Head n → Bool)

/-- Substitute the same actual image certificates through two checked
assemblies of a supported source expression. The images and the resulting
expressions need not be structurally supported. Acceptance of the transformed
codes is supplied separately by the existing `check_substitute` theorem. -/
theorem assemble_substitute_supported_values
    {context : Ctx Head n} {subject firstType secondType : Tm Head n}
    (first second : Code Head ConversionCode n) (a b : Meaning.{u} n)
    (supported : ZFSetTypeExpressionInterpretation.supported subject = true)
    (firstChecked : check R conversionCheck context subject firstType first = true)
    (secondChecked : check R conversionCheck context subject secondType second = true)
    (atFirst : assemble heads constants first subject firstType = some a)
    (atSecond : assemble heads constants second subject secondType = some b)
    (σ : Sub Head n m) (codes : Fin n → Code Head ConversionCode m)
    (images : Fin n → Meaning.{u} m)
    (atImages : ∀ index, assemble heads constants (codes index) (σ index)
      (subst σ (context.lookup index)) = some (images index)) :
    ∃ left right,
      assemble heads constants
        (first.substitute renameConversion substituteConversion σ codes subject firstType)
        (subst σ subject) (subst σ firstType) = some left ∧
      assemble heads constants
        (second.substitute renameConversion substituteConversion σ codes subject secondType)
        (subst σ subject) (subst σ secondType) = some right ∧
      left.value = right.value := by
  obtain ⟨left, atLeft, leftValues, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      first a firstChecked atFirst σ codes images atImages
  obtain ⟨right, atRight, rightValues, _⟩ :=
    assemble_substitute renameConversion substituteConversion heads constants R conversionCheck
      second b secondChecked atSecond σ codes images atImages
  refine ⟨left, right, atLeft, atRight, ?_⟩
  funext env
  rw [leftValues, rightValues, assemble_supported_values heads constants supported atFirst atSecond]

/-- Opening a binder retains agreement between the two particular source
assemblies, even when the supplied argument contains lambdas or projections.
The witnesses are results of the actual `Code.instantiate` algorithm. -/
theorem assemble_instantiate_supported_values
    {context : Ctx Head n} {A argument : Tm Head n}
    {subject firstType secondType : Tm Head (n + 1)}
    (first second : Code Head ConversionCode (n + 1))
    (argumentCode : Code Head ConversionCode n)
    (a b : Meaning.{u} (n + 1)) (argumentMeaning : Meaning.{u} n)
    (supported : ZFSetTypeExpressionInterpretation.supported subject = true)
    (firstChecked : check R conversionCheck (.snoc context A) subject firstType first = true)
    (secondChecked : check R conversionCheck (.snoc context A) subject secondType second = true)
    (atFirst : assemble heads constants first subject firstType = some a)
    (atSecond : assemble heads constants second subject secondType = some b)
    (atArgument : assemble heads constants argumentCode argument A = some argumentMeaning) :
    ∃ left right,
      assemble heads constants
        (Code.instantiate renameConversion substituteConversion subject firstType argument first argumentCode)
        (inst0 argument subject) (inst0 argument firstType) = some left ∧
      assemble heads constants
        (Code.instantiate renameConversion substituteConversion subject secondType argument second argumentCode)
        (inst0 argument subject) (inst0 argument secondType) = some right ∧
      left.value = right.value := by
  obtain ⟨left, atLeft, leftValues⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      first argumentCode a argumentMeaning firstChecked atFirst atArgument
  obtain ⟨right, atRight, rightValues⟩ :=
    assemble_instantiate renameConversion substituteConversion heads constants R conversionCheck
      second argumentCode b argumentMeaning secondChecked atSecond atArgument
  refine ⟨left, right, atLeft, atRight, ?_⟩
  funext env
  rw [leftValues, rightValues, assemble_supported_values heads constants supported atFirst atSecond]

omit [DecidableEq Head] in
/-- The source support hypothesis does not imply support of the instantiated
expression. In particular, the two transport laws above include this case. -/
theorem supported_source_with_unsupported_lambda_instance :
    ZFSetTypeExpressionInterpretation.supported (.var 0 : Tm Head 1) = true ∧
      ZFSetTypeExpressionInterpretation.supported
        (inst0 (.lam (.var 0) : Tm Head 0) (.var 0)) = false :=
  ⟨rfl, rfl⟩

#print axioms assemble_supported_values
#print axioms assemble_substitute_supported_values
#print axioms assemble_instantiate_supported_values
#print axioms supported_source_with_unsupported_lambda_instance

end ZFSetReplayInterpretation
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
