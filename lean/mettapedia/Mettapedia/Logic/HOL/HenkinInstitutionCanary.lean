import Mettapedia.Logic.HOL.HenkinInstitutionDerivation
import Mettapedia.Logic.HOL.Semantics.ModelProperties

/-!
# Discriminators for the fixed-base Henkin institution

The positive example checks the satisfaction square for a signature map that
identifies two constants.  The negative example proves that this same map does
not reflect validity: after translation the two constants are syntactically
the same, while an extensional source model keeps their interpretations
distinct.  Thus arbitrary signature maps are institution morphisms without
silently becoming conservative embeddings.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.HenkinInstitution.Canary

open CategoryTheory
open scoped CategoryTheory

/-- Source signature with two constants of one base type. -/
inductive TwoConstants : Ty Unit → Type
  | left : TwoConstants (.base ())
  | right : TwoConstants (.base ())

/-- Target signature with one constant of the same base type. -/
inductive OneConstant : Ty Unit → Type
  | point : OneConstant (.base ())

def sourceSignature : Signature Unit := ⟨TwoConstants⟩

def targetSignature : Signature Unit := ⟨OneConstant⟩

/-- A non-injective signature translation identifying the two source
constants. -/
def collapse : sourceSignature ⟶ targetSignature where
  map
    | .left => .point
    | .right => .point

/-- Equality of the two distinct source constants. -/
def sourceEquation : ClosedFormula TwoConstants :=
  .eq (.const .left) (.const .right)

/-- Equality of the unique target constant with itself. -/
def targetEquation : ClosedFormula OneConstant :=
  .eq (.const .point) (.const .point)

@[simp]
theorem translate_sourceEquation :
    (sentence.map collapse) sourceEquation = targetEquation :=
  rfl

/-- Positive control: truth commutes with translation and reduct even for a
non-injective signature morphism. -/
theorem collapse_satisfaction_square (targetModel : Model targetSignature) :
    targetModel.henkin.models targetEquation ↔
      (Model.reduct collapse targetModel).henkin.models sourceEquation := by
  rw [← translate_sourceEquation]
  exact (HenkinModel.models_reduct collapse targetModel.henkin
    sourceEquation).symm

/-- The translated reflexive equation is valid in every target model. -/
theorem targetEquation_valid :
    (institution Unit).Valid targetSignature targetEquation := by
  intro wrappedModel _modelsEmpty
  let targetModel :=
    (show CategoryTheory.Discrete (Model targetSignature) from
      wrappedModel).as
  change targetModel.henkin.Eqv (.base ())
    (targetModel.henkin.constDen OneConstant.point)
    (targetModel.henkin.constDen OneConstant.point)
  exact targetModel.henkin.eqv_refl
    (targetModel.henkin.const_mem OneConstant.point)

inductive LiftedBool : Type 1
  | false
  | true

abbrev BooleanCarrier : Unit → Type 1 := fun _ => LiftedBool

def sourceConstantDenotation :
    {type : Ty Unit} → TwoConstants type →
      Ty.denote.{0, 0} BooleanCarrier type
  | _, .left => .false
  | _, .right => .true

/-- A standard extensional model separating the two source constants. -/
def separatingHenkinModel :
    HOL.HenkinModel.{0, 0, 0} Unit TwoConstants :=
  HOL.HenkinModel.standard BooleanCarrier sourceConstantDenotation

theorem separatingHenkinModel_fullDomains :
    separatingHenkinModel.FullDomains :=
  HOL.HenkinModel.fullDomains_standard BooleanCarrier
    sourceConstantDenotation

def separatingModel : Model sourceSignature where
  henkin := separatingHenkinModel
  functionsRespectEqv :=
    separatingHenkinModel.functionsRespectEqv_of_fullDomains
      separatingHenkinModel_fullDomains

/-- Negative semantic control: the source equation is false when the two
constants denote different Boolean values. -/
theorem separatingModel_refutes_sourceEquation :
    ¬separatingModel.henkin.models sourceEquation := by
  change ¬sourceConstantDenotation TwoConstants.left =
    sourceConstantDenotation TwoConstants.right
  intro equal
  cases equal

/-- The source equation is therefore not valid. -/
theorem sourceEquation_not_valid :
    ¬(institution Unit).Valid sourceSignature sourceEquation := by
  intro valid
  exact separatingModel_refutes_sourceEquation <|
    valid (CategoryTheory.Discrete.mk separatingModel) <| by
      intro premise membership
      exact False.elim membership

/-- Proof-theoretic negative control: soundness and the separating model rule
out a derivation of the false source equation from no premises. -/
theorem sourceEquation_not_provable :
    ¬ClosedTheorySet.Provable (∅ : ClosedTheorySet TwoConstants)
      sourceEquation := by
  intro derivation
  exact sourceEquation_not_valid (provable_entails derivation)

/-- A general institution translation preserves validity forward, but this
non-injective translation cannot reflect it. -/
theorem collapse_does_not_reflect_validity :
    (institution Unit).Valid targetSignature
        (sentence.map collapse sourceEquation) ∧
      ¬(institution Unit).Valid sourceSignature sourceEquation := by
  simpa using And.intro targetEquation_valid sourceEquation_not_valid

#print axioms collapse_satisfaction_square
#print axioms targetEquation_valid
#print axioms separatingModel_refutes_sourceEquation
#print axioms sourceEquation_not_valid
#print axioms sourceEquation_not_provable
#print axioms collapse_does_not_reflect_validity

end Mettapedia.Logic.HOL.HenkinInstitution.Canary
