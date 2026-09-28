import Mettapedia.Languages.Agda.Structural.AdministrativeAdmission
import Mettapedia.Languages.Agda.Structural.AdministrativeStaticControls
import Mettapedia.Languages.Agda.Structural.StaticRegularityControls

/-!
# Dependent and administrative endpoint controls

Changing an argument changes its dependent result code. Recovering the right
action therefore requires an actual type conversion. Other controls exercise
append factorization through conversion wrappers, formation from nested
elimination equality, and context conversion using a newly added equality.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.RegularityControls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.Languages.Agda.Structural.AdministrativeStatics.Controls

abbrev family : Statics.TypeBody 0 := Statics.RegularityControls.family

noncomputable def inputFormed : CoreDerivation (Statics.formed empty (Statics.piType domain family).code) :=
  includeCanonical (Statics.canonicalOperations.piFormed
    Statics.RegularityControls.domainFormed Statics.RegularityControls.familyFormed)

noncomputable def argumentEquality : SpineEq empty (Statics.piType domain family).code
    (cons (apply expanded) nil) (cons (apply contracted) nil) (family.instantiate expanded).code :=
  Derivation.spineCons betaEqual (Derivation.spineRefl (Derivation.nil empty _))

noncomputable def argumentEndpoints : SpineEndpoints empty (Statics.piType domain family).code
    (cons (apply expanded) nil) (cons (apply contracted) nil) (family.instantiate expanded).code :=
  argumentEquality.endpoints inputFormed

/-- The right action ends at the left argument's result type, via conversion. -/
noncomputable def convertedRightAction : Action empty (Statics.piType domain family).code
    (cons (apply contracted) nil) (family.instantiate expanded).code := argumentEndpoints.right

theorem dependent_results_are_not_raw_equal :
    (family.instantiate expanded).code ≠ (family.instantiate contracted).code := by
  intro same
  cases same

noncomputable def rightActionOutputFormed : CoreDerivation (Statics.formed empty (family.instantiate expanded).code) :=
  convertedRightAction.outputFormation inputFormed

noncomputable def nestedEndpoints := orderedNestedEquality.termEndpoints

noncomputable def consPrefixEndpoints := consPrefixEquality.endpoints (CoreDerivation.typingFormation functionTyped)

noncomputable def emptyPrefixEndpoints := emptyPrefixEquality.endpoints (CoreDerivation.typingFormation functionTyped)

/-- Both boundaries genuinely change their raw annotation term. -/
noncomputable def wrappedEmptyAppend : Action empty
    (el (set (levelClosed 1)) (eliminate contracted nil)) (append nil nil)
    (el (set (levelClosed 1)) (eliminate contracted nil)) :=
  Derivation.inputConversion administrativeTypeEquality
    (Derivation.outputConversion (Derivation.append (Derivation.nil empty _) (Derivation.nil empty _))
      (administrativeOperations.typeSymmetry administrativeTypeEquality))

noncomputable def factoredWrappedEmpty := wrappedEmptyAppend.splitAppend
noncomputable def contractedWrappedEmpty := wrappedEmptyAppend.dropEmptyAppend
noncomputable def wrappedEquality := Derivation.appendEmpty wrappedEmptyAppend
noncomputable def wrappedEndpoints := wrappedEquality.endpoints administrativeTypeEquality.typeEndpoints.left

def leftContext : Statics.RawContext 1 :=
  empty.snoc (el (set (levelClosed 1)) (eliminate contracted nil))
def rightContext : Statics.RawContext 1 := empty.snoc (el (set (levelClosed 1)) contracted)

noncomputable def changedContext : ContextConversion leftContext rightContext :=
  .snoc .nil administrativeTypeEquality

noncomputable def changedContextSubstitution := changedContext.identitySubstitution

noncomputable def leftVariable : CoreDerivation
    (Statics.typed leftContext (.var .zero) (ContextGeometry.lookup leftContext .zero)) :=
  administrativeOperations.build (.variable leftContext .zero)
    (consEvidence CoreDerivation
      (administrativeOperations.extend (includeCanonical Statics.Derivation.empty)
        administrativeTypeEquality.typeEndpoints.left) (noEvidence CoreDerivation))

noncomputable def variableInChangedContext : CoreDerivation
    (Statics.typed rightContext (.var .zero) (ContextGeometry.lookup leftContext .zero)) :=
  changedContext.typing leftVariable

theorem changed_context_syntax_distinct : leftContext ≠ rightContext := by
  intro same
  cases same

noncomputable def admittedLeft : administrativeAdmission.Context :=
  ⟨⟨1, leftContext⟩, ⟨changedContextSubstitution.source⟩⟩

noncomputable def admittedRight : administrativeAdmission.Context :=
  ⟨⟨1, rightContext⟩, ⟨changedContextSubstitution.target⟩⟩

/-- The supported arrow has identity raw images but distinct dependent contexts. -/
noncomputable def admittedContextConversion :
    administrativeAdmission.Substitution admittedRight admittedLeft :=
  ⟨Telescope.identity (S := sig) .term 1, ⟨changedContextSubstitution⟩⟩

theorem admitted_contexts_remain_distinct : admittedLeft ≠ admittedRight := by
  intro same
  have raw := congrArg Subtype.val same
  have contextEq : HEq leftContext rightContext := (Sigma.mk.inj raw).2
  exact changed_context_syntax_distinct (eq_of_heq contextEq)

theorem unsupported_equality_still_cannot_supply_formation :
    Nonempty (SpineEq empty unsupportedType nil nil unsupportedType) ∧
      ¬ Nonempty (CoreDerivation (Statics.formed empty unsupportedType)) :=
  conditional_equality_does_not_supply_formation

end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.RegularityControls
