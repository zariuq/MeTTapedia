import Mettapedia.Languages.Agda.Adequacy.AdministrativeReflection
import Mettapedia.Languages.Agda.Structural.AdministrativeStaticControls
import Mettapedia.Languages.Agda.StaticSpecification.Examples

/-!
# Controls for reflection of native administrative derivations

Native constructors build administrative syntax beneath two binders and inside
changing dependent type codes. Reflection returns source proofs for those
actual trees. Unsupported projections are ruled out even in arbitrary native
contexts. Distinct conversion histories can yield the same source proof.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection.Controls

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Mettapedia.TypeTheory
open Structural
open Structural.Statics (RawTm RawTy RawContext TypeParameter TypeBody)
open Structural.AdministrativeStatics

abbrev nativeEmpty := (Telescope.RawContext.nil : RawContext 0)
abbrev nativeDomain (n : Nat) := Statics.universeType n 1
abbrev nativeOne := Statics.Boundary.oneContext
abbrev nativeTwo := nativeOne.snoc (nativeDomain 1).code

noncomputable def oneFormed := includeCanonical Statics.Boundary.oneContextFormed
noncomputable def twoFormed : CoreDerivation (Statics.context nativeTwo) :=
  administrativeOperations.extend oneFormed
    (includeCanonical (Statics.Boundary.universeFormed Statics.Boundary.oneContextFormed 1))

noncomputable def olderTyped : CoreDerivation (Statics.typed nativeTwo (.var (.succ .zero)) (nativeDomain 2).code) :=
  Derivation.core (.variable nativeTwo (.succ .zero)) (consEvidence CoreDerivation twoFormed (noEvidence CoreDerivation))

noncomputable def olderAdministrative : CoreDerivation
    (Statics.typed nativeTwo (eliminate (.var (.succ .zero)) nil) (nativeDomain 2).code) :=
  Derivation.elimination olderTyped (Derivation.nil nativeTwo _)

def innerBody : Statics.TermBody 1 := .bind (eliminate (.var (.succ .zero)) nil)
def innerType : TypeParameter 1 := Statics.piType (nativeDomain 1) (.noBind (nativeDomain 1))

noncomputable def innerTyped : CoreDerivation (Statics.typed nativeOne innerBody.lambda innerType.code) :=
  Derivation.core (.lambda nativeOne (nativeDomain 1) (.noBind (nativeDomain 1)) innerBody)
    (consEvidence CoreDerivation
      (includeCanonical (Statics.Boundary.universeFormed Statics.Boundary.oneContextFormed 1))
      (consEvidence CoreDerivation (administrativeOperations.universeFormed twoFormed 1)
        (consEvidence CoreDerivation olderAdministrative (noEvidence CoreDerivation))))

def nestedNative : RawTm 0 := lam innerBody.lambda

def constantType : TypeParameter 0 := SpineStatics.Controls.doubleArrow

noncomputable def nestedNativeTyped : CoreDerivation (Statics.typed nativeEmpty nestedNative constantType.code) :=
  Derivation.core (.lambda nativeEmpty (nativeDomain 0) (.noBind SpineStatics.Controls.arrow) (.bind innerBody.lambda))
    (consEvidence CoreDerivation AdministrativeStatics.Controls.domainFormed
      (consEvidence CoreDerivation
        (includeCanonical (SpineStatics.Controls.arrowFormed Statics.Boundary.oneContextFormed))
        (consEvidence CoreDerivation innerTyped (noEvidence CoreDerivation))))

noncomputable def reflectedNested : StaticSpecification.Typing .nil
    StaticSpecification.Examples.constantFunction StaticSpecification.Examples.constantFunctionType :=
  (interpret nestedNativeTyped .nil rfl).at rfl rfl

theorem nested_native_is_not_canonical : nestedNative ≠ embedTerm StaticSpecification.Examples.constantFunction := by
  intro same
  cases same

theorem nested_observation_keeps_the_older_variable :
    Observation.term nestedNative = some StaticSpecification.Examples.constantFunction := rfl

theorem nested_observation_does_not_capture :
    Observation.term nestedNative ≠ some (StaticSpecification.Term.lam (.bind (.lam (.bind (.var 0))))) := by
  intro same
  cases same

/-- The native functionality tree changes administrative type annotations. -/
noncomputable def reflectedDependentEquality : StaticSpecification.TypeEq .nil
    (.el 1 (StaticSpecification.Examples.closedIdentity.app (.sort 0))) (.el 1 (.sort 0)) :=
  (interpret AdministrativeStatics.Controls.changedAdministrativeType .nil rfl).at rfl rfl

theorem dependent_source_codes_stay_distinct :
    (StaticSpecification.Ty.el 1 (StaticSpecification.Examples.closedIdentity.app (.sort 0))) ≠
      (.el 1 (.sort 0) : StaticSpecification.Ty 0) := by
  intro same
  cases same

noncomputable def reflectedEmptyEquality : StaticSpecification.TermEq .nil (.sort 0) (.sort 0)
    (StaticSpecification.Ty.universe 1) :=
  (interpret AdministrativeStatics.Controls.emptyAdministrativeEquality .nil rfl).at rfl rfl rfl

noncomputable def reflectedInheritedTypeEquality : StaticSpecification.TypeEq .nil
    (.universe 0) (.universe 0) :=
  (interpret AdministrativeStatics.Controls.administrativeTypeEquality .nil rfl).at rfl rfl

noncomputable def upperTyped : CoreDerivation
    (Statics.typed nativeEmpty (Statics.universeTerm 1) (Statics.universeType 0 2).code) :=
  includeCanonical (Statics.Derivation.sort 1 Statics.Derivation.empty)

noncomputable def upperTypeEquality : CoreDerivation (Statics.typeEqual nativeEmpty
    (el (set (levelClosed 2)) (eliminate (Statics.universeTerm 1) nil)) (Statics.universeType 0 1).code) :=
  Derivation.core (.typeEquality nativeEmpty 2 (eliminate (Statics.universeTerm 1) nil) (Statics.universeTerm 1))
    (consEvidence CoreDerivation (Derivation.emptyElimination upperTyped) (noEvidence CoreDerivation))

noncomputable def inputHistory := Derivation.inputConversion upperTypeEquality (Derivation.nil nativeEmpty _)
noncomputable def outputHistory := Derivation.outputConversion (Derivation.nil nativeEmpty _) upperTypeEquality

theorem conversion_histories_differ : inputHistory ≠ outputHistory := by
  intro same
  have shapes := (IndexedPolynomial.Fix.roll.inj same).1
  cases shapes

noncomputable def inputSourceProof : StaticSpecification.Typing .nil (.sort 0) (.universe 1) :=
  (interpret inputHistory .nil rfl (.universe 1) rfl).proof (.sort 0 .nil)

noncomputable def outputSourceProof : StaticSpecification.Typing .nil (.sort 0) (.universe 1) :=
  (interpret outputHistory .nil rfl (.universe 1) rfl).proof (.sort 0 .nil)

theorem distinct_histories_can_have_the_same_source_proof : inputSourceProof = outputSourceProof := rfl

/-- Total reflection excludes projection use even beyond the embedded image. -/
theorem projection_elimination_has_no_typing {n : Nat} (Γ : RawContext n) (f : RawTm n) (A : RawTy n) :
    ¬ Nonempty (CoreDerivation (Statics.typed Γ (eliminate f (cons (proj "field") nil)) A)) := by
  rintro ⟨tree⟩
  have observed := (reflectTyping tree).typing.observed
  change ((Observation.term f).bind fun head => (none : Option (StaticSpecification.Spine n)).bind
    (fun spine => some (head.applySpine spine))) = some _ at observed
  cases h : Observation.term f <;> rw [h] at observed <;> cases observed

/-- Observation success alone does not make a malformed telescope admissible. -/
theorem malformed_embedded_context_has_no_typing (t : RawTm 1) (A : RawTy 1) :
    ¬ Nonempty (CoreDerivation
      (Statics.typed (embedContext StaticSpecification.Examples.malformedTelescope) t A)) := by
  rintro ⟨tree⟩
  exact StaticSpecification.Examples.malformed_telescope_rejected
    ⟨contextBack tree.contextOfTyping⟩

theorem observed_wrong_annotation_remains_unformed :
    ¬ Nonempty (CoreDerivation (Statics.formed nativeEmpty
      (embedTy (StaticSpecification.Ty.el 0 (.sort 0))))) := by
  rintro ⟨tree⟩
  exact StaticSpecification.Examples.wrong_annotation_rejected ⟨formationBack (Γ := .nil) tree⟩

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection.Controls
