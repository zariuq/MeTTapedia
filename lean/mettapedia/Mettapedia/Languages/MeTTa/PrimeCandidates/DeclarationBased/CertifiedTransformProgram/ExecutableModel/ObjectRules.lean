import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel.Rules
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.SetProfile.InstanceNames
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Impredicative.Package

/-!
# The object package: the executable package with the program's codes

The program's propositions are codes over the executable package:
implication, and the quantifier `all@A` and the equation `eq@A` at every
simple type `A` over `prop`, the numbers and the sets, decoded under the
identity reading. The instance names are read by the profile's parser, and the
instances are declared at the profile's own types, so the package declares
every quantifier and equation instance exactly as the profile's signature
does.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation
open Presentation.TypedEquality
open Presentation.TypedEquality.Normalization
open Presentation.TypedEquality.Impredicative
open Mettapedia.Logic

namespace CodeModel

/-! ## The names of the codes -/

abbrev propN : DeclName := SetProfile.propName
abbrev holdsN : DeclName := SetProfile.holdsName
abbrev impN : DeclName := SetProfile.impName
abbrev allNumN : DeclName := SetProfile.allName SetProfile.numTy
abbrev allPredN : DeclName := SetProfile.allName (.arr SetProfile.numTy .prop)
abbrev eqNumN : DeclName := SetProfile.eqName SetProfile.numTy

/-! ## The codes and the object package -/

/-- A simple type of the profile as a closed type of the package. -/
abbrev typeTerm (type : HOL.Ty SetProfile.SetBase) : Tower.Tm 0 :=
  FormationSensitiveHOLInterface.typeAt SetProfile.types 0 type

/-- The program's proposition codes: implication, and a quantifier and an
equation at every simple type of the profile, with the identity reading. -/
def programCodes : Codes Tower.Head where
  proofs := .sort Tower.zero
  prop := propN
  holds := holdsN
  imp := impN
  quantifiers := fun name => (SetProfile.allInstance? name).map typeTerm
  equations := fun name => (SetProfile.eqInstance? name).map typeTerm
  identity := true

/-- The executable package with the program's codes and their decoding. -/
abbrev objectRules : Rules Tower.Head := programCodes.extend rules

/-! ## The instances are the profile's -/

theorem allName_ne_codes (type : HOL.Ty SetProfile.SetBase) :
    SetProfile.allName type ≠ propN ∧ SetProfile.allName type ≠ holdsN ∧
      SetProfile.allName type ≠ impN := by
  have found := SetProfile.allInstance?_allName type
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, SetProfile.allInstance?_propName] at found; cases found
  · rw [h, SetProfile.allInstance?_holdsName] at found; cases found
  · rw [h, SetProfile.allInstance?_impName] at found; cases found

theorem eqName_ne_codes (type : HOL.Ty SetProfile.SetBase) :
    SetProfile.eqName type ≠ propN ∧ SetProfile.eqName type ≠ holdsN ∧
      SetProfile.eqName type ≠ impN := by
  have found := SetProfile.eqInstance?_eqName type
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [h, SetProfile.eqInstance?_propName] at found; cases found
  · rw [h, SetProfile.eqInstance?_holdsName] at found; cases found
  · rw [h, SetProfile.eqInstance?_impName] at found; cases found

/-- The package declares `all@A` at the profile's type of `all@A`. -/
theorem declared_allName (type : HOL.Ty SetProfile.SetBase) :
    objectRules.constantType (SetProfile.allName type) = some (SetProfile.allType type) := by
  refine programCodes.extend_constantType_of_code rules ?_
  have carrier : programCodes.quantifiers (SetProfile.allName type) = some (typeTerm type) := by
    change (SetProfile.allInstance? (SetProfile.allName type)).map typeTerm = some (typeTerm type)
    rw [SetProfile.allInstance?_allName]
    rfl
  rw [programCodes.codeType_all (allName_ne_codes type) carrier]
  rfl

/-- The package declares `eq@A` at the profile's type of `eq@A`. -/
theorem declared_eqName (type : HOL.Ty SetProfile.SetBase) :
    objectRules.constantType (SetProfile.eqName type) = some (SetProfile.eqType type) := by
  refine programCodes.extend_constantType_of_code rules ?_
  obtain ⟨hp, hh, hi⟩ := eqName_ne_codes type
  have noAll : programCodes.quantifiers (SetProfile.eqName type) = none := by
    change (SetProfile.allInstance? (SetProfile.eqName type)).map typeTerm = none
    rw [SetProfile.allInstance?_eqName]
    rfl
  have carrier : programCodes.equationCarrier (SetProfile.eqName type) = some (typeTerm type) := by
    change (if true = true then (SetProfile.eqInstance? (SetProfile.eqName type)).map typeTerm
      else none) = some (typeTerm type)
    rw [if_pos rfl, SetProfile.eqInstance?_eqName]
    rfl
  have form : programCodes.eqType (typeTerm type) = SetProfile.eqType type := by
    change Tm.pi (typeTerm type) (Tm.pi (Presentation.rename wk (typeTerm type)) (.const propN)) =
      FormationSensitiveHOLInterface.typeAt SetProfile.types 0 (.arr type (.arr type .prop))
    rw [typeTerm, FormationSensitiveHOLInterface.typeAt_rename]
    rfl
  have hp' : SetProfile.eqName type ≠ programCodes.prop := hp
  have hh' : SetProfile.eqName type ≠ programCodes.holds := hh
  have hi' : SetProfile.eqName type ≠ programCodes.imp := hi
  simp only [Codes.codeType, hp', hh', hi', if_false, noAll, carrier, Option.map_some, form]

end CodeModel

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.ExecutableModel
