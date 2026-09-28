import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.Execution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.FormationSensitiveHOLIdentityEquality

/-!
# The identity interpretation of the program's equality

A separately named interpretation profile of the certified-transform program.
The proof family at a represented equation `eq@T a b` computes to the identity
type `Id T a b`; the program's declarations and equations are unchanged.  The
profile adds this one decoding equation and no constant.

The source document's assumptions stay declared under their names.  The
profile realizes each by a typed program (`Realizations`), and the retained
source proof of `zero-add`, linked against the realizations, is identity
evidence at every index (`Translation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration Presentation.FormationSensitive
open Presentation.ConversionCoherence
open SetProfile (numTy holdsName)
open CertifiedTransformProgram.Package
open FormationSensitiveHOLIdentityEquality (DeclaredEquality IdentityStep interpret
  interpretMorphism interpret_decodes)

/-- The profile's equality is the declared `eq@T`. -/
def equality : DeclaredEquality SetProfile.signature where
  equalityName := SetProfile.eqName
  equality_eq := fun _ => rfl
  equality_lookup := SetProfile.lookup_eqName

/-- The program with represented equations read as identity types. -/
noncomputable abbrev identityRules : Rules Tower.Head :=
  interpret packageRules SetProfile.signature holdsName

theorem packageToIdentity : packageRules.Morphism identityRules (fun head => head) :=
  interpretMorphism packageRules SetProfile.signature holdsName

theorem proofToIdentity :
    (FormationSensitiveHOLGenericProofFamily.rules SetProfile.signature holdsName).Morphism
      identityRules (fun head => head) :=
  proofToPackage.comp packageToIdentity

theorem identity_decodes {n : Nat} {left right : Tower.Tm n}
    (step : IdentityStep SetProfile.signature holdsName left right) :
    identityRules.computation.step left right :=
  interpret_decodes packageRules SetProfile.signature holdsName step

/-- Judgments of the program hold in the profile. -/
theorem toIdentity {n : Nat} {Γ : Tower.Ctx n} {term type : Tower.Tm n}
    (typing : Typing R Γ term type) : Typing identityRules Γ term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using typing.mapHead packageToIdentity

theorem toIdentity_conversion {n : Nat} {left right : Tower.Tm n}
    (conversion : Conv R.headEq left right R.computation) :
    Conv identityRules.headEq left right identityRules.computation := by
  simpa only [Tm.mapHead_id] using
    conversion.mapHead (fun head => head) packageToIdentity.headEq packageToIdentity.computation

theorem toIdentity_runs {n : Nat} {left right : Tower.Tm n}
    (runs : StepStar identityRules left right) :
    Conv identityRules.headEq left right identityRules.computation :=
  stepStar_implies_conv runs

#print axioms packageToIdentity
#print axioms proofToIdentity
#print axioms toIdentity

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.CertifiedTransformProgram.IdentityEquality
