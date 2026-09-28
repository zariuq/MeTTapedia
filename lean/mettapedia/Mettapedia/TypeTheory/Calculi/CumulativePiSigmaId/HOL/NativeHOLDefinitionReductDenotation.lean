import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.HOLDefinitionAdmission
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLImpredicativeDenotation

/-!
# Source-definition admission and the denotation of its native δ target

The existing declaration checker admits a fresh closed HOL definition and its
operational rule unfolds the native name to the translated body. The total
signature denotation independently interprets that exact reduct as the source
body in any later context. This does not yet assign a denotation to the new
native declaration name or assert δ preservation for an arbitrary model of
declarations; that requires a model extension respecting the definition.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLDefinitionReductDenotation

open Mettapedia.Logic
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.FormationSensitiveHOLInterface
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOLImpredicativeRepresentation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLSignatureDenotation
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLImpredicativeDenotation

universe u v w
variable {Base : Type u} {Const : HOL.Ty Base → Type v}

/-- Admission, native unfolding, and the source meaning of the *reduct* are
joined for every typed closed source body. In particular, the body may contain
derived connectives that the partial primitive representation alone rejects. -/
theorem admitted_definition_delta_target
    (signature : LogicalSignature Base Const)
    (model : HOL.HenkinModel.{u, v, w} Base Const)
    (name : DeclName) {type : HOL.Ty Base} (body : HOL.Term Const [] type)
    (fresh : signature.rules.constantType name = none)
    (gamma : HOL.Ctx Base) :
    DeclarationAdmissionReplay.Admitted signature.rules []
      (HOLDefinitionAdmission.declarations signature name body) ∧
    Step (HOLDefinitionAdmission.rules signature name body).headEq
      (.const name : Tower.Tm gamma.length)
      (liftClosed (translate signature body))
      (HOLDefinitionAdmission.rules signature name body).computation ∧
    Denotes signature model (gamma := gamma) (type := type)
      (liftClosed (translate signature body))
      (fun _ => model.denote body (fun index => nomatch index)) := by
  exact ⟨HOLDefinitionAdmission.admitted signature name body fresh,
    HOLDefinitionAdmission.delta signature name body,
    translate_closed_denotes signature model body gamma⟩

#print axioms admitted_definition_delta_target

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLDefinitionReductDenotation
