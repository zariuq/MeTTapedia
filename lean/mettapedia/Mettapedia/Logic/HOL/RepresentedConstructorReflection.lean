import Mettapedia.Logic.HOL.ConstructorFieldRepresentation
import Mettapedia.Logic.HOL.ConstructorPayloadTransport

/-!
# Constructor reflection with a constructed field retraction

The field recovery law is derived from actual encoding and decoding programs.
The constructor law and the two selection principles remain distinct provider
inputs. Source fields must belong to the embedding's image; no global decoder
law or full-domain source constructor injectivity is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.RepresentedConstructorReflection
open MixedConstructorPayloadMaps ConstructorFieldRepresentation
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base}
    {number element branches carrier : Ty Base} {Δ : List (Formula Const Γ)}

def fieldLaw (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw)) :
    ProofSyntax Const Δ (GuardedRetraction.law (decoder raw payloadSelection fieldSelection)
      (embedding raw marker fixedBranches) (image (embedding raw marker fixedBranches))) :=
  image_retraction _ _ (roundtrip_law raw marker fixedBranches payloadSelection fieldSelection payloadChoice fieldChoice injectivity)

theorem fieldLaw_free (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element))
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (pcFree : payloadChoice.FunctionExtensionalityFree) (fcFree : fieldChoice.FunctionExtensionalityFree)
    (ciFree : injectivity.FunctionExtensionalityFree) :
    (fieldLaw raw marker fixedBranches payloadSelection fieldSelection payloadChoice fieldChoice injectivity).FunctionExtensionalityFree :=
  image_retraction_free _ _ _ (roundtrip_law_free _ _ _ _ _ _ _ _ pcFree fcFree ciFree)

def reflect (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element))
    (firstTag secondTag firstIndex secondIndex : Term Const Γ number)
    (firstElement secondElement : Term Const Γ carrier) (firstShape secondShape : Term Const Γ number)
    (firstChildren secondChildren : Term Const Γ branches)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (firstValid : ProofSyntax Const Δ (.app (image (embedding raw marker fixedBranches)) firstElement))
    (secondValid : ProofSyntax Const Δ (.app (image (embedding raw marker fixedBranches)) secondElement))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (ConstructorPayloadTransport.constructor raw (decoder raw payloadSelection fieldSelection))
        secondTag (pack secondIndex secondElement secondShape) secondChildren)
      (ConstructorProjections.apply (ConstructorPayloadTransport.constructor raw (decoder raw payloadSelection fieldSelection))
        firstTag (pack firstIndex firstElement firstShape) firstChildren))) :
    ProofSyntax Const Δ (.and (.eq (pack secondIndex secondElement secondShape) (pack firstIndex firstElement firstShape))
      (.eq secondChildren firstChildren)) :=
  ConstructorPayloadTransport.reflectGuarded raw (decoder raw payloadSelection fieldSelection)
    (embedding raw marker fixedBranches) (image (embedding raw marker fixedBranches))
    firstTag secondTag firstIndex secondIndex firstElement secondElement firstShape secondShape firstChildren secondChildren
    injectivity (fieldLaw raw marker fixedBranches payloadSelection fieldSelection payloadChoice fieldChoice injectivity)
    firstValid secondValid same

theorem reflect_free (raw : Term Const Γ (Raw number element branches carrier))
    (marker : Term Const Γ number) (fixedBranches : Term Const Γ branches)
    (payloadSelection : Term Const Γ (SelectionProofs.Selection (Payload number element)))
    (fieldSelection : Term Const Γ (SelectionProofs.Selection element))
    (firstTag secondTag firstIndex secondIndex : Term Const Γ number)
    (firstElement secondElement : Term Const Γ carrier) (firstShape secondShape : Term Const Γ number)
    (firstChildren secondChildren : Term Const Γ branches)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle fieldSelection))
    (injectivity : ProofSyntax Const Δ (ConstructorProjections.fieldInjective raw))
    (firstValid : ProofSyntax Const Δ (.app (image (embedding raw marker fixedBranches)) firstElement))
    (secondValid : ProofSyntax Const Δ (.app (image (embedding raw marker fixedBranches)) secondElement))
    (same : ProofSyntax Const Δ (.eq
      (ConstructorProjections.apply (ConstructorPayloadTransport.constructor raw (decoder raw payloadSelection fieldSelection))
        secondTag (pack secondIndex secondElement secondShape) secondChildren)
      (ConstructorProjections.apply (ConstructorPayloadTransport.constructor raw (decoder raw payloadSelection fieldSelection))
        firstTag (pack firstIndex firstElement firstShape) firstChildren)))
    (pcFree : payloadChoice.FunctionExtensionalityFree) (fcFree : fieldChoice.FunctionExtensionalityFree)
    (ciFree : injectivity.FunctionExtensionalityFree) (firstFree : firstValid.FunctionExtensionalityFree)
    (secondFree : secondValid.FunctionExtensionalityFree) (sameFree : same.FunctionExtensionalityFree) :
    (reflect raw marker fixedBranches payloadSelection fieldSelection firstTag secondTag firstIndex secondIndex
      firstElement secondElement firstShape secondShape firstChildren secondChildren
      payloadChoice fieldChoice injectivity firstValid secondValid same).FunctionExtensionalityFree :=
  ConstructorPayloadTransport.reflectGuarded_free _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ciFree
    (fieldLaw_free _ _ _ _ _ _ _ _ pcFree fcFree ciFree) firstFree secondFree sameFree

#print axioms fieldLaw
#print axioms reflect
#print axioms reflect_free
end Mettapedia.Logic.HOL.RepresentedConstructorReflection
