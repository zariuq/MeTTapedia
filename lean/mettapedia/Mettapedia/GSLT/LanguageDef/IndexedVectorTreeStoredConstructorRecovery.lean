import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFieldGuards
import Mettapedia.Logic.HOL.ConstructorArgumentMap
import Mettapedia.Logic.HOL.ConstructorGuardSubstitution
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionTransport
import Mettapedia.Logic.HOL.ConstructorAdmissionGuardTransport

/-!
# Recovery for the complete parsed stored Vector-tree constructor

The stored constructor lowers the complete solved/branch payload to the raw
signature. Its admission comes from the actual parsed field and position
programs. Original shape and padding evidence expose the payload guard;
primitive field recovery then fixes the whole admitted payload.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecovery
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding IndexedConstructorGuards
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {N A E : Ty Base} {Δ : List (Formula Const Γ)}

def storedConstructor (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E) :
    Term Const Γ (N ⇒ payloadType (VectorTreeFieldEmbedding.storedSignature N E) ⇒ (N ⇒ E) ⇒ E) :=
  ConstructorArgumentMap.constructor given.raw (VectorTreePayloadMaps.lowerProgram given)

theorem storedConstructor_subst (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (images : Subst Const Γ Ξ) :
    HOL.subst images (storedConstructor given) = storedConstructor (given.substitute images) := by
  rw [storedConstructor,ConstructorArgumentMap.constructor_subst,VectorTreePayloadMaps.lowerProgram_subst]
  rfl

def positions (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N) :
    PositionPrograms (IndexedVectorTreeStoredFieldGuards.inventory given source numbers zero one tags) :=
  (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one).positions IndexedVectorTreeStoredFieldGuards.codes Subst.id tags zero successor

def recursiveSignature (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E) : RecursiveSpacePredicate.Contextual Const Γ :=
  (positions given source numbers zero one successor tags).contextual bottom (storedConstructor given)

def domain (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E) :
    Term Const Γ (GuardedConstructorProjections.Admission N
      (payloadType (VectorTreeFieldEmbedding.storedSignature N E)) (N ⇒ E)) :=
  (recursiveSignature given source numbers zero one successor tags bottom).constructorAdmission

def recoverAdmitted (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (tag : Term Const Γ N) (payload : Term Const Γ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)))
    (children : Term Const Γ (N ⇒ E))
    (present : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (domain given source numbers zero one successor tags bottom) tag payload children)) :
    ProofSyntax Const Δ (.eq (.app (VectorTreePayloadMaps.raiseProgram given)
      (.app (VectorTreePayloadMaps.lowerProgram given) payload)) payload) :=
  VectorTreePayloadMaps.recover given source (IndexedVectorTreeStoredFieldGuards.branch numbers zero) payloadChoice fieldChoice rawLaw payload
    ((positions given source numbers zero one successor tags).admissionDataGuard bottom (storedConstructor given)
      (IndexedVectorTreeStoredFieldGuards.conditions given source numbers zero) (IndexedVectorTreeStoredFieldGuards.rowImplication Δ given source numbers zero one tags)
      tag payload children present)

theorem recoverAdmitted_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (tag : Term Const Γ N) (payload : Term Const Γ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)))
    (children : Term Const Γ (N ⇒ E))
    (present : ProofSyntax Const Δ (GuardedConstructorProjections.admitted
      (domain given source numbers zero one successor tags bottom) tag payload children))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (rawFree : rawLaw.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (recoverAdmitted given source numbers zero one successor tags bottom payloadChoice fieldChoice rawLaw
      tag payload children present).FunctionExtensionalityFree := by
  apply VectorTreePayloadMaps.recover_free
  · exact payloadFree
  · exact fieldFree
  · exact rawFree
  · exact (positions given source numbers zero one successor tags).admissionDataGuard_free bottom
      (storedConstructor given) (IndexedVectorTreeStoredFieldGuards.conditions given source numbers zero)
      (IndexedVectorTreeStoredFieldGuards.rowImplication Δ given source numbers zero one tags)
      (IndexedVectorTreeStoredFieldGuards.rowImplication_free Δ given source numbers zero one tags) tag payload children present presentFree

private theorem selectionPrinciple_subst {type : Ty Base}
    (selection : Term Const Γ (SelectionProofs.Selection type)) (images : Subst Const Γ Ξ) :
    HOL.subst images (SelectionProofs.principle selection) =
      SelectionProofs.principle (HOL.subst images selection) := by
  simp only [SelectionProofs.principle,HOL.subst,SelectionProofs.subst_instanceFormula,subst_weaken,Subst.lift]

private def shiftSelection {type : Ty Base}
    (selection : Term Const Γ (SelectionProofs.Selection type))
    (proof : ProofSyntax Const Δ (SelectionProofs.principle selection)) (images : Subst Const Γ Ξ)
    {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) assumptions) :
    ProofSyntax Const assumptions (SelectionProofs.principle (HOL.subst images selection)) :=
  .castIndices rfl (selectionPrinciple_subst selection images) (.mono transport (proof.subst images))

private theorem shiftSelection_free {type : Ty Base}
    (selection : Term Const Γ (SelectionProofs.Selection type))
    (proof : ProofSyntax Const Δ (SelectionProofs.principle selection)) (images : Subst Const Γ Ξ)
    {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) assumptions)
    (free : proof.FunctionExtensionalityFree) :
    (shiftSelection selection proof images transport).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_subst _ _).mpr free))

def payloadGuardAt (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E) (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ N) (payload : Term Const Ξ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)))
    (children : Term Const Ξ (N ⇒ E))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (domain given source numbers zero one successor tags bottom)) tag payload children)) :
    ProofSyntax Const assumptions (ConstructorDataPredicates.guard (VectorTreeFieldEmbedding.storedSignature N E)
      (IndexedVectorTreeStoredFieldGuards.conditions (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) zero) payload) := by
  have result := (positions given source numbers zero one successor tags).admissionDataGuardSubst
    bottom (storedConstructor given) (IndexedVectorTreeStoredFieldGuards.conditions given source numbers zero)
    (IndexedVectorTreeStoredFieldGuards.rowImplication Δ given source numbers zero one tags)
    images transport tag payload children present
  apply ProofSyntax.castIndices rfl ?_ result
  apply congrArg (fun conditions : ConstructorDataPredicates.Conditions Const Ξ
    (VectorTreeFieldEmbedding.storedSignature N E) => ConstructorDataPredicates.guard _ conditions payload)
  funext index
  exact IndexedVectorTreeStoredFieldGuards.conditions_subst given source numbers zero images index

theorem payloadGuardAt_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E) (images : Subst Const Γ Ξ) {assumptions : List (Formula Const Ξ)}
    (transport : ProofSyntax.OccurrenceMap (Δ.map (HOL.subst images)) assumptions)
    (tag : Term Const Ξ N) (payload : Term Const Ξ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)))
    (children : Term Const Ξ (N ⇒ E))
    (present : ProofSyntax Const assumptions (GuardedConstructorProjections.admitted
      (HOL.subst images (domain given source numbers zero one successor tags bottom)) tag payload children))
    (free : present.FunctionExtensionalityFree) :
    (payloadGuardAt given source numbers zero one successor tags bottom images transport
      tag payload children present).FunctionExtensionalityFree := by
  unfold payloadGuardAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (positions given source numbers zero one successor tags).admissionDataGuardSubst_free
    bottom (storedConstructor given) (IndexedVectorTreeStoredFieldGuards.conditions given source numbers zero)
    (IndexedVectorTreeStoredFieldGuards.rowImplication Δ given source numbers zero one tags)
    (IndexedVectorTreeStoredFieldGuards.rowImplication_free Δ given source numbers zero one tags)
    images transport tag payload children present free

def recovery (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw)) :
    ConstructorArgumentMap.Recovery Δ (VectorTreePayloadMaps.lowerProgram given) (VectorTreePayloadMaps.raiseProgram given)
      (domain given source numbers zero one successor tags bottom) := by
  intro Ξ images assumptions transport tag payload children present
  have raw : ProofSyntax Const assumptions (ConstructorProjections.fieldInjective (given.substitute images).raw) :=
    .castIndices rfl (ConstructorProjections.subst_fieldInjective images given.raw)
      (.mono transport (rawLaw.subst images))
  have recovered := VectorTreePayloadMaps.recover (given.substitute images) (HOL.subst images source)
    (IndexedVectorTreeStoredFieldGuards.branch (HOL.subst images numbers) zero)
    (shiftSelection given.payloadSelection payloadChoice images transport)
    (shiftSelection given.fieldSelection fieldChoice images transport) raw payload
    (payloadGuardAt given source numbers zero one successor tags bottom images transport tag payload children present)
  exact .castIndices rfl (by rw [VectorTreePayloadMaps.raiseProgram_subst,VectorTreePayloadMaps.lowerProgram_subst]) recovered

theorem recovery_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (rawFree : rawLaw.FunctionExtensionalityFree) :
    ConstructorArgumentMap.Recovery.Free
      (recovery given source numbers zero one successor tags bottom payloadChoice fieldChoice rawLaw) := by
  intro Ξ images assumptions transport tag payload children present free
  unfold recovery
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply VectorTreePayloadMaps.recover_free
  · exact shiftSelection_free _ _ _ _ payloadFree
  · exact shiftSelection_free _ _ _ _ fieldFree
  · exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr
        ((ProofSyntax.functionExtensionalityFree_subst _ _).mpr rawFree))
  · exact payloadGuardAt_free given source numbers zero one successor tags bottom images transport
      tag payload children present free

def fieldInjective (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw)) :
    ProofSyntax Const Δ (GuardedConstructorProjections.fieldInjective (storedConstructor given)
      (domain given source numbers zero one successor tags bottom)) :=
  ConstructorArgumentMap.fieldInjective given.raw (VectorTreePayloadMaps.lowerProgram given)
    (VectorTreePayloadMaps.raiseProgram given) (domain given source numbers zero one successor tags bottom) rawLaw
    (recovery given source numbers zero one successor tags bottom payloadChoice fieldChoice rawLaw)

theorem fieldInjective_free (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
    (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
    (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N)) (tags : Nat → Term Const Γ N)
    (bottom : Term Const Γ E)
    (payloadChoice : ProofSyntax Const Δ (SelectionProofs.principle given.payloadSelection))
    (fieldChoice : ProofSyntax Const Δ (SelectionProofs.principle given.fieldSelection))
    (rawLaw : ProofSyntax Const Δ (ConstructorProjections.fieldInjective given.raw))
    (payloadFree : payloadChoice.FunctionExtensionalityFree) (fieldFree : fieldChoice.FunctionExtensionalityFree)
    (rawFree : rawLaw.FunctionExtensionalityFree) :
    (fieldInjective given source numbers zero one successor tags bottom payloadChoice fieldChoice rawLaw).FunctionExtensionalityFree :=
  ConstructorArgumentMap.fieldInjective_free given.raw (VectorTreePayloadMaps.lowerProgram given)
    (VectorTreePayloadMaps.raiseProgram given) (domain given source numbers zero one successor tags bottom) rawLaw
    (recovery given source numbers zero one successor tags bottom payloadChoice fieldChoice rawLaw) rawFree
    (recovery_free given source numbers zero one successor tags bottom payloadChoice fieldChoice rawLaw
      payloadFree fieldFree rawFree)

#print axioms storedConstructor_subst
#print axioms recoverAdmitted
#print axioms recoverAdmitted_free
#print axioms payloadGuardAt
#print axioms payloadGuardAt_free
#print axioms recovery
#print axioms recovery_free
#print axioms fieldInjective
#print axioms fieldInjective_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecovery
