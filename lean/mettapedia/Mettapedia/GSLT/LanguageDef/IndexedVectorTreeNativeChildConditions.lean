import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchActivity
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyTransport
import Mettapedia.Logic.HOL.VectorChildArraySingleSegment
import Mettapedia.Logic.HOL.ConstructorEdgeIntroduction
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllReading

/-!
# Original Vector-tree children from an open guarded native Vector

The source branch is the actual parsed branch of the complete inventory.
Its children are the selected vector recursor followed by constant bottom,
with no extra leading or trailing children. Membership in the family derived
from that inventory supplies both least membership and the original root
index for the same child. Arithmetic and recursor computation proofs remain
explicit; no decoder or supplied complete array law is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditions
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding IndexedConstructorGuards
namespace Activity
export IndexedVectorTreeBranchActivity
  (inventory positions occurrence arguments payload allowed activity activityReadback activityReadback_free
   childGuardFromBound childGuardFromBound_free inactiveBound inactiveBound_free)
end Activity
namespace Family
export IndexedVectorTreeStoredFamily (signature inventory family construct root memberLeast memberLeast_free memberRoot memberRoot_free)
end Family
namespace Transport
export IndexedVectorTreeStoredFamilyTransport
  (family_subst family_rename least_subst least_rename active_subst active_rename edge_subst edge_rename)
end Transport
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (ops : VectorChildArrays.Operations Const) {A : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ ops.number A ops.element)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (ops.number ⇒ .prop))
  (one : ClosedTerm Const ops.number) (tags : Nat → Term Const Γ ops.number) (bottom : Term Const Γ ops.element)
  {Δ : List (Formula Const Γ)}

@[irreducible] def activeChildren (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (slot : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector))
    (active : ProofSyntax Const Δ (Activity.activity given source numbers ops.zero one ops.successor tags n q slot)) :
    ProofSyntax Const Δ (.and
      (.app (.app (.app ((Activity.positions given source numbers ops.zero one ops.successor tags).edgeProgram
        (Family.construct given)) (Activity.payload given source numbers ops.zero one tags n q)) slot)
        (.app (ops.single n vector bottom) slot))
      (.app (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
        (.app (ops.single n vector bottom) slot))) := by
  let child := Term.app (ops.single n vector bottom) slot
  let readback := Activity.activityReadback given source numbers ops.zero one ops.successor tags n q slot active
  have childMember := ops.singleMemberAtBound
    (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector bottom slot premises arithmetic member (.andER readback)
  have position := Activity.childGuardFromBound given source numbers ops.zero one ops.successor tags n q slot
    (.andEL readback) (.andER readback)
  have root : ProofSyntax Const Δ ((Activity.inventory given source numbers ops.zero one tags).rootIndex
      (Family.construct given) child .top) :=
    .impE (.eqPropEL ((Activity.inventory given source numbers ops.zero one tags).rootProgram_beta
      (Family.construct given) child .top))
      (Family.memberRoot given source numbers ops.zero one ops.successor tags bottom child childMember)
  exact .andI ((Activity.positions given source numbers ops.zero one ops.successor tags).edgeProgramFromIndex
    (Family.construct given) _ slot child .top position root)
    (Family.memberLeast given source numbers ops.zero one ops.successor tags bottom child childMember)

set_option maxHeartbeats 1000000 in
theorem activeChildren_free (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (slot : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector))
    (active : ProofSyntax Const Δ (Activity.activity given source numbers ops.zero one ops.successor tags n q slot))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (memberFree : member.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree) :
    (activeChildren ops given source numbers one tags bottom n q vector slot premises arithmetic member active).FunctionExtensionalityFree := by
  let readback := Activity.activityReadback given source numbers ops.zero one ops.successor tags n q slot active
  have readbackFree : readback.FunctionExtensionalityFree :=
    Activity.activityReadback_free given source numbers ops.zero one ops.successor tags n q slot active activeFree
  have childFree := ops.singleMemberAtBound_free
    (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector bottom slot premises arithmetic member (.andER readback)
    premisesFree arithmeticFree memberFree readbackFree
  unfold activeChildren
  constructor
  · apply PositionPrograms.edgeProgramFromIndex_free
    · exact Activity.childGuardFromBound_free _ _ _ _ _ _ _ _ _ _ _ _ readbackFree readbackFree
    · exact ⟨(Activity.inventory given source numbers ops.zero one tags).rootProgram_beta_free _ _ _,
        Family.memberRoot_free _ _ _ _ _ _ _ _ _ _ childFree⟩
  · exact Family.memberLeast_free _ _ _ _ _ _ _ _ _ _ childFree

def slotConditions (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (slot : Term Const Γ ops.number) : Formula Const Γ :=
  .and (.imp (Activity.activity given source numbers ops.zero one ops.successor tags n q slot)
    (.and (.app (.app (.app ((Activity.positions given source numbers ops.zero one ops.successor tags).edgeProgram
      (Family.construct given)) (Activity.payload given source numbers ops.zero one tags n q)) slot)
      (.app (ops.single n vector bottom) slot))
      (.app (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
        (.app (ops.single n vector bottom) slot))))
    (.imp (.not (Activity.activity given source numbers ops.zero one ops.successor tags n q slot))
      (.eq (.app (ops.single n vector bottom) slot) bottom))

@[irreducible] def sourceSlotConditions (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (slot : Term Const Γ ops.number)
    (admitted : ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n q))
    (premises : ops.ComputationPremises Δ) (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector)) :
    ProofSyntax Const Δ (slotConditions ops given source numbers one tags bottom n q vector slot) :=
  .andI (.impI (activeChildren ops given source numbers one tags bottom n q vector slot
    (premises.prepend _) (arithmetic.prepend _) (member.prepend _) (.hyp 0)))
    (.impI (ops.singlePadding (Family.family given source numbers ops.zero one ops.successor tags bottom)
      n vector bottom slot (premises.prepend _) (arithmetic.induction.prepend _) (member.prepend _)
      (Activity.inactiveBound given source numbers ops.zero one ops.successor tags n q slot (admitted.prepend _) (.hyp 0))))

theorem sourceSlotConditions_free (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (slot : Term Const Γ ops.number)
    (admitted : ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n q))
    (premises : ops.ComputationPremises Δ) (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector))
    (admittedFree : admitted.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree) :
    (sourceSlotConditions ops given source numbers one tags bottom n q vector slot admitted premises arithmetic member).FunctionExtensionalityFree := by
  unfold sourceSlotConditions
  constructor
  · apply activeChildren_free
    · exact premises.prepend_free _ premisesFree
    · exact arithmetic.prepend_free _ arithmeticFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree
    · trivial
  · apply ops.singlePadding_free
    · exact premises.prepend_free _ premisesFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr arithmeticFree.2.2
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr memberFree
    · exact Activity.inactiveBound_free _ _ _ _ _ _ _ _ _ _ _ _
        ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr admittedFree) True.intro

theorem payload_subst (images : Subst Const Γ Ξ) (n q : Term Const Γ ops.number) :
    HOL.subst images (Activity.payload given source numbers ops.zero one tags n q) =
      Activity.payload (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) ops.zero one
        (fun i => HOL.subst images (tags i)) (HOL.subst images n) (HOL.subst images q) := by
  simp only [IndexedVectorTreeBranchActivity.payload,encode_subst]
  rfl

theorem allowed_subst (images : Subst Const Γ Ξ) (n q : Term Const Γ ops.number) :
    HOL.subst images (Activity.allowed given source numbers ops.zero one tags n q) =
      Activity.allowed (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) ops.zero one
        (fun i => HOL.subst images (tags i)) (HOL.subst images n) (HOL.subst images q) := by
  simp only [IndexedVectorTreeBranchActivity.allowed,applyArguments_subst]
  change applyArguments [ops.number,ops.number]
    (HOL.subst images ((Family.inventory given source numbers ops.zero one tags).allowed ⟨1,by change 1 < 2; decide⟩)) _ = _
  rw [IndexedVectorTreeStoredFamilyTransport.allowed_subst]
  rfl

theorem payload_rename (rho : Rename Base Γ Ξ) (n q : Term Const Γ ops.number) :
    HOL.rename rho (Activity.payload given source numbers ops.zero one tags n q) =
      Activity.payload (given.substitute (Subst.ofRename rho)) (HOL.rename rho source) (HOL.rename rho numbers) ops.zero one
        (fun i => HOL.rename rho (tags i)) (HOL.rename rho n) (HOL.rename rho q) := by
  rw [← subst_ofRename rho (Activity.payload given source numbers ops.zero one tags n q),payload_subst]
  change encode [[ops.element],[ops.number,ops.number]] (1 : Fin 2)
    (HOL.subst (Subst.ofRename rho) n,HOL.subst (Subst.ofRename rho) q,PUnit.unit) =
    encode [[ops.element],[ops.number,ops.number]] (1 : Fin 2) (HOL.rename rho n,HOL.rename rho q,PUnit.unit)
  rw [subst_ofRename,subst_ofRename]

theorem allowed_rename (rho : Rename Base Γ Ξ) (n q : Term Const Γ ops.number) :
    HOL.rename rho (Activity.allowed given source numbers ops.zero one tags n q) =
      Activity.allowed (given.substitute (Subst.ofRename rho)) (HOL.rename rho source) (HOL.rename rho numbers) ops.zero one
        (fun i => HOL.rename rho (tags i)) (HOL.rename rho n) (HOL.rename rho q) := by
  simpa only [subst_ofRename] using allowed_subst ops given source numbers one tags (Subst.ofRename rho) n q

theorem childConditions_equation (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) :
    (Family.signature given source numbers ops.zero one ops.successor tags bottom).childConditions
      (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
      (Activity.payload given source numbers ops.zero one tags n q) (ops.single n vector bottom) =
    .all (slotConditions ops (given.substitute (Subst.ofRename (Rename.weaken (σ := ops.number))))
      (weaken source) (weaken numbers) one (fun i => weaken (tags i)) (weaken bottom)
      (weaken n) (weaken q) (weaken vector) (.var .vz)) := by
  have activeMoved := Transport.active_rename given source numbers ops.zero one ops.successor tags
    (Rename.weaken (σ := ops.number))
  have edgeMoved := Transport.edge_rename given source numbers ops.zero one ops.successor tags
    (Rename.weaken (σ := ops.number))
  have leastMoved := Transport.least_rename given source numbers ops.zero one ops.successor tags bottom
    (Rename.weaken (σ := ops.number))
  have payloadMoved := payload_rename ops given source numbers one tags (Rename.weaken (σ := ops.number)) n q
  have activeCode : (Family.signature given source numbers ops.zero one ops.successor tags bottom).active =
      (Activity.positions given source numbers ops.zero one ops.successor tags).activeProgram := rfl
  have edgeCode : (Family.signature given source numbers ops.zero one ops.successor tags bottom).validEdge =
      (Activity.positions given source numbers ops.zero one ops.successor tags).edgeProgram (Family.construct given) := rfl
  have bottomCode : (Family.signature given source numbers ops.zero one ops.successor tags bottom).bottom = bottom := rfl
  unfold RecursiveSpacePredicate.Contextual.childConditions slotConditions
  change Term.all _ = _
  simp only [IndexedVectorTreeBranchActivity.activity,IndexedVectorTreeBranchActivity.positions,
    weaken,activeCode,edgeCode,bottomCode,activeMoved,edgeMoved,leastMoved,payloadMoved,
    VectorChildArrays.Operations.single_rename]

def weakenVector (n : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector)) :
    ProofSyntax Const (weakenHyps (σ := ops.number) Δ) (ops.toSignature.member
      (Family.family (given.substitute (Subst.ofRename (Rename.weaken (σ := ops.number))))
        (weaken source) (weaken numbers) ops.zero one ops.successor (fun i => weaken (tags i)) (weaken bottom))
      (weaken n) (weaken vector)) :=
  .castIndices rfl (by simp only [ops.toSignature.rename_member,Transport.family_rename,weaken])
    (member.rename Rename.weaken)

theorem weakenVector_free (n : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector))
    (free : member.FunctionExtensionalityFree) :
    (weakenVector ops given source numbers one tags bottom n vector member).FunctionExtensionalityFree := by
  unfold weakenVector
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free

def weakenAllowed (n q : Term Const Γ ops.number)
    (admitted : ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n q)) :
    ProofSyntax Const (weakenHyps (σ := ops.number) Δ)
      (Activity.allowed (given.substitute (Subst.ofRename (Rename.weaken (σ := ops.number))))
        (weaken source) (weaken numbers) ops.zero one (fun i => weaken (tags i)) (weaken n) (weaken q)) :=
  .castIndices rfl (allowed_rename ops given source numbers one tags Rename.weaken n q) (admitted.rename Rename.weaken)

theorem weakenAllowed_free (n q : Term Const Γ ops.number)
    (admitted : ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n q))
    (free : admitted.FunctionExtensionalityFree) :
    (weakenAllowed ops given source numbers one tags n q admitted).FunctionExtensionalityFree := by
  unfold weakenAllowed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ProofSyntax.functionExtensionalityFree_rename _ _).mpr free

@[irreducible] def sourceChildConditions (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (admitted : ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n q))
    (premises : ops.ComputationPremises Δ) (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector)) :
    ProofSyntax Const Δ ((Family.signature given source numbers ops.zero one ops.successor tags bottom).childConditions
      (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
      (Activity.payload given source numbers ops.zero one tags n q) (ops.single n vector bottom)) :=
  .castIndices rfl (childConditions_equation ops given source numbers one tags bottom n q vector).symm
    (.allI (sourceSlotConditions ops (given.substitute (Subst.ofRename (Rename.weaken (σ := ops.number))))
      (weaken source) (weaken numbers) one (fun i => weaken (tags i)) (weaken bottom)
      (weaken n) (weaken q) (weaken vector) (.var .vz)
      (weakenAllowed ops given source numbers one tags n q admitted) (premises.weaken ops.number)
      (arithmetic.rename Rename.weaken) (weakenVector ops given source numbers one tags bottom n vector member)))

set_option maxHeartbeats 1000000 in
theorem sourceChildConditions_free (n q : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (admitted : ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n q))
    (premises : ops.ComputationPremises Δ) (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member
      (Family.family given source numbers ops.zero one ops.successor tags bottom) n vector))
    (admittedFree : admitted.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree) :
    (sourceChildConditions ops given source numbers one tags bottom n q vector admitted premises arithmetic member).FunctionExtensionalityFree := by
  unfold sourceChildConditions
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply sourceSlotConditions_free
  · exact weakenAllowed_free ops given source numbers one tags n q admitted admittedFree
  · exact premises.weaken_free ops.number premisesFree
  · exact arithmetic.rename_free Rename.weaken arithmeticFree
  · exact weakenVector_free ops given source numbers one tags bottom n vector member memberFree

def numericAllowed (n : Term Const Γ ops.number) (numeric : ProofSyntax Const Δ (.app numbers n)) :
    ProofSyntax Const Δ (Activity.allowed given source numbers ops.zero one tags n (weakenCtx Γ ops.zero)) := by
  have same := IndexedVectorTreeStoredFieldGuards.allowed_eq given source numbers ops.zero one tags ⟨1,by change 1 < 2; decide⟩
  apply ProofSyntax.castIndices rfl ?_
    (IndexedVectorTreeStoredFieldGuards.branchIntroduce given source numbers ops.zero one n (weakenCtx Γ ops.zero)
      (.andI numeric (.andI (.eqRefl _) .topI)))
  exact congrArg (fun condition => applyArguments [ops.number,ops.number] condition
    (n,weakenCtx Γ ops.zero,PUnit.unit)) same.symm

theorem numericAllowed_free (n : Term Const Γ ops.number) (numeric : ProofSyntax Const Δ (.app numbers n))
    (free : numeric.FunctionExtensionalityFree) :
    (numericAllowed ops given source numbers one tags n numeric).FunctionExtensionalityFree := by
  unfold numericAllowed
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact IndexedVectorTreeStoredFieldGuards.branchIntroduce_free _ _ _ _ _ _ _ _ ⟨free,True.intro,True.intro⟩

namespace ReaderGuard
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
variable (original : NativeVectorComputationRows.Operations Base Const) {evidence : Ty Base}
  (selection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ evidence ⇒ .prop)))

def arrays (elementSelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.element)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ original.number ⇒ original.element))) :
    VectorChildArrays.Operations Const where
  toSignature := NativeVectorComputationRows.GuardedFamily.algebra original
  head := original.head
  tail := original.tail
  elementSelection := elementSelection
  arraySelection := arraySelection

def vector_beta (predicate : Term Const Γ original.elementPredicate) (n : Term Const Γ original.number)
    (vector : Term Const Γ original.vector) :
    ProofSyntax Const Δ (.eq (.app (NativeVectorAll.Reading.vectorCode original selection predicate n) vector)
      ((NativeVectorComputationRows.GuardedFamily.algebra original).member predicate n vector)) := by
  apply ProofSyntax.castIndices rfl ?_
    (NativeVectorComputationRows.GuardedFamily.family_apply (NativeVectorAll.Reading.operations original selection) predicate n vector)
  simp only [NativeVectorAll.Reading.vectorCode,NativeVectorComputationRows.GuardedFamily.weaken_familyCode]
  rfl

theorem vector_beta_free (predicate : Term Const Γ original.elementPredicate) (n : Term Const Γ original.number)
    (vector : Term Const Γ original.vector) :
    (vector_beta original selection (Δ := Δ) predicate n vector).FunctionExtensionalityFree := by
  unfold vector_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact NativeVectorComputationRows.GuardedFamily.family_apply_free _ _ _ _

def memberOfGuard (predicate : Term Const Γ original.elementPredicate) (n : Term Const Γ original.number)
    (vector : Term Const Γ original.vector)
    (member : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection predicate n) vector)) :
    ProofSyntax Const Δ ((NativeVectorComputationRows.GuardedFamily.algebra original).member predicate n vector) :=
  .impE (.eqPropEL (vector_beta original selection predicate n vector)) member

theorem memberOfGuard_free (predicate : Term Const Γ original.elementPredicate) (n : Term Const Γ original.number)
    (vector : Term Const Γ original.vector)
    (member : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection predicate n) vector))
    (free : member.FunctionExtensionalityFree) :
    (memberOfGuard original selection predicate n vector member).FunctionExtensionalityFree :=
  ⟨vector_beta_free _ _ _ _ _,free⟩

variable (elementSelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.element)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ original.number ⇒ original.element)))
  (input : VectorTreeFieldEmbedding.Inputs Const Γ original.number A original.element)
  (answer : Term Const Γ (A ⇒ .prop)) (natural : Term Const Γ (original.number ⇒ .prop))
  (unitCode : ClosedTerm Const original.number) (ordinals : Nat → Term Const Γ original.number)
  (padding : Term Const Γ original.element)

@[irreducible] def sourceChildConditions (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (numeric : ProofSyntax Const Δ (.app natural n))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
      (Family.family input answer natural original.zero unitCode original.successor ordinals padding) n) vector)) :
    ProofSyntax Const Δ ((Family.signature input answer natural original.zero unitCode original.successor ordinals padding).childConditions
      (Family.signature input answer natural original.zero unitCode original.successor ordinals padding).least
      (Activity.payload input answer natural original.zero unitCode ordinals n (weakenCtx Γ original.zero))
      ((arrays original elementSelection arraySelection).single n vector padding)) :=
  IndexedVectorTreeNativeChildConditions.sourceChildConditions (arrays original elementSelection arraySelection)
    input answer natural unitCode ordinals padding n (weakenCtx Γ original.zero) vector
    (numericAllowed (arrays original elementSelection arraySelection) input answer natural unitCode ordinals n numeric)
    premises arithmetic (memberOfGuard original selection _ n vector member)

theorem sourceChildConditions_free (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (numeric : ProofSyntax Const Δ (.app natural n))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
      (Family.family input answer natural original.zero unitCode original.successor ordinals padding) n) vector))
    (numericFree : numeric.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree) :
    (sourceChildConditions original selection elementSelection arraySelection input answer natural unitCode ordinals padding
      n vector numeric premises arithmetic member).FunctionExtensionalityFree := by
  unfold sourceChildConditions
  apply IndexedVectorTreeNativeChildConditions.sourceChildConditions_free
  · exact numericAllowed_free _ _ _ _ _ _ _ _ numericFree
  · exact premisesFree
  · exact arithmeticFree
  · exact memberOfGuard_free _ _ _ _ _ _ memberFree

end ReaderGuard

#print axioms activeChildren
#print axioms sourceSlotConditions
#print axioms sourceSlotConditions_free
#print axioms sourceChildConditions
#print axioms sourceChildConditions_free
#print axioms ReaderGuard.sourceChildConditions
#print axioms ReaderGuard.sourceChildConditions_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditions
