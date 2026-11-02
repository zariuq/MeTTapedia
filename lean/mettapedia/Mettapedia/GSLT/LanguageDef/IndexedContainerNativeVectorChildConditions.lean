import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorScopeTransport
import Mettapedia.Logic.HOL.ContextualRecursiveSpaceProofs

/-!
# Complete child conditions for the original mixed-vector source

One joint field predicate retains ordinary recursive membership and the
original root-index section. Active lookup proves both for the same actual
array value. Inactive positions contain padding. Source admissibility,
arithmetic and the six array computation laws remain explicit premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditions
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V original)
open IndexedContainerNativeVectorPositionReading
open IndexedContainerNativeVectorInactivePadding
open IndexedContainerNativeVectorActiveMembership
open IndexedContainerNativeVectorActiveEdge
open IndexedContainerNativeVectorChildGuard
open IndexedContainerNativeVectorScopeTransport
open FiniteConstructorEncoding PredicateFixedPoint

variable {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}
    (elementSelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ E)))
    (arraySelection : ClosedTerm Const (SelectionProofs.Selection (N ⇒ V ⇒ N ⇒ E)))
    (payload elements : Term Const Γ (E ⇒ .prop))
    (construct : Term Const Γ (N ⇒ payloadType [[N,E,N]] ⇒ (N ⇒ E) ⇒ E))

def joint : Term Const Γ (E ⇒ .prop) := intersection elements (rootPredicate payload construct)

@[irreducible] def certifiedJointMember (point : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app elements point))
    (root : ProofSyntax Const Δ ((constructors payload).rootIndex construct point .top))
    (memberFree : member.FunctionExtensionalityFree) (rootFree : root.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (.app (joint payload elements construct) point) // proof.FunctionExtensionalityFree } :=
  ⟨.impE (.eqPropER (intersection_beta elements (rootPredicate payload construct) point))
      (.andI member ((constructors payload).rootAt_intro construct .top point root)),
   ⟨intersection_beta_free _ _ _,memberFree,(constructors payload).rootAt_intro_free _ _ _ root rootFree⟩⟩

theorem joint_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (joint payload elements construct) =
      joint (HOL.subst images payload) (HOL.subst images elements) (HOL.subst images construct) := by
  simp only [joint, subst_intersection, rootPredicate_subst]

set_option backward.isDefEq.respectTransparency true in
theorem joint_rename (rho : Rename Base Γ Ξ) :
    HOL.rename rho (joint payload elements construct) =
      joint (HOL.rename rho payload) (HOL.rename rho elements) (HOL.rename rho construct) := by
  rw [← subst_ofRename rho (joint payload elements construct), joint_subst]
  rw [subst_ofRename rho payload, subst_ofRename rho elements, subst_ofRename rho construct]

def activeConclusion (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N) : Formula Const Γ :=
  let child : Term Const Γ E := .app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot
  .and (.app (.app (.app ((positions payload).edgeProgram construct) (encoded payload length tag shape)) slot) child)
    (.app elements child)

def sourceActiveConditions (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after))
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (activeFree : active.FunctionExtensionalityFree) :
    ProofSyntax Const Δ (activeConclusion elementSelection arraySelection payload elements construct
      length tag before vector after bottom shape slot) := by
  let child : Term Const Γ E := .app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot
  have joined : ProofSyntax Const Δ (.and (.app elements child) (.app (rootPredicate payload construct) child)) :=
    .impE (.eqPropEL (intersection_beta elements (rootPredicate payload construct) child))
      (sourceActiveMember elementSelection arraySelection payload (joint payload elements construct)
        length tag before vector after bottom shape slot premises arithmetic beforeMember vectorMember afterMember active)
  exact .andI
    ((positions payload).edgeProgramFromIndex construct _ slot child .top
      (childGuardFromActivity payload length tag shape slot active activeFree)
      ((constructors payload).rootAt_elim construct .top child (.andER joined)))
    (.andEL joined)

theorem sourceActiveConditions_free (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after))
    (active : ProofSyntax Const Δ (.app (sourceActivity payload length tag shape) slot))
    (activeFree : active.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) :
    (sourceActiveConditions elementSelection arraySelection payload elements construct length tag before vector after bottom
      shape slot premises arithmetic beforeMember vectorMember afterMember active activeFree).FunctionExtensionalityFree := by
  have joinedFree := And.intro (intersection_beta_free (Δ := Δ) elements (rootPredicate payload construct)
    (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot))
    (sourceActiveMember_free elementSelection arraySelection payload (joint payload elements construct)
      length tag before vector after bottom shape slot premises arithmetic beforeMember vectorMember afterMember active
      premisesFree arithmeticFree beforeFree vectorFree afterFree activeFree)
  unfold sourceActiveConditions
  exact ⟨(positions payload).edgeProgramFromIndex_free _ _ _ _ _ _ _
    (childGuardFromActivity_free payload length tag shape slot active activeFree)
    ((constructors payload).rootAt_elim_free _ _ _ _ joinedFree), joinedFree⟩

def slotConditions (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N) : Formula Const Γ :=
  let active : Formula Const Γ := .app (sourceActivity payload length tag shape) slot
  .and (.imp active (activeConclusion elementSelection arraySelection payload elements construct
    length tag before vector after bottom shape slot))
    (.imp (.not active) (.eq
      (.app ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) slot) bottom))

def sourceSlotConditions (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after)) :
    ProofSyntax Const Δ (slotConditions elementSelection arraySelection payload elements construct
      length tag before vector after bottom shape slot) :=
  .andI (.impI (sourceActiveConditions elementSelection arraySelection payload elements construct
    length tag before vector after bottom shape slot (premises.prepend _) (arithmetic.prepend _)
    (beforeMember.prepend _) (vectorMember.prepend _) (afterMember.prepend _) (.hyp 0) True.intro))
    (.impI (sourceInactivePadding elementSelection arraySelection payload (joint payload elements construct)
      length tag before vector after bottom shape slot (allowed.prepend _) (arithmetic.induction.prepend _)
      (arithmetic.separation.prepend _) (premises.prepend _) (vectorMember.prepend _) (.hyp 0)))

theorem sourceSlotConditions_free (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape slot : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after))
    (allowedFree : allowed.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) :
    (sourceSlotConditions elementSelection arraySelection payload elements construct length tag before vector after bottom
      shape slot allowed premises arithmetic beforeMember vectorMember afterMember).FunctionExtensionalityFree := by
  unfold sourceSlotConditions
  constructor
  · apply sourceActiveConditions_free
    · exact premises.prepend_free _ premisesFree
    · exact arithmetic.prepend_free _ arithmeticFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr beforeFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr vectorFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr afterFree
  · apply sourceInactivePadding_free
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr allowedFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr arithmeticFree.2.2
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr arithmeticFree.1
    · exact premises.prepend_free _ premisesFree
    · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr vectorFree
    · trivial

def weakenElement (point : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app (joint payload elements construct) point)) :
    ProofSyntax Const (weakenHyps (σ := N) Δ)
      (.app (joint (weaken payload) (weaken elements) (weaken construct)) (weaken point)) :=
  ProofSyntax.castIndices rfl (by simp only [HOL.rename, joint_rename, weaken]) (member.rename Rename.weaken)

theorem weakenElement_free (point : Term Const Γ E)
    (member : ProofSyntax Const Δ (.app (joint payload elements construct) point))
    (free : member.FunctionExtensionalityFree) :
    (weakenElement payload elements construct point member).FunctionExtensionalityFree := by
  simpa only [weakenElement, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

def weakenVector (length : Term Const Γ N) (vector : Term Const Γ V)
    (member : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector)) :
    ProofSyntax Const (weakenHyps (σ := N) Δ) ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint (weaken payload) (weaken elements) (weaken construct)) (weaken length) (weaken vector)) :=
  ProofSyntax.castIndices rfl (by simp only [IndexedVectorPredicate.Signature.rename_member, joint_rename, weaken])
    (member.rename Rename.weaken)

theorem weakenVector_free (length : Term Const Γ N) (vector : Term Const Γ V)
    (member : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector)) (free : member.FunctionExtensionalityFree) :
    (weakenVector elementSelection arraySelection payload elements construct length vector member).FunctionExtensionalityFree := by
  simpa only [weakenVector, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

def weakenAllowed (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape)) :
    ProofSyntax Const (weakenHyps (σ := N) Δ)
      (sourceAllowed (weaken payload) (weaken length) (weaken tag) (weaken shape)) :=
  ProofSyntax.castIndices rfl (by
    have same := sourceAllowed_subst (Subst.ofRename (Rename.weaken (σ := N))) payload length tag shape
    simp only [subst_ofRename] at same
    exact same) (allowed.rename Rename.weaken)

theorem weakenAllowed_free (length : Term Const Γ N) (tag : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape)) (free : allowed.FunctionExtensionalityFree) :
    (weakenAllowed payload length tag shape allowed).FunctionExtensionalityFree := by
  simpa only [weakenAllowed, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

theorem childConditions_equation (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape : Term Const Γ N) :
    ((positions payload).contextual bottom construct).childConditions elements (encoded payload length tag shape)
      ((arrayOperations elementSelection arraySelection).mixed length before vector after bottom) =
      .all (slotConditions elementSelection arraySelection (weaken payload) (weaken elements) (weaken construct)
        (weaken length) (weaken tag) (weaken before) (weaken vector) (weaken after) (weaken bottom) (weaken shape) (.var .vz)) := by
  have activeSame := activeProgram_subst (Subst.ofRename (Rename.weaken (σ := N))) payload
  have payloadSame := encoded_subst (Subst.ofRename (Rename.weaken (σ := N))) payload length tag shape
  have edgeSame := edgeProgram_subst (Subst.ofRename (Rename.weaken (σ := N))) payload construct
  simp only [subst_ofRename] at activeSame payloadSame edgeSame
  have payloadRename := subst_ofRename (Rename.weaken (σ := N)) payload
  let activeMap : Term Const (N :: Γ) (E ⇒ .prop) → Term Const (N :: Γ) (payloadType [[N,E,N]] ⇒ N ⇒ .prop) :=
    fun p => (positions p).activeProgram
  let payloadMap : Term Const (N :: Γ) (E ⇒ .prop) → Term Const (N :: Γ) (payloadType [[N,E,N]]) :=
    fun p => encoded p (weaken length) (weaken tag) (weaken shape)
  let edgeMap : Term Const (N :: Γ) (E ⇒ .prop) → Term Const (N :: Γ) (payloadType [[N,E,N]] ⇒ N ⇒ E ⇒ .prop) :=
    fun p => (positions p).edgeProgram (weaken construct)
  have activeMoved := congrArg activeMap payloadRename
  have payloadMoved := congrArg payloadMap payloadRename
  have edgeMoved := congrArg edgeMap payloadRename
  have activeSame := activeSame.trans activeMoved
  have payloadSame := payloadSame.trans payloadMoved
  have edgeSame := edgeSame.trans edgeMoved
  dsimp only [activeMap, payloadMap, edgeMap] at activeSame payloadSame edgeSame
  simp only [positions, encoded] at activeSame payloadSame edgeSame
  unfold RecursiveSpacePredicate.Contextual.childConditions IndexedConstructorGuards.PositionPrograms.contextual
  unfold slotConditions activeConclusion sourceActivity IndexedConstructorGuards.PositionPrograms.sourceActive
  change Term.all _ = _
  simp only [positions, encoded, weaken, activeSame, payloadSame, edgeSame, VectorChildArrays.Operations.mixed_rename]

@[irreducible] def sourceChildConditions (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after)) :
    ProofSyntax Const Δ (((positions payload).contextual bottom construct).childConditions
      elements (encoded payload length tag shape) ((arrayOperations elementSelection arraySelection).mixed
        length before vector after bottom)) :=
  ProofSyntax.castIndices rfl
    (childConditions_equation elementSelection arraySelection payload elements construct length tag before vector after bottom shape).symm
    (.allI (sourceSlotConditions elementSelection arraySelection (weaken payload) (weaken elements) (weaken construct)
      (weaken length) (weaken tag) (weaken before) (weaken vector) (weaken after) (weaken bottom) (weaken shape) (.var .vz)
      (weakenAllowed payload length tag shape allowed) (premises.weaken N) (arithmetic.rename Rename.weaken)
      (weakenElement payload elements construct before beforeMember)
      (weakenVector elementSelection arraySelection payload elements construct length vector vectorMember)
      (weakenElement payload elements construct after afterMember)))

set_option backward.isDefEq.respectTransparency true in
theorem sourceChildConditions_free (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after))
    (allowedFree : allowed.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) :
    (sourceChildConditions elementSelection arraySelection payload elements construct length tag before vector after bottom
      shape allowed premises arithmetic beforeMember vectorMember afterMember).FunctionExtensionalityFree := by
  have free := sourceSlotConditions_free elementSelection arraySelection (weaken payload) (weaken elements) (weaken construct)
    (weaken length) (weaken tag) (weaken before) (weaken vector) (weaken after) (weaken bottom) (weaken shape) (.var .vz)
    (weakenAllowed payload length tag shape allowed) (premises.weaken N) (arithmetic.rename Rename.weaken)
    (weakenElement payload elements construct before beforeMember)
    (weakenVector elementSelection arraySelection payload elements construct length vector vectorMember)
    (weakenElement payload elements construct after afterMember)
    (weakenAllowed_free _ _ _ _ allowed allowedFree) (premises.weaken_free N premisesFree)
    (arithmetic.rename_free Rename.weaken arithmeticFree)
    (weakenElement_free _ _ _ _ beforeMember beforeFree)
    (weakenVector_free _ _ _ _ _ _ _ vectorMember vectorFree)
    (weakenElement_free _ _ _ _ afterMember afterFree)
  simpa only [sourceChildConditions, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.FunctionExtensionalityFree] using free

#print axioms sourceSlotConditions_free
#print axioms sourceChildConditions_free

set_option backward.isDefEq.respectTransparency true in
@[irreducible] def certifiedChildConditions (length : Term Const Γ N) (tag before : Term Const Γ E) (vector : Term Const Γ V)
    (after bottom : Term Const Γ E) (shape : Term Const Γ N)
    (allowed : ProofSyntax Const Δ (sourceAllowed payload length tag shape))
    (premises : (arrayOperations elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app (joint payload elements construct) before))
    (vectorMember : ProofSyntax Const Δ ((arrayOperations elementSelection arraySelection).toSignature.member
      (joint payload elements construct) length vector))
    (afterMember : ProofSyntax Const Δ (.app (joint payload elements construct) after))
    (allowedFree : allowed.FunctionExtensionalityFree)
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) :
    { proof : ProofSyntax Const Δ (((positions payload).contextual bottom construct).childConditions
      elements (encoded payload length tag shape) ((arrayOperations elementSelection arraySelection).mixed
        length before vector after bottom)) // proof.FunctionExtensionalityFree } :=
  ⟨sourceChildConditions elementSelection arraySelection payload elements construct length tag before vector after bottom
      shape allowed premises arithmetic beforeMember vectorMember afterMember,
   sourceChildConditions_free elementSelection arraySelection payload elements construct length tag before vector after bottom
      shape allowed premises arithmetic beforeMember vectorMember afterMember allowedFree premisesFree arithmeticFree
      beforeFree vectorFree afterFree⟩

#print axioms certifiedChildConditions
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorChildConditions
