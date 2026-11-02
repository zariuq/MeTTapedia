import Mettapedia.Logic.HOL.VectorChildArrayBoundary
import Mettapedia.Logic.HOL.IndexedVectorLookupCoverage
import Mettapedia.Logic.HOL.OrderedMixedPositionReadback
import Mettapedia.Logic.HOL.OrderedPositionActivityReadback

/-!
# Membership of the actual mixed child array at canonical positions

Scalar fields use their exact leading/trailing equations. An interior bound
constructs a scoped vector lookup witness, and the existing array lookup law
transports the same element predicate to the actual array value. No lookup
witness, array value, or global element choice is assumed.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays.Operations
open SuccessorOrder OrderedPositionPrograms IndexedVectorLookupWitnesses
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} (ops : VectorChildArrays.Operations Const)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)}

def mixedMemberAtWitness (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (evidence ops.toSignature predicate index vector position)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom)
      (.app (weakenCtx Γ ops.successor) position))) := by
  apply ProofSyntax.exE present
  let body : Formula Const (ops.element :: Γ) :=
    .and (IndexedVectorPositions.lookup ops.toSignature (weaken index) (weaken vector) (weaken position) (.var .vz))
      (.app (weaken predicate) (.var .vz))
  let current := (premises.weaken ops.element).prepend body
  have same := ops.mixedAtLookup (weaken index) (weaken before) (weaken vector) (weaken after) (weaken bottom)
    (weaken position) (.var .vz) current (.andEL (.hyp 0))
  apply ProofSyntax.castIndices rfl ?_
    (.impE (.eqPropER (.eqAppArg (weaken predicate) same)) (.andER (.hyp 0)))
  simp only [weaken,HOL.rename,mixed_rename,rename_weakenCtx]

theorem mixedMemberAtWitness_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (position : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (present : ProofSyntax Const Δ (evidence ops.toSignature predicate index vector position))
    (premisesFree : premises.FunctionExtensionalityFree) (presentFree : present.FunctionExtensionalityFree) :
    (ops.mixedMemberAtWitness predicate index before vector after bottom position premises present).FunctionExtensionalityFree := by
  unfold mixedMemberAtWitness
  refine ⟨presentFree,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  refine ⟨?_,True.intro⟩
  exact ops.mixedAtLookup_free _ _ _ _ _ _ _ _ _
    ((premises.weaken ops.element).prepend_free _ (premises.weaken_free _ premisesFree)) trivial

def mixedMemberInterior (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot offset : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ ops.successor) offset)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less ops.successor)) offset) index)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom) slot)) :=
  .impE (.eqPropER (.eqAppArg predicate (.eqAppArg (ops.mixed index before vector after bottom) address)))
    (ops.mixedMemberAtWitness predicate index before vector after bottom offset premises
      (IndexedVectorLookupCoverage.witnessFromBound ops.toSignature predicate index vector offset arithmetic member bounded))

theorem mixedMemberInterior_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot offset : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ ops.successor) offset)))
    (bounded : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (less ops.successor)) offset) index))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (memberFree : member.FunctionExtensionalityFree) (addressFree : address.FunctionExtensionalityFree)
    (boundedFree : bounded.FunctionExtensionalityFree) :
    (ops.mixedMemberInterior predicate index before vector after bottom slot offset premises arithmetic member address bounded).FunctionExtensionalityFree :=
  ⟨addressFree,ops.mixedMemberAtWitness_free _ _ _ _ _ _ _ premises _ premisesFree
    (IndexedVectorLookupCoverage.witnessFromBound_free _ _ _ _ _ arithmetic member bounded arithmeticFree memberFree boundedFree)⟩

def mixedMemberLeading (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ) (member : ProofSyntax Const Δ (.app predicate before))
    (address : ProofSyntax Const Δ (.eq slot (weakenCtx Γ ops.zero))) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom) slot)) :=
  .impE (.eqPropER (.eqAppArg predicate
    (.eqTrans (.eqAppArg (ops.mixed index before vector after bottom) address)
      (ops.mixedLeading index before vector after bottom premises)))) member

theorem mixedMemberLeading_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ) (member : ProofSyntax Const Δ (.app predicate before))
    (address : ProofSyntax Const Δ (.eq slot (weakenCtx Γ ops.zero)))
    (premisesFree : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (addressFree : address.FunctionExtensionalityFree) :
    (ops.mixedMemberLeading predicate index before vector after bottom slot premises member address).FunctionExtensionalityFree :=
  ⟨⟨addressFree,ops.mixedLeading_free _ _ _ _ _ premises premisesFree⟩,memberFree⟩

def mixedMemberTrailing (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (member : ProofSyntax Const Δ (.app predicate after))
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ ops.successor) index))) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom) slot)) :=
  .impE (.eqPropER (.eqAppArg predicate
    (.eqTrans (.eqAppArg (ops.mixed index before vector after bottom) address)
      (ops.mixedTrailing predicate index before vector after bottom premises vectorMember)))) member

theorem mixedMemberTrailing_free (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (member : ProofSyntax Const Δ (.app predicate after))
    (address : ProofSyntax Const Δ (.eq slot (.app (weakenCtx Γ ops.successor) index)))
    (premisesFree : premises.FunctionExtensionalityFree) (vectorMemberFree : vectorMember.FunctionExtensionalityFree)
    (memberFree : member.FunctionExtensionalityFree) (addressFree : address.FunctionExtensionalityFree) :
    (ops.mixedMemberTrailing predicate index before vector after bottom slot premises vectorMember member address).FunctionExtensionalityFree :=
  ⟨⟨addressFree,ops.mixedTrailing_free _ _ _ _ _ _ premises vectorMember premisesFree vectorMemberFree⟩,memberFree⟩

#print axioms mixedMemberAtWitness_free
#print axioms mixedMemberInterior_free

def mixedMemberFromCases {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (cases : ProofSyntax Const Δ (mixedCases ops.zero ops.successor index slot firstIndex vectorIndex lastIndex target)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom) slot)) := by
  apply ProofSyntax.orE cases
  · exact ops.mixedMemberLeading predicate index before vector after bottom slot
      (premises.prepend _) (beforeMember.prepend _) (.andEL (.hyp 0))
  · let remaining : Formula Const Γ := .or
      (.ex (.and (.eq (weaken slot) (.app (weakenCtx _ ops.successor) (.var .vz)))
        (.and (.app (.app (weakenCtx _ (less ops.successor)) (.var .vz)) (weaken index))
          (.eq (weaken target) (weaken vectorIndex)))))
      (.and (.eq slot (.app (weakenCtx Γ ops.successor) index)) (.eq target lastIndex))
    apply ProofSyntax.orE (.hyp (Δ := remaining :: Δ) 0)
    · let interior : Formula Const Γ := .ex (.and (.eq (weaken slot) (.app (weakenCtx _ ops.successor) (.var .vz)))
        (.and (.app (.app (weakenCtx _ (less ops.successor)) (.var .vz)) (weaken index))
          (.eq (weaken target) (weaken vectorIndex))))
      apply ProofSyntax.exE (.hyp (Δ := interior :: remaining :: Δ) 0)
      let body : Formula Const (ops.number :: Γ) := .and (.eq (weaken slot) (.app (weakenCtx _ ops.successor) (.var .vz)))
        (.and (.app (.app (weakenCtx _ (less ops.successor)) (.var .vz)) (weaken index))
          (.eq (weaken target) (weaken vectorIndex)))
      let currentPremises := ((((premises.prepend remaining).prepend interior).weaken ops.number).prepend body)
      let currentArithmetic := ((((arithmetic.prepend remaining).prepend interior).rename Rename.weaken).prepend body)
      have currentVector : ProofSyntax Const (body :: weakenHyps (interior :: remaining :: Δ))
          (ops.toSignature.member (weaken predicate) (weaken index) (weaken vector)) := by
        apply ProofSyntax.castIndices rfl ?_
          ((((vectorMember.prepend remaining).prepend interior).rename Rename.weaken).prepend body)
        exact ops.toSignature.rename_member Rename.weaken predicate index vector
      apply ProofSyntax.castIndices rfl ?_
        (ops.mixedMemberInterior (weaken predicate) (weaken index) (weaken before) (weaken vector)
          (weaken after) (weaken bottom) (weaken slot) (.var .vz) currentPremises currentArithmetic currentVector
          (.andEL (.hyp 0)) (.andEL (.andER (.hyp 0))))
      simp only [weaken,HOL.rename,mixed_rename]
    · exact ops.mixedMemberTrailing predicate index before vector after bottom slot
        ((premises.prepend remaining).prepend _) ((vectorMember.prepend remaining).prepend _)
        ((afterMember.prepend remaining).prepend _) (.andEL (.hyp 0))

theorem mixedMemberFromCases_free {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (cases : ProofSyntax Const Δ (mixedCases ops.zero ops.successor index slot firstIndex vectorIndex lastIndex target))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) (casesFree : cases.FunctionExtensionalityFree) :
    (ops.mixedMemberFromCases predicate index before vector after bottom slot firstIndex vectorIndex lastIndex target
      premises arithmetic beforeMember vectorMember afterMember cases).FunctionExtensionalityFree := by
  unfold mixedMemberFromCases
  refine ⟨casesFree,?_,True.intro,?_,?_⟩
  · exact ops.mixedMemberLeading_free _ _ _ _ _ _ _ _ _ _ (premises.prepend_free _ premisesFree)
      ((ProofSyntax.functionExtensionalityFree_mono _ _).mpr beforeFree) trivial
  · refine ⟨True.intro,?_⟩
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    apply mixedMemberInterior_free
    · apply ComputationPremises.prepend_free
      apply ComputationPremises.weaken_free
      iterate 2 apply ComputationPremises.prepend_free
      exact premisesFree
    · apply PeanoEvidence.prepend_free
      apply PeanoEvidence.rename_free
      iterate 2 apply PeanoEvidence.prepend_free
      exact arithmeticFree
    · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
        ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using vectorFree
    · trivial
    · trivial
  · apply mixedMemberTrailing_free
    · iterate 2 apply ComputationPremises.prepend_free
      exact premisesFree
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using vectorFree
    · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using afterFree
    · trivial

def mixedMemberAtCanonical {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (related : ProofSyntax Const Δ (compileAt ops.zero ops.successor
      (mixedPlan ops.zero ops.successor index firstIndex vectorIndex lastIndex) Subst.id slot target)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom) slot)) :=
  ops.mixedMemberFromCases predicate index before vector after bottom slot firstIndex vectorIndex lastIndex target
    premises arithmetic beforeMember vectorMember afterMember
    (mixedReadback ops.zero ops.successor index slot firstIndex vectorIndex lastIndex target arithmetic related)

theorem mixedMemberAtCanonical_free {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (firstIndex vectorIndex lastIndex target : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (related : ProofSyntax Const Δ (compileAt ops.zero ops.successor
      (mixedPlan ops.zero ops.successor index firstIndex vectorIndex lastIndex) Subst.id slot target))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) (relatedFree : related.FunctionExtensionalityFree) :
    (ops.mixedMemberAtCanonical predicate index before vector after bottom slot firstIndex vectorIndex lastIndex target
      premises arithmetic beforeMember vectorMember afterMember related).FunctionExtensionalityFree :=
  ops.mixedMemberFromCases_free _ _ _ _ _ _ _ _ _ _ _ premises arithmetic beforeMember vectorMember afterMember _
    premisesFree arithmeticFree beforeFree vectorFree afterFree
    (mixedReadback_free _ _ _ _ _ _ _ _ arithmetic related arithmeticFree relatedFree)

#print axioms mixedMemberAtCanonical_free

def mixedMemberAtActivePlan {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (firstIndex vectorIndex lastIndex : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (active : ProofSyntax Const Δ (activeAt ops.zero ops.successor
      (mixedPlan ops.zero ops.successor index firstIndex vectorIndex lastIndex) slot)) :
    ProofSyntax Const Δ (.app predicate (.app (ops.mixed index before vector after bottom) slot)) := by
  apply ProofSyntax.exE active
  let images : Subst Const Γ (indexType :: Γ) := Subst.ofRename Rename.weaken
  let plan := mixedPlan ops.zero ops.successor index firstIndex vectorIndex lastIndex
  let body := compileAt ops.zero ops.successor plan images (weaken slot) (.var .vz)
  let assumptions := body :: weakenHyps Δ
  let currentPremises := (premises.weaken indexType).prepend body
  let currentArithmetic := (arithmetic.rename Rename.weaken).prepend body
  have currentVector : ProofSyntax Const assumptions
      (ops.toSignature.member (weaken predicate) (weaken index) (weaken vector)) :=
    ProofSyntax.castIndices rfl (ops.toSignature.rename_member Rename.weaken predicate index vector)
      ((vectorMember.rename Rename.weaken).prepend body)
  have currentBefore : ProofSyntax Const assumptions (.app (weaken predicate) (weaken before)) :=
    (beforeMember.rename Rename.weaken).prepend body
  have currentAfter : ProofSyntax Const assumptions (.app (weaken predicate) (weaken after)) :=
    (afterMember.rename Rename.weaken).prepend body
  have currentLookup : ProofSyntax Const assumptions (compileAt ops.zero ops.successor
      (mixedPlan ops.zero ops.successor (weaken index) (weaken firstIndex) (weaken vectorIndex) (weaken lastIndex))
      Subst.id (weaken slot) (.var .vz)) := by
    apply ProofSyntax.castIndices rfl ?_ (.hyp (Δ := assumptions) 0)
    change body = _
    have bridge := compileAt_substitute ops.zero ops.successor plan images Subst.id (weaken slot) (.var .vz)
    simp only [HOL.subst_id] at bridge
    rw [mixedPlan_substitute] at bridge
    simpa only [body,plan,images,subst_ofRename,weaken] using bridge.symm
  apply ProofSyntax.castIndices rfl ?_
    (ops.mixedMemberAtCanonical (weaken predicate) (weaken index) (weaken before) (weaken vector) (weaken after)
      (weaken bottom) (weaken slot) (weaken firstIndex) (weaken vectorIndex) (weaken lastIndex) (.var .vz)
      currentPremises currentArithmetic currentBefore currentVector currentAfter currentLookup)
  simp only [weaken,HOL.rename,mixed_rename]

theorem mixedMemberAtActivePlan_free {indexType : Ty Base} (predicate : Term Const Γ (ops.element ⇒ .prop))
    (index : Term Const Γ ops.number) (before : Term Const Γ ops.element) (vector : Term Const Γ ops.vector)
    (after bottom : Term Const Γ ops.element) (slot : Term Const Γ ops.number)
    (firstIndex vectorIndex lastIndex : Term Const Γ indexType)
    (premises : ops.ComputationPremises Δ) (arithmetic : PeanoEvidence ops.successor ops.zero Δ)
    (beforeMember : ProofSyntax Const Δ (.app predicate before))
    (vectorMember : ProofSyntax Const Δ (ops.toSignature.member predicate index vector))
    (afterMember : ProofSyntax Const Δ (.app predicate after))
    (active : ProofSyntax Const Δ (activeAt ops.zero ops.successor
      (mixedPlan ops.zero ops.successor index firstIndex vectorIndex lastIndex) slot))
    (premisesFree : premises.FunctionExtensionalityFree) (arithmeticFree : arithmetic.Free)
    (beforeFree : beforeMember.FunctionExtensionalityFree) (vectorFree : vectorMember.FunctionExtensionalityFree)
    (afterFree : afterMember.FunctionExtensionalityFree) (activeFree : active.FunctionExtensionalityFree) :
    (ops.mixedMemberAtActivePlan predicate index before vector after bottom slot firstIndex vectorIndex lastIndex
      premises arithmetic beforeMember vectorMember afterMember active).FunctionExtensionalityFree := by
  unfold mixedMemberAtActivePlan
  refine ⟨activeFree,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply mixedMemberAtCanonical_free
  · exact (premises.weaken indexType).prepend_free _ (premises.weaken_free _ premisesFree)
  · exact (arithmetic.rename Rename.weaken).prepend_free _ (arithmetic.rename_free _ arithmeticFree)
  · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using beforeFree
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using vectorFree
  · simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using afterFree
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    trivial

#print axioms mixedMemberAtActivePlan_free
end Mettapedia.Logic.HOL.VectorChildArrays.Operations
