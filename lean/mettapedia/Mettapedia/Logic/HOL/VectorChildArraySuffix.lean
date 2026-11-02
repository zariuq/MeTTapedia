import Mettapedia.Logic.HOL.VectorChildArrayLookup
import Mettapedia.Logic.HOL.SuccessorOrderTransforms

/-!
# Uniform suffix behavior of constructed vector child arrays

The boundary invariant quantifies the suffix offset and absolute position
inside the vector-induction motive. The supplied sum relation identifies the
same position throughout the proof. Its zero and successor transformations
require no additional Peano premises.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.VectorChildArrays
open FiniteConstructorEncoding
universe u v
variable {Base : Type u} {Const : Ty Base → Type v}

namespace Operations
variable (ops : Operations Const) {Γ Ξ : Ctx Base} {Δ : List (Formula Const Γ)}

namespace ComputationPremises
variable {ops}

def rename (premises : ops.ComputationPremises Δ) (rho : Rename Base Γ Ξ) :
    ops.ComputationPremises (Δ.map (HOL.rename rho)) where
  elementChoice := ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using selectionLaw_subst (Subst.ofRename rho) _ ops.elementSelection)
    (premises.elementChoice.rename rho)
  elementRecursion := ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using ops.recursionLaw_subst (Subst.ofRename rho) ops.element)
    (premises.elementRecursion.rename rho)
  arrayChoice := ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using selectionLaw_subst (Subst.ofRename rho) _ ops.arraySelection)
    (premises.arrayChoice.rename rho)
  arrayRecursion := ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using ops.recursionLaw_subst (Subst.ofRename rho) (ops.vector ⇒ ops.ArrayType))
    (premises.arrayRecursion.rename rho)
  head := ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using ops.headLaw_subst (Subst.ofRename rho)) (premises.head.rename rho)
  tail := ProofSyntax.castIndices rfl
    (by simpa only [subst_ofRename] using ops.tailLaw_subst (Subst.ofRename rho)) (premises.tail.rename rho)

def weaken (premises : ops.ComputationPremises Δ) (type : Ty Base) :
    ops.ComputationPremises (HOL.weakenHyps (σ := type) Δ) := premises.rename Rename.weaken

theorem rename_free (premises : ops.ComputationPremises Δ) (rho : Rename Base Γ Ξ)
    (free : premises.FunctionExtensionalityFree) : (premises.rename rho).FunctionExtensionalityFree := by
  simpa only [FunctionExtensionalityFree, rename, ProofSyntax.functionExtensionalityFree_castIndices,
    ProofSyntax.functionExtensionalityFree_rename] using free

theorem weaken_free (premises : ops.ComputationPremises Δ) (type : Ty Base)
    (free : premises.FunctionExtensionalityFree) : (premises.weaken type).FunctionExtensionalityFree :=
  premises.rename_free Rename.weaken free
end ComputationPremises

def sumAt (first offset total : Term Const Γ ops.number) : Formula Const Γ :=
  .app (.app (.app (weakenCtx Γ (SuccessorOrder.sum ops.zero ops.successor)) first) offset) total

@[simp] theorem sumAt_subst (images : Subst Const Γ Ξ) (first offset total : Term Const Γ ops.number) :
    HOL.subst images (ops.sumAt first offset total) =
      ops.sumAt (HOL.subst images first) (HOL.subst images offset) (HOL.subst images total) := by
  simp only [sumAt, HOL.subst, subst_weakenCtx]

@[simp] theorem sumAt_rename (rho : Rename Base Γ Ξ) (first offset total : Term Const Γ ops.number) :
    HOL.rename rho (ops.sumAt first offset total) =
      ops.sumAt (HOL.rename rho first) (HOL.rename rho offset) (HOL.rename rho total) := by
  simpa only [subst_ofRename] using ops.sumAt_subst (Subst.ofRename rho) first offset total

def suffixPointBody (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) :
    ArgumentBody Const Γ [ops.number,ops.number] := fun images fields =>
  .imp (ops.sumAt (HOL.subst images index) fields.1 fields.2.1)
    (.eq (.app (ops.suffix (HOL.subst images index) (HOL.subst images vector) (HOL.subst images rest)) fields.2.1)
      (.app (HOL.subst images rest) fields.1))

theorem suffixPointBody_natural (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) :
    NaturalBody (ops.suffixPointBody rest index vector) := by
  intro Δ Ω earlier later fields
  simp only [suffixPointBody, HOL.subst, sumAt_subst, suffix_subst, HOL.subst_comp, substituteArguments]
  rfl

def suffixCondition (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) : Formula Const Γ :=
  forallArguments [ops.number,ops.number] (ops.suffixPointBody rest index vector)

@[simp] theorem suffixCondition_subst (images : Subst Const Γ Ξ) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) :
    HOL.subst images (ops.suffixCondition rest index vector) =
      ops.suffixCondition (HOL.subst images rest) (HOL.subst images index) (HOL.subst images vector) := by
  unfold suffixCondition
  rw [forallArguments_subst _ _ _ (ops.suffixPointBody_natural rest index vector)]
  apply congrArg (forallArguments [ops.number,ops.number])
  funext laterContext later fields
  simp only [suffixPointBody, HOL.subst_comp]
  rfl

@[simp] theorem suffixCondition_rename (rho : Rename Base Γ Ξ) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) :
    HOL.rename rho (ops.suffixCondition rest index vector) =
      ops.suffixCondition (HOL.rename rho rest) (HOL.rename rho index) (HOL.rename rho vector) := by
  simpa only [subst_ofRename] using ops.suffixCondition_subst (Subst.ofRename rho) rest index vector

def boundaryMotiveBody (rest : Term Const Γ ops.ArrayType) : ArgumentBody Const Γ [ops.number,ops.vector] :=
  fun images fields => ops.suffixCondition (HOL.subst images rest) fields.1 fields.2.1

theorem boundaryMotiveBody_natural (rest : Term Const Γ ops.ArrayType) : NaturalBody (ops.boundaryMotiveBody rest) := by
  intro Δ Ω earlier later fields
  simp only [boundaryMotiveBody, suffixCondition_subst, HOL.subst_comp, substituteArguments]
  rfl

def boundaryMotive (rest : Term Const Γ ops.ArrayType) : Term Const Γ ops.toSignature.Property :=
  abstractArguments [ops.number,ops.vector] (ops.boundaryMotiveBody rest)

@[simp] theorem boundaryMotive_subst (images : Subst Const Γ Ξ) (rest : Term Const Γ ops.ArrayType) :
    HOL.subst images (ops.boundaryMotive rest) = ops.boundaryMotive (HOL.subst images rest) := by
  unfold boundaryMotive
  rw [abstractArguments_subst _ _ _ (ops.boundaryMotiveBody_natural rest)]
  apply congrArg (abstractArguments [ops.number,ops.vector])
  funext laterContext later fields
  simp only [boundaryMotiveBody, HOL.subst_comp]
  rfl

@[simp] theorem boundaryMotive_rename (rho : Rename Base Γ Ξ) (rest : Term Const Γ ops.ArrayType) :
    HOL.rename rho (ops.boundaryMotive rest) = ops.boundaryMotive (HOL.rename rho rest) := by
  simpa only [subst_ofRename] using ops.boundaryMotive_subst (Subst.ofRename rho) rest

def suffixAt (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (offset total : Term Const Γ ops.number)
    (given : ProofSyntax Const Δ (ops.suffixCondition rest index vector)) :
    ProofSyntax Const Δ (.imp (ops.sumAt index offset total)
      (.eq (.app (ops.suffix index vector rest) total) (.app rest offset))) := by
  apply ProofSyntax.castIndices rfl ?_
    (forallArguments_elim _ _ (ops.suffixPointBody_natural rest index vector) (offset,total,PUnit.unit) given)
  simp only [suffixPointBody, HOL.subst_id]

theorem suffixAt_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) (offset total : Term Const Γ ops.number)
    (given : ProofSyntax Const Δ (ops.suffixCondition rest index vector)) (free : given.FunctionExtensionalityFree) :
    (ops.suffixAt rest index vector offset total given).FunctionExtensionalityFree := by
  unfold suffixAt
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact forallArguments_elim_free _ _ _ _ given free

def boundaryMotive_apply (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) :
    ProofSyntax Const Δ (.eq (PredicatePair.holds (ops.boundaryMotive rest) index vector)
      (ops.suffixCondition rest index vector)) := by
  apply ProofSyntax.castIndices rfl ?_
    (abstractArguments_beta _ _ (ops.boundaryMotiveBody_natural rest) (index,vector,PUnit.unit))
  have identityTerm : HOL.subst (fun entry => Term.var entry) rest = rest :=
    ProofSyntax.term_subst_of_identity (fun _ => rfl) rest
  simp only [boundaryMotiveBody, identityTerm]
  rfl

theorem boundaryMotive_apply_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (vector : Term Const Γ ops.vector) :
    (ops.boundaryMotive_apply (Δ := Δ) rest index vector).FunctionExtensionalityFree := by
  unfold boundaryMotive_apply
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def boundaryBasePoint (rest : Term Const Γ ops.ArrayType) (offset total : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (.imp (ops.sumAt (weakenCtx Γ ops.zero) offset total)
      (.eq (.app (ops.suffix (weakenCtx Γ ops.zero) (weakenCtx Γ ops.nil) rest) total) (.app rest offset))) :=
  .impI (.eqTrans (.eqApp total (ops.suffix_zero (weakenCtx Γ ops.nil) rest
      (premises.arrayChoice.prepend _) (premises.arrayRecursion.prepend _)))
    (.eqAppArg rest (.eqSymm (SuccessorOrder.sumZeroReflect ops.successor ops.zero offset total (.hyp 0)))))

theorem boundaryBasePoint_free (rest : Term Const Γ ops.ArrayType) (offset total : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ) (free : premises.FunctionExtensionalityFree) :
    (ops.boundaryBasePoint rest offset total premises).FunctionExtensionalityFree := by
  unfold boundaryBasePoint
  refine ⟨?_,SuccessorOrder.sumZeroReflect_free _ _ _ _ _ True.intro⟩
  apply ops.suffix_zero_free
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using free.2.2.1
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono] using free.2.2.2.1

def boundaryBaseBranch (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ) :
    ArgumentProof Δ [ops.number,ops.number]
      (ops.suffixPointBody rest (weakenCtx Γ ops.zero) (weakenCtx Γ ops.nil)) := by
  intro Ξ images fields
  apply ProofSyntax.castIndices rfl ?_
    (ops.boundaryBasePoint (HOL.subst images rest) fields.1 fields.2.1 (premises.subst images))
  simp only [suffixPointBody, subst_weakenCtx]

theorem boundaryBaseBranch_free (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ)
    (free : premises.FunctionExtensionalityFree) (images : Subst Const Γ Ξ) fields :
    (ops.boundaryBaseBranch rest premises images fields).FunctionExtensionalityFree := by
  unfold boundaryBaseBranch
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact ops.boundaryBasePoint_free _ _ _ _ (premises.subst_free images free)

def boundaryBase (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (PredicatePair.holds (ops.boundaryMotive rest) (weakenCtx Γ ops.zero) (weakenCtx Γ ops.nil)) :=
  .impE (.eqPropER (ops.boundaryMotive_apply rest _ _))
    (forallArguments_intro _ _ (ops.boundaryBaseBranch rest premises))

theorem boundaryBase_free (rest : Term Const Γ ops.ArrayType) (premises : ops.ComputationPremises Δ)
    (free : premises.FunctionExtensionalityFree) : (ops.boundaryBase rest premises).FunctionExtensionalityFree :=
  ⟨ops.boundaryMotive_apply_free _ _ _,forallArguments_intro_free _ _ _ (ops.boundaryBaseBranch_free rest premises free)⟩

@[simp] theorem suffix_rename (rho : Rename Base Γ Ξ) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) :
    HOL.rename rho (ops.suffix index vector rest) =
      ops.suffix (HOL.rename rho index) (HOL.rename rho vector) (HOL.rename rho rest) := by
  simpa only [subst_ofRename] using ops.suffix_subst (Subst.ofRename rho) index vector rest

@[simp] theorem consValue_rename (rho : Rename Base Γ Ξ) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector) :
    HOL.rename rho (ops.toSignature.consValue index head tail) =
      ops.toSignature.consValue (HOL.rename rho index) (HOL.rename rho head) (HOL.rename rho tail) := by
  simpa only [subst_ofRename] using ops.toSignature.subst_consValue (Subst.ofRename rho) index head tail

def boundarySuccessorAtPredecessor (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (offset total predecessor : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (ops.suffixCondition rest index tail))
    (position : ProofSyntax Const Δ (.eq total (.app (weakenCtx Γ ops.successor) predecessor)))
    (sum : ProofSyntax Const Δ (ops.sumAt index offset predecessor)) :
    ProofSyntax Const Δ (.eq (.app (ops.suffix (.app (weakenCtx Γ ops.successor) index)
      (ops.toSignature.consValue index head tail) rest) total) (.app rest offset)) :=
  .eqTrans (.eqAppArg (ops.suffix (.app (weakenCtx Γ ops.successor) index)
    (ops.toSignature.consValue index head tail) rest) position)
    (.eqTrans (.eqApp (.app (weakenCtx Γ ops.successor) predecessor)
      (ops.suffix_cons index head tail rest premises.arrayChoice premises.arrayRecursion
        (ops.headAt index head tail premises.head) (ops.tailAt index head tail premises.tail)))
      (.eqTrans (ops.prepend_successor head (ops.suffix index tail rest) predecessor
          premises.elementChoice premises.elementRecursion)
        (.impE (ops.suffixAt rest index tail offset predecessor previous) sum)))

theorem boundarySuccessorAtPredecessor_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (offset total predecessor : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (ops.suffixCondition rest index tail))
    (position : ProofSyntax Const Δ (.eq total (.app (weakenCtx Γ ops.successor) predecessor)))
    (sum : ProofSyntax Const Δ (ops.sumAt index offset predecessor))
    (free : premises.FunctionExtensionalityFree) (previousFree : previous.FunctionExtensionalityFree)
    (positionFree : position.FunctionExtensionalityFree) (sumFree : sum.FunctionExtensionalityFree) :
    (ops.boundarySuccessorAtPredecessor rest index head tail offset total predecessor premises previous position sum).FunctionExtensionalityFree := by
  unfold boundarySuccessorAtPredecessor
  exact ⟨positionFree,
    ⟨ops.suffix_cons_free _ _ _ _ _ _ _ _ free.2.2.1 free.2.2.2.1
      (ops.headAt_free _ _ _ _ free.2.2.2.2.1) (ops.tailAt_free _ _ _ _ free.2.2.2.2.2),
      ⟨ops.prepend_successor_free _ _ _ _ _ free.1 free.2.1,
        ⟨ops.suffixAt_free _ _ _ _ _ previous previousFree,sumFree⟩⟩⟩⟩

def boundarySuccessorPoint (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (offset total : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (ops.suffixCondition rest index tail))
    (sum : ProofSyntax Const Δ (ops.sumAt (.app (weakenCtx Γ ops.successor) index) offset total)) :
    ProofSyntax Const Δ (.eq (.app (ops.suffix (.app (weakenCtx Γ ops.successor) index)
      (ops.toSignature.consValue index head tail) rest) total) (.app rest offset)) := by
  have witness := SuccessorOrder.sumLeftSuccessor ops.successor ops.zero index offset total sum
  apply ProofSyntax.exE witness
  let body : Formula Const (ops.number :: Γ) :=
    .and (.eq (weaken total) (.app (weakenCtx _ ops.successor) (.var .vz)))
      (ops.sumAt (weaken index) (weaken offset) (.var .vz))
  let assumptions := body :: weakenHyps Δ
  have supplied : ProofSyntax Const assumptions body := .hyp 0
  have old : ProofSyntax Const assumptions (ops.suffixCondition (weaken rest) (weaken index) (weaken tail)) := by
    apply ProofSyntax.castIndices rfl ?_ ((previous.rename Rename.weaken).prepend body)
    exact ops.suffixCondition_rename Rename.weaken rest index tail
  have result := ops.boundarySuccessorAtPredecessor (weaken rest) (weaken index) (weaken head) (weaken tail)
    (weaken offset) (weaken total) (.var .vz) ((premises.weaken ops.number).prepend body) old (.andEL supplied) (.andER supplied)
  apply ProofSyntax.castIndices rfl ?_ result
  simp only [weaken, HOL.rename, suffix_rename, consValue_rename, rename_weakenCtx]

theorem boundarySuccessorPoint_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (offset total : Term Const Γ ops.number) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (ops.suffixCondition rest index tail))
    (sum : ProofSyntax Const Δ (ops.sumAt (.app (weakenCtx Γ ops.successor) index) offset total))
    (free : premises.FunctionExtensionalityFree) (previousFree : previous.FunctionExtensionalityFree)
    (sumFree : sum.FunctionExtensionalityFree) :
    (ops.boundarySuccessorPoint rest index head tail offset total premises previous sum).FunctionExtensionalityFree := by
  unfold boundarySuccessorPoint
  refine ⟨SuccessorOrder.sumLeftSuccessor_free _ _ _ _ _ sum sumFree, ?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ops.boundarySuccessorAtPredecessor_free
  · exact (premises.weaken ops.number).prepend_free _ (premises.weaken_free ops.number free)
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono, ProofSyntax.functionExtensionalityFree_rename] using previousFree
  · trivial
  · trivial

def boundarySuccessorBranch (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (ops.suffixCondition rest index tail)) :
    ArgumentProof Δ [ops.number,ops.number] (ops.suffixPointBody rest
      (.app (weakenCtx Γ ops.successor) index) (ops.toSignature.consValue index head tail)) := by
  intro Ξ images fields
  have old : ProofSyntax Const (Δ.map (HOL.subst images))
      (ops.suffixCondition (HOL.subst images rest) (HOL.subst images index) (HOL.subst images tail)) :=
    ProofSyntax.castIndices rfl (ops.suffixCondition_subst images rest index tail) (previous.subst images)
  apply ProofSyntax.castIndices rfl ?_
    (.impI (ops.boundarySuccessorPoint (HOL.subst images rest) (HOL.subst images index) (HOL.subst images head)
      (HOL.subst images tail) fields.1 fields.2.1 ((premises.subst images).prepend _) (old.prepend _) (.hyp 0)))
  simp only [suffixPointBody, HOL.subst, subst_weakenCtx, IndexedVectorPredicate.Signature.subst_consValue]
  rfl

theorem boundarySuccessorBranch_free (rest : Term Const Γ ops.ArrayType) (index : Term Const Γ ops.number)
    (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector) (premises : ops.ComputationPremises Δ)
    (previous : ProofSyntax Const Δ (ops.suffixCondition rest index tail))
    (free : premises.FunctionExtensionalityFree) (previousFree : previous.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) fields :
    (ops.boundarySuccessorBranch rest index head tail premises previous images fields).FunctionExtensionalityFree := by
  unfold boundarySuccessorBranch
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ops.boundarySuccessorPoint_free
  · exact (premises.subst images).prepend_free _ (premises.subst_free images free)
  · simpa only [ProofSyntax.prepend, ProofSyntax.functionExtensionalityFree_mono,
      ProofSyntax.functionExtensionalityFree_castIndices, ProofSyntax.functionExtensionalityFree_subst] using previousFree
  · trivial

def boundaryStepPoint (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (ops.toSignature.stepBody elements (ops.boundaryMotive rest) index head tail) := by
  let a := Term.app elements head
  let b := ops.toSignature.member elements index tail
  let c := PredicatePair.holds (ops.boundaryMotive rest) index tail
  refine .impI (.impI (.impI ?_))
  let current := ((premises.prepend a).prepend b).prepend c
  have previous : ProofSyntax Const (c :: b :: a :: Δ) (ops.suffixCondition rest index tail) :=
    .impE (.eqPropEL (ops.boundaryMotive_apply rest index tail)) (.hyp 0)
  exact .impE (.eqPropER (ops.boundaryMotive_apply rest
    (.app (weakenCtx Γ ops.successor) index) (ops.toSignature.consValue index head tail)))
    (forallArguments_intro _ _ (ops.boundarySuccessorBranch rest index head tail current previous))

theorem boundaryStepPoint_free (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (head : Term Const Γ ops.element) (tail : Term Const Γ ops.vector)
    (premises : ops.ComputationPremises Δ) (free : premises.FunctionExtensionalityFree) :
    (ops.boundaryStepPoint elements rest index head tail premises).FunctionExtensionalityFree := by
  unfold boundaryStepPoint
  refine ⟨ops.boundaryMotive_apply_free _ _ _, ?_⟩
  apply forallArguments_intro_free
  intro Ξ images fields
  apply ops.boundarySuccessorBranch_free
  · exact ((premises.prepend _).prepend _).prepend_free _
      ((premises.prepend _).prepend_free _ (premises.prepend_free _ free))
  · exact ⟨ops.boundaryMotive_apply_free _ _ _,True.intro⟩

def boundaryStep (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (premises : ops.ComputationPremises Δ) :
    ProofSyntax Const Δ (ops.toSignature.stepCondition elements (ops.boundaryMotive rest)) := by
  refine .allI (.allI (.allI ?_))
  let elements' := weaken (σ := ops.vector) (weaken (σ := ops.element) (weaken (σ := ops.number) elements))
  let rest' := weaken (σ := ops.vector) (weaken (σ := ops.element) (weaken (σ := ops.number) rest))
  let current := ((premises.weaken ops.number).weaken ops.element).weaken ops.vector
  apply ProofSyntax.castIndices rfl ?_
    (ops.boundaryStepPoint elements' rest' (.var (.vs (.vs .vz))) (.var (.vs .vz)) (.var .vz) current)
  simp only [elements',rest',weaken,boundaryMotive_rename]

theorem boundaryStep_free (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (premises : ops.ComputationPremises Δ) (free : premises.FunctionExtensionalityFree) :
    (ops.boundaryStep elements rest premises).FunctionExtensionalityFree := by
  unfold boundaryStep
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ops.boundaryStepPoint_free
  exact ((premises.weaken ops.number).weaken ops.element).weaken_free ops.vector
    ((premises.weaken ops.number).weaken_free ops.element (premises.weaken_free ops.number free))

def suffixOfMembership (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector)) :
    ProofSyntax Const Δ (ops.suffixCondition rest index vector) :=
  .impE (.eqPropEL (ops.boundaryMotive_apply rest index vector))
    (ops.toSignature.inductionProof elements (ops.boundaryMotive rest) index vector
      (ops.boundaryBase rest premises) (ops.boundaryStep elements rest premises) member)

theorem suffixOfMembership_free (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree) :
    (ops.suffixOfMembership elements rest index vector premises member).FunctionExtensionalityFree :=
  ⟨ops.boundaryMotive_apply_free _ _ _,ops.toSignature.inductionProof_free elements (ops.boundaryMotive rest)
    index vector (ops.boundaryBase rest premises) (ops.boundaryStep elements rest premises) member
    (ops.boundaryBase_free rest premises free) (ops.boundaryStep_free elements rest premises free) memberFree⟩

def valueAfterVector (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (offset total : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (sum : ProofSyntax Const Δ (ops.sumAt index offset total)) :
    ProofSyntax Const Δ (.eq (.app (ops.suffix index vector rest) total) (.app rest offset)) :=
  .impE (ops.suffixAt rest index vector offset total (ops.suffixOfMembership elements rest index vector premises member)) sum

theorem valueAfterVector_free (elements : Term Const Γ (ops.element ⇒ .prop)) (rest : Term Const Γ ops.ArrayType)
    (index : Term Const Γ ops.number) (vector : Term Const Γ ops.vector) (offset total : Term Const Γ ops.number)
    (premises : ops.ComputationPremises Δ)
    (member : ProofSyntax Const Δ (ops.toSignature.member elements index vector))
    (sum : ProofSyntax Const Δ (ops.sumAt index offset total))
    (free : premises.FunctionExtensionalityFree) (memberFree : member.FunctionExtensionalityFree)
    (sumFree : sum.FunctionExtensionalityFree) :
    (ops.valueAfterVector elements rest index vector offset total premises member sum).FunctionExtensionalityFree :=
  ⟨ops.suffixAt_free _ _ _ _ _ _ (ops.suffixOfMembership_free elements rest index vector premises member free memberFree),sumFree⟩

#print axioms valueAfterVector
#print axioms valueAfterVector_free
end Operations
end Mettapedia.Logic.HOL.VectorChildArrays
