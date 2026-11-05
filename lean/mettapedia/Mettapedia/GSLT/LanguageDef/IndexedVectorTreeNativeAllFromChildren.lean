import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditions
import Mettapedia.Logic.HOL.IndexedChildHypotheses
import Mettapedia.Logic.HOL.SuccessorOrderSubstitution
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeVectorAllPositionEvidence

/-!
# Positional induction evidence for the original Vector-tree All interface

Every requested source lookup is connected to the same value in the actual
ordered child array. Its derived-family root and the retained guarded
induction contract supply motive evidence at that value. The original All
producer consumes these positional proofs with its own explicit computation
laws. Evidence remains existential; no global witness is selected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllFromChildren
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open FiniteConstructorEncoding CurriedPredicates
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  {element evidence : Ty Base} {Δ : List (Formula Const Γ)}

def existsMotive (motive : Term Const Γ (element ⇒ evidence ⇒ .prop)) : Term Const Γ (element ⇒ .prop) :=
  .lam (existsValue [] (.app (weaken motive) (.var .vz)))

@[simp] theorem existsMotive_subst (images : Subst Const Γ Ξ)
    (motive : Term Const Γ (element ⇒ evidence ⇒ .prop)) :
    HOL.subst images (existsMotive motive) = existsMotive (HOL.subst images motive) := by
  simp only [existsMotive,HOL.subst,existsValue_subst,subst_weaken,Subst.lift]

@[irreducible] def existsMotive_beta (motive : Term Const Γ (element ⇒ evidence ⇒ .prop)) (point : Term Const Γ element) :
    ProofSyntax Const Δ (.eq (.app (existsMotive motive) point) (existsValue [] (.app motive point))) := by
  apply ProofSyntax.castIndices rfl ?_ (.beta point (existsValue [] (.app (weaken motive) (.var .vz))))
  simp only [existsMotive,instantiate,existsValue_subst,HOL.subst,Subst.single,PredicateFixedPoint.subst_single_weaken]

theorem existsMotive_beta_free (motive : Term Const Γ (element ⇒ evidence ⇒ .prop)) (point : Term Const Γ element) :
    (existsMotive_beta (Δ := Δ) motive point).FunctionExtensionalityFree := by
  unfold existsMotive_beta
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

def indexedMotive (motive : Term Const Γ (element ⇒ evidence ⇒ .prop)) : Term Const Γ (element ⇒ .prop ⇒ .prop) :=
  .lam (.lam (.app (weaken (weaken (existsMotive motive))) (.var (.vs .vz))))

@[simp] theorem indexedMotive_subst (images : Subst Const Γ Ξ)
    (motive : Term Const Γ (element ⇒ evidence ⇒ .prop)) :
    HOL.subst images (indexedMotive motive) = indexedMotive (HOL.subst images motive) := by
  simp only [indexedMotive,HOL.subst,subst_weaken,existsMotive_subst,Subst.lift,HOL.rename,Rename.weaken]

@[irreducible] def indexedMotive_beta (motive : Term Const Γ (element ⇒ evidence ⇒ .prop))
    (point : Term Const Γ element) (target : Term Const Γ .prop) :
    ProofSyntax Const Δ (.eq (.app (.app (indexedMotive motive) point) target) (existsValue [] (.app motive point))) := by
  have reduced : ProofSyntax Const Δ (.eq (.app (.app (indexedMotive motive) point) target)
      (.app (existsMotive motive) point)) := by
    apply ProofSyntax.castIndices rfl ?_ (CurriedGuardProgramProofs.beta2
      (.app (weaken (weaken (existsMotive motive))) (.var (.vs .vz))) point target)
    simp only [indexedMotive,instantiate,HOL.subst,subst_weaken,Subst.lift,Subst.single,
      PredicateFixedPoint.subst_single_weaken]
    rw [← weaken,PredicateFixedPoint.subst_single_weaken]
  exact .eqTrans reduced (existsMotive_beta motive point)

theorem indexedMotive_beta_free (motive : Term Const Γ (element ⇒ evidence ⇒ .prop))
    (point : Term Const Γ element) (target : Term Const Γ .prop) :
    (indexedMotive_beta (Δ := Δ) motive point target).FunctionExtensionalityFree := by
  unfold indexedMotive_beta
  refine ⟨?_,existsMotive_beta_free motive point⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact CurriedGuardProgramProofs.beta2_free _ _ _

variable (original : NativeVectorComputationRows.Operations Base Const)
  (elementSelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.element)))
  (arraySelection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ original.number ⇒ original.element)))
  {A W : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ original.number A original.element)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (original.number ⇒ .prop))
  (one : ClosedTerm Const original.number) (tags : Nat → Term Const Γ original.number)
  (bottom : Term Const Γ original.element) (motive : Term Const Γ (original.element ⇒ W ⇒ .prop))

abbrev arrays := IndexedVectorTreeNativeChildConditions.ReaderGuard.arrays original elementSelection arraySelection
def family := IndexedVectorTreeStoredFamily.family given source numbers original.zero one original.successor tags bottom
def signature := IndexedVectorTreeStoredFamily.signature given source numbers original.zero one original.successor tags bottom
def root := IndexedVectorTreeStoredFamily.root given source numbers original.zero one tags

def inductionPredicate : Term Const Γ (original.element ⇒ .prop) :=
  PredicateFixedPoint.intersection (signature original given source numbers one tags bottom).least
    (IndexedPredicateInduction.lift (root original given source numbers one tags) (indexedMotive motive))

def contract (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector) : Formula Const Γ :=
  (signature original given source numbers one tags bottom).childConditions
    (inductionPredicate original given source numbers one tags bottom motive)
    (IndexedVectorTreeBranchActivity.payload given source numbers original.zero one tags n q)
    ((arrays original elementSelection arraySelection).single n vector bottom)

@[irreducible] def pointEvidence (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (position : Term Const Γ original.number) (point : Term Const Γ original.element)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (lookup : ProofSyntax Const Δ (IndexedVectorPositions.lookup (arrays original elementSelection arraySelection).toSignature n vector position point)) :
    ProofSyntax Const Δ (existsValue [] (.app motive point)) := by
  let ops := arrays original elementSelection arraySelection
  let child := Term.app (ops.single n vector bottom) position
  let bounded := IndexedVectorPositionBounds.lessOfLookup ops.toSignature n vector position point arithmetic.induction lookup
  let active := IndexedVectorTreeBranchActivity.activityFromBound given source numbers original.zero one original.successor tags
    n q position allowed bounded
  let childMember := ops.singleMemberAtBound (family original given source numbers one tags bottom) n vector bottom position
    premises arithmetic member bounded
  let rootProof := IndexedVectorTreeStoredFamily.memberRoot given source numbers original.zero one original.successor tags bottom child childMember
  let hypothesis := (signature original given source numbers one tags bottom).indexedChildHypothesis
    (root original given source numbers one tags) (indexedMotive motive)
    (IndexedVectorTreeBranchActivity.payload given source numbers original.zero one tags n q) (ops.single n vector bottom)
    position .top conditions active rootProof
  let same := ops.singleAtLookup n vector bottom position point premises lookup
  have atPoint : ProofSyntax Const Δ (.app (.app (indexedMotive motive) point) .top) :=
    .impE (.eqPropEL (.eqApp .top (.eqAppArg (indexedMotive motive) same))) (.andER hypothesis)
  exact .impE (.eqPropEL (indexedMotive_beta motive point .top)) atPoint

theorem pointEvidence_free (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (position : Term Const Γ original.number) (point : Term Const Γ original.element)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (lookup : ProofSyntax Const Δ (IndexedVectorPositions.lookup (arrays original elementSelection arraySelection).toSignature n vector position point))
    (allowedFree : allowed.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) (lookupFree : lookup.FunctionExtensionalityFree) :
    (pointEvidence original elementSelection arraySelection given source numbers one tags bottom motive n q vector position point
      allowed premises arithmetic member conditions lookup).FunctionExtensionalityFree := by
  let ops := arrays original elementSelection arraySelection
  let bounded := IndexedVectorPositionBounds.lessOfLookup ops.toSignature n vector position point arithmetic.induction lookup
  have boundedFree : bounded.FunctionExtensionalityFree :=
    IndexedVectorPositionBounds.lessOfLookup_free _ _ _ _ _ _ _ arithmeticFree.2.2 lookupFree
  let childMember := ops.singleMemberAtBound (family original given source numbers one tags bottom) n vector bottom position
    premises arithmetic member bounded
  have childFree : childMember.FunctionExtensionalityFree :=
    ops.singleMemberAtBound_free _ _ _ _ _ premises arithmetic member bounded premisesFree arithmeticFree memberFree boundedFree
  unfold pointEvidence
  refine ⟨indexedMotive_beta_free _ _ _, ?_, ?_⟩
  · exact ops.singleAtLookup_free _ _ _ _ _ premises lookup premisesFree lookupFree
  · apply RecursiveSpacePredicate.Contextual.indexedChildHypothesis_free
    · exact conditionsFree
    · exact IndexedVectorTreeBranchActivity.activityFromBound_free _ _ _ _ _ _ _ _ _ _ _ _ allowedFree boundedFree
    · exact IndexedVectorTreeStoredFamily.memberRoot_free _ _ _ _ _ _ _ _ _ _ childFree

theorem inductionPredicate_subst (images : Subst Const Γ Ξ) :
    HOL.subst images (inductionPredicate original given source numbers one tags bottom motive) =
      inductionPredicate original (given.substitute images) (HOL.subst images source) (HOL.subst images numbers)
        one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom) (HOL.subst images motive) := by
  simp only [inductionPredicate,signature,root,PredicateFixedPoint.subst_intersection,
    IndexedPredicateInduction.subst_lift,indexedMotive_subst,IndexedVectorTreeStoredFamilyTransport.least_subst,
    IndexedVectorTreeStoredFamilyTransport.root_subst]

private theorem childConditions_congr {first second : RecursiveSpacePredicate.Contextual Const Ξ}
    (same : first = second)
    (firstPredicate : Term Const Ξ (first.space ⇒ .prop)) (secondPredicate : Term Const Ξ (second.space ⇒ .prop))
    (firstPayload : Term Const Ξ first.payload) (secondPayload : Term Const Ξ second.payload)
    (firstChildren : Term Const Ξ (first.number ⇒ first.space)) (secondChildren : Term Const Ξ (second.number ⇒ second.space))
    (predicates : HEq firstPredicate secondPredicate) (payloads : HEq firstPayload secondPayload)
    (children : HEq firstChildren secondChildren) :
    first.childConditions firstPredicate firstPayload firstChildren =
      second.childConditions secondPredicate secondPayload secondChildren := by
  cases same
  cases predicates
  cases payloads
  cases children
  rfl

theorem contract_subst (images : Subst Const Γ Ξ) (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector) :
    HOL.subst images (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector) =
      contract original elementSelection arraySelection (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom) (HOL.subst images motive)
        (HOL.subst images n) (HOL.subst images q) (HOL.subst images vector) := by
  unfold contract
  rw [RecursiveSpacePredicate.Contextual.subst_childConditions]
  apply childConditions_congr
    (IndexedVectorTreeStoredFamilyTransport.signature_subst images given source numbers original.zero one original.successor tags bottom)
  · exact heq_of_eq (inductionPredicate_subst original given source numbers one tags bottom motive images)
  · exact heq_of_eq (IndexedVectorTreeNativeChildConditions.payload_subst (arrays original elementSelection arraySelection)
      given source numbers one tags images n q)
  · exact heq_of_eq ((arrays original elementSelection arraySelection).single_subst images n vector bottom)

def mappedVector (images : Subst Const Γ Ξ) (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector)) :
    ProofSyntax Const (Δ.map (HOL.subst images)) ((arrays original elementSelection arraySelection).toSignature.member
      (family original (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)) (HOL.subst images n) (HOL.subst images vector)) :=
  .castIndices rfl (by simp only [IndexedVectorPredicate.Signature.subst_member,family,
    IndexedVectorTreeStoredFamilyTransport.family_subst]) (member.subst images)

theorem mappedVector_free (images : Subst Const Γ Ξ) (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector)) (free : member.FunctionExtensionalityFree) :
    (mappedVector original elementSelection arraySelection given source numbers one tags bottom images n vector member).FunctionExtensionalityFree := by
  unfold mappedVector
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr free

@[irreducible] def mappedContract (images : Subst Const Γ Ξ) (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector)) :
    ProofSyntax Const (Δ.map (HOL.subst images))
      (contract original elementSelection arraySelection (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom) (HOL.subst images motive)
        (HOL.subst images n) (HOL.subst images q) (HOL.subst images vector)) :=
  .castIndices rfl (contract_subst original elementSelection arraySelection given source numbers one tags bottom motive images n q vector)
    (conditions.subst images)

attribute [local irreducible] contract inductionPredicate ProofSyntax.castIndices

theorem mappedContract_free (images : Subst Const Γ Ξ) (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (free : conditions.FunctionExtensionalityFree) :
    (mappedContract original elementSelection arraySelection given source numbers one tags bottom motive images n q vector conditions).FunctionExtensionalityFree := by
  unfold mappedContract
  exact (ProofSyntax.functionExtensionalityFree_castIndices rfl
    (contract_subst original elementSelection arraySelection given source numbers one tags bottom motive images n q vector)
    (conditions.subst images)).mpr ((ProofSyntax.functionExtensionalityFree_subst images conditions).mpr free)

def positionBranch (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector)) :
    ArgumentProof Δ (NativeVectorAll.PositionEvidence.Fields original)
      (NativeVectorAll.PositionEvidence.body original motive n vector) := by
  intro Ξ images fields
  let lookup := IndexedVectorPositions.lookup (arrays original elementSelection arraySelection).toSignature
    (HOL.subst images n) (HOL.subst images vector) fields.1 fields.2.1
  let admitted : ProofSyntax Const (Δ.map (HOL.subst images))
      (IndexedVectorTreeBranchActivity.allowed (given.substitute images) (HOL.subst images source)
        (HOL.subst images numbers) original.zero one (fun i => HOL.subst images (tags i)) (HOL.subst images n) (HOL.subst images q)) :=
    .castIndices rfl (IndexedVectorTreeNativeChildConditions.allowed_subst
      (arrays original elementSelection arraySelection) given source numbers one tags images n q) (allowed.subst images)
  let children := mappedContract original elementSelection arraySelection given source numbers one tags bottom motive images n q vector conditions
  change ProofSyntax Const (Δ.map (HOL.subst images))
    (.imp lookup (existsValue [] (.app (HOL.subst images motive) fields.2.1)))
  exact .impI (pointEvidence original elementSelection arraySelection (given.substitute images) (HOL.subst images source)
    (HOL.subst images numbers) one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom) (HOL.subst images motive)
    (HOL.subst images n) (HOL.subst images q) (HOL.subst images vector) fields.1 fields.2.1
    (admitted.prepend lookup) ((premises.subst images).prepend lookup) ((arithmetic.subst images).prepend lookup)
    ((mappedVector original elementSelection arraySelection given source numbers one tags bottom images n vector member).prepend lookup)
    (children.prepend lookup) (.hyp 0))

theorem positionBranch_free (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (allowedFree : allowed.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) (images : Subst Const Γ Ξ) fields :
    (positionBranch original elementSelection arraySelection given source numbers one tags bottom motive n q vector
      allowed premises arithmetic member conditions images fields).FunctionExtensionalityFree := by
  unfold positionBranch
  apply pointEvidence_free
  · apply (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
    apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact (ProofSyntax.functionExtensionalityFree_subst _ _).mpr allowedFree
  · exact (premises.subst images).prepend_free _ (premises.subst_free images premisesFree)
  · exact (arithmetic.subst images).prepend_free _ (arithmetic.subst_free images arithmeticFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      (mappedVector_free original elementSelection arraySelection given source numbers one tags bottom images n vector member memberFree)
  · exact (ProofSyntax.functionExtensionalityFree_mono _ _).mpr
      (mappedContract_free original elementSelection arraySelection given source numbers one tags bottom motive images n q vector conditions conditionsFree)
  · trivial

@[irreducible] def positionCondition (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector)) :
    ProofSyntax Const Δ (NativeVectorAll.PositionEvidence.condition original motive n vector) :=
  forallArguments_intro _ _ (positionBranch original elementSelection arraySelection given source numbers one tags bottom motive
    n q vector allowed premises arithmetic member conditions)

theorem positionCondition_free (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (allowedFree : allowed.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) :
    (positionCondition original elementSelection arraySelection given source numbers one tags bottom motive n q vector
      allowed premises arithmetic member conditions).FunctionExtensionalityFree := by
  unfold positionCondition
  exact forallArguments_intro_free _ _ _ (positionBranch_free original elementSelection arraySelection
    given source numbers one tags bottom motive n q vector allowed premises arithmetic member conditions
    allowedFree premisesFree arithmeticFree memberFree conditionsFree)

variable (pairs : PredicateSigma.Operations Const W) (witness : ClosedTerm Const W)
  (selection : ClosedTerm Const (SelectionProofs.Selection (original.number ⇒ original.vector ⇒ W ⇒ .prop)))

@[irreducible] def produce (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ) :
    ProofSyntax Const Δ (NativeVectorAll.Existence.query original pairs witness selection
      (family original given source numbers one tags bottom) motive n vector) :=
  NativeVectorAll.PositionEvidence.produce original pairs witness selection
    (family original given source numbers one tags bottom) motive n vector allPremises member
    (positionCondition original elementSelection arraySelection given source numbers one tags bottom motive n q vector
      allowed premises arithmetic member conditions)

theorem produce_free (n q : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (allowed : ProofSyntax Const Δ (IndexedVectorTreeBranchActivity.allowed given source numbers original.zero one tags n q))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ ((arrays original elementSelection arraySelection).toSignature.member
      (family original given source numbers one tags bottom) n vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive n q vector))
    (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ)
    (allowedFree : allowed.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) (allFree : allPremises.FunctionExtensionalityFree) :
    (produce original elementSelection arraySelection given source numbers one tags bottom motive pairs witness selection
      n q vector allowed premises arithmetic member conditions allPremises).FunctionExtensionalityFree := by
  unfold produce
  exact NativeVectorAll.PositionEvidence.produce_free _ _ _ _ _ _ _ _ allPremises member _
    allFree memberFree (positionCondition_free original elementSelection arraySelection given source numbers one tags bottom motive
      n q vector allowed premises arithmetic member conditions allowedFree premisesFree arithmeticFree memberFree conditionsFree)

namespace ReaderGuard

@[irreducible] def produce (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (numeric : ProofSyntax Const Δ (.app numbers n))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
      (family original given source numbers one tags bottom) n) vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive
      n (weakenCtx Γ original.zero) vector))
    (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ) :
    ProofSyntax Const Δ (NativeVectorAll.Existence.query original pairs witness selection
      (family original given source numbers one tags bottom) motive n vector) :=
  IndexedVectorTreeNativeAllFromChildren.produce original elementSelection arraySelection given source numbers one tags bottom motive
    pairs witness selection n (weakenCtx Γ original.zero) vector
    (IndexedVectorTreeNativeChildConditions.numericAllowed (arrays original elementSelection arraySelection)
      given source numbers one tags n numeric) premises arithmetic
    (IndexedVectorTreeNativeChildConditions.ReaderGuard.memberOfGuard original selection _ n vector member) conditions allPremises

theorem produce_free (n : Term Const Γ original.number) (vector : Term Const Γ original.vector)
    (numeric : ProofSyntax Const Δ (.app numbers n))
    (premises : (arrays original elementSelection arraySelection).ComputationPremises Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence original.successor original.zero Δ)
    (member : ProofSyntax Const Δ (.app (NativeVectorAll.Reading.vectorCode original selection
      (family original given source numbers one tags bottom) n) vector))
    (conditions : ProofSyntax Const Δ (contract original elementSelection arraySelection given source numbers one tags bottom motive
      n (weakenCtx Γ original.zero) vector))
    (allPremises : NativeVectorAll.Existence.ComputationPremises original selection Δ)
    (numericFree : numeric.FunctionExtensionalityFree) (premisesFree : premises.FunctionExtensionalityFree)
    (arithmeticFree : arithmetic.Free) (memberFree : member.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) (allFree : allPremises.FunctionExtensionalityFree) :
    (produce original elementSelection arraySelection given source numbers one tags bottom motive pairs witness selection
      n vector numeric premises arithmetic member conditions allPremises).FunctionExtensionalityFree := by
  unfold produce
  exact IndexedVectorTreeNativeAllFromChildren.produce_free original elementSelection arraySelection
    given source numbers one tags bottom motive pairs witness selection n (weakenCtx Γ original.zero) vector
    (IndexedVectorTreeNativeChildConditions.numericAllowed (arrays original elementSelection arraySelection)
      given source numbers one tags n numeric) premises arithmetic
    (IndexedVectorTreeNativeChildConditions.ReaderGuard.memberOfGuard original selection _ n vector member) conditions allPremises
    (IndexedVectorTreeNativeChildConditions.numericAllowed_free _ _ _ _ _ _ _ _ numericFree)
    premisesFree arithmeticFree
    (IndexedVectorTreeNativeChildConditions.ReaderGuard.memberOfGuard_free original selection _ n vector member memberFree)
    conditionsFree allFree

end ReaderGuard

#print axioms indexedMotive_beta_free
#print axioms pointEvidence
#print axioms pointEvidence_free
#print axioms positionCondition_free
#print axioms produce
#print axioms produce_free
#print axioms ReaderGuard.produce_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeAllFromChildren
