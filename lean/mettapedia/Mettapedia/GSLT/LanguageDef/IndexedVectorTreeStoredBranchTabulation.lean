import Mettapedia.Logic.HOL.VectorTabulationObservations
import Mettapedia.Logic.HOL.ConstructorEdgeIndexReadback
import Mettapedia.Logic.HOL.ContextualSlotConditions
import Mettapedia.Logic.HOL.BoundedFunctionEvidence
import Mettapedia.Logic.HOL.OrderedPositionIndexComparisons
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeNativeChildConditions

/-!
# Reifying a native Vector from the original stored branch child contract

The source children remain an arbitrary open function. The actual parsed
branch guard supplies bounded membership in the same derived family and
canonical padding. The selected tabulator then constructs a native Vector;
its reconstructed child function agrees at every position. The original
answer predicate, arity, separate shape field and row occurrence are retained.
No restriction of stored-family admission to a chosen representation image is
introduced, and no whole-function or arbitrary parent-motive transport follows
from the pointwise theorem alone.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchTabulation
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding IndexedConstructorGuards CurriedPredicates OrderedPositionPrograms
namespace Activity
export IndexedVectorTreeBranchActivity
  (inventory positions occurrence plans arguments payload allowed activity activityFromBound activityFromBound_free
   activityReadback activityReadback_free labelProof labelProof_free)
end Activity
namespace Family
export IndexedVectorTreeStoredFamily (family signature construct root family_beta family_beta_free)
end Family
namespace Transport
export IndexedVectorTreeStoredFamilyTransport (signature_subst least_subst family_subst family_rename)
end Transport
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base}
  (ops : VectorChildArrays.Operations Const) {A : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ ops.number A ops.element)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (ops.number ⇒ .prop))
  (one : ClosedTerm Const ops.number) (tags : Nat → Term Const Γ ops.number) (bottom : Term Const Γ ops.element)
  {Δ : List (Formula Const Γ)}

private theorem castFreeForward {H K : List (Formula Const Ξ)} {first second : Formula Const Ξ}
    (proof : ProofSyntax Const H first) (free : proof.FunctionExtensionalityFree)
    (hypotheses : H = K) (formula : first = second) :
    (proof.castIndices hypotheses formula).FunctionExtensionalityFree :=
  (ProofSyntax.functionExtensionalityFree_castIndices hypotheses formula proof).mpr free

@[irreducible] private def moveIndex {H K : List (Formula Const Ξ)} {first second : Formula Const Ξ}
    (proof : ProofSyntax Const H first) (hypotheses : H = K) (formula : first = second) :
    ProofSyntax Const K second := proof.castIndices hypotheses formula

private theorem moveIndex_free {H K : List (Formula Const Ξ)} {first second : Formula Const Ξ}
    (proof : ProofSyntax Const H first) (free : proof.FunctionExtensionalityFree)
    (hypotheses : H = K) (formula : first = second) :
    (moveIndex proof hypotheses formula).FunctionExtensionalityFree := by
  unfold moveIndex
  exact castFreeForward proof free hypotheses formula

def family := Family.family given source numbers ops.zero one ops.successor tags bottom
abbrev signature : RecursiveSpacePredicate.Contextual Const Γ where
  number := ops.number
  payload := payloadType (VectorTreeFieldEmbedding.storedSignature ops.number ops.element)
  space := ops.element
  bottom := bottom
  construct := Family.construct given
  validShape := (Family.signature given source numbers ops.zero one ops.successor tags bottom).validShape
  active := (Activity.positions given source numbers ops.zero one ops.successor tags).activeProgram
  validEdge := (Activity.positions given source numbers ops.zero one ops.successor tags).edgeProgram (Family.construct given)

theorem signature_original : signature ops given source numbers one tags bottom =
    Family.signature given source numbers ops.zero one ops.successor tags bottom := by
  rfl

def payload (n q : Term Const Γ ops.number) :
    Term Const Γ (payloadType (VectorTreeFieldEmbedding.storedSignature ops.number ops.element)) :=
  Activity.payload given source numbers ops.zero one tags n q
def allowed (n q : Term Const Γ ops.number) := Activity.allowed given source numbers ops.zero one tags n q
abbrev contract (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType) : Formula Const Γ :=
  (signature ops given source numbers one tags bottom).childConditions
    (signature ops given source numbers one tags bottom).least (payload ops given source numbers one tags n q) children

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

private theorem least_heq {first second : RecursiveSpacePredicate.Contextual Const Ξ}
    (same : first = second) : HEq first.least second.least := by
  cases same
  rfl

theorem contract_original (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType) :
    contract ops given source numbers one tags bottom n q children =
      (Family.signature given source numbers ops.zero one ops.successor tags bottom).childConditions
        (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
        (Activity.payload given source numbers ops.zero one tags n q) children := by
  unfold contract
  apply childConditions_congr (signature_original ops given source numbers one tags bottom)
  · exact least_heq (signature_original ops given source numbers one tags bottom)
  · rfl
  · rfl

@[irreducible] def fromOriginal (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ
      ((Family.signature given source numbers ops.zero one ops.successor tags bottom).childConditions
        (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
        (Activity.payload given source numbers ops.zero one tags n q) children)) :
    ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children) :=
  moveIndex conditions rfl (contract_original ops given source numbers one tags bottom n q children).symm

theorem fromOriginal_free (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ
      ((Family.signature given source numbers ops.zero one ops.successor tags bottom).childConditions
        (Family.signature given source numbers ops.zero one ops.successor tags bottom).least
        (Activity.payload given source numbers ops.zero one tags n q) children))
    (free : conditions.FunctionExtensionalityFree) :
    (fromOriginal ops given source numbers one tags bottom n q children conditions).FunctionExtensionalityFree := by
  unfold fromOriginal
  exact moveIndex_free conditions free rfl _

theorem signature_subst (images : Subst Const Γ Ξ) :
    (signature ops given source numbers one tags bottom).subst images =
      signature ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom) :=
  (congrArg (fun value => value.subst images) (signature_original ops given source numbers one tags bottom)).trans
    ((Transport.signature_subst images given source numbers ops.zero one ops.successor tags bottom).trans
      (signature_original ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)).symm)

theorem contract_subst (images : Subst Const Γ Ξ) (n q : Term Const Γ ops.number)
    (children : Term Const Γ ops.ArrayType) :
    HOL.subst images (contract ops given source numbers one tags bottom n q children) =
      contract ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)
        (HOL.subst images n) (HOL.subst images q) (HOL.subst images children) := by
  unfold contract
  rw [RecursiveSpacePredicate.Contextual.subst_childConditions]
  apply childConditions_congr
    (signature_subst ops given source numbers one tags bottom images)
  · exact (heq_of_eq ((signature ops given source numbers one tags bottom).subst_least images)).trans
      (least_heq (signature_subst ops given source numbers one tags bottom images))
  · exact heq_of_eq (IndexedVectorTreeNativeChildConditions.payload_subst ops given source numbers one tags images n q)
  · rfl

theorem contract_rename (rho : Rename Base Γ Ξ) (n q : Term Const Γ ops.number)
    (children : Term Const Γ ops.ArrayType) :
    HOL.rename rho (contract ops given source numbers one tags bottom n q children) =
      contract ops (given.substitute (Subst.ofRename rho)) (HOL.rename rho source) (HOL.rename rho numbers) one
        (fun i => HOL.rename rho (tags i)) (HOL.rename rho bottom)
        (HOL.rename rho n) (HOL.rename rho q) (HOL.rename rho children) := by
  simpa only [subst_ofRename] using contract_subst ops given source numbers one tags bottom (Subst.ofRename rho) n q children

@[irreducible] def contractAt (n q slot : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children)) :
    ProofSyntax Const Δ ((signature ops given source numbers one tags bottom).slotConditions
      (signature ops given source numbers one tags bottom).least (payload ops given source numbers one tags n q)
      children slot) :=
  (signature ops given source numbers one tags bottom).slotEvidence
    (signature ops given source numbers one tags bottom).least (payload ops given source numbers one tags n q)
    children slot conditions

set_option backward.isDefEq.respectTransparency true in
theorem contractAt_free (n q slot : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (free : conditions.FunctionExtensionalityFree) :
    (contractAt ops given source numbers one tags bottom n q slot children conditions).FunctionExtensionalityFree := by
  unfold contractAt
  with_reducible
    exact (signature ops given source numbers one tags bottom).slotEvidence_free
      (signature ops given source numbers one tags bottom).least (payload ops given source numbers one tags n q)
      children slot conditions free

@[irreducible] def comparison (n q slot : Term Const Γ ops.number) :
    ProofSyntax Const Δ ((Activity.positions given source numbers ops.zero one ops.successor tags).indexComparison
      (Activity.occurrence given source numbers ops.zero one tags) (Activity.arguments given source numbers ops.zero one tags n q)
      slot .top) :=
  PositionPrograms.uniformIndexComparison (Activity.inventory given source numbers ops.zero one tags) ops.zero ops.successor
    (Activity.plans given source numbers ops.zero one tags) (Activity.occurrence given source numbers ops.zero one tags)
    (Activity.arguments given source numbers ops.zero one tags n q) slot .top (by
      intro position
      change Fin 1 at position
      have same : position = 0 := Subsingleton.elim _ _
      subst position
      exact Activity.labelProof given source numbers ops.zero one tags n q)

@[irreducible] def childRoot (n q slot : Term Const Γ ops.number) (child : Term Const Γ ops.element)
    (edge : ProofSyntax Const Δ (.app (.app (.app
      (signature ops given source numbers one tags bottom).validEdge (payload ops given source numbers one tags n q)) slot) child)) :
    ProofSyntax Const Δ (.app (.app (Family.root given source numbers ops.zero one tags) child) .top) :=
  (Activity.positions given source numbers ops.zero one ops.successor tags).rootAtRequestedIndex
    (Family.construct given) (Activity.occurrence given source numbers ops.zero one tags)
    (Activity.arguments given source numbers ops.zero one tags n q) slot child .top edge
    (comparison ops given source numbers one tags n q slot)

@[irreducible] def memberAtBound (n q slot : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) slot) n)) :
    ProofSyntax Const Δ (.app (family ops given source numbers one tags bottom) (.app children slot)) := by
  have active := Activity.activityFromBound given source numbers ops.zero one ops.successor tags n q slot admitted bound
  have present := ProofSyntax.impE (ProofSyntax.andEL
    (contractAt ops given source numbers one tags bottom n q slot children conditions)) active
  exact .impE (.eqPropER (Family.family_beta given source numbers ops.zero one ops.successor tags bottom (.app children slot)))
    (.andI (.andER present) (childRoot ops given source numbers one tags bottom n q slot (.app children slot) (.andEL present)))

@[irreducible] def paddingAtNotBound (n q slot : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) slot) n))) :
    ProofSyntax Const Δ (.eq (.app children slot) bottom) := by
  have absent : ProofSyntax Const Δ (.not (Activity.activity given source numbers ops.zero one ops.successor tags n q slot)) :=
    .notI (.notE (inactive.prepend _) (.andER (Activity.activityReadback given source numbers ops.zero one ops.successor tags
      n q slot (.hyp 0))))
  exact .impE (.andER (contractAt ops given source numbers one tags bottom n q slot children conditions)) absent

@[irreducible] def boundedBranch (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children)) :
    ArgumentProof Δ [ops.number] (BoundedFunctionEvidence.body ops.toSignature
      (family ops given source numbers one tags bottom) n children) := by
  intro Ξ images fields
  let bound : Formula Const Ξ := .app (.app (weakenCtx _ (SuccessorOrder.less ops.successor)) fields.1) (HOL.subst images n)
  let admitted' : ProofSyntax Const (Δ.map (HOL.subst images))
      (allowed ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images n) (HOL.subst images q)) :=
    .castIndices rfl (IndexedVectorTreeNativeChildConditions.allowed_subst ops given source numbers one tags images n q)
      (admitted.subst images)
  let conditions' : ProofSyntax Const (Δ.map (HOL.subst images))
      (contract ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)
        (HOL.subst images n) (HOL.subst images q) (HOL.subst images children)) :=
    .castIndices rfl (contract_subst ops given source numbers one tags bottom images n q children) (conditions.subst images)
  change ProofSyntax Const (Δ.map (HOL.subst images)) (.imp bound
    (.app (HOL.subst images (family ops given source numbers one tags bottom)) (.app (HOL.subst images children) fields.1)))
  apply ProofSyntax.impI
  let actual := memberAtBound ops (given.substitute images) (HOL.subst images source)
    (HOL.subst images numbers) one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)
    (HOL.subst images n) (HOL.subst images q) fields.1 (HOL.subst images children)
    (admitted'.prepend bound) (conditions'.prepend bound) (.hyp (Δ := bound :: Δ.map (HOL.subst images)) 0)
  have formulaEq :
      (Term.app (family ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers)
        one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)) (.app (HOL.subst images children) fields.1)) =
      (Term.app (HOL.subst images (family ops given source numbers one tags bottom)) (.app (HOL.subst images children) fields.1)) := by
    simp only [family,Transport.family_subst]
  exact moveIndex actual rfl formulaEq

@[irreducible] def boundedFamily (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children)) :
    ProofSyntax Const Δ (VectorTabulation.Shifted.bounded ops.toSignature
      (family ops given source numbers one tags bottom) n children) :=
  BoundedFunctionEvidence.introduce ops.toSignature (family ops given source numbers one tags bottom) n children
    (boundedBranch ops given source numbers one tags bottom n q children admitted conditions)

@[irreducible] def canonicalPadding (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children)) :
    ProofSyntax Const Δ (VectorTabulation.Shifted.paddingCondition ops n children bottom) := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  let rho : Subst Const Γ (ops.number :: Γ) := Subst.ofRename (Rename.weaken (Γ := Γ) (σ := ops.number))
  let inactive : Formula Const (ops.number :: Γ) :=
    .not (.app (.app (weakenCtx _ (SuccessorOrder.less ops.successor)) (.var .vz)) (weaken n))
  have conditions' : ProofSyntax Const (inactive :: weakenHyps Δ)
      (contract ops (given.substitute rho) (weaken source) (weaken numbers) one (fun i => weaken (tags i))
        (weaken bottom) (weaken n) (weaken q) (weaken children)) :=
    .castIndices rfl (contract_rename ops given source numbers one tags bottom Rename.weaken n q children)
      ((conditions.rename Rename.weaken).prepend inactive)
  exact paddingAtNotBound ops (given.substitute rho) (weaken source) (weaken numbers) one (fun i => weaken (tags i))
    (weaken bottom) (weaken n) (weaken q) (.var .vz) (weaken children) conditions' (.hyp (Δ := inactive :: weakenHyps Δ) 0)

def vector (selection : ClosedTerm Const (VectorTabulation.Shifted.Selection ops.toSignature))
    (n : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType) : Term Const Γ ops.vector :=
  VectorTabulation.Shifted.tabulate ops.toSignature selection n children

@[irreducible] def vectorMember (selection : ClosedTerm Const (VectorTabulation.Shifted.Selection ops.toSignature))
    (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (tabulation : VectorTabulation.Shifted.ComputationPremises ops selection Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children)) :
    ProofSyntax Const Δ (ops.toSignature.member (family ops given source numbers one tags bottom) n
      (vector ops selection n children)) :=
  VectorTabulation.Shifted.member ops.toSignature selection (family ops given source numbers one tags bottom)
    n children tabulation.choice tabulation.recursion induction
    (boundedFamily ops given source numbers one tags bottom n q children admitted conditions)

@[irreducible] def childRoundtrip (selection : ClosedTerm Const (VectorTabulation.Shifted.Selection ops.toSignature))
    (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (tabulation : VectorTabulation.Shifted.ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children)) :
    ProofSyntax Const Δ (.all (.eq
      (.app (weaken (ops.single n (vector ops selection n children) bottom)) (.var .vz))
      (.app (weaken children) (.var .vz)))) :=
  VectorTabulation.Shifted.pointwise ops selection (family ops given source numbers one tags bottom)
    n children bottom tabulation arithmetic arrays
    (boundedFamily ops given source numbers one tags bottom n q children admitted conditions)
    (canonicalPadding ops given source numbers one tags bottom n q children conditions)

theorem comparison_free (n q slot : Term Const Γ ops.number) :
    (comparison (Δ := Δ) ops given source numbers one tags n q slot).FunctionExtensionalityFree := by
  unfold comparison
  apply PositionPrograms.uniformIndexComparison_free
  intro position
  change Fin 1 at position
  have same : position = 0 := Subsingleton.elim _ _
  subst position
  exact Activity.labelProof_free given source numbers ops.zero one tags n q

theorem childRoot_free (n q slot : Term Const Γ ops.number) (child : Term Const Γ ops.element)
    (edge : ProofSyntax Const Δ (.app (.app (.app
      (signature ops given source numbers one tags bottom).validEdge (payload ops given source numbers one tags n q)) slot) child))
    (free : edge.FunctionExtensionalityFree) :
    (childRoot ops given source numbers one tags bottom n q slot child edge).FunctionExtensionalityFree := by
  unfold childRoot
  exact PositionPrograms.rootAtRequestedIndex_free _ _ _ _ _ _ _ edge _ free
    (comparison_free ops given source numbers one tags n q slot)

theorem memberAtBound_free (n q slot : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (bound : ProofSyntax Const Δ (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) slot) n))
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (boundFree : bound.FunctionExtensionalityFree) :
    (memberAtBound ops given source numbers one tags bottom n q slot children admitted conditions bound).FunctionExtensionalityFree := by
  let active := Activity.activityFromBound given source numbers ops.zero one ops.successor tags n q slot admitted bound
  let present := ProofSyntax.impE (ProofSyntax.andEL
    (contractAt ops given source numbers one tags bottom n q slot children conditions)) active
  have presentFree : present.FunctionExtensionalityFree := And.intro
    (contractAt_free ops given source numbers one tags bottom n q slot children conditions conditionsFree)
    (Activity.activityFromBound_free given source numbers ops.zero one ops.successor tags n q slot admitted bound admittedFree boundFree)
  unfold memberAtBound
  exact ⟨Family.family_beta_free given source numbers ops.zero one ops.successor tags bottom (.app children slot),presentFree,
    childRoot_free ops given source numbers one tags bottom n q slot (.app children slot) (.andEL present) presentFree⟩

theorem paddingAtNotBound_free (n q slot : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (inactive : ProofSyntax Const Δ (.not (.app (.app (weakenCtx Γ (SuccessorOrder.less ops.successor)) slot) n)))
    (conditionsFree : conditions.FunctionExtensionalityFree) (inactiveFree : inactive.FunctionExtensionalityFree) :
    (paddingAtNotBound ops given source numbers one tags bottom n q slot children conditions inactive).FunctionExtensionalityFree := by
  unfold paddingAtNotBound
  exact ⟨contractAt_free ops given source numbers one tags bottom n q slot children conditions conditionsFree,
    (ProofSyntax.functionExtensionalityFree_mono _ _).mpr inactiveFree,
    Activity.activityReadback_free given source numbers ops.zero one ops.successor tags n q slot
      (.hyp (Δ := Activity.activity given source numbers ops.zero one ops.successor tags n q slot :: Δ) 0) True.intro⟩

theorem boundedBranch_free (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree)
    (images : Subst Const Γ Ξ) (fields : Arguments Const Ξ [ops.number]) :
    (boundedBranch ops given source numbers one tags bottom n q children admitted conditions images fields).FunctionExtensionalityFree := by
  let bound : Formula Const Ξ := .app (.app (weakenCtx _ (SuccessorOrder.less ops.successor)) fields.1) (HOL.subst images n)
  let admitted' : ProofSyntax Const (Δ.map (HOL.subst images))
      (allowed ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images n) (HOL.subst images q)) :=
    .castIndices rfl (IndexedVectorTreeNativeChildConditions.allowed_subst ops given source numbers one tags images n q)
      (admitted.subst images)
  let conditions' : ProofSyntax Const (Δ.map (HOL.subst images))
      (contract ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers) one
        (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)
        (HOL.subst images n) (HOL.subst images q) (HOL.subst images children)) :=
    .castIndices rfl (contract_subst ops given source numbers one tags bottom images n q children) (conditions.subst images)
  let actual := memberAtBound ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers)
    one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)
    (HOL.subst images n) (HOL.subst images q) fields.1 (HOL.subst images children)
    (admitted'.prepend bound) (conditions'.prepend bound) (.hyp (Δ := bound :: Δ.map (HOL.subst images)) 0)
  have actualFree : actual.FunctionExtensionalityFree := by
    apply memberAtBound_free
    · simpa only [admitted',ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
        ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_subst] using admittedFree
    · simpa only [conditions',ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono,
        ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.functionExtensionalityFree_subst] using conditionsFree
    · trivial
  have formulaEq :
      (Term.app (family ops (given.substitute images) (HOL.subst images source) (HOL.subst images numbers)
        one (fun i => HOL.subst images (tags i)) (HOL.subst images bottom)) (.app (HOL.subst images children) fields.1)) =
      (Term.app (HOL.subst images (family ops given source numbers one tags bottom)) (.app (HOL.subst images children) fields.1)) := by
    simp only [family,Transport.family_subst]
  have transportedFree := moveIndex_free actual actualFree rfl formulaEq
  simpa only [boundedBranch,id_eq,ProofSyntax.FunctionExtensionalityFree] using transportedFree

theorem boundedFamily_free (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (boundedFamily ops given source numbers one tags bottom n q children admitted conditions).FunctionExtensionalityFree := by
  unfold boundedFamily
  exact BoundedFunctionEvidence.introduce_free _ _ _ _ _
    (boundedBranch_free ops given source numbers one tags bottom n q children admitted conditions admittedFree conditionsFree)

theorem canonicalPadding_free (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (free : conditions.FunctionExtensionalityFree) :
    (canonicalPadding ops given source numbers one tags bottom n q children conditions).FunctionExtensionalityFree := by
  unfold canonicalPadding
  apply paddingAtNotBound_free
  · simpa only [ProofSyntax.functionExtensionalityFree_castIndices,ProofSyntax.prepend,
      ProofSyntax.functionExtensionalityFree_mono,ProofSyntax.functionExtensionalityFree_rename] using free
  · trivial

theorem vectorMember_free (selection : ClosedTerm Const (VectorTabulation.Shifted.Selection ops.toSignature))
    (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (tabulation : VectorTabulation.Shifted.ComputationPremises ops selection Δ)
    (induction : ProofSyntax Const Δ (NaturalRecursionProofs.inductionPrinciple
      (weakenCtx Γ ops.zero) (weakenCtx Γ ops.successor)))
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (tabulationFree : tabulation.Free) (inductionFree : induction.FunctionExtensionalityFree)
    (admittedFree : admitted.FunctionExtensionalityFree) (conditionsFree : conditions.FunctionExtensionalityFree) :
    (vectorMember ops given source numbers one tags bottom selection n q children tabulation induction admitted conditions).FunctionExtensionalityFree := by
  unfold vectorMember
  exact VectorTabulation.Shifted.member_free _ _ _ _ _ _ _ _ _ tabulationFree.1 tabulationFree.2 inductionFree
    (boundedFamily_free _ _ _ _ _ _ _ _ _ _ _ _ admittedFree conditionsFree)

theorem childRoundtrip_free (selection : ClosedTerm Const (VectorTabulation.Shifted.Selection ops.toSignature))
    (n q : Term Const Γ ops.number) (children : Term Const Γ ops.ArrayType)
    (tabulation : VectorTabulation.Shifted.ComputationPremises ops selection Δ)
    (arithmetic : SuccessorOrder.PeanoEvidence ops.successor ops.zero Δ)
    (arrays : ops.ComputationPremises Δ)
    (admitted : ProofSyntax Const Δ (allowed ops given source numbers one tags n q))
    (conditions : ProofSyntax Const Δ (contract ops given source numbers one tags bottom n q children))
    (tabulationFree : tabulation.Free) (arithmeticFree : arithmetic.Free)
    (arraysFree : arrays.FunctionExtensionalityFree) (admittedFree : admitted.FunctionExtensionalityFree)
    (conditionsFree : conditions.FunctionExtensionalityFree) :
    (childRoundtrip ops given source numbers one tags bottom selection n q children tabulation arithmetic arrays admitted conditions).FunctionExtensionalityFree := by
  unfold childRoundtrip
  exact VectorTabulation.Shifted.pointwise_free _ _ _ _ _ _ _ _ _ _ _ tabulationFree arithmeticFree arraysFree
    (boundedFamily_free _ _ _ _ _ _ _ _ _ _ _ _ admittedFree conditionsFree)
    (canonicalPadding_free _ _ _ _ _ _ _ _ _ _ _ conditionsFree)

#print axioms comparison
#print axioms memberAtBound
#print axioms boundedFamily
#print axioms canonicalPadding
#print axioms vectorMember
#print axioms vectorMember_free
#print axioms childRoundtrip_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredBranchTabulation
