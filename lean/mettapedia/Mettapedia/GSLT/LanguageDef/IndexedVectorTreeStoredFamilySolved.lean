import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeBranchActivity
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyConstructors
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyTransport

/-!
# The original solved constructor introduces the derived family

Its actual parsed position plan is empty. Encoded activity therefore implies
an empty existential. Constant-bottom children discharge the complete child
contract, including inactive padding. The original answer predicate supplies
the only field premise; no child-contract or whole-membership premise is used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilySolved
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open FiniteConstructorEncoding IndexedConstructorGuards
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ Ξ : Ctx Base} {N A E : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)
  {Δ : List (Formula Const Γ)}

def occurrence : Fin (VectorTreeFieldEmbedding.storedSignature N E).length := ⟨0,by change 0 < 2; decide⟩
def payload (field : Term Const Γ E) : Term Const Γ (payloadType (VectorTreeFieldEmbedding.storedSignature N E)) :=
  encode (VectorTreeFieldEmbedding.storedSignature N E) occurrence (field,PUnit.unit)
def children : Term Const Γ (N ⇒ E) := .lam (weaken bottom)
def signature := IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom

@[irreducible] def inactive (field : Term Const Γ E) (slot : Term Const Γ N) :
    ProofSyntax Const Δ (.not (.app (.app
      (IndexedVectorTreeBranchActivity.positions given source numbers zero one successor tags).activeProgram
      (payload field)) slot)) := by
  apply ProofSyntax.notI
  let active := Term.app (.app
    (IndexedVectorTreeBranchActivity.positions given source numbers zero one successor tags).activeProgram
    (payload field)) slot
  have original := PositionPrograms.activityToCanonical
    (Δ := active :: Δ)
    (IndexedVectorTreeBranchActivity.inventory given source numbers zero one tags) zero successor
    (IndexedVectorTreeBranchActivity.plans given source numbers zero one tags)
    occurrence (field,PUnit.unit) [] OrderedPositionPrograms.PlanEquations.nil slot (.hyp 0)
  exact .exE (.andER original) (.hyp 0)

theorem inactive_free (field : Term Const Γ E) (slot : Term Const Γ N) :
    (inactive given source numbers zero one successor tags (Δ := Δ) field slot).FunctionExtensionalityFree := by
  unfold inactive
  refine And.intro ?_ True.intro
  exact PositionPrograms.activityToCanonical_free _ _ _ _ _ _ _ _ _ _ True.intro True.intro

theorem payload_rename (rho : Rename Base Γ Ξ) (field : Term Const Γ E) :
    HOL.rename rho (payload (N := N) field) = payload (HOL.rename rho field) := by
  have mapped : substituteArguments (Subst.ofRename rho)
      ((VectorTreeFieldEmbedding.storedSignature N E).get occurrence) (field,PUnit.unit) =
      (HOL.rename rho field,PUnit.unit) := by
    change (subst (Subst.ofRename rho) field,PUnit.unit) = _
    rw [subst_ofRename]
  simpa only [payload, mapped, subst_ofRename] using
    encode_subst (Subst.ofRename rho) (VectorTreeFieldEmbedding.storedSignature N E) occurrence (field,PUnit.unit)

@[irreducible] private def raisedInactive (field : Term Const Γ E) :
    ProofSyntax Const (weakenHyps (σ := N) Δ)
      (.not (.app (.app (weaken (signature given source numbers zero one successor tags bottom).active)
        (weaken (payload field))) (.var .vz))) :=
  ProofSyntax.castIndices rfl (by
    have moved := IndexedVectorTreeStoredFamilyTransport.active_rename
      given source numbers zero one successor tags (Rename.weaken (σ := N))
    have activeCode : (signature given source numbers zero one successor tags bottom).active =
        (IndexedVectorTreeStoredConstructorRecovery.positions given source numbers zero one successor tags).activeProgram := rfl
    simp only [activeCode, IndexedVectorTreeBranchActivity.positions, weaken, moved, payload_rename])
    (inactive (given.substitute (Subst.ofRename (Rename.weaken (σ := N))))
      (weaken source) (weaken numbers) zero one successor (fun i => weaken (tags i))
      (Δ := weakenHyps (σ := N) Δ) (weaken field) (.var .vz))

set_option maxHeartbeats 1000000 in
private theorem raisedInactive_free (field : Term Const Γ E) :
    (raisedInactive given source numbers zero one successor tags bottom (Δ := Δ) field).FunctionExtensionalityFree := by
  unfold raisedInactive
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact inactive_free _ _ _ _ _ _ _ _ _

@[irreducible] private def paddingAt {B : Type u} {C : Ty B → Type v} {Ω : Ctx B}
    {number element : Ty B} {assumptions : List (Formula C Ω)}
    (bottom : Term C Ω element) (slot : Term C Ω number) :
    ProofSyntax C assumptions (.eq (.app (.lam (weaken bottom)) slot) bottom) :=
  ProofSyntax.castIndices rfl (congrArg (Term.eq (.app (.lam (weaken bottom)) slot))
    (instantiate_weaken slot bottom)) (.beta slot (weaken bottom))

private theorem paddingAt_free {B : Type u} {C : Ty B → Type v} {Ω : Ctx B}
    {number element : Ty B} {assumptions : List (Formula C Ω)}
    (bottom : Term C Ω element) (slot : Term C Ω number) :
    (paddingAt (assumptions := assumptions) bottom slot).FunctionExtensionalityFree := by
  unfold paddingAt
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr True.intro

@[irreducible] def childConditions (field : Term Const Γ E) :
    ProofSyntax Const Δ ((signature given source numbers zero one successor tags bottom).childConditions
      (signature given source numbers zero one successor tags bottom).least (payload field) (children bottom)) := by
  let absent := raisedInactive given source numbers zero one successor tags bottom (Δ := Δ) field
  apply RecursiveSpacePredicate.Contextual.childConditions_intro
  · exact .impI (.botE (.notE (absent.prepend _) (.hyp 0)))
  · exact .impI (.botE (.notE (absent.prepend _) (.hyp 0)))
  · apply ProofSyntax.impI
    apply ProofSyntax.castIndices rfl ?_ (paddingAt (weaken bottom) (.var (.vz : Var (N :: Γ) N)))
    simp only [children, HOL.weaken, HOL.rename, HOL.rename_comp]
    rfl

set_option maxHeartbeats 1000000 in
theorem childConditions_free (field : Term Const Γ E) :
    (childConditions given source numbers zero one successor tags bottom (Δ := Δ) field).FunctionExtensionalityFree := by
  unfold childConditions
  apply RecursiveSpacePredicate.Contextual.childConditions_intro_free
  · refine ⟨?_,True.intro⟩
    simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using
      (raisedInactive_free given source numbers zero one successor tags bottom (Δ := Δ) field)
  · refine ⟨?_,True.intro⟩
    simpa only [ProofSyntax.prepend,ProofSyntax.functionExtensionalityFree_mono] using
      (raisedInactive_free given source numbers zero one successor tags bottom (Δ := Δ) field)
  · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
    exact paddingAt_free _ _

def arguments (field : Term Const Γ E) : Arguments Const Γ
    ((IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one).fields
      (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence (N := N) (E := E)))) :=
  (field,PUnit.unit)

def value (field : Term Const Γ E) : Term Const Γ E :=
  IndexedVectorTreeStoredFamilyConstructors.value given source numbers zero one tags (children bottom)
    occurrence (arguments one field)

private def fieldEvidence (field : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (given.predicate source) field)) :
    (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one).Evidence Δ
      (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence (N := N) (E := E))) Subst.id (arguments one field) := by
  refine ⟨?_,PUnit.unit⟩
  apply ProofSyntax.castIndices rfl ?_ present
  exact (congrArg (fun predicate => Term.app predicate field)
    (IndexedVectorTreeStoredFieldGuards.subst_parameter_id one (given.predicate source))).symm

private theorem fieldEvidence_free (field : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (given.predicate source) field))
    (free : present.FunctionExtensionalityFree) :
    (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one).EvidenceFree Δ
      (IndexedVectorTreeStoredFamilyConstructors.originalCode (occurrence (N := N) (E := E))) Subst.id
      (arguments one field) (fieldEvidence given source numbers zero one field present) := by
  unfold fieldEvidence
  refine ⟨?_,True.intro⟩
  dsimp only []
  exact (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr free

@[irreducible] def member (field : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (given.predicate source) field)) :
    ProofSyntax Const Δ (.app (IndexedVectorTreeStoredFamily.family
      given source numbers zero one successor tags bottom)
      (value given source numbers zero one tags bottom field)) :=
  IndexedVectorTreeStoredFamilyConstructors.constructorMember
    given source numbers zero one successor tags bottom (children bottom) occurrence (arguments one field)
    (fieldEvidence given source numbers zero one field present)
    (childConditions given source numbers zero one successor tags bottom field)

theorem member_free (field : Term Const Γ E)
    (present : ProofSyntax Const Δ (.app (given.predicate source) field))
    (free : present.FunctionExtensionalityFree) :
    (member given source numbers zero one successor tags bottom field present).FunctionExtensionalityFree := by
  unfold member
  exact IndexedVectorTreeStoredFamilyConstructors.constructorMember_free _ _ _ _ _ _ _ _ _ _ _ _ _
    (fieldEvidence_free given source numbers zero one field present free)
    (childConditions_free given source numbers zero one successor tags bottom field)

def fromAnswer (answer : Term Const Γ A) (present : ProofSyntax Const Δ (.app source answer)) :
    ProofSyntax Const Δ (.app (IndexedVectorTreeStoredFamily.family
      given source numbers zero one successor tags bottom)
      (value given source numbers zero one tags bottom (.app given.encode answer))) :=
  member given source numbers zero one successor tags bottom (.app given.encode answer)
    (ConstructorPredicateRepresentation.introduce given.encode source answer present)

theorem fromAnswer_free (answer : Term Const Γ A) (present : ProofSyntax Const Δ (.app source answer))
    (free : present.FunctionExtensionalityFree) :
    (fromAnswer given source numbers zero one successor tags bottom answer present).FunctionExtensionalityFree :=
  member_free given source numbers zero one successor tags bottom (.app given.encode answer) _
    (ConstructorPredicateRepresentation.introduce_free given.encode source answer present free)

#print axioms inactive
#print axioms inactive_free
#print axioms childConditions
#print axioms childConditions_free
#print axioms member_free
#print axioms fromAnswer_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilySolved
