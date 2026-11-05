import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamily

/-!
# Original constructor evidence introduces the derived stored family

Both parsed occurrences retain their original fields and computed result.
The complete active-edge, least-membership and inactive-padding child
contract is an explicit proof input. The construction introduces the actual
least/root family; it neither assumes whole membership nor selects a family
predicate by an equality premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyConstructors
open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open FiniteConstructorEncoding IndexedContainerPositionTerms
universe u v
variable {Base : Type u} {Const : Ty Base → Type v} {Γ : Ctx Base} {N A E : Ty Base}
  (given : VectorTreeFieldEmbedding.Inputs Const Γ N A E)
  (source : Term Const Γ (A ⇒ .prop)) (numbers : Term Const Γ (N ⇒ .prop))
  (zero one : ClosedTerm Const N) (successor : ClosedTerm Const (N ⇒ N))
  (tags : Nat → Term Const Γ N) (bottom : Term Const Γ E)

def originalCode (occurrence : Fin 2) :=
  IndexedVectorTreeStoredFieldGuards.codes.get ⟨occurrence.val,by exact occurrence.isLt⟩

variable {Δ : List (Formula Const Γ)}
  (children : Term Const Γ (N ⇒ E))
  (occurrence : Fin (VectorTreeFieldEmbedding.storedSignature N E).length)
  (arguments : Arguments Const Γ
    ((IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one).fields (originalCode occurrence)))
  (evidence : (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one).Evidence Δ
    (originalCode occurrence) Subst.id arguments)

def payload := payloadTerm (IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one)
  IndexedVectorTreeStoredFieldGuards.codes occurrence arguments

def value : Term Const Γ E :=
  (IndexedVectorTreeStoredFamily.inventory given source numbers zero one tags).constructorValue
    (IndexedVectorTreeStoredFamily.construct given) occurrence
    (inventoryArguments (IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one)
      IndexedVectorTreeStoredFieldGuards.codes occurrence arguments) children

theorem originalResult_true :
    (IndexedVectorTreeStoredFieldGuards.reading (Γ := Γ) (E := E) one).indexTerm
      (originalCode occurrence) Subst.id arguments = .top := by
  rcases occurrence with ⟨index,bound⟩
  match index with
  | 0 => rfl
  | 1 => rfl

variable (childProof : ProofSyntax Const Δ
  ((IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).childConditions
    (IndexedVectorTreeStoredFamily.signature given source numbers zero one successor tags bottom).least
    (payload one occurrence arguments) children))

@[irreducible] def constructorMember :
    ProofSyntax Const Δ (.app (IndexedVectorTreeStoredFamily.family
      given source numbers zero one successor tags bottom) (value given source numbers zero one tags children occurrence arguments)) := by
  have original := IndexedContainerInventory.constructorMemberProof IndexedVectorTreeStoredFieldGuards.codes
    (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one) Subst.id tags zero successor bottom
    (IndexedVectorTreeStoredFamily.construct given) children occurrence arguments evidence childProof
  have atTrue : ProofSyntax Const Δ (.app (.app (IndexedVectorTreeStoredFamily.member
      given source numbers zero one successor tags bottom)
      (value given source numbers zero one tags children occurrence arguments)) .top) :=
    .castIndices rfl (congrArg (fun index => Term.app
      (Term.app (IndexedVectorTreeStoredFamily.member given source numbers zero one successor tags bottom)
        (value given source numbers zero one tags children occurrence arguments)) index)
      (originalResult_true one occurrence arguments)) original
  exact .impE (.eqPropER (IndexedVectorTreeStoredFamily.family_application
    given source numbers zero one successor tags bottom
      (value given source numbers zero one tags children occurrence arguments))) atTrue

theorem constructorMember_free
    (fieldFree : (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one).EvidenceFree Δ
      (originalCode occurrence) Subst.id arguments evidence)
    (childFree : childProof.FunctionExtensionalityFree) :
    (constructorMember given source numbers zero one successor tags bottom children occurrence arguments evidence childProof).FunctionExtensionalityFree := by
  unfold constructorMember
  refine ⟨IndexedVectorTreeStoredFamily.family_application_free given source numbers zero one successor tags bottom _,?_⟩
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact IndexedContainerInventory.constructorMemberProof_free IndexedVectorTreeStoredFieldGuards.codes
    (IndexedVectorTreeStoredFieldGuards.guards given source numbers zero one) Subst.id tags zero successor bottom
    (IndexedVectorTreeStoredFamily.construct given) children occurrence arguments evidence childProof fieldFree childFree

#print axioms originalResult_true
#print axioms constructorMember
#print axioms constructorMember_free
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyConstructors
