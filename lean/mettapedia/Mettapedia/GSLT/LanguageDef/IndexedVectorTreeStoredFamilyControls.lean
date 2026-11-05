import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyConstructors
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecoveryControls

/-!
# Retained membership in the actual derived stored family

The original source predicate remains restrictive. The solved field is its
actual represented true value, and its retained field proof introduces the
source witness explicitly. Constructor membership retains the complete child
contract as a hypothesis, independently realizable in the existing model.
No primitive FieldImages interface or source-family equivalence is asserted.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyControls

open Mettapedia.Logic Mettapedia.Logic.HOL Mettapedia.TypeTheory
open FiniteConstructorEncoding IndexedContainerPositionTerms IndexedConstructorGuards
open FiniteConstructorFieldEmbeddingControls (Base N A E Number Element Space)
open VectorTreeSuccessorFixture
open IndexedVectorTreeStoredConstructorRecoveryControls (numbers bottom inventory signature constructor)

def family := IndexedVectorTreeStoredFamily.family given onlyTrue numbers zero one successor numeral bottom
def occurrence : Fin (VectorTreeFieldEmbedding.storedSignature N E).length := ⟨0, by decide⟩
def sourceField : ClosedTerm Const A := .const (.old (.answer true))
def arguments : Arguments Const []
    ((IndexedVectorTreeStoredFieldGuards.reading (Γ := []) (E := E) one).fields
      (IndexedVectorTreeStoredFamilyConstructors.originalCode occurrence)) :=
  (.app given.encode sourceField, PUnit.unit)
abbrev PayloadTy : Ty Base := payloadType (VectorTreeFieldEmbedding.storedSignature N E)
def payload : ClosedTerm Const PayloadTy := IndexedVectorTreeStoredFamilyConstructors.payload one occurrence arguments
def value : ClosedTerm Const E := IndexedVectorTreeStoredFamilyConstructors.value given onlyTrue numbers zero one numeral
  given.children occurrence arguments
def activity : ClosedTerm Const (PayloadTy ⇒ N ⇒ .prop) := signature.active
def childContract : ClosedFormula Const := signature.childConditions signature.least payload given.children

def sourceMember : ProofSyntax Const [childContract] (.app onlyTrue sourceField) :=
  .impE (.eqPropER (.beta sourceField (.eq (.var .vz) (.const (.old (.answer true))))))
    (.eqRefl sourceField)

def imageMember : ProofSyntax Const [childContract]
    (.app (given.predicate onlyTrue) (.app given.encode sourceField)) :=
  ConstructorPredicateRepresentation.introduce given.encode onlyTrue sourceField sourceMember

def evidence : (IndexedVectorTreeStoredFieldGuards.guards given onlyTrue numbers zero one).Evidence
    [childContract] (IndexedVectorTreeStoredFamilyConstructors.originalCode occurrence) Subst.id arguments := by
  refine ⟨?_, PUnit.unit⟩
  apply ProofSyntax.castIndices rfl ?_ imageMember
  exact (congrArg (fun predicate => Term.app predicate (.app given.encode sourceField))
    (IndexedVectorTreeStoredFieldGuards.subst_parameter_id one (given.predicate onlyTrue))).symm

theorem evidence_free : (IndexedVectorTreeStoredFieldGuards.guards given onlyTrue numbers zero one).EvidenceFree
    [childContract] (IndexedVectorTreeStoredFamilyConstructors.originalCode occurrence) Subst.id arguments evidence := by
  unfold evidence
  refine ⟨?_, True.intro⟩
  dsimp only []
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  apply ConstructorPredicateRepresentation.introduce_free
  trivial

def memberProof : ProofSyntax Const [childContract] (.app family value) :=
  IndexedVectorTreeStoredFamilyConstructors.constructorMember given onlyTrue numbers zero one successor numeral bottom
    given.children occurrence arguments evidence (.hyp 0)

theorem memberProof_free : memberProof.FunctionExtensionalityFree :=
  IndexedVectorTreeStoredFamilyConstructors.constructorMember_free (Δ := [childContract])
    given onlyTrue numbers zero one successor numeral bottom given.children occurrence arguments evidence (.hyp 0)
    evidence_free True.intro

def leastProof : ProofSyntax Const [childContract] (.app signature.least value) :=
  IndexedVectorTreeStoredFamily.memberLeast given onlyTrue numbers zero one successor numeral bottom value memberProof

def rootProof : ProofSyntax Const [childContract]
    (.app (.app (IndexedVectorTreeStoredFamily.root given onlyTrue numbers zero one numeral) value) .top) :=
  IndexedVectorTreeStoredFamily.memberRoot given onlyTrue numbers zero one successor numeral bottom value memberProof

theorem leastProof_free : leastProof.FunctionExtensionalityFree :=
  IndexedVectorTreeStoredFamily.memberLeast_free given onlyTrue numbers zero one successor numeral bottom
    value memberProof memberProof_free

theorem rootProof_free : rootProof.FunctionExtensionalityFree :=
  IndexedVectorTreeStoredFamily.memberRoot_free given onlyTrue numbers zero one successor numeral bottom
    value memberProof memberProof_free

private theorem inactive_of_empty_row {B : Type} {C : Ty B → Type} {Γ : Ctx B}
    (interpretation : HenkinModel.{0,0,0} B C) (allValues : interpretation.FullDomains)
    {table : ConstructorPrograms C Γ} (positions : PositionPrograms table)
    (environment : interpretation.Valuation Γ) (selected : Fin table.fields.length)
    (fields : Arguments C Γ (table.fields.get selected))
    (slot : Ty.denote interpretation.Carrier table.number)
    (empty : ∀ index, ¬ positions.related interpretation environment
      ⟨selected,denoteArguments interpretation _ fields environment⟩ slot index) :
    ¬ (interpretation.denote positions.activeProgram environment
      (interpretation.denote (encode table.fields selected fields) environment) slot).down := by
  intro active
  obtain ⟨data, ⟨_, index, related⟩, same⟩ :=
    (positions.activeProgram_denote interpretation allValues environment _ slot).mp active
  have identified := TypeTheory.FiniteConstructorEncoding.encode_injective _ _
    ((encode_denote interpretation table.fields selected fields environment).symm.trans same)
  subst data
  exact empty index related

set_option maxHeartbeats 2000000 in
theorem no_active_position (slot : Ty.denote model.Carrier N) :
    ¬ (model.denote activity values (model.denote payload values) slot).down := by
  exact inactive_of_empty_row model full
    (IndexedVectorTreeStoredConstructorRecovery.positions given onlyTrue numbers zero one successor numeral)
    values occurrence arguments slot (fun _ related => related)

theorem child_contract_realizable : (model.denote childContract values).down := by
  change (model.denote (signature.childConditions signature.least payload given.children) values).down
  simp only [RecursiveSpacePredicate.Contextual.childConditions, HenkinModel.denote, PreModel.denote,
    Soundness.denote_weaken, PreModel.extend]
  intro slot _
  constructor
  · intro active
    exact False.elim (no_active_position slot active)
  · intro _
    exact model.eqv_refl (full _ _)

theorem child_assumptions_realizable : Soundness.SatisfiesHyps model values [childContract] := by
  intro formula member
  obtain rfl := List.mem_singleton.mp member
  exact child_contract_realizable

theorem actual_family_member_holds : (model.denote (.app family value) values).down :=
  Soundness.extDerivation_sound memberProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) child_assumptions_realizable

def falseField : ClosedTerm Const E := .app given.encode (.const (.old (.answer false)))

theorem original_false_field_refused :
    ¬ (model.denote (.app (given.predicate onlyTrue) falseField) values).down := rejected_false

theorem missing_original_field_proof_refused :
    ¬ Nonempty (ProofSyntax Const [] (.app (given.predicate onlyTrue) falseField)) := by
  rintro ⟨proof⟩
  apply original_false_field_refused
  apply Soundness.extDerivation_sound proof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial)
  intro formula member
  cases member

def badChildren : ClosedTerm Const (N ⇒ E) := .lam (weaken value)

theorem value_not_bottom : model.denote value values ≠ model.denote bottom values := by
  intro same
  exact Mettapedia.Languages.HOLLight.RecursiveSpaceSemantics.construct_ne_bottom
    FiniteConstructorFieldEmbeddingControls.filler _ _ _ same

theorem bad_children_value (slot : Ty.denote model.Carrier N) :
    model.denote badChildren values slot = model.denote value values := by
  change model.denote (weaken value) (model.extend values slot) = model.denote value values
  exact Soundness.denote_weaken model value values slot

theorem omitted_padding_refused :
    ¬ (model.denote (signature.childConditions signature.least payload badChildren) values).down := by
  intro present
  simp only [RecursiveSpacePredicate.Contextual.childConditions, HenkinModel.denote, PreModel.denote,
    Soundness.denote_weaken, PreModel.extend] at present
  have atZero := (present (model.denote zero values) (full _ _)).2 (no_active_position _)
  have same := model.eq_of_eqv_of_fullDomains full atZero
  exact value_not_bottom ((bad_children_value _).symm.trans same)

#print axioms evidence_free
#print axioms memberProof
#print axioms memberProof_free
#print axioms leastProof_free
#print axioms rootProof_free
#print axioms no_active_position
#print axioms child_contract_realizable
#print axioms actual_family_member_holds
#print axioms missing_original_field_proof_refused
#print axioms omitted_padding_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredFamilyControls
