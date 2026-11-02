import Mettapedia.GSLT.LanguageDef.AdmittedContainerProofs
import Mettapedia.GSLT.LanguageDef.AdmittedContainerPredicateControls

/-!
# Admitted Vector retained-membership controls

Both constructor schemas retain their complete child-condition hypothesis.
The result index is computed from the original source fields. A semantic
negative control refutes a closed membership proof for bottom in the same
admitted family; parent-only root evidence does not remove this boundary.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerProofControls
open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open AdmittedContainerHOL AdmittedContainerGeneratedControls
open AdmittedContainerPredicateControls.Closed (zeroCode successorCode program)
open IndexedContainerPositionTerms

noncomputable section

def recursive := recursiveSignature block registered (guards := guards) Subst.id numeral
  zeroCode successorCode bottomCode constructorCode

def nilConditions : ClosedFormula Symbol := recursive.childConditions recursive.least
  (payloadTerm reading (codes block registered) nilOccurrence nilArguments) bottomChildren
def consConditions : ClosedFormula Symbol := recursive.childConditions recursive.least
  (payloadTerm reading (codes block registered) consOccurrence consArguments) bottomChildren

@[irreducible] def nilMember : ProofSyntax Symbol [nilConditions] (.app (.app program nilProgram) nilIndex) :=
  constructorMemberProof block registered guards Subst.id numeral zeroCode successorCode bottomCode constructorCode
    bottomChildren nilOccurrence nilArguments PUnit.unit (.hyp 0)

def consFields : guards.Evidence [consConditions] (codeAt reading (codes block registered) consOccurrence) Subst.id consArguments :=
  ⟨.impE (.eqPropER (.beta _ _)) .topI, .impE (.eqPropER (.beta _ _)) .topI, PUnit.unit⟩

theorem consFields_free : guards.EvidenceFree [consConditions]
    (codeAt reading (codes block registered) consOccurrence) Subst.id consArguments consFields := by
  change _ ∧ _ ∧ True
  simp only [consFields, ProofSyntax.FunctionExtensionalityFree, and_self]

@[irreducible] def consMember : ProofSyntax Symbol [consConditions] (.app (.app program consProgram) consIndex) :=
  constructorMemberProof block registered guards Subst.id numeral zeroCode successorCode bottomCode constructorCode
    bottomChildren consOccurrence consArguments consFields (.hyp 0)

theorem nilMember_free : nilMember.FunctionExtensionalityFree := by
  unfold nilMember
  exact constructorMemberProof_free block registered guards Subst.id numeral zeroCode successorCode bottomCode constructorCode
    bottomChildren nilOccurrence nilArguments PUnit.unit
    (show ProofSyntax Symbol [nilConditions] nilConditions from .hyp 0) True.intro True.intro

theorem consMember_free : consMember.FunctionExtensionalityFree := by
  unfold consMember
  exact constructorMemberProof_free block registered guards Subst.id numeral zeroCode successorCode bottomCode constructorCode
    bottomChildren consOccurrence consArguments consFields (.hyp 0) consFields_free True.intro

def nilRootFromMember : ProofSyntax Symbol [nilConditions]
    (.app (.app (constructorInventory.rootProgram constructorCode) nilProgram) nilIndex) :=
  memberRoot block registered guards Subst.id numeral zeroCode successorCode bottomCode constructorCode _ _ nilMember

theorem nilRootFromMember_free : nilRootFromMember.FunctionExtensionalityFree :=
  memberRoot_free block registered guards Subst.id numeral zeroCode successorCode bottomCode constructorCode _ _ nilMember nilMember_free

theorem nil_index_source : model.denote nilIndex empty = interpreted.index IndexedInductiveNatVec.Natural.zero :=
  nilIndex_meaning
theorem cons_index_source : model.denote consIndex empty =
    interpreted.index (IndexedInductiveNatVec.Natural.succ IndexedInductiveNatVec.Natural.zero) := consIndex_meaning

theorem bottom_has_no_closed_member_proof :
    ¬ Nonempty (ProofSyntax Symbol [] (.app (.app program bottomCode) nilIndex)) := by
  rintro ⟨proof⟩
  have valid := Soundness.extDerivation_sound proof.erase (M := model) (ρ := empty)
    (model.functionsRespectEqv_of_fullDomains full) (by intro _ impossible; nomatch impossible)
    (by intro _ impossible; nomatch impossible)
  change (model.denote program empty (model.denote bottomCode empty) (model.denote nilIndex empty)).down at valid
  rw [nilIndex_meaning] at valid
  exact AdmittedContainerPredicateControls.Closed.bottom_refused IndexedInductiveNatVec.Natural.zero valid

theorem root_and_bad_child_controls :
    IndexedPolynomial.RecursiveSpaceRepresentation.ConstructorRoot
      (IndexedPositiveContainer.RecursiveSpaceRepresentation.blockPresentation sourceOrder block registered)
      (nativePayload block registered sourceOrder interpreted)
      (fun _ => nativeConstructor block registered sourceOrder interpreted constructorCode empty)
      environment (IndexedInductiveNatVec.Natural.succ IndexedInductiveNatVec.Natural.zero)
      (model.denote consProgram empty) ∧
      ¬ (model.denote program empty badConsValue
        (interpreted.index (IndexedInductiveNatVec.Natural.succ IndexedInductiveNatVec.Natural.zero))).down :=
  ⟨compiled_cons_root, AdmittedContainerPredicateControls.Closed.bad_child_refused⟩

namespace Open
abbrev ConstructorType := number ⇒ payload ⇒ (number ⇒ space) ⇒ space
abbrev context : Ctx BaseCode := [number ⇒ space, ConstructorType, space, element, number]

def substitution : Subst Symbol [] context := fun impossible => nomatch impossible
def numeral : Nat → Term Symbol context number
  | 0 => .const .zero
  | n + 1 => .app (.const .successor) (numeral n)

def sourceGuards : FieldGuards reading where
  value _ := .lam .top
  shape _ _ impossible _ := by cases impossible

theorem sourceGuards_agree : sourceGuards = guards := by
  unfold sourceGuards guards IndexedInductiveHOLRealization.guards
  congr 1
  · funext sort
    cases sort <;> rfl

theorem sourceGuards_images : FieldImages interpreted sourceGuards :=
  sourceGuards_agree.symm ▸ images

def bottom : Term Symbol context space := .var (.vs (.vs .vz))
def construct : Term Symbol context ConstructorType := .var (.vs .vz)
def children : Term Symbol context (number ⇒ space) := .var .vz
def arguments : FiniteConstructorEncoding.Arguments Symbol context
    (reading.fields (codeAt reading (codes block registered) consOccurrence)) :=
  (.var (.vs (.vs (.vs (.vs .vz)))), .var (.vs (.vs (.vs .vz))), PUnit.unit)

def fieldEvidence : sourceGuards.Evidence ([] : List (Formula Symbol context))
    (codeAt reading (codes block registered) consOccurrence) substitution arguments :=
  ⟨.impE (.eqPropER (.beta _ _)) .topI, .impE (.eqPropER (.beta _ _)) .topI, PUnit.unit⟩

def signature := recursiveSignature block registered (guards := sourceGuards) substitution numeral zeroCode successorCode bottom construct
def conditions := signature.childConditions signature.least
  (payloadTerm reading (codes block registered) consOccurrence arguments) children
def sourceInventory := inventory block registered sourceGuards substitution numeral
def value := sourceInventory.constructorValue construct consOccurrence
  (inventoryArguments reading (codes block registered) consOccurrence arguments) children
def index := reading.indexTerm (codeAt reading (codes block registered) consOccurrence) substitution arguments
def program := memberProgram block registered (guards := sourceGuards) substitution numeral zeroCode successorCode bottom construct

def parentShape : ProofSyntax Symbol [] (signature.shapeAt (numeral consOccurrence.val)
    (payloadTerm reading (codes block registered) consOccurrence arguments)) :=
  .impE (.eqPropER (sourceInventory.shapeProgram_beta _ _))
    (sourceGuards.shapeProof (codes block registered) substitution numeral consOccurrence arguments fieldEvidence)

theorem parentShape_free : parentShape.FunctionExtensionalityFree := by
  refine ⟨sourceInventory.shapeProgram_beta_free _ _, ?_⟩
  apply sourceGuards.shapeProof_free
  change _ ∧ _ ∧ True
  simp only [fieldEvidence, ProofSyntax.FunctionExtensionalityFree, and_self]

def parentRoot : ProofSyntax Symbol [] (.app (.app (sourceInventory.rootProgram construct) value) index) :=
  .impE (.eqPropER (sourceInventory.rootProgram_beta construct _ _))
    (rootProof block registered sourceGuards substitution numeral construct children consOccurrence arguments fieldEvidence)

theorem parentRoot_free : parentRoot.FunctionExtensionalityFree := by
  refine ⟨sourceInventory.rootProgram_beta_free construct _ _, ?_⟩
  apply rootProof_free
  change _ ∧ _ ∧ True
  simp only [fieldEvidence, ProofSyntax.FunctionExtensionalityFree, and_self]

def fieldsAtPremise : sourceGuards.Evidence [conditions]
    (codeAt reading (codes block registered) consOccurrence) substitution arguments :=
  ⟨.impE (.eqPropER (.beta _ _)) .topI, .impE (.eqPropER (.beta _ _)) .topI, PUnit.unit⟩

theorem fieldsAtPremise_free : sourceGuards.EvidenceFree [conditions]
    (codeAt reading (codes block registered) consOccurrence) substitution arguments fieldsAtPremise := by
  change _ ∧ _ ∧ True
  simp only [fieldsAtPremise, ProofSyntax.FunctionExtensionalityFree, and_self]

def childPremise : ProofSyntax Symbol [conditions] conditions := .hyp ⟨0, by decide⟩
theorem childPremise_free : childPremise.FunctionExtensionalityFree := by
  simp only [childPremise, ProofSyntax.FunctionExtensionalityFree]

@[irreducible] def proof : ProofSyntax Symbol [conditions] (.app (.app program value) index) :=
  constructorMemberProof block registered sourceGuards substitution numeral zeroCode successorCode bottom construct
    children consOccurrence arguments fieldsAtPremise childPremise

theorem proof_free : proof.FunctionExtensionalityFree := by
  unfold proof
  exact constructorMemberProof_free block registered sourceGuards substitution numeral zeroCode successorCode bottom construct
    children consOccurrence arguments fieldsAtPremise childPremise fieldsAtPremise_free childPremise_free
end Open

#print axioms nilMember
#print axioms consMember_free
#print axioms bottom_has_no_closed_member_proof

end
end Mettapedia.GSLT.LanguageDef.AdmittedContainerProofControls
