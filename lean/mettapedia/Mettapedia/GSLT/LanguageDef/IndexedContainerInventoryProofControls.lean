import Mettapedia.Logic.HOL.IndexedContainerInventoryProofs
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeInventoryControls

/-!
# Retained constructor membership over the complete indexed Vector-tree inventory

The solved constructor has a real Boolean field. Its field evidence is built
with beta and truth introduction; its complete child contract remains an
explicit hypothesis. The existing standard model realizes that contract
independently: solved has no active positions and its children are bottom.
Wrong result indices and omitted inactive padding are refused separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerInventoryProofControls

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedPolynomial.Description IndexedPositiveContainer IndexedContainerPositionTerms
open FiniteConstructorEncoding
open IndexedVectorTreeInventoryControls

def occurrence : Fin (codes.map reading.fields).length := ⟨0, by decide⟩
def arguments : Arguments Symbol [] (reading.fields (codeAt reading codes occurrence)) :=
  (.const (.answer true), PUnit.unit)
def children : ClosedTerm Symbol (N ⇒ S) := .lam (weaken bottom)
def signature := IndexedContainerInventory.recursiveSignature codes (guards := guards)
  Subst.id numeral zero successor bottom constructor
def payload := payloadTerm reading codes occurrence arguments
def value := (guards.constructors codes Subst.id numeral).constructorValue constructor occurrence
  (inventoryArguments reading codes occurrence arguments) children
def childContract : ClosedFormula Symbol := signature.childConditions signature.least payload children

def evidence : guards.Evidence [childContract] (codeAt reading codes occurrence) Subst.id arguments :=
  ⟨.impE (.eqPropER (.beta (.const (Symbol.answer true)) .top)) .topI, PUnit.unit⟩

theorem evidence_free : guards.EvidenceFree [childContract]
    (codeAt reading codes occurrence) Subst.id arguments evidence := by
  trivial

def memberProof : ProofSyntax Symbol [childContract] (.app (.app program value) .top) :=
  IndexedContainerInventory.constructorMemberProof codes guards Subst.id numeral zero successor bottom constructor
    children occurrence arguments evidence (.hyp 0)

theorem memberProof_free : memberProof.FunctionExtensionalityFree :=
  IndexedContainerInventory.constructorMemberProof_free (assumptions := [childContract]) codes guards Subst.id numeral zero successor bottom constructor
    children occurrence arguments evidence (.hyp 0) evidence_free True.intro

def leastProof : ProofSyntax Symbol [childContract] (.app signature.least value) :=
  IndexedContainerInventory.memberLeast codes guards Subst.id numeral zero successor bottom constructor value .top memberProof

def rootProof : ProofSyntax Symbol [childContract]
    (.app (.app ((guards.constructors codes Subst.id numeral).rootProgram constructor) value) .top) :=
  IndexedContainerInventory.memberRoot codes guards Subst.id numeral zero successor bottom constructor value .top memberProof

theorem leastProof_free : leastProof.FunctionExtensionalityFree :=
  IndexedContainerInventory.memberLeast_free codes guards Subst.id numeral zero successor bottom constructor
    value .top memberProof memberProof_free

theorem rootProof_free : rootProof.FunctionExtensionalityFree :=
  IndexedContainerInventory.memberRoot_free codes guards Subst.id numeral zero successor bottom constructor
    value .top memberProof memberProof_free

def point : ConstructorPoint reading codes environment :=
  ⟨occurrence, (), true, ⟨⟨rfl⟩⟩⟩

theorem payload_denote : model.denote payload empty =
    IndexedContainerInventory.nativePayload codes ordered realization environment
      (IndexedContainerInventory.sourcePoint codes environment point) :=
  IndexedContainerInventory.payloadTerm_denote codes ordered realization environment point arguments empty rfl

theorem no_active_position (slot : Ty.denote model.Carrier N) :
    ¬ (model.denote signature.active empty (model.denote payload empty) slot).down := by
  rcases slot with ⟨slot⟩
  intro active
  have exactPositions := IndexedContainerInventory.activeProgram_exact codes ordered realization images
    Subst.id numeral empty environment represented_context zero successor full empty rfl (fun _ => rfl) point slot
  have present : (model.denote (guards.positions codes Subst.id numeral zero successor).activeProgram empty
      (IndexedContainerInventory.nativePayload codes ordered realization environment
        (IndexedContainerInventory.sourcePoint codes environment point)) (realization.numbers slot)).down := by
    rw [← payload_denote]
    exact active
  obtain ⟨position, _⟩ := exactPositions.mp present
  exact PEmpty.elim position

theorem child_contract_realizable : (model.denote childContract empty).down := by
  change (model.denote (signature.childConditions signature.least payload children) empty).down
  simp only [RecursiveSpacePredicate.Contextual.childConditions, HenkinModel.denote, PreModel.denote,
    Soundness.denote_weaken, PreModel.extend]
  intro slot _
  constructor
  · intro active
    exact False.elim (no_active_position slot active)
  · intro _
    exact model.eqv_refl (full _ _)

theorem assumptions_realizable : Soundness.SatisfiesHyps model empty [childContract] := by
  intro formula member
  obtain rfl := List.mem_singleton.mp member
  exact child_contract_realizable

theorem retained_member_holds : (model.denote (.app (.app program value) .top) empty).down :=
  Soundness.extDerivation_sound memberProof.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem wrong_result_index_refused : ¬ (model.denote (.app (.app program value) .bot) empty).down :=
  wrong_index_refused _

def badChildren : ClosedTerm Symbol (N ⇒ S) := .lam (weaken value)

theorem value_not_bottom : model.denote value empty ≠ model.denote bottom empty := by
  intro same
  have trees := congrArg ULift.down same
  exact RecursiveSpace.construct_ne_bottom _ _ _ trees

theorem omitted_padding_refused :
    ¬ (model.denote (signature.childConditions signature.least payload badChildren) empty).down := by
  intro present
  simp only [RecursiveSpacePredicate.Contextual.childConditions, HenkinModel.denote, PreModel.denote,
    Soundness.denote_weaken, PreModel.extend] at present
  have atZero := (present (realization.numbers 0) (full _ _)).2 (no_active_position _)
  exact value_not_bottom (model.eq_of_eqv_of_fullDomains full atZero)

#print axioms memberProof
#print axioms memberProof_free
#print axioms leastProof_free
#print axioms rootProof_free
#print axioms child_contract_realizable
#print axioms retained_member_holds
#print axioms wrong_result_index_refused
#print axioms omitted_padding_refused

end Mettapedia.GSLT.LanguageDef.IndexedContainerInventoryProofControls
