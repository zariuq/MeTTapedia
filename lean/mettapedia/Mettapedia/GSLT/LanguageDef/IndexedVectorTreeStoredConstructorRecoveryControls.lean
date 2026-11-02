import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecovery
import Mettapedia.Logic.HOL.VectorTreeSuccessorFixture

/-!
# Actual stored-constructor domain in the successor fixture

The closed arithmetic and real recursive-space provider interpret the original
parsed solved/branch inventory. Constant bottom children provide an explicit
padding witness. Admission here is shape and padding; recursive least-family
membership and native source-context adequacy are separate obligations.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecoveryControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding CurriedPredicates IndexedConstructorGuards
open FiniteConstructorFieldEmbeddingControls (Base N A E P Number Element Space)
open VectorTreeSuccessorFixture

abbrev Stored := VectorTreeFieldEmbedding.storedSignature N E
abbrev Payload := payloadType Stored

def numbers : ClosedTerm Const (N ⇒ .prop) := .lam .top
def bottom : ClosedTerm Const E := embed (.const .bottom)
def inventory := IndexedVectorTreeStoredFieldGuards.inventory given onlyTrue numbers zero one numeral
def signature := IndexedVectorTreeStoredConstructorRecovery.recursiveSignature given onlyTrue numbers zero one successor numeral bottom
def domain := IndexedVectorTreeStoredConstructorRecovery.domain given onlyTrue numbers zero one successor numeral bottom
def constructor := IndexedVectorTreeStoredConstructorRecovery.storedConstructor given

def solved (answer : Bool) : ClosedTerm Const Payload :=
  FiniteConstructorEncoding.encode Stored ⟨0,by decide⟩ (.app given.encode (.const (.old (.answer answer))),PUnit.unit)
def branch (n q : Nat) : ClosedTerm Const Payload :=
  FiniteConstructorEncoding.encode Stored ⟨1,by decide⟩ (numeral n,numeral q,PUnit.unit)
def shape (tag : ClosedTerm Const N) (payload : ClosedTerm Const Payload) : ClosedFormula Const :=
  .app (.app inventory.shapeProgram tag) payload
def admitted (tag : ClosedTerm Const N) (payload : ClosedTerm Const Payload) : ClosedFormula Const :=
  GuardedConstructorProjections.admitted domain tag payload given.children

def fieldLaw : ProofSyntax Const premises (GuardedConstructorProjections.fieldInjective constructor domain) :=
  IndexedVectorTreeStoredConstructorRecovery.fieldInjective given onlyTrue numbers zero one successor numeral bottom
    (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)

theorem fieldLaw_free : fieldLaw.FunctionExtensionalityFree := by
  apply IndexedVectorTreeStoredConstructorRecovery.fieldInjective_free
  all_goals trivial

theorem fieldLaw_holds : (model.denote (GuardedConstructorProjections.fieldInjective constructor domain) values).down :=
  Soundness.extDerivation_sound fieldLaw.erase (model.functionsRespectEqv_of_fullDomains full)
    (fun _ => trivial) assumptions_realizable

theorem two_admission_reflection (tag : Number)
    (payload : Ty.denote model.Carrier Payload) (children : Ty.denote model.Carrier (N ⇒ E))
    (present : (model.denote domain values tag payload children).down)
    (otherTag : Number) (otherPayload : Ty.denote model.Carrier Payload)
    (otherChildren : Ty.denote model.Carrier (N ⇒ E))
    (otherPresent : (model.denote domain values otherTag otherPayload otherChildren).down)
    (same : model.denote constructor values otherTag otherPayload otherChildren =
      model.denote constructor values tag payload children) :
    otherPayload = payload ∧ otherChildren = children :=
  (GuardedConstructorProjections.fieldInjective_denote_full model full constructor domain values).mp
    fieldLaw_holds tag payload children present otherTag otherPayload otherChildren otherPresent same

theorem shape_on_encoded (tag : ClosedTerm Const N) (occurrence : Fin Stored.length)
    (arguments : Arguments Const [] (Stored.get occurrence)) :
    (model.denote (shape tag (FiniteConstructorEncoding.encode Stored occurrence arguments)) values).down ↔
      inventory.dataAllowed model values ⟨occurrence,denoteArguments model _ arguments values⟩ ∧
        model.denote tag values = model.denote (inventory.numeral occurrence.val) values := by
  refine (inventory.shapeProgram_denote model full values
    (model.denote tag values) (model.denote (FiniteConstructorEncoding.encode Stored occurrence arguments) values)).trans ?_
  constructor
  · rintro ⟨data,allowed,same⟩
    have identified := TypeTheory.FiniteConstructorEncoding.encode_injective _ _
      ((encode_denote model Stored occurrence arguments values).symm.trans same)
    subst data
    exact allowed
  · intro allowed
    exact ⟨_,allowed,encode_denote model Stored occurrence arguments values⟩

theorem allowed_applied (occurrence : Fin Stored.length)
    (arguments : Arguments Const [] (Stored.get occurrence)) :
    inventory.dataAllowed model values ⟨occurrence,denoteArguments model _ arguments values⟩ ↔
      (model.denote (applyArguments _ (IndexedVectorTreeStoredFieldGuards.conditions given onlyTrue numbers zero occurrence) arguments) values).down := by
  have equivalent := Soundness.extDerivation_sound (M := model) (ρ := values)
    (IndexedVectorTreeStoredFieldGuards.application_eq (Δ := []) given onlyTrue numbers zero one occurrence arguments).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial)
    (by intro formula present; cases present)
  have original : inventory.dataAllowed model values ⟨occurrence,denoteArguments model _ arguments values⟩ ↔
      (model.denote (applyArguments _ (inventory.allowed occurrence) arguments) values).down := by
    rw [ConstructorPrograms.dataAllowed,holds,applyArguments_denote]
  have point := IndexedVectorTreeStoredFieldGuards.allowed_eq given onlyTrue numbers zero one numeral occurrence
  have same := congrArg (fun condition : ClosedTerm Const (handlerType (Stored.get occurrence)) =>
    (model.denote (applyArguments _ condition arguments) values).down) point
  exact original.trans ((Iff.of_eq same).trans equivalent)

theorem solved_shape_true : (model.denote (shape zero (solved true)) values).down := by
  apply (shape_on_encoded zero ⟨0,by decide⟩ _).mpr
  constructor
  · exact (allowed_applied _ _).mpr accepted_true
  · rfl

theorem solved_shape_false_refused : ¬ (model.denote (shape zero (solved false)) values).down := by
  intro present
  have allowed := (shape_on_encoded zero ⟨0,by decide⟩ _).mp present
  exact rejected_false ((allowed_applied _ _).mp allowed.1)

theorem branch_shape_iff (n q : Nat) :
    (model.denote (shape one (branch n q)) values).down ↔ q = 0 := by
  have allowed := allowed_applied ⟨1,by decide⟩ (numeral n,numeral q,PUnit.unit)
  change inventory.dataAllowed model values _ ↔
    (True ∧ (model.denote (numeral q) values = model.denote zero values ∧ True)) at allowed
  refine (shape_on_encoded one ⟨1,by decide⟩ (numeral n,numeral q,PUnit.unit)).trans ?_
  constructor
  · intro present
    have same : (ULift.up q : Number) = ULift.up 0 := by
      simpa only [numeral_meaning,zero_meaning] using (allowed.mp present.1).2.1
    exact congrArg ULift.down same
  · intro canonical
    subst q
    exact ⟨allowed.mpr ⟨True.intro,rfl,True.intro⟩,rfl⟩

theorem domain_iff_shape (tag : ClosedTerm Const N) (payload : ClosedTerm Const Payload) :
    (model.denote (admitted tag payload) values).down ↔ (model.denote (shape tag payload) values).down := by
  change (model.denote signature.constructorAdmission values (model.denote tag values)
    (model.denote payload values) (model.denote given.children values)).down ↔ _
  rw [signature.constructorAdmission_denote_full model full]
  constructor
  · exact fun present => present.1
  · intro present
    exact ⟨present,fun _ _ => rfl⟩

theorem solved_admitted : (model.denote (admitted zero (solved true)) values).down :=
  (domain_iff_shape _ _).mpr solved_shape_true

theorem false_answer_refused : ¬ (model.denote (admitted zero (solved false)) values).down :=
  fun present => solved_shape_false_refused ((domain_iff_shape _ _).mp present)

theorem actual_branch_two_zero_admitted : (model.denote (admitted one (branch 2 0)) values).down :=
  (domain_iff_shape _ _).mpr ((branch_shape_iff 2 0).mpr rfl)

theorem actual_branch_two_two_refused : ¬ (model.denote (admitted one (branch 2 2)) values).down := by
  intro present
  have impossible := (branch_shape_iff 2 2).mp ((domain_iff_shape _ _).mp present)
  exact Nat.noConfusion impossible


def recoveryImplication (tag : ClosedTerm Const N) (payload : ClosedTerm Const Payload) :
    ProofSyntax Const premises (.imp (admitted tag payload)
      (.eq (.app (VectorTreePayloadMaps.raiseProgram given)
        (.app (VectorTreePayloadMaps.lowerProgram given) payload)) payload)) :=
  .impI (IndexedVectorTreeStoredConstructorRecovery.recoverAdmitted given onlyTrue numbers zero one successor numeral bottom
    (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩) (.hyp ⟨3,by simp [premises]⟩)
    tag payload given.children (.hyp 0))

theorem recoveryImplication_free (tag : ClosedTerm Const N) (payload : ClosedTerm Const Payload) :
    (recoveryImplication tag payload).FunctionExtensionalityFree := by
  unfold recoveryImplication
  apply IndexedVectorTreeStoredConstructorRecovery.recoverAdmitted_free
  all_goals trivial

theorem payload_roundtrip (tag : ClosedTerm Const N) (payload : ClosedTerm Const Payload)
    (present : (model.denote (admitted tag payload) values).down) :
    model.denote (VectorTreePayloadMaps.raiseProgram given) values
      (model.denote (VectorTreePayloadMaps.lowerProgram given) values (model.denote payload values)) =
      model.denote payload values := by
  have checked := Soundness.extDerivation_sound (M := model) (ρ := values) (recoveryImplication tag payload).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realizable
  exact model.eq_of_eqv_of_fullDomains full (checked present)

theorem solved_payload_roundtrip :
    model.denote (VectorTreePayloadMaps.raiseProgram given) values
      (model.denote (VectorTreePayloadMaps.lowerProgram given) values (model.denote (solved true) values)) =
      model.denote (solved true) values := payload_roundtrip zero (solved true) solved_admitted

theorem branch_payload_roundtrip :
    model.denote (VectorTreePayloadMaps.raiseProgram given) values
      (model.denote (VectorTreePayloadMaps.lowerProgram given) values (model.denote (branch 2 0) values)) =
      model.denote (branch 2 0) values := payload_roundtrip one (branch 2 0) actual_branch_two_zero_admitted

#print axioms fieldLaw
#print axioms fieldLaw_free
#print axioms two_admission_reflection
#print axioms solved_admitted
#print axioms false_answer_refused
#print axioms actual_branch_two_zero_admitted
#print axioms actual_branch_two_two_refused
#print axioms recoveryImplication_free
#print axioms solved_payload_roundtrip
#print axioms branch_payload_roundtrip
end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecoveryControls
