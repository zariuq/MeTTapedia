import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalGuardSemantics
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorConstructorBoundary

/-!
# Nonempty generated admission and recovery at the installed constructor

The source payload predicate selects the natural zero. Every source length
has an admitted encoded payload and a canonical zero child array. These are
admission witnesses, not inhabitants of the source's least recursive family.
In particular admission does not supply the complete child-condition premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel.Controls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial
open IndexedContainerNativeVectorMethodReading (Base Const N E parameter)
open IndexedContainerNativeVectorPositionReading IndexedContainerNativeVectorChildGuard
open FiniteConstructorEncoding

def predicate (n : Nat) : Prop := n = 0
def tag : ClosedTerm Const E := parameter 22 _
def children : ClosedTerm Const (N ⇒ E) := parameter 24 _
def sourcePayload (length : Nat) : ClosedTerm Const (payloadType fields) :=
  encoded payloadPredicate (numeral [] length) tag (numeral [] 0)
def semanticData (length : Nat) : SourceData := ⟨⟨0,by decide⟩,.up length,.up 0,.up 0,PUnit.unit⟩

theorem dataEquiv_semanticData (length : Nat) : dataEquiv (semanticData length) = (.up length,.up 0,.up 0) := rfl
theorem tag_denote : (model predicate).denote tag (values predicate) = ULift.up 0 := rfl
theorem children_denote : (model predicate).denote children (values predicate) = fun _ => ULift.up 0 := rfl

theorem payload_matching (length : Nat) :
    payloadEquivalence (model predicate) fields ((model predicate).denote (sourcePayload length) (values predicate)) =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote.{0,0} carrier) fields (semanticData length) := by
  change payloadEquivalence (model predicate) fields
    ((model predicate).denote (encode fields ⟨0,by decide⟩
      (numeral [] length,tag,numeral [] 0,PUnit.unit)) (values predicate)) = _
  rw [encode_denote]
  apply congrArg (Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote.{0,0} carrier) fields)
  change (⟨⟨0,by decide⟩,(model predicate).denote (numeral [] length) (values predicate),
    (model predicate).denote tag (values predicate),(model predicate).denote (numeral [] 0) (values predicate),PUnit.unit⟩ : SourceData) = _
  simp only [numeral_denote,tag_denote]
  rfl

theorem allowed (length : Nat) : inventory.dataAllowed (model predicate) (values predicate) (semanticData length) := by
  change True ∧ ((0:Nat) = 0 ∧ ((ULift.up 0 : ULift.{1} Nat) = ULift.up 0 ∧ True))
  exact ⟨True.intro,rfl,rfl,True.intro⟩

theorem admission_holds (length : Nat) : (model predicate).models
    (GuardedConstructorProjections.admitted sourceDomain (numeral [] 0) (sourcePayload length) children) := by
  apply (sourceSignature.constructorAdmission_models_full (model predicate) (full predicate)
    (values predicate) (numeral [] 0) (sourcePayload length) children).mpr
  simp only [numeral_denote]
  constructor
  · apply (inventory.shapeProgram_denote (model predicate) (full predicate) (values predicate) (.up 0) _).mpr
    exact ⟨semanticData length,⟨allowed length,rfl⟩,payload_matching length⟩
  · intro slot _inactive
    rfl

def assumptions (length : Nat) : List (ClosedFormula Const) :=
  [SelectionProofs.principle payloadSelection,SelectionProofs.principle childrenSelection,
    GuardedConstructorProjections.fieldInjective constructor sourceDomain,
    GuardedConstructorProjections.admitted sourceDomain (numeral [] 0) (sourcePayload length) children]

theorem assumptions_realizable (length : Nat) : Soundness.SatisfiesHyps (model predicate) (values predicate) (assumptions length) := by
  intro formula present
  simp only [assumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (payloadSelection_holds predicate)
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (childrenSelection_holds predicate)
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (guarded_injectivity_holds predicate)
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (admission_holds length)

def value (length : Nat) := ConstructorProjections.apply constructor (numeral [] 0) (sourcePayload length) children
def payloadRecovered (length : Nat) : ProofSyntax Const (assumptions length)
    (.eq (.app (GuardedConstructorProjections.secondProjection payloadSelection constructor sourceDomain) (value length))
      (sourcePayload length)) :=
  GuardedConstructorProjections.second_at payloadSelection constructor sourceDomain (numeral [] 0) (sourcePayload length) children
    (.hyp (Δ := assumptions length) ⟨0,by change 0 < 4; decide⟩)
    (.hyp (Δ := assumptions length) ⟨2,by change 2 < 4; decide⟩)
    (.hyp (Δ := assumptions length) ⟨3,by change 3 < 4; decide⟩)
def childrenRecovered (length : Nat) : ProofSyntax Const (assumptions length)
    (.eq (.app (GuardedConstructorProjections.thirdProjection childrenSelection constructor sourceDomain) (value length)) children) :=
  GuardedConstructorProjections.third_at childrenSelection constructor sourceDomain (numeral [] 0) (sourcePayload length) children
    (.hyp (Δ := assumptions length) ⟨1,by change 1 < 4; decide⟩)
    (.hyp (Δ := assumptions length) ⟨2,by change 2 < 4; decide⟩)
    (.hyp (Δ := assumptions length) ⟨3,by change 3 < 4; decide⟩)

theorem payload_recovered (length : Nat) :
    (model predicate).denote (.app (GuardedConstructorProjections.secondProjection payloadSelection constructor sourceDomain)
      (value length)) (values predicate) = (model predicate).denote (sourcePayload length) (values predicate) := by
  apply (model predicate).eq_of_eqv_of_fullDomains (full predicate)
  exact Soundness.extDerivation_sound (payloadRecovered length).erase
    ((model predicate).functionsRespectEqv_of_fullDomains (full predicate)) (fun _ => True.intro)
    (assumptions_realizable length)

theorem children_recovered (length : Nat) :
    (model predicate).denote (.app (GuardedConstructorProjections.thirdProjection childrenSelection constructor sourceDomain)
      (value length)) (values predicate) = (model predicate).denote children (values predicate) := by
  apply (model predicate).eq_of_eqv_of_fullDomains (full predicate)
  exact Soundness.extDerivation_sound (childrenRecovered length).erase
    ((model predicate).functionsRespectEqv_of_fullDomains (full predicate)) (fun _ => True.intro)
    (assumptions_realizable length)

theorem value_nonzero (length : Nat) : ((model predicate).denote (value length) (values predicate)).down ≠ 0 := by
  have matching := payload_matching length
  change payloadEquivalence basis fields ((model predicate).denote (sourcePayload length) (values predicate)) =
    Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote.{0,0} basis.Carrier) fields (semanticData length) at matching
  change FiniteConstructorEncoding.NaturalRealization.construct.{0,0,0} basis fields arity 0
    ((model predicate).denote (sourcePayload length) (values predicate)) (fun _ => 0) ≠ 0
  unfold FiniteConstructorEncoding.NaturalRealization.construct
  rw [matching,Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.construct_encode]
  exact Nat.succ_ne_zero _

theorem output_reflects_length (first second : Nat)
    (same : (model predicate).denote (value first) (values predicate) =
      (model predicate).denote (value second) (values predicate)) : first = second := by
  let projection := (model predicate).denote
    (GuardedConstructorProjections.secondProjection payloadSelection constructor sourceDomain) (values predicate)
  have recovered := congrArg projection same
  change (model predicate).denote (.app
    (GuardedConstructorProjections.secondProjection payloadSelection constructor sourceDomain) (value first)) (values predicate) =
    (model predicate).denote (.app
      (GuardedConstructorProjections.secondProjection payloadSelection constructor sourceDomain) (value second)) (values predicate) at recovered
  rw [payload_recovered,payload_recovered] at recovered
  have encoded := congrArg (payloadEquivalence (model predicate) fields) recovered
  rw [payload_matching,payload_matching] at encoded
  have data := Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective (Ty.denote.{0,0} carrier) fields encoded
  simpa only [dataEquiv_semanticData] using congrArg (fun data : SourceData => (dataEquiv data).1.down) data

theorem false_child_conditions_refused (length : Nat) : ¬ (model predicate).models
    (sourceSignature.childConditions (.lam .bot) (sourcePayload length) children) := by
  intro conditions
  have active : ((model predicate).denote positionPrograms.activeProgram (values predicate)
      ((model predicate).denote (sourcePayload length) (values predicate)) (.up 0)).down := by
    apply (active_at_payload predicate _ (semanticData length) (payload_matching length) (.up 0)).mpr
    exact ⟨allowed length,by simp only [arity,dataEquiv_semanticData]; omega⟩
  exact sourceSignature.childConditions_false_no_active (model predicate) (full predicate)
    (values predicate) (sourcePayload length) children conditions (.up 0) active

theorem raw_injectivity_refused : ¬ (model predicate).models (ConstructorInjectivity.statement constructor) := by
  intro claimed
  exact IndexedContainerNativeVectorConstructorBoundary.original_reading_refuses_full_injectivity
    (model predicate) (full predicate) payloadPredicate constructor bottom (values predicate)
    (((model predicate).models_iff_denote_closed _ (values predicate)).mp claimed)

#print axioms assumptions_realizable
#print axioms payload_recovered
#print axioms false_child_conditions_refused
#print axioms raw_injectivity_refused
#print axioms output_reflects_length
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel.Controls
