import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorComputationModel
import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalGuardSemantics

/-!
# Natural constructor and array/All operations in one interpretation

The constructor's established natural encoding coexists with the original
list operations, all three recursion result types and nontrivial tree
evidence. The generated constructor domain supplies represented data and
canonical padding in this richer model, yielding semantic guarded uniqueness.
No object-level native uniqueness certificate is inferred from this model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalComputationModel
open Mettapedia.Logic Mettapedia.Logic.HOL
open IndexedContainerNativeVectorMethodReading (Base Const N E V W original)
open IndexedContainerNativeVectorPositionReading IndexedContainerNativeVectorChildGuard
open FiniteConstructorEncoding OrderedPositionPrograms
open Mettapedia.TypeTheory.IndexedPolynomial

abbrev carrier := IndexedContainerNativeVectorComputationModel.carrier Nat
abbrev fields := IndexedContainerNativeVectorNaturalModel.fields
abbrev Raw := Ty.denote.{0,0} carrier (payloadType fields)
abbrev SourceData := Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote.{0,0} carrier) fields
noncomputable def basis : HenkinModel.{0,0,0} Base Const :=
  .standard carrier
    (fun {type} _ => IndexedContainerNativeVectorComputationModel.defaultValue 0 type)
def dataEquiv : SourceData ≃ ULift.{1} Nat × ULift.{1} Nat × ULift.{1} Nat where
  toFun := by
    rintro ⟨occurrence,data⟩
    have only : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
    cases only
    exact (data.1,data.2.1,data.2.2.1)
  invFun := fun data => ⟨⟨0,by decide⟩,data.1,data.2.1,data.2.2,PUnit.unit⟩
  left_inv := by
    rintro ⟨occurrence,data⟩
    have only : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
    cases only
    rfl
  right_inv := fun _ => rfl
instance : Encodable SourceData := Encodable.ofEquiv (ULift.{1} Nat × ULift.{1} Nat × ULift.{1} Nat) dataEquiv
instance : Encodable (Mettapedia.TypeTheory.FiniteConstructorEncoding.Data (Ty.denote.{0,0} basis.Carrier) fields) := by
  change Encodable SourceData
  infer_instance
def arity (data : SourceData) : Nat := (dataEquiv data).1.down+2
noncomputable def constructorMeaning (tag : ULift.{1} Nat) (payload : Raw)
    (children : ULift.{1} Nat → ULift.{1} Nat) : ULift.{1} Nat :=
  .up (FiniteConstructorEncoding.NaturalRealization.construct.{0,0,0} basis fields arity tag.down payload
    (fun slot => (children (.up slot)).down))
abbrev constructor := IndexedContainerNativeVectorNaturalModel.constructor
abbrev bottom := IndexedContainerNativeVectorNaturalModel.bottom
abbrev payloadPredicate := IndexedContainerNativeVectorNaturalModel.payloadPredicate
abbrev payloadSelection := IndexedContainerNativeVectorNaturalModel.payloadSelection
abbrev childrenSelection := IndexedContainerNativeVectorNaturalModel.childrenSelection
abbrev sourceDomain := IndexedContainerNativeVectorNaturalModel.sourceDomain

@[irreducible] noncomputable def extra (predicate : Nat → Prop) : IndexedContainerNativeVectorComputationModel.Assignment Nat :=
  IndexedContainerNativeVectorComputationModel.assign 25 (type := N ⇒ payloadType fields ⇒ (N ⇒ E) ⇒ E) constructorMeaning
    (IndexedContainerNativeVectorComputationModel.assign 27 (type := SelectionProofs.Selection (payloadType fields))
      (HOLLightStandardTheory.selectionOperation carrier (IndexedContainerNativeVectorComputationModel.inhabitant 0) (payloadType fields))
      (IndexedContainerNativeVectorComputationModel.assign 28 (type := SelectionProofs.Selection (N ⇒ E))
        (HOLLightStandardTheory.selectionOperation carrier (IndexedContainerNativeVectorComputationModel.inhabitant 0) (N ⇒ E))
        (IndexedContainerNativeVectorComputationModel.assign 26 (type := E) (.up 0)
          (IndexedContainerNativeVectorComputationModel.assign 20 (type := E ⇒ .prop) (fun value => .up (predicate value.down))
            (fun {type} _ => IndexedContainerNativeVectorComputationModel.defaultValue 0 type)))))
noncomputable def model (predicate : Nat → Prop) : HenkinModel.{0,0,0} Base Const :=
  .standard carrier (IndexedContainerNativeVectorComputationModel.meaning 0 (extra predicate))
def values (predicate : Nat → Prop) : (model predicate).Valuation [] := fun entry => nomatch entry
theorem full (predicate : Nat → Prop) : (model predicate).FullDomains := IndexedContainerNativeVectorComputationModel.full 0 (extra predicate)

theorem constructor_denote (predicate : Nat → Prop) (tag : ULift.{1} Nat) (payload : Raw)
    (children : ULift.{1} Nat → ULift.{1} Nat) :
    (model predicate).denote constructor (values predicate) tag payload children =
      constructorMeaning tag payload children := by unfold model extra; rfl

theorem bottom_denote (predicate : Nat → Prop) :
    (model predicate).denote bottom (values predicate) = ULift.up 0 := by unfold model extra; rfl

abbrev inventory := IndexedContainerNativeVectorNaturalModel.inventory
abbrev positionPrograms := IndexedContainerNativeVectorNaturalModel.positionPrograms

theorem zero_denote (predicate : Nat → Prop) : (model predicate).denote original.zero (values predicate) = .up 0 := rfl
theorem successor_denote (predicate : Nat → Prop) (n : Nat) :
    (model predicate).denote original.successor (values predicate) (.up n) = .up (n+1) := rfl
theorem numeral_denote (predicate : Nat → Prop) (n : Nat) :
    (model predicate).denote (numeral [] n) (values predicate) = .up n := by
  induction n with
  | zero => exact zero_denote predicate
  | succ n previous =>
      change ULift.up (((model predicate).denote (numeral [] n) (values predicate)).down+1) = _
      rw [previous]

theorem fields_evaluate (predicate : Nat → Prop) (data : SourceData) :
    evaluateFields (model predicate) Equiv.ulift.symm _ (values predicate) data.2 (plans payloadPredicate data.1) =
      [(1,ULift.up True),((dataEquiv data).1.down,ULift.up True),(1,ULift.up True)] := by
  rcases data with ⟨occurrence,data⟩
  have only : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
  cases only
  rcases data with ⟨length,head,shape,_end⟩
  rfl

theorem related_iff (predicate : Nat → Prop) (data : SourceData) (slot : ULift.{1} Nat) (index : ULift.{1} Prop) :
    positionPrograms.related (model predicate) (values predicate) data slot index ↔
      (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
        [(1,ULift.up True),((dataEquiv data).1.down,ULift.up True),(1,ULift.up True)])[slot.down]? = some index := by
  have compared := IndexedConstructorGuards.PositionPrograms.ofSegments_related inventory original.zero original.successor
    (plans payloadPredicate) (model predicate) Equiv.ulift.symm (full predicate) (values predicate)
    (zero_denote predicate) (successor_denote predicate) (values predicate) data slot index
  change positionPrograms.related (model predicate) (values predicate) data slot index ↔
    (Mettapedia.TypeTheory.OrderedPositionSegments.flatten
      (evaluateFields (model predicate) Equiv.ulift.symm _ (values predicate) data.2 (plans payloadPredicate data.1)))[slot.down]? = some index at compared
  rw [fields_evaluate] at compared
  exact compared

theorem active_at_payload (predicate : Nat → Prop) (payload : Raw) (data : SourceData)
    (matching : payloadEquivalence (model predicate) fields payload =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote.{0,0} carrier) fields data)
    (slot : ULift.{1} Nat) :
    ((model predicate).denote positionPrograms.activeProgram (values predicate) payload slot).down ↔
      inventory.dataAllowed (model predicate) (values predicate) data ∧ slot.down < arity data := by
  rw [positionPrograms.activeProgram_denote (model predicate) (full predicate)]
  change (∃ other : SourceData,
    (inventory.dataAllowed (model predicate) (values predicate) other ∧
      ∃ index : ULift.{1} Prop, positionPrograms.related (model predicate) (values predicate) other slot index) ∧
    payloadEquivalence (model predicate) fields payload =
      Mettapedia.TypeTheory.FiniteConstructorEncoding.encode (Ty.denote.{0,0} carrier) fields other) ↔ _
  rw [matching]
  have activity : (∃ index : ULift.{1} Prop,
      positionPrograms.related (model predicate) (values predicate) data slot index) ↔ slot.down < arity data := by
    simp only [related_iff]
    rw [Mettapedia.TypeTheory.OrderedPositionSegments.active_iff,
      Mettapedia.TypeTheory.OrderedPositionSegments.length_flatten]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,arity]
    omega
  constructor
  · rintro ⟨other,valid,same⟩
    have exactData := Mettapedia.TypeTheory.FiniteConstructorEncoding.encode_injective (Ty.denote.{0,0} carrier) fields same
    cases exactData
    exact ⟨valid.1,activity.mp valid.2⟩
  · intro valid
    exact ⟨data,⟨valid.1,activity.mpr valid.2⟩,rfl⟩

def allowedMeaning (predicate : Nat → Prop) (tag : Nat) (data : SourceData) (_children : Nat → Nat) : Prop :=
  inventory.dataAllowed (model predicate) (values predicate) data ∧ tag = data.1.val

theorem domain_admitted (predicate : Nat → Prop) (tag : ULift.{1} Nat) (payload : Raw)
    (children : ULift.{1} Nat → ULift.{1} Nat)
    (admitted : ((model predicate).denote sourceDomain (values predicate) tag payload children).down) :
    FiniteConstructorEncoding.NaturalRealization.Admitted.{0,0,0} basis fields arity (allowedMeaning predicate)
      tag.down payload (fun slot => (children (.up slot)).down) := by
  obtain ⟨shape,padding⟩ := (IndexedContainerNativeVectorNaturalModel.sourceSignature.constructorAdmission_denote_full
    (model predicate) (full predicate) (values predicate) tag payload children).mp admitted
  obtain ⟨data,⟨permitted,tagSame⟩,matching⟩ := (inventory.shapeProgram_denote (model predicate) (full predicate)
    (values predicate) tag payload).mp shape
  have numericTag : tag.down = data.1.val := by
    have equality := congrArg ULift.down tagSame
    change tag.down = ((model predicate).denote (numeral [] data.1.val) (values predicate)).down at equality
    simpa only [numeral_denote] using equality
  have canonical : (Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.slots (arity data)).Canonical 0
      (fun slot => (children (.up slot)).down) := by
    intro slot outside
    have beyond := (SlotEncoding.finite_decoded_iff (Equiv.refl _) slot).mp outside
    have inactive : ¬ ((model predicate).denote positionPrograms.activeProgram (values predicate) payload (.up slot)).down := by
      rw [active_at_payload predicate payload data matching]
      exact fun active => Nat.not_lt_of_ge beyond active.2
    have same := padding (.up slot) inactive
    change children (.up slot) = (model predicate).denote bottom (values predicate) at same
    rw [bottom_denote] at same
    exact congrArg ULift.down same
  exact ⟨data,matching,⟨permitted,numericTag⟩,canonical⟩

theorem guarded_injectivity_holds (predicate : Nat → Prop) :
    (model predicate).models (GuardedConstructorProjections.fieldInjective constructor sourceDomain) := by
  apply (GuardedConstructorProjections.fieldInjective_models_full.{0,0,0}
    (first := N) (second := payloadType fields) (third := N ⇒ E) (carrier := E) (model predicate) (full predicate)
    constructor sourceDomain (values predicate)).mpr
  intro tag payload children original tag' payload' children' candidate same
  simp only [constructor_denote] at same
  have recovered := FiniteConstructorEncoding.NaturalRealization.fields_of_eq.{0,0,0} basis fields arity
    (allowedMeaning predicate) tag'.down tag.down payload' payload
    (fun slot => (children' (.up slot)).down) (fun slot => (children (.up slot)).down)
    (domain_admitted predicate tag' payload' children' candidate)
    (domain_admitted predicate tag payload children original) (congrArg ULift.down same)
  have childrenSame : children' = children := by
    funext slot
    apply ULift.ext
    exact congrFun recovered.2.2 slot.down
  exact ⟨recovered.2.1,childrenSame⟩

theorem computationAssumptions_realizable (predicate : Nat → Prop) :
    Soundness.SatisfiesHyps (model predicate) (values predicate)
      IndexedContainerNativeVectorEvidenceModel.assumptions := IndexedContainerNativeVectorComputationModel.assumptions_realizable 0 (extra predicate)

theorem payloadSelection_holds (predicate : Nat → Prop) :
    (model predicate).models (SelectionProofs.principle payloadSelection) := by
  unfold model extra
  intro question _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier (IndexedContainerNativeVectorComputationModel.inhabitant 0)
    (payloadType fields) question ⟨value,present⟩
theorem childrenSelection_holds (predicate : Nat → Prop) :
    (model predicate).models (SelectionProofs.principle childrenSelection) := by
  unfold model extra
  intro question _ value _ present
  exact HOLLightStandardTheory.selectionOperation_specified carrier (IndexedContainerNativeVectorComputationModel.inhabitant 0)
    (N ⇒ E) question ⟨value,present⟩

def profileAssumptions : List (ClosedFormula Const) :=
  [SelectionProofs.principle payloadSelection,SelectionProofs.principle childrenSelection,
    GuardedConstructorProjections.fieldInjective constructor sourceDomain,
    NaturalNumeralProofs.separation original.zero original.successor,
    NaturalNumeralProofs.injectivity original.successor] ++ IndexedContainerNativeVectorEvidenceModel.assumptions

theorem profileAssumptions_realizable (predicate : Nat → Prop) :
    Soundness.SatisfiesHyps (model predicate) (values predicate) profileAssumptions := by
  intro formula present
  simp only [profileAssumptions,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with (rfl | rfl | rfl | rfl | rfl) | present
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (payloadSelection_holds predicate)
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (childrenSelection_holds predicate)
  · exact ((model predicate).models_iff_denote_closed _ (values predicate)).mp (guarded_injectivity_holds predicate)
  · exact IndexedContainerNativeVectorComputationModel.separation_holds 0 (extra predicate)
  · exact IndexedContainerNativeVectorComputationModel.injectivity_holds 0 (extra predicate)
  · exact computationAssumptions_realizable predicate _ present

#print axioms active_at_payload
#print axioms guarded_injectivity_holds
#print axioms computationAssumptions_realizable
#print axioms profileAssumptions_realizable
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalComputationModel
