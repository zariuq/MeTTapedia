import Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel
import Mettapedia.Logic.HOL.ContextualConstructorAdmissionSemantics

/-!
# Original generated guards at the natural constructor realization

The compiled source plans determine the active interval. The actual generated
shape and padding guard therefore establishes represented data and canonical
children for the installed natural constructor. Guarded uniqueness is derived
from that construction rather than supplied as a model assumption.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel
open Mettapedia.Logic Mettapedia.Logic.HOL
open Mettapedia.TypeTheory.IndexedPolynomial
open IndexedContainerNativeVectorMethodReading (Base Const N E original)
open IndexedContainerNativeVectorPositionReading IndexedContainerNativeVectorChildGuard
open FiniteConstructorEncoding OrderedPositionPrograms

def inventory := constructors payloadPredicate
def positionPrograms := positions payloadPredicate
def sourceSignature := IndexedContainerNativeVectorConstructorAdmission.signature payloadPredicate constructor bottom
def sourceDomain := IndexedContainerNativeVectorConstructorAdmission.domain payloadPredicate constructor bottom

theorem numeral_denote (predicate : Nat → Prop) (n : Nat) :
    (model predicate).denote (numeral [] n) (values predicate) = ULift.up n := by
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
  obtain ⟨shape,padding⟩ := (sourceSignature.constructorAdmission_denote_full (model predicate) (full predicate)
    (values predicate) tag payload children).mp admitted
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
    exact congrArg ULift.down same
  exact ⟨data,matching,⟨permitted,numericTag⟩,canonical⟩

theorem guarded_injectivity_holds (predicate : Nat → Prop) :
    (model predicate).models (GuardedConstructorProjections.fieldInjective constructor sourceDomain) := by
  apply (GuardedConstructorProjections.fieldInjective_models_full.{0,0,0}
    (first := N) (second := payloadType fields) (third := N ⇒ E) (carrier := E) (model predicate) (full predicate)
    constructor sourceDomain (values predicate)).mpr
  intro tag payload children original tag' payload' children' candidate same
  change constructorMeaning tag' payload' children' = constructorMeaning tag payload children at same
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

#print axioms domain_admitted
#print axioms guarded_injectivity_holds
end Mettapedia.GSLT.LanguageDef.IndexedContainerNativeVectorNaturalModel
