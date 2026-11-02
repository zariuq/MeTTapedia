import Mettapedia.TypeTheory.FiniteConstructorNaturalRealization

/-!
# Represented mixed fields and canonical child arrays

The source has the ordered fields number, element, number. Its middle Vector
contributes the first field's count, between two scalar positions. Repeated
children remain separate positions. A changed inactive tail is observationally
erased by construction but fails admission, separating guarded from raw
function injectivity.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.Controls
open IndexedPolynomial
inductive SourceSort where | number | element
  deriving DecidableEq
def Value : SourceSort → Type := fun _ => Nat
def signature : Signature (SortCode := SourceSort) := [[.number,.element,.number]]

def dataEquiv : Data Value signature ≃ Nat × Nat × Nat where
  toFun := by
    rintro ⟨occurrence,fields⟩
    have same : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
    cases same
    exact (fields.1,fields.2.1,fields.2.2.1)
  invFun := fun fields => ⟨⟨0,by decide⟩,fields.1,fields.2.1,fields.2.2,PUnit.unit⟩
  left_inv := by
    rintro ⟨occurrence,fields⟩
    have same : occurrence = ⟨0,by decide⟩ := Fin.eq_zero occurrence
    cases same
    rfl
  right_inv := fun _ => rfl

instance : Encodable (Data Value signature) := Encodable.ofEquiv (Nat × Nat × Nat) dataEquiv

def data (length head shape : Nat) : Data Value signature := dataEquiv.symm (length,head,shape)
@[simp] theorem dataEquiv_data (length head shape : Nat) : dataEquiv (data length head shape) = (length,head,shape) :=
  dataEquiv.apply_symm_apply _
def arity (fields : Data Value signature) : Nat := (dataEquiv fields).1 + 2
def children (length head : Nat) (slot : Nat) : Nat := if slot < length + 2 then head else 0
def allowed (tag : Nat) (fields : Data Value signature) (branches : Nat → Nat) : Prop :=
  tag = 0 ∧ (dataEquiv fields).2.2 = 0 ∧ branches 0 = (dataEquiv fields).2.1

theorem children_canonical (length head : Nat) :
    (slots (arity (data length head 0))).Canonical 0 (children length head) := by
  intro slot outside
  have beyond := (SlotEncoding.finite_decoded_iff (Equiv.refl _) slot).mp outside
  change length + 2 ≤ slot at beyond
  exact if_neg (Nat.not_lt_of_ge beyond)

theorem source_admitted (length head : Nat) :
    Admitted Value signature arity allowed 0 (encode Value signature (data length head 0)) (children length head) := by
  apply admitted_encode
  · exact ⟨rfl,by simp,by simp [children]⟩
  · exact children_canonical length head

theorem source_nonzero (length head : Nat) :
    construct Value signature arity 0 (encode Value signature (data length head 0)) (children length head) ≠ 0 :=
  construct_nonzero Value signature arity allowed _ _ _ (source_admitted length head)

theorem node_readback (length head : Nat) :
    decodeNode Value signature
      (construct Value signature arity 0 (encode Value signature (data length head 0)) (children length head)) =
      some (0,data length head 0,List.replicate (length+2) head) := by
  rw [decodeNode_construct]
  apply congrArg some
  apply congrArg (Prod.mk 0)
  apply congrArg (Prod.mk (data length head 0))
  have count : arity (data length head 0) = length + 2 := by simp only [arity,dataEquiv_data]
  rw [count]
  change List.ofFn (fun slot : Fin (length+2) => if slot.val < length+2 then head else 0) = _
  simp only [if_pos (Fin.isLt _)]
  exact List.ofFn_const _ _

theorem source_fields_separated (firstLength firstHead secondLength secondHead : Nat)
    (same : construct Value signature arity 0 (encode Value signature (data firstLength firstHead 0)) (children firstLength firstHead) =
      construct Value signature arity 0 (encode Value signature (data secondLength secondHead 0)) (children secondLength secondHead)) :
    firstLength = secondLength ∧ firstHead = secondHead := by
  have fields := fields_of_eq Value signature arity allowed _ _ _ _ _ _
    (source_admitted firstLength firstHead) (source_admitted secondLength secondHead) same
  have decoded := encode_injective Value signature fields.2.1
  have pairSame := congrArg dataEquiv decoded
  exact ⟨congrArg Prod.fst pairSame,congrArg (fun fields => fields.2.1) pairSame⟩

theorem duplicate_children_retained : snapshot (arity (data 2 7 0)) (children 2 7) = [7,7,7,7] := by
  simp only [arity,dataEquiv_data]
  decide +kernel

theorem zero_vector_retains_scalars : snapshot (arity (data 0 7 0)) (children 0 7) = [7,7] := by
  simp only [arity,dataEquiv_data]
  decide +kernel

def hiddenTail (slot : Nat) : Nat := if slot = 4 then 9 else children 2 7 slot

theorem hidden_tail_same_snapshot : snapshot 4 hiddenTail = snapshot 4 (children 2 7) := by
  apply congrArg List.ofFn
  funext slot
  exact if_neg (Nat.ne_of_lt slot.isLt)

theorem hidden_tail_same_output :
    construct Value signature arity 0 (encode Value signature (data 2 7 0)) hiddenTail =
      construct Value signature arity 0 (encode Value signature (data 2 7 0)) (children 2 7) := by
  rw [construct_encode,construct_encode]
  simpa only [arity,dataEquiv_data] using
    congrArg (fun snapshot => Nat.succ (Encodable.encode (0,data 2 7 0,snapshot))) hidden_tail_same_snapshot

theorem hidden_tail_distinct : hiddenTail ≠ children 2 7 := by
  intro same
  have atFour := congrFun same 4
  change (9:Nat) = 0 at atFour
  exact Nat.noConfusion atFour

theorem hidden_tail_not_canonical : ¬ (slots (arity (data 2 7 0))).Canonical 0 hiddenTail := by
  intro canonical
  have atFour := canonical 4 ((SlotEncoding.finite_decoded_iff (Equiv.refl _) 4).mpr (by decide))
  change (9:Nat) = 0 at atFour
  exact Nat.noConfusion atFour

theorem hidden_tail_not_admitted :
    ¬ Admitted Value signature arity allowed 0 (encode Value signature (data 2 7 0)) hiddenTail := by
  rintro ⟨fields,same,_permitted,canonical⟩
  have exactData := encode_injective Value signature same
  cases exactData
  exact hidden_tail_not_canonical canonical

theorem raw_fields_not_injective :
    ¬ (∀ first second : Nat → Nat,
      construct Value signature arity 0 (encode Value signature (data 2 7 0)) first =
        construct Value signature arity 0 (encode Value signature (data 2 7 0)) second → first = second) :=
  fun injective => hidden_tail_distinct (injective _ _ hidden_tail_same_output)

#print axioms source_fields_separated
#print axioms raw_fields_not_injective
end Mettapedia.TypeTheory.FiniteConstructorEncoding.NaturalRealization.Controls
