import Mettapedia.TypeTheory.FiniteConstructorNaturality

/-!
# Guarded field-map controls

Two natural-valued fields and an empty constructor retain their occurrences.
Mapping natural fields to Booleans is reversible on zero and one. Outside
that guard, distinct source payloads have the same mapped payload.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FiniteConstructorEncoding.MapControls
open IndexedPolynomial.Description
inductive FieldSort where | scalar
  deriving DecidableEq
abbrev Source : FieldSort → Type := fun _ => Nat
abbrev Target : FieldSort → Type := fun _ => Bool
def signature : Signature (SortCode := FieldSort) := [[.scalar,.scalar],[],[.scalar]]
def lower (_sort : FieldSort) (value : Nat) : Bool := value != 0
def raise (_sort : FieldSort) (value : Bool) : Nat := if value then 1 else 0
def guard (_sort : FieldSort) (value : Nat) := value < 2

theorem recover (sort : FieldSort) (value : Nat) (valid : guard sort value) : raise sort (lower sort value) = value := by
  change value < 2 at valid
  cases value with
  | zero => rfl
  | succ value =>
      have only : value = 0 := by omega
      subst value
      rfl

def data : Data Source signature := ⟨⟨0,by decide⟩,0,1,PUnit.unit⟩
def targetData : Data Target signature := ⟨⟨0,by decide⟩,false,true,PUnit.unit⟩
theorem fields_are_mapped : mapData lower signature data = targetData := rfl
theorem represented_roundtrip :
    mapPayload raise signature (mapPayload lower signature (encode Source signature data)) = encode Source signature data :=
  mapPayload_roundtrip lower raise guard recover signature _ ⟨data,by change (0:Nat) < 2 ∧ 1 < 2 ∧ True; decide +kernel,rfl⟩

def emptyData : Data Source signature := ⟨⟨1,by decide⟩,PUnit.unit⟩
def singletonData : Data Source signature := ⟨⟨2,by decide⟩,0,PUnit.unit⟩
theorem constructors_stay_distinct :
    mapPayload lower signature (encode Source signature emptyData) ≠
      mapPayload lower signature (encode Source signature singletonData) := by
  intro same
  rw [mapPayload_encode,mapPayload_encode] at same
  have occurrence := congrArg (fun data => data.1.val) (encode_injective Target signature same)
  change (1 : Nat) = 2 at occurrence
  cases occurrence

def one : Data Source signature := ⟨⟨2,by decide⟩,1,PUnit.unit⟩
def two : Data Source signature := ⟨⟨2,by decide⟩,2,PUnit.unit⟩
theorem outside_guard_collapses : mapPayload lower signature (encode Source signature one) =
    mapPayload lower signature (encode Source signature two) := by
  rw [mapPayload_encode,mapPayload_encode]
  rfl
theorem original_payloads_distinct : encode Source signature one ≠ encode Source signature two := by
  intro same
  have fields := Sigma.mk.inj (encode_injective Source signature same)
  have impossible : (1 : Nat) = 2 := congrArg Prod.fst (eq_of_heq fields.2)
  cases impossible
theorem invalid_payload_is_excluded : ¬ payloadGuard guard signature (encode Source signature two) := by
  rintro ⟨selected,valid,same⟩
  have sameData := encode_injective Source signature same
  cases sameData
  change (2:Nat) < 2 ∧ True at valid
  exact (Nat.lt_irrefl 2) valid.1
theorem guards_cannot_be_dropped : ¬ Function.Injective (mapPayload lower signature) := by
  intro injective
  exact original_payloads_distinct (injective outside_guard_collapses)

#print axioms represented_roundtrip
#print axioms constructors_stay_distinct
#print axioms guards_cannot_be_dropped
end Mettapedia.TypeTheory.FiniteConstructorEncoding.MapControls
