import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Fixed-width information at finite interfaces

An interface code has an encoder and a partial decoder. The decoder recovers
every encoded value; unused words need not denote anything. Exactly `b` binary
positions are modeled by `Fin (2^b)`. This gives a finite coding optimum, not
a physical byte bound, a shortest-program algorithm, or a Kolmogorov claim.

Retained side information changes the question: a context-indexed decoder
needs enough words for each fibre, whereas a decoder that must also recover
the context needs enough words for their disjoint union.
-/

set_option autoImplicit false

namespace Mettapedia.InformationTheory.FiniteInterfaceCoding

universe u v

abbrev Word (bits : Nat) := Fin (2 ^ bits)

structure Code (Value : Type u) (bits : Nat) where
  encode : Value → Word bits
  decode : Word bits → Option Value
  roundtrip : ∀ value, decode (encode value) = some value

theorem Code.injective {Value : Type u} {bits : Nat} (code : Code Value bits) :
    Function.Injective code.encode := by
  intro first second same
  have decoded := congrArg code.decode same
  simpa only [code.roundtrip, Option.some.injEq] using decoded

theorem Code.card_bound {Value : Type u} [Finite Value] {bits : Nat} (code : Code Value bits) :
    Nat.card Value ≤ 2 ^ bits := by
  simpa using Nat.card_le_card_of_injective code.encode code.injective

/-- An explicit finite enumeration constructs both directions. -/
def ofEnumeration {Value : Type u} {count bits : Nat} (enumeration : Value ≃ Fin count)
    (fits : count ≤ 2 ^ bits) : Code Value bits where
  encode value := ⟨(enumeration value).val, (enumeration value).isLt.trans_le fits⟩
  decode word := if inside : word.val < count then some (enumeration.symm ⟨word.val, inside⟩) else none
  roundtrip value := by
    simp only [dif_pos (enumeration value).isLt]
    exact congrArg some (enumeration.symm_apply_apply value)

theorem ofEnumeration_unused_word {Value : Type u} {count bits : Nat}
    (enumeration : Value ≃ Fin count) (fits : count ≤ 2 ^ bits) (word : Word bits)
    (unused : count ≤ word.val) : (ofEnumeration enumeration fits).decode word = none := by
  simp [ofEnumeration, Nat.not_lt_of_ge unused]

noncomputable def optimal {Value : Type u} [Finite Value] : Code Value (Nat.clog 2 (Nat.card Value)) := by
  letI := Fintype.ofFinite Value
  apply ofEnumeration (Fintype.equivFin Value)
  simpa only [Nat.card_eq_fintype_card] using Nat.le_pow_clog (b := 2) (by decide) (Nat.card Value)

theorem exists_code_iff {Value : Type u} [Finite Value] (bits : Nat) :
    Nonempty (Code Value bits) ↔ Nat.card Value ≤ 2 ^ bits := by
  constructor
  · rintro ⟨code⟩
    exact code.card_bound
  · intro bound
    let := Fintype.ofFinite Value
    exact ⟨ofEnumeration (Fintype.equivFin Value) (by simpa only [Nat.card_eq_fintype_card] using bound)⟩

theorem minimum_width {Value : Type u} [Finite Value] (bits : Nat) :
    Nonempty (Code Value bits) ↔ Nat.clog 2 (Nat.card Value) ≤ bits := by
  rw [exists_code_iff, Nat.clog_le_iff_le_pow (by decide : 1 < 2)]

def Sufficient {State : Type u} (relation : Setoid State) {Summary : Type v}
    (summary : State → Summary) : Prop :=
  ∀ left right, summary left = summary right → relation.r left right

noncomputable def representatives {State : Type u} (relation : Setoid State) {Summary : Type v}
    (summary : State → Summary) : Quotient relation → Summary :=
  fun cls => summary cls.out

theorem representatives_injective {State : Type u} (relation : Setoid State) {Summary : Type v}
    (summary : State → Summary) (sufficient : Sufficient relation summary) :
    Function.Injective (representatives relation summary) := by
  intro first second same
  have equivalent := sufficient first.out second.out same
  have equal : Quotient.mk relation first.out = Quotient.mk relation second.out := Quotient.sound equivalent
  simpa only [Quotient.out_eq] using equal

theorem summary_card_bound {State : Type u} (relation : Setoid State) [Finite (Quotient relation)] {Summary : Type v}
    [Finite Summary] (summary : State → Summary) (sufficient : Sufficient relation summary) :
    Nat.card (Quotient relation) ≤ Nat.card Summary :=
  Nat.card_le_card_of_injective _ (representatives_injective relation summary sufficient)

theorem sufficient_word_lower_bound {State : Type u} (relation : Setoid State) [Finite (Quotient relation)]
    {bits : Nat} (summary : State → Word bits) (sufficient : Sufficient relation summary) :
    Nat.clog 2 (Nat.card (Quotient relation)) ≤ bits := by
  apply (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr
  simpa using summary_card_bound relation summary sufficient

/-- Encode the quotient rather than the original state. The generic
enumeration is classical; concrete enumeration arguments remain data. -/
noncomputable def quotientSummary {State : Type u} (relation : Setoid State) [Finite (Quotient relation)] :
    State → Word (Nat.clog 2 (Nat.card (Quotient relation))) :=
  fun state => (optimal (Value := Quotient relation)).encode (Quotient.mk relation state)

theorem quotientSummary_exact {State : Type u} (relation : Setoid State) [Finite (Quotient relation)] (left right : State) :
    quotientSummary relation left = quotientSummary relation right ↔ relation.r left right := by
  constructor
  · intro same
    exact Quotient.exact ((optimal (Value := Quotient relation)).injective same)
  · intro equivalent
    exact congrArg (optimal (Value := Quotient relation)).encode (Quotient.sound equivalent)

theorem exists_sufficient_word_iff {State : Type u} (relation : Setoid State) [Finite (Quotient relation)] (bits : Nat) :
    (∃ summary : State → Word bits, Sufficient relation summary) ↔
      Nat.clog 2 (Nat.card (Quotient relation)) ≤ bits := by
  constructor
  · rintro ⟨summary, sufficient⟩
    exact sufficient_word_lower_bound relation summary sufficient
  · intro bound
    obtain ⟨code⟩ := (minimum_width (Value := Quotient relation) bits).mpr bound
    refine ⟨fun state => code.encode (Quotient.mk relation state), ?_⟩
    intro left right same
    exact Quotient.exact (code.injective same)

/-- The decoder receives the already retained context. -/
abbrev FibreCode (Context : Type u) (Value : Context → Type v) (bits : Nat) :=
  ∀ context, Code (Value context) bits

theorem fibre_code_iff {Context : Type u} {Value : Context → Type v} [∀ context, Finite (Value context)]
    (bits : Nat) : Nonempty (FibreCode Context Value bits) ↔
      ∀ context, Nat.card (Value context) ≤ 2 ^ bits := by
  constructor
  · rintro ⟨code⟩ context
    exact (code context).card_bound
  · intro bounds
    classical
    exact ⟨fun context => Classical.choice ((exists_code_iff (Value := Value context) bits).mpr (bounds context))⟩

/-- Without retained context the code must distinguish the disjoint union. -/
theorem unframed_code_iff {Context : Type u} [Fintype Context] {Value : Context → Type v}
    [∀ context, Finite (Value context)] (bits : Nat) :
    Nonempty (Code (Sigma Value) bits) ↔ (∑ context, Nat.card (Value context)) ≤ 2 ^ bits := by
  rw [exists_code_iff, Nat.card_sigma]

noncomputable def fibreWidth {Context : Type u} [Fintype Context] (Value : Context → Type v) : Nat :=
  Finset.univ.sup (fun context => Nat.clog 2 (Nat.card (Value context)))

theorem minimum_fibre_width {Context : Type u} [Fintype Context] {Value : Context → Type v}
    [∀ context, Finite (Value context)] (bits : Nat) :
    Nonempty (FibreCode Context Value bits) ↔ fibreWidth Value ≤ bits := by
  simp only [fibre_code_iff, fibreWidth, Finset.sup_le_iff, Finset.mem_univ, true_implies,
    Nat.clog_le_iff_le_pow (by decide : 1 < 2)]

/-- Charging a context code as well as a fibre code is sufficient for the
joint interface. The context has not disappeared from the memory budget. -/
theorem context_and_fibre_budget {Context : Type u} [Fintype Context] {Value : Context → Type v}
    [∀ context, Finite (Value context)] {contextBits valueBits : Nat}
    (context : Code Context contextBits) (fibres : FibreCode Context Value valueBits) :
    Nonempty (Code (Sigma Value) (contextBits + valueBits)) := by
  apply (unframed_code_iff _).mpr
  have localBounds := Finset.sum_le_sum (s := Finset.univ)
    (f := fun c => Nat.card (Value c)) (g := fun _ => 2 ^ valueBits)
    (fun c _ => (fibres c).card_bound)
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at localBounds
  have contextBound : Fintype.card Context ≤ 2 ^ contextBits := by
    simpa only [Nat.card_eq_fintype_card] using context.card_bound
  calc
    _ ≤ Fintype.card Context * 2 ^ valueBits := localBounds
    _ ≤ 2 ^ contextBits * 2 ^ valueBits := Nat.mul_le_mul_right _ contextBound
    _ = _ := (Nat.pow_add ..).symm

namespace Controls

def boolean : Code Bool 1 where
  encode value := if value then 1 else 0
  decode word := some (word.val = 1)
  roundtrip value := by cases value <;> rfl

theorem one_bit_per_known_context : Nonempty (FibreCode Bool (fun _ => Bool) 1) := ⟨fun _ => boolean⟩

theorem one_bit_cannot_also_recover_context : ¬Nonempty (Code (Bool × Bool) 1) := by
  rw [exists_code_iff]
  norm_num [Nat.card_prod, Nat.card_eq_fintype_card]

def threeValues : Code (Fin 3) 2 := ofEnumeration (Equiv.refl _) (by decide)

theorem three_values_require_two_bits : ¬Nonempty (Code (Fin 3) 1) ∧ Nonempty (Code (Fin 3) 2) := by
  constructor
  · rw [exists_code_iff]
    norm_num
  · exact ⟨threeValues⟩

theorem unused_code_is_not_a_fabricated_value : threeValues.decode 3 = none := by decide +kernel

theorem empty_interface_needs_no_bits : Nonempty (Code (Fin 0) 0) := by
  rw [exists_code_iff]
  simp

end Controls

end Mettapedia.InformationTheory.FiniteInterfaceCoding
