import Mettapedia.Machines.TIsa.StoreInstructions.StorePublication

/-!
# Closed occurrence queries read one multiplicity

An exact bucket supplies a common observation for presence,
absence and exact count. An exact bucket describes the selected
value at this snapshot; head or argument keys that allow false
positives cannot justify using its length as a value count.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.IndexedGuard

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (Check)
open Derivation (Matcher Store passes)
open PackedOccurrences (Codes)

inductive Query where
  | any
  | absent
  | count (expected : ℕ)
  deriving DecidableEq

def Query.check {T : Type*} (query : Query) (pattern : T) : Check T :=
  match query with
  | .any => .predicate .any pattern
  | .absent => .predicate .none pattern
  | .count expected => .count pattern expected

def Query.accepts (query : Query) (number : ℕ) : Bool :=
  match query with
  | .any => decide (0 < number)
  | .absent => decide (number = 0)
  | .count expected => decide (number = expected)

def Query.condition : Query → Comparison
  | .any => .notEqual
  | _ => .equal

def Query.target : Query → ℕ
  | .count expected => expected
  | _ => 0

theorem Query.word_decision (query : Query) (number : ℕ)
    (numberFits : number < 2 ^ 64) (targetFits : query.target < 2 ^ 64) :
    query.condition.evaluate (BitVec.ofNat 64 number) (BitVec.ofNat 64 query.target) = query.accepts number := by
  have exact (n k : ℕ) (nFits : n < 2 ^ 64) (kFits : k < 2 ^ 64) :
      (BitVec.ofNat 64 n == BitVec.ofNat 64 k) = decide (n = k) := by
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt nFits, Nat.mod_eq_of_lt kFits]
  cases query with
  | any =>
    simp only [Query.condition, Query.accepts, Query.target, Comparison.evaluate, bne, exact number 0 numberFits (by decide)]
    by_cases zero : number = 0
    · simp [zero]
    · simp [zero, Nat.pos_of_ne_zero zero]
  | absent => exact exact number 0 numberFits (by decide)
  | count expected => exact exact number expected numberFits targetFits

universe u v w
variable {T : Type u} {V : Type v} {B : Type w} [DecidableEq V] {keys : ℕ}

def countOf (store : Store V) (value : V) : ℕ :=
  store.occurrences.countP (fun occurrence => decide (occurrence.2 = value))

def ExactBucket (classify : V → Fin keys) (store : Store V) (value : V) : Prop :=
  ∀ atom ∈ store.occurrences, classify atom.2 = classify value ↔ atom.2 = value

omit [DecidableEq V] in
theorem injective_bucket (classify : V → Fin keys) (injective : Function.Injective classify)
    (store : Store V) (value : V) : ExactBucket classify store value :=
  fun _ _ => ⟨fun equal => injective equal, congrArg classify⟩

theorem count_in_word (codes : Codes V) {store : Store V} {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes store = some packed) (value : V) : countOf store value < 2 ^ 64 := by
  have width := packed.sizeWord.isLt
  rw [(PackedOccurrences.pack_roundtrip codes formed).2] at width
  exact lt_of_le_of_lt List.countP_le_length width

theorem lengthWord_exact (codes : Codes V) (classify : V → Fin keys)
    {store : Store V} {snapshot : StorePublication.Snapshot}
    (formed : StorePublication.encode codes classify store = some snapshot) (value : V)
    (exactKey : ExactBucket classify store value) :
    PackedIndex.lengthWord? snapshot.index (classify value).val = some (BitVec.ofNat 64 (countOf store value)) := by
  have found := StorePublication.reads_published codes classify formed (classify value)
  have expected := PackedIndex.candidates_length codes snapshot.data snapshot.index (classify value).val found
  have same : (store.occurrences.filter fun atom => classify atom.2 == classify value) =
      store.occurrences.filter (fun atom => decide (atom.2 = value)) := by
    apply List.filter_congr
    intro atom member
    apply Bool.eq_iff_iff.mpr
    rw [beq_iff_eq, decide_eq_true_eq]
    exact exactKey atom member
  rw [same, ← List.countP_eq_length_filter] at expected
  exact expected

theorem passes_from_count (M : Matcher T V B) (store : Store V) (bindings : B) (query : Query)
    (pattern : T) (value : V) (instantiated : M.instantiate bindings pattern = some value) :
    passes M store bindings (query.check pattern) = query.accepts (countOf store value) := by
  cases query with
  | any =>
    apply Bool.eq_iff_iff.mpr
    simp only [Query.check, passes, instantiated, Query.accepts, countOf,
      List.any_eq_true, decide_eq_true_eq, List.countP_pos_iff]
  | absent =>
    apply Bool.eq_iff_iff.mpr
    simp only [Query.check, passes, instantiated, Query.accepts, countOf,
      Bool.not_eq_true', List.any_eq_false, decide_eq_true_eq, List.countP_eq_zero]
  | count _ =>
    simp only [Query.check, passes, instantiated, Query.accepts, countOf]
    rfl

theorem execute_count_read (M : Matcher T V B) (st : StoreInstructions.State V B)
    (level : ℕ) (dst : P1Source.Reg) (query : Query) (pattern : T) (value : V)
    (instantiated : M.instantiate (st.levels level).bindings pattern = some value) :
    executeInstruction M st (.transform (.test (.check (query.check pattern)) level dst)) =
      .ok (st.write dst (booleanWord (query.accepts (countOf st.store value)))) := by
  simp only [executeInstructionWith, P1Source.Instruction.view, StoreProfile.step, StoreProfile.ground,
    Derivation.Determinate.apply, passes_from_count M st.store _ query pattern value instantiated]
  cases query.accepts (countOf st.store value) <;>
    simp [booleanWord, StoreInstructions.State.setLevel, Function.update_eq_self]

theorem unrepresentable_target_refuses (codes : Codes V) {store : Store V} {packed : PackedOccurrences.Layout}
    (formed : PackedOccurrences.pack codes store = some packed) (value : V) {target : ℕ} (large : 2 ^ 64 ≤ target) :
    (Query.count target).accepts (countOf store value) = false := by
  have width := count_in_word codes formed value
  exact decide_eq_false (by omega)

namespace Examples

private def two : Store Word := ⟨[(2, 42), (7, 42)], 8⟩

theorem one_witness_but_two_occurrences :
    Query.any.accepts (countOf two 42) = true ∧
    (Query.count 2).accepts (countOf two 42) = true ∧ (Query.count 1).accepts (countOf two 42) = false := by
  decide +kernel

theorem zero_count_is_absence :
    Query.absent.accepts (countOf two 17) = true ∧ Query.any.accepts (countOf two 17) = false := by decide +kernel

private def mixed : Store Word := ⟨[(2, 42), (7, 17)], 8⟩

theorem colliding_bucket_is_not_an_exact_count_key :
    ¬ ExactBucket (fun _ : Word => (0 : Fin 1)) mixed 42 := by
  intro exactKey
  have incorrect := (exactKey (7, 17) (by simp [mixed])).mp rfl
  change (17 : Word) = 42 at incorrect
  exact (by decide : (17 : Word) ≠ 42) incorrect

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.IndexedGuard
