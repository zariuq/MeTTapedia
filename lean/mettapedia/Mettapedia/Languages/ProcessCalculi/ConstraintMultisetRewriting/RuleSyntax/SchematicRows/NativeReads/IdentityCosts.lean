import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.OccurrenceKey
import Mathlib.Tactic

/-!
# The cost of repeated linear occurrence registration

The reference searches already registered origins before appending a new one,
as the native adapter does. For pairwise fresh origins its key comparisons
grow quadratically. Lossless origin encoding avoids these registry comparisons
but its arithmetic, decoding, bounded-word refusal and native storage lookup
costs remain separate. A primitive event is not a machine instruction.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IdentityCosts

def search (key : OccurrenceKey) : List OccurrenceKey → Nat × Option Nat
  | [] => (0, none)
  | first :: rest =>
      if key = first then (1, some 0) else
        let later := search key rest
        (later.1 + 1, later.2.map (· + 1))

theorem notMem_search (key : OccurrenceKey) (rows : List OccurrenceKey) (missing : key ∉ rows) :
    search key rows = (rows.length, none) := by
  induction rows with
  | nil => rfl
  | cons first rows ih =>
      have unequal : key ≠ first := fun equal => missing (List.mem_cons.mpr (Or.inl equal))
      have later : key ∉ rows := fun member => missing (List.mem_cons_of_mem _ member)
      simp [search, unequal, ih later]

structure Registration where
  work : Nat
  handle : Nat
  rows : List OccurrenceKey

def register (rows : List OccurrenceKey) (key : OccurrenceKey) : Registration :=
  let found := search key rows
  match found.2 with
  | some index => ⟨found.1, index + 1, rows⟩
  | none => ⟨found.1, rows.length + 1, rows ++ [key]⟩

theorem fresh_register (rows : List OccurrenceKey) (key : OccurrenceKey) (missing : key ∉ rows) :
    register rows key = ⟨rows.length, rows.length + 1, rows ++ [key]⟩ := by
  simp only [register, notMem_search key rows missing]

def run : List OccurrenceKey → List OccurrenceKey → Nat
  | _, [] => 0
  | known, next :: rest =>
      let result := register known next
      result.work + run result.rows rest

def triangle : Nat → Nat
  | 0 => 0
  | n + 1 => triangle n + n

theorem fresh_run_work (known incoming : List OccurrenceKey) (distinct : incoming.Nodup)
    (fresh : ∀ key ∈ incoming, key ∉ known) :
    run known incoming = incoming.length * known.length + triangle incoming.length := by
  induction incoming generalizing known with
  | nil => simp [run, triangle]
  | cons first incoming ih =>
      have notKnown := fresh first (List.mem_cons_self ..)
      have nextFresh : ∀ key ∈ incoming, key ∉ known ++ [first] := by
        intro key member present
        rcases List.mem_append.mp present with old | same
        · exact fresh key (List.mem_cons_of_mem _ member) old
        · have equal := List.mem_singleton.mp same
          have notLater := (List.nodup_cons.mp distinct).1
          exact notLater (equal ▸ member)
      simp only [run, fresh_register known first notKnown]
      rw [ih (known ++ [first]) (List.nodup_cons.mp distinct).2 nextFresh]
      simp only [List.length_cons, List.length_append, List.length_nil, triangle]
      ring

theorem triangle_twice (n : Nat) : 2 * triangle n = n * (n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [triangle]
      cases n with
      | zero => rfl
      | succ n =>
          simp only [Nat.add_sub_cancel] at ih ⊢
          nlinarith

theorem whole_registration_is_quadratic (incoming : List OccurrenceKey) (distinct : incoming.Nodup) :
    2 * run [] incoming = incoming.length * (incoming.length - 1) := by
  rw [fresh_run_work [] incoming distinct (by simp), List.length_nil, Nat.mul_zero, Nat.zero_add]
  exact triangle_twice incoming.length

theorem fourfold_primitive_budget (n : Nat) (large : 49 ≤ n) : 4 * (6 * n) ≤ triangle n := by
  have exactCost := triangle_twice n
  have lower : 48 ≤ n - 1 := by omega
  have product := Nat.mul_le_mul_left n lower
  nlinarith

#print axioms fresh_run_work
#print axioms whole_registration_is_quadratic
#print axioms fourfold_primitive_budget

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.SchematicRows.NativeReads.IdentityCosts
