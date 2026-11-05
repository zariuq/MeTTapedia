import Mathlib.Data.List.Basic

/-! Set-valued output into an occurrence-preserving destination. Publication
adds absent values without deduplicating or reordering the existing store.
This is a sequential value model; it grants no native transaction or lifetime
guarantee. Each budget unit considers one output, including an existing one. -/

set_option autoImplicit false

namespace Mettapedia.Machines.SetOutputPublication

variable {α : Type*} [BEq α] [LawfulBEq α]

def insertFresh (store : List α) (value : α) : List α :=
  if value ∈ store then store else store ++ [value]

def publish (store : List α) : List α → List α
  | [] => store
  | value :: rest => publish (insertFresh store value) rest

@[simp] theorem mem_insertFresh (store : List α) (value observed : α) :
    observed ∈ insertFresh store value ↔ observed ∈ store ∨ observed = value := by
  by_cases present : value ∈ store
  · simp [insertFresh, present]
    aesop
  · simp [insertFresh, present]

@[simp] theorem mem_publish (store outputs : List α) (value : α) :
    value ∈ publish store outputs ↔ value ∈ store ∨ value ∈ outputs := by
  induction outputs generalizing store with
  | nil => simp [publish]
  | cons head tail ih => simp [publish, ih, or_assoc]

theorem insertFresh_prefix (store : List α) (value : α) :
    store.IsPrefix (insertFresh store value) := by
  by_cases present : value ∈ store
  · simp [insertFresh, present]
  · exact ⟨[value], by simp [insertFresh, present]⟩

theorem publish_prefix (store outputs : List α) : store.IsPrefix (publish store outputs) := by
  induction outputs generalizing store with
  | nil => simp [publish]
  | cons head tail ih => exact (insertFresh_prefix store head).trans (ih _)

theorem publish_existing (store outputs : List α) (present : ∀ value ∈ outputs, value ∈ store) :
    publish store outputs = store := by
  induction outputs with
  | nil => rfl
  | cons head tail ih =>
    simp only [publish, insertFresh, if_pos (present head List.mem_cons_self)]
    exact ih (fun value member => present value (List.mem_cons_of_mem _ member))

theorem publish_idempotent (store outputs : List α) :
    publish (publish store outputs) outputs = publish store outputs :=
  publish_existing _ _ (fun value member => (mem_publish store outputs value).mpr (Or.inr member))

theorem publish_append (store first second : List α) :
    publish store (first ++ second) = publish (publish store first) second := by
  induction first generalizing store with
  | nil => rfl
  | cons head tail ih => simpa only [List.cons_append, publish] using ih (insertFresh store head)

theorem insertFresh_existing_count (store : List α) (value observed : α)
    (present : observed ∈ store) :
    (insertFresh store value).count observed = store.count observed := by
  by_cases h : value ∈ store
  · simp [insertFresh, h]
  · have different : observed ≠ value := by rintro rfl; exact h present
    simp [insertFresh, h, Ne.symm different]

theorem publish_existing_count (store outputs : List α) (value : α) (present : value ∈ store) :
    (publish store outputs).count value = store.count value := by
  induction outputs generalizing store with
  | nil => rfl
  | cons head tail ih =>
    rw [publish, ih _ ((mem_insertFresh _ _ _).mpr (Or.inl present))]
    exact insertFresh_existing_count store head value present

structure State (α : Type*) where
  store : List α
  pending : List α
  deriving Repr, DecidableEq

def advance : Nat → State α → State α
  | 0, state => state
  | _ + 1, ⟨store, []⟩ => ⟨store, []⟩
  | ticks + 1, ⟨store, value :: rest⟩ => advance ticks ⟨insertFresh store value, rest⟩

theorem advance_add (first second : Nat) (state : State α) :
    advance (first + second) state = advance second (advance first state) := by
  induction first generalizing state with
  | zero => simp [advance]
  | succ first ih =>
    rcases state with ⟨store, pending⟩
    cases pending with
    | nil => cases second <;> simp [advance]
    | cons value rest => simpa [Nat.succ_add, advance] using ih ⟨insertFresh store value, rest⟩

/-- The already-published store plus the residual outputs has exactly the
same eventual value as the original session. No fixed-point claim is made. -/
theorem advance_completion (budget : Nat) (state : State α) :
    publish (advance budget state).store (advance budget state).pending =
      publish state.store state.pending := by
  induction budget generalizing state with
  | zero => rfl
  | succ budget ih =>
    rcases state with ⟨store, pending⟩
    cases pending with
    | nil => rfl
    | cons value rest => exact ih ⟨insertFresh store value, rest⟩

theorem advance_all (store outputs : List α) :
    advance outputs.length ⟨store, outputs⟩ = ⟨publish store outputs, []⟩ := by
  induction outputs generalizing store with
  | nil => rfl
  | cons value rest ih => simpa [advance, publish] using ih (insertFresh store value)

example : publish [1, 1, 9] [1, 2, 2, 3] = [1, 1, 9, 2, 3] := by decide +kernel
example : publish [1, 1] [1] ≠ ([1, 1] ++ [1]).eraseDups := by decide +kernel
example : (advance 1 (⟨[1], [1, 2]⟩ : State Nat)).pending = [2] := rfl
example : advance 1 (⟨[1], [1, 2]⟩ : State Nat) ≠ advance 2 ⟨[1], [1, 2]⟩ := by decide +kernel

#print axioms publish_existing_count
#print axioms advance_add

end Mettapedia.Machines.SetOutputPublication
