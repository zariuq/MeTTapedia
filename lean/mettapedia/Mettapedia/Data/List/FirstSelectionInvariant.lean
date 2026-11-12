import Mettapedia.Data.List.FirstSelection

/-! Pointwise invariants survive the exact selected suffix and a first
selected replacement that preserves that invariant. -/

set_option autoImplicit false

namespace List.FirstSelection

universe u
variable {α : Type u}

theorem After.of_append {selected : α → Bool} {before : List α} {chosen : α} {rest : List α}
    (missed : ∀ value ∈ before, selected value = false) (yes : selected chosen = true) :
    After selected (before ++ chosen :: rest) rest := by
  induction before with
  | nil => exact .here yes
  | cons first tail ih =>
      exact .skip (missed first List.mem_cons_self)
        (ih (fun value present => missed value (List.mem_cons_of_mem first present)))

theorem After.unique {selected : α → Bool} {source first second : List α}
    (left : After selected source first) (right : After selected source second) : first = second :=
  Option.some.inj (left.computed.symm.trans right.computed)

theorem After.exists_of_mem {selected : α → Bool} {source : List α} {chosen : α}
    (present : chosen ∈ source) (yes : selected chosen = true) :
    ∃ rest, After selected source rest := by
  induction source with
  | nil => cases present
  | cons first tail ih =>
      cases choice : selected first with
      | true => exact ⟨tail,.here choice⟩
      | false =>
          rcases List.mem_cons.mp present with rfl | later
          · simp only [choice,Bool.false_eq_true] at yes
          · obtain ⟨rest,found⟩ := ih later
            exact ⟨rest,.skip choice found⟩

theorem Change.exists_of_mem {replace : α → Option α} {source : List α} {chosen next : α}
    (present : chosen ∈ source) (yes : replace chosen = some next) :
    ∃ changed, Change replace source changed := by
  induction source with
  | nil => cases present
  | cons first tail ih =>
      cases choice : replace first with
      | some value => exact ⟨value :: tail,.here choice⟩
      | none =>
          rcases List.mem_cons.mp present with rfl | later
          · rw [choice] at yes
            cases yes
          · obtain ⟨changed,found⟩ := ih later
            exact ⟨first :: changed,.skip choice found⟩

theorem After.preserves_all {selected : α → Bool} {source suffix : List α}
    (found : After selected source suffix) (property : α → Prop)
    (all : ∀ value ∈ source, property value) : ∀ value ∈ suffix, property value := by
  obtain ⟨before,chosen,original,yes,earlier⟩ := found.prefix
  intro value present
  apply all value
  rw [original]
  exact List.mem_append_right _ (List.mem_cons_of_mem _ present)

theorem Change.preserves_all {replace : α → Option α} {source changed : List α}
    (found : Change replace source changed) (property : α → Prop)
    (all : ∀ value ∈ source, property value)
    (replacement : ∀ first next, property first → replace first = some next → property next) :
    ∀ value ∈ changed, property value := by
  obtain ⟨before,first,next,rest,original,target,replaced,earlier⟩ := found.prefix
  intro value present
  rw [target] at present
  rcases List.mem_append.mp present with previous | after
  · apply all value
    rw [original]
    exact List.mem_append_left _ previous
  · rcases List.mem_cons.mp after with rfl | later
    · apply replacement first value _ replaced
      apply all first
      rw [original]
      exact List.mem_append_right _ List.mem_cons_self
    · apply all value
      rw [original]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ later)

end List.FirstSelection
