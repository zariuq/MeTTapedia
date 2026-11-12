import Mathlib.Data.List.Basic

/-!
# Suffix and update operations at the first selected occurrence

The independent relations retain source order, an unchanged prefix and the
exact selected occurrence. A missing selection refuses; it is not replaced
by an empty suffix or an unchanged successful update.
-/

set_option autoImplicit false

namespace List.FirstSelection

universe u
variable {α : Type u}

def after? (selected : α → Bool) : List α → Option (List α)
  | [] => none
  | first :: rest => if selected first then some rest else after? selected rest

inductive After (selected : α → Bool) : List α → List α → Prop where
  | here {first rest} : selected first = true → After selected (first :: rest) rest
  | skip {first rest suffix} : selected first = false → After selected rest suffix →
      After selected (first :: rest) suffix

theorem After.computed {selected : α → Bool} {source suffix : List α}
    (found : After selected source suffix) : after? selected source = some suffix := by
  induction found with
  | here chosen => simp only [after?,chosen,↓reduceIte]
  | skip missed _ ih => simp only [after?,missed,Bool.false_eq_true,↓reduceIte,ih]

theorem after_sound (selected : α → Bool) (source suffix : List α)
    (computed : after? selected source = some suffix) : After selected source suffix := by
  induction source with
  | nil => cases computed
  | cons first rest ih =>
      cases choice : selected first with
      | false => exact .skip choice (ih (by simpa only [after?,choice,Bool.false_eq_true,↓reduceIte] using computed))
      | true =>
          simp only [after?,choice,↓reduceIte,Option.some.injEq] at computed
          subst suffix
          exact .here choice

theorem after_iff (selected : α → Bool) (source suffix : List α) :
    after? selected source = some suffix ↔ After selected source suffix :=
  ⟨after_sound selected source suffix,After.computed⟩

theorem After.prefix {selected : α → Bool} {source suffix : List α}
    (found : After selected source suffix) :
    ∃ before chosen, source = before ++ chosen :: suffix ∧ selected chosen = true ∧
      ∀ value ∈ before, selected value = false := by
  induction found with
  | @here chosen suffix yes => exact ⟨[],chosen,rfl,yes,by simp⟩
  | @skip first rest suffix no edge ih =>
      obtain ⟨before,chosen,rfl,yes,earlier⟩ := ih
      exact ⟨first :: before,chosen,rfl,yes,by simpa only [mem_cons,forall_eq_or_imp] using And.intro no earlier⟩

def change? (replace : α → Option α) : List α → Option (List α)
  | [] => none
  | first :: rest =>
      match replace first with
      | some next => some (next :: rest)
      | none => (change? replace rest).map (first :: ·)

inductive Change (replace : α → Option α) : List α → List α → Prop where
  | here {first next rest} : replace first = some next →
      Change replace (first :: rest) (next :: rest)
  | skip {first rest changed} : replace first = none → Change replace rest changed →
      Change replace (first :: rest) (first :: changed)

theorem Change.computed {replace : α → Option α} {source changed : List α}
    (found : Change replace source changed) : change? replace source = some changed := by
  induction found with
  | here replaced => simp only [change?,replaced]
  | skip missed _ ih => simp only [change?,missed,ih,Option.map_some]

theorem change_sound (replace : α → Option α) (source changed : List α)
    (computed : change? replace source = some changed) : Change replace source changed := by
  induction source generalizing changed with
  | nil => cases computed
  | cons first rest ih =>
      cases replacement : replace first with
      | some next =>
          simp only [change?,replacement,Option.some.injEq] at computed
          subst changed
          exact .here replacement
      | none =>
          simp only [change?,replacement,Option.map_eq_some_iff] at computed
          obtain ⟨tail,found,rfl⟩ := computed
          exact .skip replacement (ih tail found)

theorem change_iff (replace : α → Option α) (source changed : List α) :
    change? replace source = some changed ↔ Change replace source changed :=
  ⟨change_sound replace source changed,Change.computed⟩

theorem Change.prefix {replace : α → Option α} {source changed : List α}
    (found : Change replace source changed) :
    ∃ before first next rest,
      source = before ++ first :: rest ∧ changed = before ++ next :: rest ∧
      replace first = some next ∧ ∀ value ∈ before, replace value = none := by
  induction found with
  | @here first next rest replaced => exact ⟨[],first,next,rest,rfl,rfl,replaced,by simp⟩
  | @skip head tail changed missed edge ih =>
      obtain ⟨before,first,next,rest,rfl,rfl,replaced,earlier⟩ := ih
      exact ⟨head :: before,first,next,rest,rfl,rfl,replaced,
        by simpa only [mem_cons,forall_eq_or_imp] using And.intro missed earlier⟩

theorem Change.length {replace : α → Option α} {source changed : List α}
    (found : Change replace source changed) : changed.length = source.length := by
  induction found with
  | here => rfl
  | skip _ _ ih => simpa only [length_cons] using congrArg Nat.succ ih

end List.FirstSelection
