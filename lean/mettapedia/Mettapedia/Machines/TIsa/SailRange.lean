import Mettapedia.Machines.TIsa.SailSupport
import Mathlib.Data.List.Range

/-!
# Inclusive Sail ranges as checked monadic folds

The original IntRange loop with positive unit stride is equivalent to an
ordinary finite list fold when each successful iteration yields. The proof
uses its actual recursion equation, including the empty range. Monadic errors
retain their original short-circuit behavior.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.SailRange

def ascending (count : Nat) : IntRange := { start := 0, stop := (count : Int) - 1 }

theorem ite_bind {m : Type → Type} [Monad m] {α β : Type}
    (condition : Prop) [Decidable condition] (left right : m α) (next : α → m β) :
    ((if condition then left else right) >>= next) =
      (if condition then left >>= next else right >>= next) := by
  by_cases holds : condition <;> simp only [holds, ite_true, ite_false]

theorem loop_foldlM {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}
    (count remaining offset : Nat) (bounds : offset + remaining = count)
    (body : Int → β → m β) (initial : β)
    (aligned : ((offset : Int) - (ascending count).start) % (ascending count).step = 0) :
    IntRange.forIn'.loop (ascending count) (fun index _ value => do
      pure (.yield (← body index value))) initial (offset : Int) aligned =
      (List.range' offset remaining).foldlM (fun value (index : Nat) => body (index : Int) value) initial := by
  induction remaining generalizing offset initial with
  | zero =>
    rw [IntRange.forIn'.loop.eq_1]
    have outside : ¬(offset : Int) ∈ ascending count := by
      simp [ascending, Membership.mem]
      omega
    rw [dif_neg outside]
    rfl
  | succ remaining ih =>
    rw [IntRange.forIn'.loop.eq_1]
    have inside : (offset : Int) ∈ ascending count := by
      simp [ascending, Membership.mem]
      omega
    rw [dif_pos inside]
    simp only [bind_assoc, pure_bind]
    change (do let value ← body (offset : Int) initial
               IntRange.forIn'.loop (ascending count) _ value ((offset + 1 : Nat) : Int) _) =
      (do let value ← body (offset : Int) initial
          (List.range' (offset + 1) remaining).foldlM (fun value (index : Nat) => body (index : Int) value) value)
    congr 1
    funext value
    exact ih (offset + 1) (by omega) value _

theorem forIn_foldlM {m : Type → Type} [Monad m] [LawfulMonad m] {β : Type}
    (count : Nat) (body : Int → β → m β) (initial : β) :
    forIn (ascending count) initial (fun index value => do pure (.yield (← body index value))) =
      (List.range count).foldlM (fun value (index : Nat) => body (index : Int) value) initial := by
  change IntRange.forIn' (ascending count) initial _ = _
  unfold IntRange.forIn'
  simpa only [List.range_eq_range', ascending, Int.natCast_zero] using
    loop_foldlM count count 0 (by omega) body initial (by simp [ascending])

namespace Controls

theorem three_iterations :
    (forIn (ascending 3) ([] : List Int) (fun index values =>
      pure (.yield (values ++ [index]))) : Id (List Int)) = [0, 1, 2] := by
  change (forIn (ascending 3) ([] : List Int) (fun index values => do
    pure (.yield (← (pure (values ++ [index]) : Id (List Int))))) : Id (List Int)) = _
  rw [forIn_foldlM]
  rfl

theorem zero_iterations :
    (forIn (ascending 0) (17 : Nat) (fun _ value => pure (.yield (value + 1))) : Id Nat) = 17 := by
  change (forIn (ascending 0) (17 : Nat) (fun _ value => do
    pure (.yield (← (pure (value + 1) : Id Nat)))) : Id Nat) = _
  rw [forIn_foldlM]
  rfl

private def failingStep (index : Int) (value : Nat) : Except Nat Nat :=
  if index = 1 then .error 1 else .ok (value + 1)

theorem iteration_error_stops :
    (forIn (ascending 3) (0 : Nat) (fun index value => do
      pure (.yield (← failingStep index value))) : Except Nat Nat) = Except.error 1 := by
  rw [forIn_foldlM]
  rfl

end Controls
end Mettapedia.Machines.TIsa.SailRange

#print axioms Mettapedia.Machines.TIsa.SailRange.forIn_foldlM
