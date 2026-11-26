import Mettapedia.Machines.TIsa.StoreInstructions.PackedSubstitution
import Mettapedia.Machines.TIsa.StoreInstructions.PackedEquations

/-!
# Coordinates of an ordered packed agenda extension

When its length is known, the existing ordered prefix operation
can be realized by filling a fresh suffix in descending order.
Its new head depends on the length; the bottom record names
the old suffix. There is no need to materialize the reverse of
the input sequence merely to obtain these destinations.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.StoreInstructions.PackedAgendaCoordinates

open PackedEquations (Arena Node prependWords)

def headAfter (start : ℕ) (tail : Word) : ℕ → Word
  | 0 => tail
  | n + 1 => BitVec.ofNat 64 (start + (n + 1))

def recordAt (start : ℕ) (tail : Word) (i : ℕ) (equation : Word × Word) : Node :=
  ⟨headAfter start tail i, equation.1, equation.2⟩

structure Coordinates (prior updated : Arena) (tail head : Word) (inserted : List (Word × Word)) : Prop where
  size : updated.size = prior.size + inserted.length
  root : head = headAfter prior.size tail inserted.length
  preserved : ∀ i : ℕ, i < prior.size → updated[i]? = prior[i]?
  placement : ∀ (i : ℕ) (equation : Word × Word), inserted.reverse[i]? = some equation →
    updated[prior.size + i]? = some (recordAt prior.size tail i equation)

theorem coordinates (prior : Arena) (tail : Word) (inserted : List (Word × Word))
    {updated : Arena} {head : Word} (built : prependWords prior tail inserted = some (updated, head)) :
    Coordinates prior updated tail head inserted := by
  induction inserted generalizing updated head with
  | nil =>
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj built)
    exact ⟨by simp, rfl, fun _ _ => rfl, by simp⟩
  | cons first rest ih =>
    rcases first with ⟨left, right⟩
    obtain ⟨⟨mid, anchor⟩, earlier, added⟩ := Option.bind_eq_some_iff.mp built
    have atMid := ih earlier
    change PackedEquations.append mid ⟨anchor, left, right⟩ = some (updated, head) at added
    unfold PackedEquations.append at added
    split at added
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj added)
      have midSize := atMid.size
      refine ⟨by simp [atMid.size, Nat.add_assoc], by simp [PackedEquations.next, headAfter, atMid.size, Nat.add_assoc],
        fun i below => ?_, ?_⟩
      · rw [Array.getElem?_push, if_neg (show i ≠ mid.size by omega)]
        exact atMid.preserved i below
      · intro i equation present
        rw [List.reverse_cons] at present
        by_cases earlier : i < rest.reverse.length
        · rw [List.getElem?_append_left earlier] at present
          have below : prior.size + i < mid.size := by
            rw [List.length_reverse] at earlier
            omega
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt below)]
          exact atMid.placement i equation present
        · have bound := (List.getElem?_eq_some_iff.mp present).1
          simp only [List.length_append, List.length_reverse, List.length_cons, List.length_nil] at bound earlier
          have last : i = rest.length := by omega
          subst i
          rw [List.getElem?_append_right (by simp), List.length_reverse, Nat.sub_self] at present
          have selected : (left, right) = equation := Option.some.inj present
          rw [← selected, ← atMid.size, Array.getElem?_push_size]
          rw [recordAt, atMid.root]
    · cases added

/-- The source cursor may enumerate from head to tail and
decrement the destination ordinal. The ordinary packed prefix
and this placement have the same record at every destination. -/
theorem Coordinates.descending {prior updated : Arena} {tail head : Word} {inserted : List (Word × Word)}
    (layout : Coordinates prior updated tail head inserted) (i : ℕ) (equation : Word × Word)
    (present : inserted[i]? = some equation) :
    let lower := inserted.length - 1 - i
    updated[prior.size + lower]? = some (recordAt prior.size tail lower equation) := by
  have bound := (List.getElem?_eq_some_iff.mp present).1
  apply layout.placement
  rwa [List.getElem?_reverse' (by omega : inserted.length - 1 - i + i + 1 = inserted.length)]

private theorem mapM_at {A B : Type*} (convert : A → Option B) (before : List A) {after : List B}
    (result : before.mapM convert = some after) :
    before.length = after.length ∧ ∀ (i : ℕ) (x : A), before[i]? = some x → after[i]? = convert x := by
  induction before generalizing after with
  | nil =>
    obtain rfl := Option.some.inj result
    exact ⟨rfl, by simp⟩
  | cons first rest ih =>
    rw [List.mapM_cons] at result
    obtain ⟨x, selected, continuation⟩ := Option.bind_eq_some_iff.mp result
    obtain ⟨later, rewritten, built⟩ := Option.bind_eq_some_iff.mp continuation
    obtain rfl := Option.some.inj built
    have ⟨length, read⟩ := ih rewritten
    refine ⟨by simp [length], ?_⟩
    intro i value found
    cases i with
    | zero =>
      obtain rfl := Option.some.inj found
      exact selected.symm
    | succ i => exact read i value found

/-- The destination for remapping one equation depends only on
its original position and the original suffix length.
In particular, two equal input equations still have distinct
destinations. -/
theorem remapped_destination (prior : Arena) (tail : Word)
    (mapping : Array Word) (input output : List (Word × Word))
    (remapped : PackedSubstitution.remapPending mapping input = some output)
    {updated : Arena} {head : Word} (built : prependWords prior tail output = some (updated, head))
    (i : ℕ) (original rewritten : Word × Word) (atInput : input[i]? = some original)
    (atMap : PackedSubstitution.mappedPair mapping original = some rewritten) :
    let lower := input.length - 1 - i
    updated[prior.size + lower]? = some (recordAt prior.size tail lower rewritten) := by
  have ⟨sameSize, found⟩ := mapM_at (PackedSubstitution.mappedPair mapping) input remapped
  rw [sameSize]
  exact (coordinates prior tail output built).descending i rewritten ((found i _ atInput).trans atMap)

theorem remap_length (mapping : Array Word) (input output : List (Word × Word))
    (remapped : PackedSubstitution.remapPending mapping input = some output) :
    output.length = input.length :=
  (mapM_at (PackedSubstitution.mappedPair mapping) input remapped).1.symm

theorem distinct_destinations {size n i j : ℕ} (inI : i < n) (inJ : j < n) (different : i ≠ j) :
    size + (n - 1 - i) ≠ size + (n - 1 - j) := by omega

namespace Examples

private def duplicated : List (Word × Word) := [(10, 11), (12, 13), (10, 11)]

theorem fills_three_distinct_records_and_retains_order :
    (prependWords #[] 0 duplicated).bind (fun pair => PackedEquations.readWords pair.1 pair.2) =
      some duplicated := by decide +kernel

theorem forward_push_reverses_the_observable_agenda :
    (prependWords #[] 0 ([(10, 11), (12, 13)] : List (Word × Word)).reverse).bind
      (fun pair => PackedEquations.readWords pair.1 pair.2) ≠ some [(10, 11), (12, 13)] := by decide +kernel

end Examples

end Mettapedia.Machines.TIsa.StoreInstructions.PackedAgendaCoordinates
