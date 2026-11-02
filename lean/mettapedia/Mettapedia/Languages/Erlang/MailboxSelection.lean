import Mettapedia.Languages.Erlang.Mailbox

/-! Exact first-match selection, with the unmatched prefix retained. The
selector includes pattern and guard checks; its implementation is a separate
sequential-language obligation. These laws quantify over arbitrary selectors
and retain duplicate message occurrences. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Erlang.Mailbox

variable {α β : Type*}

theorem selectFirst_append_skipped (select : α → Option β) (before after : List α)
    (skipped : ∀ message ∈ before, select message = none) :
    selectFirst select (before ++ after) =
      (selectFirst select after).map (fun pair => (pair.1, before ++ pair.2)) := by
  induction before with
  | nil => simp
  | cons head tail ih =>
      have first := skipped head List.mem_cons_self
      have rest := ih (fun message member => skipped message (List.mem_cons_of_mem _ member))
      simp only [List.cons_append, selectFirst, first, rest]
      cases selectFirst select after <;> rfl

theorem selectFirst_of_first {select : α → Option β} {before after : List α} {message : α} {result : β}
    (skipped : ∀ prior ∈ before, select prior = none) (selected : select message = some result) :
    selectFirst select (before ++ message :: after) = some (result, before ++ after) := by
  rw [selectFirst_append_skipped select before _ skipped]
  simp [selectFirst, selected]

theorem selectFirst_some_iff {select : α → Option β} {messages : List α} {result : β} {rest : List α} :
    selectFirst select messages = some (result, rest) ↔
      ∃ before message after, messages = before ++ message :: after ∧
        select message = some result ∧ (∀ prior ∈ before, select prior = none) ∧
        rest = before ++ after := by
  constructor
  · exact selectFirst_some
  · rintro ⟨before, message, after, rfl, selected, skipped, rfl⟩
    exact selectFirst_of_first skipped selected

/- Distinct equal occurrences remain in the residual list. -/
theorem selectFirst_duplicate {select : α → Option β} {message : α} {result : β} {after : List α}
    (selected : select message = some result) :
    selectFirst select (message :: message :: after) = some (result, message :: after) := by
  simp [selectFirst, selected]

/-- Swapping two matching messages changes the complete receive result even
when their clause results agree: the remaining message still differs. -/
theorem selectFirst_order_sensitive {select : α → Option β} {first second : α}
    {left right : β} (firstMatches : select first = some left)
    (secondMatches : select second = some right) (different : first ≠ second) :
    selectFirst select [first, second] ≠ selectFirst select [second, first] := by
  intro equal
  have pairs : (left, [second]) = (right, [first]) := by
    apply Option.some.inj
    simpa only [selectFirst, firstMatches, secondMatches] using equal
  exact different (List.cons.inj (congrArg Prod.snd pairs)).1.symm

/-- A representation that identifies every permutation cannot implement this
ordered receive operation. This applies to bags, irrespective of their index
or decoding algorithm; it does not exclude bags carrying extra order data. -/
theorem no_perm_invariant_receive {State : Type*} (encode : List α → State)
    (forgetsOrder : ∀ before after, before.Perm after → encode before = encode after)
    {select : α → Option β} {first second : α} {left right : β}
    (firstMatches : select first = some left) (secondMatches : select second = some right)
    (different : first ≠ second) :
    ¬ ∃ receive : State → Option (β × List α),
      ∀ messages, receive (encode messages) = selectFirst select messages := by
  rintro ⟨receive, correct⟩
  apply selectFirst_order_sensitive firstMatches secondMatches different
  calc
    selectFirst select [first, second] = receive (encode [first, second]) := (correct _).symm
    _ = receive (encode [second, first]) :=
      congrArg receive (forgetsOrder _ _ (List.Perm.swap _ _ []))
    _ = selectFirst select [second, first] := correct _

/-- Even the value-only observation cannot forget order if two matching
messages select different results. -/
theorem no_perm_invariant_value {State : Type*} (encode : List α → State)
    (forgetsOrder : ∀ before after, before.Perm after → encode before = encode after)
    {select : α → Option β} {first second : α} {left right : β}
    (firstMatches : select first = some left) (secondMatches : select second = some right)
    (different : left ≠ right) :
    ¬ ∃ receive : State → Option β,
      ∀ messages, receive (encode messages) = (selectFirst select messages).map Prod.fst := by
  rintro ⟨receive, correct⟩
  have equal : (selectFirst select [first, second]).map Prod.fst =
      (selectFirst select [second, first]).map Prod.fst := by
    rw [← correct, ← correct]
    exact congrArg receive (forgetsOrder _ _ (List.Perm.swap _ _ []))
  exact different (by simpa only [selectFirst, firstMatches, secondMatches, Option.map_some,
    Option.some.injEq] using equal)

namespace Controls

/-- The guard skips two messages and removes only the first accepted occurrence. -/
theorem skipped_prefix_and_duplicate_survive :
    selectFirst (fun n : Nat => if n = 2 then some n else none) [0, 1, 2, 2, 3] =
      some (2, [0, 1, 2, 3]) := rfl

/-- Matching return values alone conceal different retained process states. -/
theorem equal_values_different_residuals :
    let select := fun _ : Nat => some true
    (selectFirst select [0, 1]).map Prod.fst = (selectFirst select [1, 0]).map Prod.fst ∧
      selectFirst select [0, 1] ≠ selectFirst select [1, 0] := by
  exact ⟨rfl, selectFirst_order_sensitive rfl rfl (by decide)⟩

theorem first_value_depends_on_order :
    (selectFirst (fun n : Nat => some n) [0, 1]).map Prod.fst = some 0 ∧
      (selectFirst (fun n : Nat => some n) [1, 0]).map Prod.fst = some 1 := ⟨rfl, rfl⟩

end Controls

end Mettapedia.Languages.Erlang.Mailbox
