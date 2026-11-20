import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation.Cost

/-!
# An ordered failure continuation for a shared-world schedule

A scheduler selects an occurrence by position. A reply replaces that
occurrence in place, carrying the other alternatives in their original
order. Forgetting order yields exactly the source replacement bag.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.ContextualFamily

namespace OrderedAgenda

variable {A : Type}

def replace (items : List A) (chosen : Fin items.length) (replies : List A) : List A :=
  items.take chosen.val ++ replies ++ items.drop (chosen.val + 1)

def pending (items : List A) (chosen : Fin items.length) : List A := replace items chosen []

/-- Traversal and grafting in a pointer machine. A cell inspection and
a new link each cost one unit. The untouched suffix stays shared. -/
def graft : List A → List A → List A × Nat
  | [], suffix => (suffix, 1)
  | item :: rest, suffix =>
    let copied := graft rest suffix
    (item :: copied.1, copied.2 + 2)

theorem graft_exact (first later : List A) :
    graft first later = (first ++ later, 2 * first.length + 1) := by
  induction first with
  | nil => rfl
  | cons item rest ih =>
    simp only [graft, ih, List.cons_append, List.length_cons]
    congr 1

/-- Follow the selected occurrence, call its service once, and splice
the ordered reply. An unavailable reply aborts the entire splice. -/
def meteredSplice {R : Type} (reply : A → Option (R × List A) × Nat) :
    (items : List A) → Fin items.length → Option (R × List A) × Nat
  | [], position => Fin.elim0 position
  | item :: suffix, ⟨0, _⟩ =>
    let response := reply item
    match response.1 with
    | none => (none, response.2 + 1)
    | some (result, emitted) =>
      let output := graft emitted suffix
      (some (result, output.1), response.2 + 1 + output.2)
  | item :: suffix, ⟨position + 1, fits⟩ =>
    let later := meteredSplice reply suffix ⟨position, Nat.lt_of_succ_lt_succ fits⟩
    (later.1.map (fun (result, tail) => (result, item :: tail)), later.2 + 2)

def emittedWork {R : Type} : Option (R × List A) → Nat
  | none => 0
  | some (_, items) => 2 * items.length + 1

theorem meteredSplice_exact {R : Type} (reply : A → Option (R × List A) × Nat)
    (items : List A) (position : Fin items.length) :
    let response := reply (items.get position)
    meteredSplice reply items position =
      (response.1.map (fun (result, emitted) => (result, replace items position emitted)),
        response.2 + 2 * position.val + 1 + emittedWork response.1) := by
  induction items with
  | nil => exact Fin.elim0 position
  | cons item rest ih =>
    obtain ⟨index, within⟩ := position
    cases index with
    | zero =>
      cases got : (reply item).1 with
      | none => simp [meteredSplice, got, emittedWork]
      | some pair =>
        rcases pair with ⟨result, emitted⟩
        simp [meteredSplice, got, emittedWork, graft_exact, replace]
    | succ index =>
      have fits : index < rest.length := Nat.lt_of_succ_lt_succ within
      simp only [meteredSplice, ih ⟨index, fits⟩, List.get_cons_succ, Option.map_map]
      change ((reply (rest.get ⟨index, fits⟩)).1.map _, _) = _
      congr 1
      omega

theorem as_multiset (items : List A) (chosen : Fin items.length) :
    (items : Multiset A) = items.get chosen ::ₘ (pending items chosen : Multiset A) := by
  change (items : Multiset A) = ((items.get chosen :: pending items chosen : List A) : Multiset A)
  apply Multiset.coe_eq_coe.mpr
  have pieces : items = items.take chosen.val ++ (items.get chosen :: items.drop (chosen.val + 1)) := by
    calc
      items = items.take (chosen.val + 1) ++ items.drop (chosen.val + 1) :=
        (List.take_append_drop _ _).symm
      _ = _ := by
        simp only [List.take_succ_eq_append_getElem chosen.isLt, List.get_eq_getElem,
          List.append_assoc, List.singleton_append]
  exact (List.Perm.of_eq pieces).trans (by simpa only [pending, replace, List.append_nil] using
    (List.perm_middle (a := items.get chosen) (l₁ := items.take chosen.val) (l₂ := items.drop (chosen.val + 1))))

theorem replace_multiset (items : List A) (chosen : Fin items.length) (replies : List A) :
    (replace items chosen replies : Multiset A) = (replies : Multiset A) + (pending items chosen : Multiset A) := by
  rw [Multiset.coe_add]
  apply Multiset.coe_eq_coe.mpr
  simpa only [pending, replace, List.append_assoc, List.append_nil] using
    List.perm_append_comm_assoc (items.take chosen.val) replies (items.drop (chosen.val + 1))

variable {S : Signature} {κ : Keys S} {Γ : Ctx S} {star : S.Srt}
  {D : Discipline S Γ star} {P : Program κ Γ star D.Ty} {supply : Nat → Term S Γ star}

/-- Selected effects change the shared world once. The remainder of the
agenda survives in the charged source move even when the reply is empty. -/
theorem charged_replacement
    (strategy : Strategy κ Γ star D.Ty) (before after : World κ Γ star)
    (items : List (Branch κ Γ star D.Ty)) (chosen : Fin items.length)
    (replies : List (Branch κ Γ star D.Ty))
    (selects : strategy.chooses ⟨before, (items : Multiset _)⟩ (items.get chosen))
    (live : Solvable (items.get chosen).store)
    (response : Move D P supply before (items.get chosen) after (replies : Multiset _)) :
    ChargedStep D P supply strategy ⟨before, (items : Multiset _)⟩
      (charge strategy ⟨before, (items : Multiset _)⟩ (items.get chosen) replies)
      ⟨after, (replace items chosen replies : Multiset _)⟩ := by
  have chosenBag := as_multiset items chosen
  rw [chosenBag] at selects
  rw [chosenBag, replace_multiset]
  exact .move before after (items.get chosen) (pending items chosen) replies selects live response

namespace Controls

theorem failure_keeps_the_other_equal_occurrence :
    pending ([4, 7, 4] : List Nat) ⟨2, by decide⟩ = [4, 7] ∧
      pending ([4, 7, 4] : List Nat) ⟨0, by decide⟩ = [7, 4] := by decide +kernel

theorem expanded_replies_keep_the_caller_order :
    replace ([4, 7, 4] : List Nat) ⟨1, by decide⟩ [1, 2, 1] = [4, 1, 2, 1, 4] := by decide +kernel

end Controls
end OrderedAgenda
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.SourceLanguage.Preparation
