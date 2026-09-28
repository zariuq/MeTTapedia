import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup
import Mathlib.Logic.Function.Basic

/-!
# A variable index whose proposals the list confirms

The runtime keeps lists of variables: a call's variables, the fresh cells an
import made, the variables of a host goal.  Asking one whether it holds a
variable by scanning it costs its length, so filling a list of `n` variables
one lookup at a time costs `n²`.

A hashed table answers in constant time.  It only proposes a position, and
the list confirms it: the variable is at that position of the list
(`lookup`).  A confirmed answer is always right (`lookup_sound`), however
stale the table.  A list that is emptied and refilled keeps its table without
clearing it: old entries propose positions the list no longer confirms.

A table is complete for a list when it proposes, for each variable of the
list, a position that holds it (`Complete`).  Then a lookup finds exactly the
variables of the list (`lookup_complete`, `lookup_none`).  Recording each
variable as it is appended keeps a table complete (`complete_append`).  A
list filled by appending only the variables a lookup did not find holds
each variable once (`nodup_of_fill`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.VariableIndex

universe u

variable {V : Type u} [DecidableEq V]

/-- The position the table proposes for `v`, when the list confirms it. -/
def lookup (l : List V) (proposal : V → Option ℕ) (v : V) : Option ℕ :=
  match proposal v with
  | some p => if l[p]? = some v then some p else none
  | none => none

/-- A confirmed position holds the variable. -/
theorem lookup_sound {l : List V} {proposal : V → Option ℕ} {v : V} {p : ℕ}
    (h : lookup l proposal v = some p) : l[p]? = some v := by
  unfold lookup at h
  split at h
  · split at h
    · cases h
      assumption
    · cases h
  · cases h

/-- The table proposes, for every variable of the list, a position holding
it. -/
def Complete (l : List V) (proposal : V → Option ℕ) : Prop :=
  ∀ v ∈ l, ∃ p, proposal v = some p ∧ l[p]? = some v

/-- A complete table finds every variable of the list. -/
theorem lookup_complete {l : List V} {proposal : V → Option ℕ} {v : V}
    (h : Complete l proposal) (hv : v ∈ l) : ∃ p, lookup l proposal v = some p := by
  obtain ⟨p, hp, hlp⟩ := h v hv
  exact ⟨p, by simp [lookup, hp, hlp]⟩

/-- A lookup finds nothing that is not in the list. -/
theorem lookup_none {l : List V} {proposal : V → Option ℕ} {v : V}
    (hv : v ∉ l) : lookup l proposal v = none := by
  cases h : lookup l proposal v with
  | none => rfl
  | some p =>
      exact absurd (List.mem_of_getElem? (lookup_sound h)) hv

/-- Recording an appended variable at its position keeps a table complete. -/
theorem complete_append {l : List V} {proposal : V → Option ℕ} (v : V)
    (h : Complete l proposal) :
    Complete (l ++ [v]) (Function.update proposal v (some l.length)) := by
  intro w hw
  by_cases hwv : w = v
  · subst hwv
    refine ⟨l.length, by simp, ?_⟩
    simp
  · rcases List.mem_append.mp hw with hl | hs
    · obtain ⟨p, hp, hlp⟩ := h w hl
      refine ⟨p, by simp [hwv, hp], ?_⟩
      obtain ⟨hlt, -⟩ := List.getElem?_eq_some_iff.mp hlp
      rw [List.getElem?_append_left hlt]
      exact hlp
    · simp at hs
      exact absurd hs hwv

omit [DecidableEq V] in
/-- The empty list's table is complete, whatever it holds. -/
theorem complete_nil (proposal : V → Option ℕ) : Complete [] proposal := by
  intro v hv
  cases hv

/-- A list filled by appending each variable a lookup did not find, and
recording it, holds each variable once. -/
theorem nodup_of_fill :
    ∀ (xs : List V) (l : List V) (proposal : V → Option ℕ),
      l.Nodup → Complete l proposal →
      ∃ (l' : List V) (proposal' : V → Option ℕ),
        l'.Nodup ∧ Complete l' proposal' ∧ ∀ v, v ∈ l' ↔ v ∈ l ∨ v ∈ xs
  | [], l, proposal, hnd, hc => ⟨l, proposal, hnd, hc, fun v => by simp⟩
  | x :: xs, l, proposal, hnd, hc => by
      cases hfind : lookup l proposal x with
      | some p =>
          have hx : x ∈ l := List.mem_of_getElem? (lookup_sound hfind)
          obtain ⟨l', proposal', hnd', hc', hmem⟩ :=
            nodup_of_fill xs l proposal hnd hc
          refine ⟨l', proposal', hnd', hc', fun v => ?_⟩
          rw [hmem v]
          constructor
          · rintro (h | h)
            · exact .inl h
            · exact .inr (List.mem_cons_of_mem x h)
          · rintro (h | h)
            · exact .inl h
            · rcases List.mem_cons.mp h with rfl | h
              · exact .inl hx
              · exact .inr h
      | none =>
          have hx : x ∉ l := fun hx =>
            let ⟨_, hp⟩ := lookup_complete hc hx
            by rw [hfind] at hp; cases hp
          have hnd1 : (l ++ [x]).Nodup := by
            rw [List.nodup_append_comm]
            exact List.nodup_cons.mpr ⟨hx, hnd⟩
          obtain ⟨l', proposal', hnd', hc', hmem⟩ :=
            nodup_of_fill xs (l ++ [x]) _ hnd1 (complete_append x hc)
          refine ⟨l', proposal', hnd', hc', fun v => ?_⟩
          rw [hmem v]
          simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
          exact or_assoc

namespace Controls

/-- A stale proposal, left from a list since emptied and refilled with other
variables, is not confirmed. -/
theorem stale_not_confirmed :
    lookup [2, 3] (fun v => if v = 7 then some 1 else none) 7 = none := by
  decide

/-- A proposal the list confirms is the variable's position. -/
theorem confirmed :
    lookup [2, 7, 3] (fun v => if v = 7 then some 1 else none) 7 = some 1 := by
  decide

end Controls

end Mettapedia.Machines.VariableIndex
