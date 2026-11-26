import Mettapedia.GSLT.Equations.Preference
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Quot

/-!
# A preferred section from finitely many written representatives

The generated equality class can be infinite. Preference only ranks the
finite set of written representatives in that class. A candidate in a
sink component is eligible; a score resolves preferences between eligible
candidates, without changing the quotient. Classes with no written
representative admit the usual quotient section.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Equations.PreferredSection

open Preference (Eligible Reach)

variable {A : Type*}

def induced (written : Finset A) (edge : A → A → Prop) (u v : A) : Prop :=
  u ∈ written ∧ v ∈ written ∧ edge u v

theorem reach_inside {s : Finset A} {edge : A → A → Prop} {u v : A}
    (starts : u ∈ s) (path : Reach (induced s edge) u v) : v ∈ s := by
  cases path with
  | refl => exact starts
  | tail _ last => exact last.2.1

noncomputable def reachable (s : Finset A) (edge : A → A → Prop) (u : A) : Finset A := by
  classical exact s.filter (Reach (induced s edge) u)

theorem exists_eligible (s : Finset A) (edge : A → A → Prop) (nonempty : s.Nonempty) :
    ∃ u ∈ s, Eligible (induced s edge) u := by
  classical
  obtain ⟨u, inside, smallest⟩ := s.exists_min_image
    (fun u => (reachable s edge u).card) nonempty
  refine ⟨u, inside, ?_⟩
  intro v forward
  have insideV := reach_inside inside forward
  by_contra cannot
  have subset : reachable s edge v ⊆ reachable s edge u := by
    intro z found
    obtain ⟨member, onward⟩ := Finset.mem_filter.mp found
    exact Finset.mem_filter.mpr ⟨member, forward.trans onward⟩
  have strict : reachable s edge v ⊂ reachable s edge u := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨subset, ?_⟩
    intro same
    have arrives : u ∈ reachable s edge u := Finset.mem_filter.mpr ⟨inside, .refl⟩
    rw [← same] at arrives
    exact cannot (Finset.mem_filter.mp arrives).2
  exact (Nat.not_lt_of_ge (smallest v insideV)) (Finset.card_lt_card strict)

noncomputable def members (e : Setoid A) (written : Finset A) (c : Quotient e) : Finset A := by
  classical exact written.filter (fun a => Quotient.mk e a = c)

noncomputable def eligibleMembers (s : Finset A) (edge : A → A → Prop) : Finset A := by
  classical exact s.filter (Eligible (induced s edge))

theorem eligible_nonempty {s : Finset A} {edge : A → A → Prop} (h : s.Nonempty) :
    (eligibleMembers s edge).Nonempty := by
  classical
  obtain ⟨u, member, chosen⟩ := exists_eligible s edge h
  exact ⟨u, Finset.mem_filter.mpr ⟨member, chosen⟩⟩

noncomputable def printed (e : Setoid A) (written : Finset A)
    (edge : A → A → Prop) (score : A → Nat) (c : Quotient e) : A := by
  classical
  let s := members e written c
  exact if h : s.Nonempty then
    (Finset.exists_min_image (eligibleMembers s edge) score (eligible_nonempty h)).choose
  else c.out

theorem printed_preferred (e : Setoid A) (written : Finset A) (edge : A → A → Prop)
    (score : A → Nat) (c : Quotient e) (nonempty : (members e written c).Nonempty) :
    printed e written edge score c ∈ eligibleMembers (members e written c) edge ∧
      ∀ a ∈ eligibleMembers (members e written c) edge, score (printed e written edge score c) ≤ score a := by
  classical
  rw [printed, dif_pos nonempty]
  exact (Finset.exists_min_image (eligibleMembers (members e written c) edge) score
    (eligible_nonempty nonempty)).choose_spec

@[simp] theorem printed_section (e : Setoid A) (written : Finset A)
    (edge : A → A → Prop) (score : A → Nat) (c : Quotient e) :
    Quotient.mk e (printed e written edge score c) = c := by
  classical
  by_cases someWritten : (members e written c).Nonempty
  · have eligible := (printed_preferred e written edge score c someWritten).1
    have member : printed e written edge score c ∈ members e written c :=
      (Finset.mem_filter.mp eligible).1
    exact (Finset.mem_filter.mp member).2
  · rw [printed, dif_neg someWritten]
    exact Quotient.out_eq c

theorem same_print_iff (e : Setoid A) (written : Finset A) (edge : A → A → Prop)
    (score : A → Nat) (x y : A) :
    printed e written edge score (Quotient.mk e x) = printed e written edge score (Quotient.mk e y) ↔
      e.r x y := by
  constructor
  · intro equal
    apply Quotient.exact
    simpa only [printed_section] using congrArg (Quotient.mk e) equal
  · intro equivalent
    exact congrArg (printed e written edge score) (Quotient.sound equivalent)

section Controls

theorem outgoing_without_return_is_not_eligible :
    ¬ Eligible (fun a b : Bool => a = false ∧ b = true) false := by
  intro wins
  have impossible := wins true (.single ⟨rfl, rfl⟩)
  cases impossible with
  | tail _ last => cases last.2

theorem directed_cycle_keeps_both_candidates :
    Eligible (fun a b : Bool => a ≠ b) false ∧ Eligible (fun a b : Bool => a ≠ b) true := by
  constructor <;> intro y _ <;> cases y
  · exact .refl
  · exact .single (by decide)
  · exact .single (by decide)
  · exact .refl

end Controls

end Mettapedia.GSLT.Equations.PreferredSection
