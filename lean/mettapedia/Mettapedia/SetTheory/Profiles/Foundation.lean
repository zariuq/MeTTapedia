import Mettapedia.SetTheory.Profiles.Principles

/-!
# Membership induction against Quine atoms

Membership induction yields that no set is a member of itself, and therefore
that there is no Quine atom. A Quine atom is a self-member, so it refutes
membership induction and refutes irreflexivity of membership.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.Profiles

universe u

variable {S : Type u} {mem : Mem S}

/-- Membership induction yields that no set belongs to itself. -/
theorem irreflexive_of_induction (ind : HasMemInduction mem) : ∀ x, ¬ mem x x := by
  refine ind (fun x => ¬ mem x x) ?_
  intro x ih hx
  exact ih x hx hx

/-- Membership induction yields that there is no Quine atom. -/
theorem noQuineAtom_of_induction (ind : HasMemInduction mem) : ¬ HasQuineAtom mem := by
  intro atom
  obtain ⟨q, hq⟩ := atom
  exact irreflexive_of_induction ind q ((hq q).2 rfl)

/-- A Quine atom belongs to itself. -/
theorem selfMember_of_quineAtom (atom : HasQuineAtom mem) : ∃ x, mem x x := by
  obtain ⟨q, hq⟩ := atom
  exact ⟨q, (hq q).2 rfl⟩

/-- A Quine atom refutes membership induction. -/
theorem quineAtom_refutes_induction (atom : HasQuineAtom mem) : ¬ HasMemInduction mem :=
  fun ind => noQuineAtom_of_induction ind atom

/-- A Quine atom refutes irreflexivity of membership. -/
theorem quineAtom_refutes_irreflexive (atom : HasQuineAtom mem) : ¬ ∀ x, ¬ mem x x := by
  intro irr
  obtain ⟨q, hq⟩ := atom
  exact irr q ((hq q).2 rfl)

end Mettapedia.SetTheory.Profiles
