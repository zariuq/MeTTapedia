import Mettapedia.Languages.MeTTa.PeTTa.LibTransform
import Mettapedia.Machines.Step.Firing

/-!
# The transform library's firing is a firing of the algebra

`LibTransform` models the library on a store that is a list of atoms.  A
footprint lists the atoms a candidate reads and takes; the library validates it
by counting copies (`valid`), the candidate walk finds every read atom in the
store, and the commit removes the takes (`commit`).

Read as multisets, that is the firing of `Firing` with the footprint's reads
and takes, no `absent` predicate and no output to the store (the library's
`absent` conditions are evaluated by the walk before validation, and its
instances go to the caller).

* `enabled_iff`: the firing is enabled exactly when the footprint validates
  and every read atom is stored.
* `fire_eq_commit`: firing it leaves the multiset of the committed store.
* `commits_commute`: so two footprints that are independent in the sense of
  `Firing.Indep` each still validate after the other's commit, and the two
  orders of commit leave the same multiset.

Positive example: `Controls.independent_takes_commute`.  Negative example:
`Controls.one_copy_two_takes` (two takes of one stored copy are each valid and
are not independent: the second does not validate after the first).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Step.FiringLibrary

open Mettapedia.Languages.MeTTa.PeTTa.LibTransform
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- The firing a library footprint stands for. -/
def ofFootprint (fp : Footprint) : Firing Atom where
  reads := (reads fp : List Atom)
  takes := (takes fp : List Atom)
  absent _ := False
  outputs := 0

/-- **The library validates exactly the enabled firings.** -/
theorem enabled_iff (s : Store) (fp : Footprint) :
    (ofFootprint fp).Enabled (s : Multiset Atom) ↔
      valid s fp = true ∧ ∀ a ∈ reads fp, a ∈ s := by
  rw [valid_iff_le]
  unfold Firing.Enabled ofFootprint
  simp only [Firing.mem_sub_iff, Multiset.mem_coe, count_coe, not_false_eq_true, implies_true,
    and_true]
  constructor
  · rintro ⟨le, rd⟩
    refine ⟨⟨le, fun a _ hr => rd a hr⟩, fun a hr => ?_⟩
    exact List.count_pos_iff.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) (rd a hr))
  · rintro ⟨⟨le, both⟩, stored⟩
    refine ⟨le, fun a hr => ?_⟩
    by_cases taken : a ∈ takes fp
    · exact both a taken hr
    · rw [List.count_eq_zero_of_not_mem taken]
      exact List.count_pos_iff.mpr (stored a hr)

/-- **The library's commit is the firing's effect.** -/
theorem fire_eq_commit (s : Store) (fp : Footprint) :
    (ofFootprint fp).fire (s : Multiset Atom) = (commit fp s : Multiset Atom) := by
  rw [commit_coe]
  simp [Firing.fire, ofFootprint]

/-- **Independent footprints commit in either order.**  Each still validates,
with its read atoms stored, after the other's commit, and the two orders leave
the same multiset of atoms. -/
theorem commits_commute (s : Store) (fp gp : Footprint)
    (vf : valid s fp = true) (rf : ∀ a ∈ reads fp, a ∈ s)
    (vg : valid s gp = true) (rg : ∀ a ∈ reads gp, a ∈ s)
    (ind : Firing.Indep (ofFootprint fp) (ofFootprint gp) (s : Multiset Atom)) :
    (valid (commit fp s) gp = true ∧ ∀ a ∈ reads gp, a ∈ commit fp s) ∧
      (valid (commit gp s) fp = true ∧ ∀ a ∈ reads fp, a ∈ commit gp s) ∧
      (commit gp (commit fp s) : Multiset Atom) = (commit fp (commit gp s) : Multiset Atom) := by
  have ef := (enabled_iff s fp).mpr ⟨vf, rf⟩
  have eg := (enabled_iff s gp).mpr ⟨vg, rg⟩
  obtain ⟨efg, egf, eq⟩ := Firing.indep_commute ef eg ind
  rw [fire_eq_commit] at efg
  rw [fire_eq_commit] at egf
  rw [fire_eq_commit, fire_eq_commit, fire_eq_commit, fire_eq_commit] at eq
  exact ⟨(enabled_iff _ gp).mp efg, (enabled_iff _ fp).mp egf, eq⟩

namespace Controls

def a : Atom := .symbol "a"
def b : Atom := .symbol "b"

/-- Positive: a take of `a` and a take of `b` over `[a, b]` are independent, so
they commit in either order to the same store. -/
theorem independent_takes_commute :
    (commit [(.take, b)] (commit [(.take, a)] [a, b]) : Multiset Atom) =
      (commit [(.take, a)] (commit [(.take, b)] [a, b]) : Multiset Atom) := by
  refine (commits_commute [a, b] [(.take, a)] [(.take, b)] (by decide) (by decide) (by decide)
    (by decide) ⟨by decide, by decide, by decide, ?_, ?_⟩).2.2
  · exact fun _ _ h => h
  · exact fun _ _ h => h

/-- Negative: over one copy of `a` two takes of `a` each validate, and the
second does not validate after the first has committed. -/
theorem one_copy_two_takes :
    valid [a] [(.take, a)] = true ∧ valid (commit [(.take, a)] [a]) [(.take, a)] = false := by
  decide

end Controls

end Mettapedia.Machines.Step.FiringLibrary
