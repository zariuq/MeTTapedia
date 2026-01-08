import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Ordered-group background (Clay–Rolfsen Ch.2, Hölder context)

This file collects the parts of the ordered-group background that are already available in
mathlib, and repackages them with names/citations that align with the K&S discussion.

Primary source:
- Clay & Rolfsen, “Ordered Groups and Topology” (arXiv:1511.05088), Chapter 2 “Hölder’s theorem”.
  Local PDF: `literature/KS_codex/Clay_Mann_2015_Ordered_Groups_Topology.pdf`

In particular, Clay–Rolfsen Problem 2.3 (“for any non-identity `g` and any `h`, find `n : ℤ`
with `g^n ≤ h < g^(n+1)`”) matches mathlib’s `existsUnique_zpow_near_of_one_lt` once translated
to mathlib’s `MulArchimedean` setting.
-/

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Literature

open Classical

section

variable {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [MulArchimedean G]

/-!
## “Archimedean floor” for powers (Clay–Rolfsen Problem 2.3)

Mathlib already provides a strong form: existence *and uniqueness* of the integer exponent.
-/

theorem existsUnique_zpow_near_of_one_lt_of_mulArchimedean {a : G} (ha : 1 < a) (g : G) :
    ∃! k : ℤ, a ^ k ≤ g ∧ g < a ^ (k + 1) :=
  by
    simpa using (_root_.existsUnique_zpow_near_of_one_lt (a := a) ha g)

end

end Mettapedia.ProbabilityTheory.KnuthSkilling.Literature
