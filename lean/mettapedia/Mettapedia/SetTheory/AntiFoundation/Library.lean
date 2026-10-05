import Mettapedia.TypeTheory.MaterialSets.Hypersets.AntiFoundation

/-!
# The full Aczel model, reexported

`HSet` is hypersets modulo bisimilarity. Every graph with nodes in `Type u`
has one decoration there. The one-node loop and the two-node cycle both denote
the unique Quine atom, and the graphs themselves are not equal. This module
only imports that development.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.AntiFoundation

universe u

open Mettapedia.TypeTheory.MaterialSets.Hypersets

theorem library_afa {α : Type u} (r : α → α → Prop) : ∃! d, HSet.IsDecoration r d :=
  HSet.existsUnique_isDecoration r

theorem library_one_quine {x : HSet.{u}} : x = {x} ↔ x = HSet.quineAtom :=
  HSet.eq_singleton_self_iff

theorem library_loop_equiv_twoCycle : HSet.loop ≈ HSet.twoCycle :=
  HSet.loop_equiv_twoCycle

theorem library_loop_ne_twoCycle : HSet.loop ≠ HSet.twoCycle :=
  HSet.loop_ne_twoCycle

theorem library_loops_same_set : HSet.mk HSet.loop = HSet.mk HSet.twoCycle :=
  HSet.mk_loop.trans HSet.mk_twoCycle.symm

end Mettapedia.SetTheory.AntiFoundation
