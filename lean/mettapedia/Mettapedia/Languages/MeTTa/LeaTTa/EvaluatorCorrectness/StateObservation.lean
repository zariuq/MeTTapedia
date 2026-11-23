import MettaHyperonFull.Minimal.Interpreter

namespace Mettapedia.Languages.MeTTa.LeaTTa

open Metta (Atom)
open Metta.Minimal (St World resolveStates stateHandle)

/-- When every lookup misses, resolving state handles preserves the whole atom. -/
theorem resolveStates_eq_self_of_lookup_none (world : World)
    (misses : ∀ id : Nat, world.store[id]? = none)
    (atom : Atom) : resolveStates world atom = atom := by
  cases atom with
  | sym _ => simp only [resolveStates]
  | var _ => simp only [resolveStates]
  | gnd _ => simp only [resolveStates]
  | expr children =>
      unfold resolveStates
      split
      next _ id same => rw [misses]; exact same.symm
      next _ children' _ same =>
        have : children = children' := Atom.expr.inj same
        subst children'
        apply congrArg Atom.expr
        calc
          children.map (resolveStates world) = children.map id := by
            apply List.map_congr_left
            intro child membership
            exact resolveStates_eq_self_of_lookup_none world misses child
          _ = children := List.map_id children
      next _ _ _ => rfl
termination_by sizeOf atom
decreasing_by
  have smaller := List.sizeOf_lt_of_mem membership
  simp_wf
  omega

/-- The initial world has no cells to dereference. -/
theorem resolveStates_init_world (atom : Atom) : resolveStates St.init.world atom = atom :=
  resolveStates_eq_self_of_lookup_none _ (by simp [St.init, World.empty]) atom

example : resolveStates St.init.world (.expr [.sym "query", stateHandle 0]) =
    .expr [.sym "query", stateHandle 0] := resolveStates_init_world _

example : resolveStates { World.empty with store := (∅ : Std.HashMap Nat Atom).insert 0 (.sym "recorded") } (stateHandle 0) =
    .sym "recorded" := by simp [resolveStates, stateHandle]

end Mettapedia.Languages.MeTTa.LeaTTa
