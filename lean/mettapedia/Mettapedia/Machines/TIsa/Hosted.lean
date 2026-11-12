import Mettapedia.Machines.TIsa.Cells
import Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation

/-!
# The scalar profile's GSLT and generated native logic

The operational theory is the existing resource transform system. Theorems
below connect its bag execution to scalar readback in both directions. No
separate ISA state machine is used as the definition of the calculus.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.TIsa.Hosted

open Cells
open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis

universe u
variable {Key : Type u} [DecidableEq Key]

/-- Exact readback of all source-authorized resource successors. -/
theorem rewrite_iff_scalar_update (keys : Finset Key) (values : Key → Word)
    (after : Multiset (Cell Key)) :
    (system (Key := Key)).theory.rewrites (encode keys values) after ↔
      ∃ action : Action Key, ∃ result : Word,
        action.support ⊆ keys ∧
        action.scalar.evaluate (action.inputs.map values) = some result ∧
        after = encode keys (Function.update values action.destination result) := by
  constructor
  · rintro ⟨action, invocation, enabled, rfl⟩
    exact ⟨action, invocation.result, ((enabled_iff action invocation keys values).mp enabled).1,
      enabled_computes action invocation keys values enabled,
      fire_refines_update action invocation keys values enabled⟩
  · rintro ⟨action, result, inScope, computes, rfl⟩
    obtain ⟨invocation, enabled, same⟩ := scalar_update_realized action keys values result inScope computes
    exact ⟨action, invocation, enabled, same.symm⟩

/-- OSLF's forward diamond observes exactly scalar updates, with no new outcomes. -/
theorem nativeDiamond_iff_scalar_update (post : Multiset (Cell Key) → Prop)
    (keys : Finset Key) (values : Key → Word) :
    (semanticDiamond (system (Key := Key)).theory (nativePredicate system post)).1
        (encode keys values) ↔
      ∃ action : Action Key, ∃ result : Word,
        action.support ⊆ keys ∧
        action.scalar.evaluate (action.inputs.map values) = some result ∧
        post (encode keys (Function.update values action.destination result)) := by
  rw [nativeDiamond_iff]
  constructor
  · rintro ⟨after, step, holds⟩
    obtain ⟨action, result, inScope, computes, rfl⟩ :=
      (rewrite_iff_scalar_update keys values after).mp step
    exact ⟨action, result, inScope, computes, holds⟩
  · rintro ⟨action, result, inScope, computes, holds⟩
    exact ⟨_, (rewrite_iff_scalar_update keys values _).mpr
      ⟨action, result, inScope, computes, rfl⟩, holds⟩

/-- The generated box is a predecessor property, including in this profile. -/
theorem nativeBox_predecessors (pre : Multiset (Cell Key) → Prop) (after : Multiset (Cell Key)) :
    (semanticBox (system (Key := Key)).theory (nativePredicate system pre)).1 after ↔
      ∀ before, (system (Key := Key)).theory.rewrites before after → pre before :=
  Mettapedia.OSLF.Bridges.GSLT.ResourceSeparation.nativeBox_predecessors
    system (nativePredicate system pre) after

end Mettapedia.Machines.TIsa.Hosted
