import MettaHyperonFull.Minimal.Interpreter
import MettaHyperonFull.Proofs.BindingLaws

/-!
# Collapse/superpose binding round-trip

The published `collapse-bind` instruction stores every result together with
its binding set in an opaque grounded payload.  `superpose-bind` later restores
that payload and merges it with the bindings at the continuation point.

Before repair #22, LeaTTa stored `()` in every collapsed pair, so a binding
created by the collapsed computation disappeared when the pair was resumed.
The positive canaries below pin the lossless runtime carrier and its resumption
behavior.  The negative canary keeps malformed, manually constructed pairs
outside that protocol from being mistaken for binding payloads.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaCollapseBindingCounterexample

open Metta
open Metta.Minimal

private def captured : Bindings :=
  [.val "q" (.sym "A")]

/-- The opaque carrier restores every relation in its original order. -/
theorem stored_bindings_roundtrip :
    Bindings.restore (Bindings.store captured) = captured := by
  exact Bindings.restore_store captured

/-- A collapsed alternative resumed with no additional bindings recovers the
exact binding set that accompanied the result. -/
theorem superpose_restores_captured_binding :
    superposeItems [] []
        (.expr [.sym "Hit", .gnd (.bindings (Bindings.store captured))]) =
      [finItem [] (.sym "Hit") captured] := by
  have hloop : Bindings.hasLoop captured = false :=
    Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Atom.vars])
  simp [superposeItems, Bindings.restore_store,
    Bindings.merge_empty_right, hloop]

/-- A syntactic pair whose second component is not the opaque binding carrier
does not acquire fabricated bindings. -/
theorem malformed_pair_does_not_decode_bindings :
    superposeItems [] [] (.expr [.sym "Hit", .unit]) =
      [finItem [] (.sym "Hit") []] := by
  rfl

end Mettapedia.Languages.MeTTa.HE.LeaTTaCollapseBindingCounterexample
