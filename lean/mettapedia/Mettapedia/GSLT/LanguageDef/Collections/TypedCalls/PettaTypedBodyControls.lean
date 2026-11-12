import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyRun
import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaCallerReturnRunFixtures

/-!
# All-budget typed body controls and rejected frame metadata

The general packet theorem is instantiated on the live-source fixtures, not
only on a variable-only toy driver. Query and type-guard multiplicities remain
those of the actual source machine. Exact closed-run counts are separate
execution controls, not inferred from this value-prefix theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open EagerDFS.Destination
open PettaOccurrenceOverlay PettaFrameScopes
open PettaCallerReturnRunFixtures

theorem fixture_head_checked (bad polymorphic repeatedEquation : Bool) (rows : List Atom) :
    Bridges.ScopedReturnFunction.checksHead (program bad polymorphic repeatedEquation rows) "keep" 0 12 = true := by
  cases bad <;> cases polymorphic <;> cases repeatedEquation <;> rfl

theorem every_fixture_budget_preserves_the_ordered_value_prefix
    (operations : Services Unit) (bad polymorphic repeatedEquation : Bool) (rows : List Atom) (fuel : Nat) :
    let source := program bad polymorphic repeatedEquation rows
    let packets := ((PettaOccurrenceOverlay.machine operations .eagerValue source).run fuel
      (initial operations source)).1
    packets.map CollectedAnswer.value = List.replicate packets.length (num 4) := by
  exact PettaTypedBodyRun.checked_ground_body_values operations _ "keep" 0 12
    (fixture_head_checked bad polymorphic repeatedEquation rows) control [num 4] (num 4) (.var "result")
    rfl rfl () [] (Allocator.empty 8 64) ⟨Effects.loaded _, [], []⟩ fuel
    (by simp [num, encode, Mettapedia.Logic.LP.Term.isGround])

theorem synthetic_correct_depth_is_bounded : Bounded (synthetic 1) := by
  apply Scoped.root
  intro item member
  cases List.mem_singleton.mp member
  intro frame member
  cases List.mem_singleton.mp member
  exact ⟨by decide, by decide⟩

theorem synthetic_incorrect_depth_is_rejected : ¬ Bounded (synthetic 2) := by
  intro bounded
  have checked := (PettaCallerReturnPublication.rootDepthCheck_iff _).mpr (root_depths _ bounded)
  have refused : PettaCallerReturnPublication.rootDepthCheck (synthetic 2) = false := by decide
  rw [refused] at checked
  cases checked

theorem changed_return_recipe_is_not_certified :
    Bridges.ScopedReturnFunction.checksHead
      (program false false false [num 7] (.grounded (.string "wrong"))) "keep" 0 12 = false := by decide

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.PettaTypedBodyControls
