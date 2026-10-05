import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoRuntime

/-!
# Discriminating controls for the actual runtime inventory

The positive entry contains both an application and a persistent definition.
The rejected configurations test stale and duplicate tokens, unissued replies,
source-name aliasing and mismatched stored handlers. Each tests a specific
condition needed to invert arbitrary actual runtime communications.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryControls

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryInventory

abbrev publicScope : Ctx sig := [.nm, .nm]

def retainedIdentity : NamePassingLambda.Expr publicScope :=
  .defn (.lam (.var .zero)) (.app (.var .zero) (.succ .zero))

/-- The whole concrete compiler initializes this nontrivial source program. -/
theorem retained_identity_runtime :
    ∃ (code : Code 0) (activities : List (Activity (.nm :: publicScope))),
      NamePassingRho.compile retainedIdentity (fun _ name => Var.succ name) .zero
        (RhoUnaryWorld.initial (.nm :: publicScope)).world = some code ∧
      Inventory (RhoUnaryWorld.initial (.nm :: publicScope)) activities ∧
      StructuralEq (MonadicProtocol.lower
        (NamePassingLambda.compile retainedIdentity (fun _ name => Var.succ name) .zero))
        (source activities) ∧
      Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
        (RhoUnaryExecution.runtime code 3)
        (actual (RhoUnaryWorld.initial (.nm :: publicScope)).world activities) :=
  NamePassingRhoRuntime.fresh_runtime retainedIdentity

theorem stale_token_rejected :
    ¬ Inventory (RhoUnaryWorld.initial publicScope)
      [.allocatorReady, .token 3] := by
  intro inventory
  have impossible := inventory.token_unique
  simp [tokens, tokenSeed, List.filterMap_cons, RhoUnaryWorld.initial, publicScope] at impossible

theorem duplicate_token_rejected :
    ¬ Inventory (RhoUnaryWorld.initial publicScope)
      [.allocatorReady, .token 2, .token 2] := by
  intro inventory
  have impossible := congrArg List.length inventory.token_unique
  simp [tokens, tokenSeed, List.filterMap_cons] at impossible

/-- The cursor seed is fresh but has not yet been issued as a reply. -/
theorem unissued_reply_rejected :
    ¬ Inventory (RhoUnaryWorld.initial publicScope)
      [.allocatorReady, .token 2, .reply 2, .privateScope nil .nil] := by
  intro inventory
  have impossible := inventory.reply_below 2 (by simp [replies, replySeed])
  change 2 < 2 at impossible
  omega

theorem source_owner_alias_rejected :
    ¬ Inventory (RhoUnaryWorld.initial publicScope)
      [.allocatorReady, .token 2, .ready .zero nil .nil 0] := by
  intro inventory
  have ownerMember : (⟨0, .zero, nil⟩ : Owner publicScope) ∈
      listeners [.allocatorReady, .token 2, .ready .zero nil .nil 0] := by
    simp [listeners, listener]
  have impossible := inventory.owner_fresh _ ownerMember .zero
  exact impossible rfl

def sendingBody : Proc (.nm :: publicScope) := out1 (.var .zero) (.var .zero)

theorem sendingBody_guarded : GuardedUnary sendingBody := .out1 _ _

/-- Equal self-channel seeds do not certify that the received code belongs
to the listener. The actual source continuation is part of the owner. -/
theorem mismatched_handler_rejected :
    ¬ Inventory (RhoUnaryWorld.initial publicScope).advance
      [.allocatorReady, .token 3, .rearm .zero nil .nil 2,
        .sendCode .zero sendingBody sendingBody_guarded 2] := by
  intro inventory
  have owners := inventory.rearm_owner .zero .zero nil sendingBody .nil sendingBody_guarded 2
    (by simp) (by simp)
  have impossible : (nil : Proc (.nm :: publicScope)) = sendingBody := owners.2
  cases impossible

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryControls
