import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryDelivery

/-!
# Administrative rho phases preserve the source readout

Server installation, stored-code restoration and allocator work use the
actual COMM contractums. They preserve the source process modulo its own
parallel equations. An arbitrary frame and every duplicate occurrence are
retained. Server restoration requires the same stored handler template;
the inventory proves that condition for actual matching image occurrences.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministration

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive
open RhoUnaryPhase RhoUnaryReindex
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

theorem source_admin_prefix {Γ : Ctx sig} (administration frame : List (Activity Γ))
    (noSource : ∀ activity ∈ administration, activity.source = nil) :
    StructuralEq (source (administration ++ frame)) (source frame) := by
  induction administration with
  | nil => exact .refl _
  | cons activity rest ih =>
      have empty := noSource activity (by simp)
      have after := ih (fun other member => noSource other (by simp [member]))
      change StructuralEq (par activity.source (source (rest ++ frame))) (source frame)
      rw [empty]
      exact .trans (.par (.refl _) after) (.trans (.parComm _ _) (.parUnit _))

theorem source_admin_replace {Γ : Ctx sig} (first second frame : List (Activity Γ))
    (firstEmpty : ∀ activity ∈ first, activity.source = nil)
    (secondEmpty : ∀ activity ∈ second, activity.source = nil) :
    StructuralEq (source (first ++ frame)) (source (second ++ frame)) :=
  .trans (source_admin_prefix first frame firstEmpty)
    (.symm (source_admin_prefix second frame secondEmpty))

theorem install_delivery {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (world : World Γ 0) (seed : Nat) (frame : List (Activity Γ)) :
    StructuralEq (source (.install channel body guarded :: .reply seed :: frame))
        (source (.ready channel body guarded seed :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (installBody channel guarded world).term (seedCode seed) ::
            (headers world frame).map Header.pattern))
        (actual world (.ready channel body guarded seed :: frame)) := by
  constructor
  · change StructuralEq (par (rep (inp1 (.var channel) body)) (par nil (source frame)))
      (par (rep (inp1 (.var channel) body)) (source frame))
    exact .par (.refl _) (.trans (.parComm _ _) (.parUnit _))
  · rw [install_received channel guarded world seed]
    exact .refl _

theorem persistent_rearm {Γ : Ctx sig} (channel : Var Γ .nm)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (world : World Γ 0) (self : Nat) (frame : List (Activity Γ)) :
    StructuralEq (source (.rearm channel body guarded self :: .sendCode channel body guarded self :: frame))
        (source (.ready channel body guarded self :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst
            (GuardedReplication.body (allocatedName self) (world channel).term (ordinary guarded world).term)
            (stored channel guarded world self) :: (headers world frame).map Header.pattern))
        (actual world (.ready channel body guarded self :: frame)) := by
  constructor
  · change StructuralEq (par (rep (inp1 (.var channel) body)) (par nil (source frame)))
      (par (rep (inp1 (.var channel) body)) (source frame))
    exact .par (.refl _) (.trans (.parComm _ _) (.parUnit _))
  · rw [persistent_rearmed channel guarded world self]
    exact .refl _

theorem allocator_request {Γ : Ctx sig} (world : World Γ 0) (frame : List (Activity Γ)) :
    StructuralEq (source (.allocatorReady :: .request :: frame))
        (source (.allocatorSendCode :: .allocatorRearm :: .seedInput :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst
            (RhoScopedServers.parallel [send allocatorSelf.term
              (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term),
              GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term,
              (allocationHandler allocatorState).term])
            (NameValue.reserved Reserved.reply : NameValue 0).payload ::
              (headers world frame).map Header.pattern))
        (actual world (.allocatorSendCode :: .allocatorRearm :: .seedInput :: frame)) := by
  constructor
  · exact source_admin_replace [.allocatorReady, .request]
      [.allocatorSendCode, .allocatorRearm, .seedInput] frame (by simp [Activity.source])
        (by simp [Activity.source])
  · rw [allocator_received world]
    exact Context.par_flatten_head _ _

theorem allocator_rearm {Γ : Ctx sig} (world : World Γ 0) (frame : List (Activity Γ)) :
    StructuralEq (source (.allocatorRearm :: .allocatorSendCode :: frame))
        (source (.allocatorReady :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst
            (GuardedReplication.body allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term)
            (GuardedReplication.code allocatorSelf.term allocatorRequest.term (allocationHandler allocatorState).term) ::
              (headers world frame).map Header.pattern))
        (actual world (.allocatorReady :: frame)) := by
  constructor
  · exact source_admin_replace [.allocatorRearm, .allocatorSendCode]
      [.allocatorReady] frame (by simp [Activity.source]) (by simp [Activity.source])
  · rw [allocator_rearmed world]
    exact .refl _

theorem token_transfer {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ)) :
    StructuralEq (source (.seedInput :: .token world.available :: frame))
        (source (.reply world.available :: .token (world.available + 1) :: frame)) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst
            (RhoScopedServers.parallel [send (.apply "NQuote" [.apply "PDrop" [allocatorReply.term]]) (drop 0),
              send allocatorState.term (send (.bvar 0) RhoScopedAllocation.zero)])
            (seedCode world.available) :: (headers world.world frame).map Header.pattern))
        (actual world.advance.world (.reply world.available :: .token (world.available + 1) :: frame)) := by
  constructor
  · exact source_admin_replace [.seedInput, .token world.available]
      [.reply world.available, .token (world.available + 1)] frame
        (by simp [Activity.source]) (by simp [Activity.source])
  · rw [token_received world.world world.available, SeedWorld.advance_world]
    exact Context.par_flatten_head _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministration
