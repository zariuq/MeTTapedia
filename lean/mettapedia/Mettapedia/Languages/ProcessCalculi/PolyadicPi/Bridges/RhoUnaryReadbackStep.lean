import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryOccurrence
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCommitment
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryAdministration
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryPreservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryScope

/-!
# Exact source readback of selected concrete core-rho firings

The matcher supplies the input and output occurrences. Their concrete phase
contractum has another compiler image with its complete inventory. Public
communication advances the source by one real pi step; implementation work
preserves it by structural equations. A delivered private name extends the
source telescope while preserving every old source-name interpretation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadbackStep

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive
open RhoUnaryImage RhoUnaryInventory RhoUnaryPairInversion RhoUnaryOccurrence RhoUnaryCredit
open ScopedActiveFrontier
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedServers RhoScopedAllocation

/-- The supplied rho endpoint is retained. Scope records only newly opened
source restrictions; implementation names remain in the concrete inventory. -/
structure Result {Γ : Ctx sig} (beforeWorld : SeedWorld Γ)
    (before : List (Activity Γ)) (target : Pattern) where
  context : Ctx sig
  scope : Scope Γ context
  world : SeedWorld context
  activities : List (Activity context)
  inventory : Inventory world activities
  names : ∀ name, world.index (scope.inclusion .nm name) = beforeWorld.index name
  cursor : beforeWorld.available ≤ world.available
  charge : Nat
  credit : total activities + 1 = total before + charge
  status : (charge = 0 ∧ StructuralEq (RhoUnaryActive.source before)
      (scope.close (RhoUnaryActive.source activities))) ∨
    (0 < charge ∧ StepModulo (RhoUnaryActive.source before)
      (scope.close (RhoUnaryActive.source activities)))
  endpoint : StructuralCongruence target (actual world.world activities)

/-- Forget the accounting distinction while retaining its real source law. -/
theorem Result.source {Γ : Ctx sig} {world : SeedWorld Γ} {before : List (Activity Γ)}
    {target : Pattern} (result : Result world before target) :
    StructuralEq (RhoUnaryActive.source before) (result.scope.close (RhoUnaryActive.source result.activities)) ∨
      StepModulo (RhoUnaryActive.source before) (result.scope.close (RhoUnaryActive.source result.activities)) :=
  result.status.elim (fun unchanged => .inl unchanged.2) (fun advanced => .inr advanced.2)

private def unchanged {Γ : Ctx sig} {world : SeedWorld Γ}
    {before after : List (Activity Γ)} {target : Pattern}
    (inventory : Inventory world after)
    (source : StructuralEq (RhoUnaryActive.source before) (RhoUnaryActive.source after))
    (credited : total after + 1 = total before)
    (endpoint : StructuralCongruence target (actual world.world after)) :
    Result world before target :=
  ⟨Γ, .nil, world, after, inventory, fun _ => rfl, Nat.le_refl _,
    0, by simpa using credited, .inl ⟨rfl, source⟩, endpoint⟩

private def committed {Γ : Ctx sig} {world : SeedWorld Γ}
    {before after : List (Activity Γ)} {target : Pattern} (charge : Nat)
    (positive : 0 < charge) (inventory : Inventory world after)
    (source : StepModulo (RhoUnaryActive.source before) (RhoUnaryActive.source after))
    (credited : total after + 1 = total before + charge)
    (endpoint : StructuralCongruence target (actual world.world after)) :
    Result world before target :=
  ⟨Γ, .nil, world, after, inventory, fun _ => rfl, Nat.le_refl _,
    charge, credited, .inr ⟨positive, source⟩, endpoint⟩

/-- The public firing commits the supplied ordinary source communication. -/
theorem ordinary_public {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel datum : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (frame : List (Activity Γ))
    (inventory : Inventory world (.input channel body guarded :: .output channel datum :: frame)) :
    ∃ result : Result world (.input channel body guarded :: .output channel datum :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (ordinary guarded world.world).term (world.world datum).payload ::
          (headers world.world frame).map Header.pattern)),
      0 < result.charge ∧ StructuralEq (result.scope.close (source result.activities))
        (par (inst body (.var datum)) (source frame)) := by
  obtain ⟨image, initial, sourceStep, targetEq, balanced, credited, sourceAfter⟩ :=
    RhoUnaryCommitment.ordinary_commitment_exact channel datum guarded world frame
  have remainder := RhoUnaryInventoryPreservation.ordinary_remove channel datum guarded inventory
  refine ⟨committed (after := image ++ frame) (work (inst body (.var datum)) + 1) (by omega)
    (RhoUnaryInventoryPreservation.initial_prefix initial balanced remainder) sourceStep ?_ targetEq,
    ?_, ?_⟩
  · simp only [total_append, total_cons, credit]
    rw [credited]
    omega
  · change 0 < work (inst body (.var datum)) + 1
    omega
  · exact sourceAfter

/-- Persistent receipt commits now; the same owner survives while rearming. -/
theorem persistent_public {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel datum : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (self : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world (.ready channel body guarded self :: .output channel datum :: frame)) :
    ∃ result : Result world (.ready channel body guarded self :: .output channel datum :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload ::
          (headers world.world frame).map Header.pattern)),
      0 < result.charge ∧ StructuralEq (result.scope.close (source result.activities))
        (par (inst body (.var datum)) (par (rep (inp1 (.var channel) body)) (source frame))) := by
  obtain ⟨image, initial, sourceStep, targetEq, balanced, credited, sourceAfter⟩ :=
    RhoUnaryCommitment.persistent_commitment_exact channel datum guarded world self frame
  have remainder := RhoUnaryInventoryPreservation.persistent_release channel datum guarded self inventory
  refine ⟨committed (after := image ++ .sendCode channel body guarded self :: .rearm channel body guarded self :: frame)
    (work (inst body (.var datum)) + 2) (by omega)
    (RhoUnaryInventoryPreservation.initial_prefix initial balanced remainder) sourceStep ?_ targetEq,
    ?_, ?_⟩
  · simp only [total_append, total_cons, credit]
    rw [credited]
    omega
  · change 0 < work (inst body (.var datum)) + 2
    omega
  · exact sourceAfter

/-- The previous existence API projects the same supplied ordinary receipt. -/
theorem ordinary {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel datum : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (frame : List (Activity Γ))
    (inventory : Inventory world (.input channel body guarded :: .output channel datum :: frame)) :
    Nonempty (Result world (.input channel body guarded :: .output channel datum :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (RhoUnaryActive.ordinary guarded world.world).term (world.world datum).payload ::
          (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _, _⟩ := ordinary_public world channel datum guarded frame inventory
  exact ⟨result⟩

theorem persistent {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel datum : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (self : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world (.ready channel body guarded self :: .output channel datum :: frame)) :
    Nonempty (Result world (.ready channel body guarded self :: .output channel datum :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (readyBody channel guarded world.world self) (world.world datum).payload ::
          (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _, _⟩ := persistent_public world channel datum guarded self frame inventory
  exact ⟨result⟩

/-- Installing a source server consumes this delivered implementation name. -/
theorem install_administrative {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (seed : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world (.install channel body guarded :: .reply seed :: frame)) :
    ∃ result : Result world (.install channel body guarded :: .reply seed :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (installBody channel guarded world.world).term (seedCode seed) ::
          (headers world.world frame).map Header.pattern)), result.charge = 0 := by
  obtain ⟨sourceEq, targetEq⟩ :=
    RhoUnaryAdministration.install_delivery channel guarded world.world seed frame
  refine ⟨unchanged (RhoUnaryInventoryPreservation.install_reply channel guarded seed inventory)
    sourceEq ?_ targetEq, rfl⟩
  simp only [total_cons, credit]
  omega

/-- Rearming uses the same actual stored handler and preserves the source. -/
theorem rearm_administrative {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (self : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world
      (.rearm channel body guarded self :: .sendCode channel body guarded self :: frame)) :
    ∃ result : Result world
      (.rearm channel body guarded self :: .sendCode channel body guarded self :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst
          (GuardedReplication.body (allocatedName self) (world.world channel).term
            (RhoUnaryActive.ordinary guarded world.world).term)
          (stored channel guarded world.world self) :: (headers world.world frame).map Header.pattern)),
      result.charge = 0 := by
  obtain ⟨sourceEq, targetEq⟩ :=
    RhoUnaryAdministration.persistent_rearm channel guarded world.world self frame
  refine ⟨unchanged (RhoUnaryInventoryPreservation.persistent_rearm channel guarded self inventory)
    sourceEq ?_ targetEq, rfl⟩
  simp only [total_cons, credit]
  omega

/-- Starting a request is an actual allocator COMM, administrative to pi. -/
theorem allocator_request_administrative {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ))
    (inventory : Inventory world (.allocatorReady :: .request :: frame)) :
    ∃ result : Result world (.allocatorReady :: .request :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst ((Activity.allocatorReady : Activity Γ).header world.world).content
          ((Activity.request : Activity Γ).header world.world).content ::
            (headers world.world frame).map Header.pattern)), result.charge = 0 := by
  obtain ⟨sourceEq, targetEq⟩ := RhoUnaryAdministration.allocator_request world.world frame
  refine ⟨unchanged (RhoUnaryInventoryPreservation.allocator_request inventory)
    sourceEq ?_ targetEq, rfl⟩
  simp only [total_cons, credit]
  omega

/-- The allocator's code receipt restores its original request guard. -/
theorem allocator_rearm_administrative {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ))
    (inventory : Inventory world (.allocatorRearm :: .allocatorSendCode :: frame)) :
    ∃ result : Result world (.allocatorRearm :: .allocatorSendCode :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst ((Activity.allocatorRearm : Activity Γ).header world.world).content
          ((Activity.allocatorSendCode : Activity Γ).header world.world).content ::
            (headers world.world frame).map Header.pattern)), result.charge = 0 := by
  obtain ⟨sourceEq, targetEq⟩ := RhoUnaryAdministration.allocator_rearm world.world frame
  refine ⟨unchanged (RhoUnaryInventoryPreservation.allocator_rearm inventory)
    sourceEq ?_ targetEq, rfl⟩
  simp only [total_cons, credit]
  omega

/-- Consuming the unique live token issues its old seed and advances it. -/
theorem token_administrative {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ))
    (inventory : Inventory world (.seedInput :: .token world.available :: frame)) :
    ∃ result : Result world (.seedInput :: .token world.available :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst ((Activity.seedInput : Activity Γ).header world.world).content
          ((Activity.token world.available : Activity Γ).header world.world).content ::
            (headers world.world frame).map Header.pattern)), result.charge = 0 := by
  obtain ⟨sourceEq, targetEq⟩ := RhoUnaryAdministration.token_transfer world frame
  refine ⟨⟨Γ, .nil, world.advance,
    .reply world.available :: .token (world.available + 1) :: frame,
    RhoUnaryInventoryPreservation.issue_seed inventory, fun _ => rfl,
    Nat.le_succ _, 0, ?_, .inl ⟨rfl, sourceEq⟩, targetEq⟩, rfl⟩
  simp only [total_cons, credit]
  omega

/-- The delivered name extends the actual receiving source binder. -/
theorem private_scope_administrative {Γ : Ctx sig} (world : SeedWorld Γ)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (seed : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world (.privateScope body guarded :: .reply seed :: frame)) :
    ∃ result : Result world (.privateScope body guarded :: .reply seed :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (RhoUnaryActive.ordinary guarded world.world).term (seedCode seed) ::
          (headers world.world frame).map Header.pattern)), result.charge = 0 := by
  obtain ⟨returned, fresh⟩ := RhoUnaryInventoryScope.private_reply_facts guarded seed inventory
  obtain ⟨image, initial, sourceEq, targetEq, balanced, credited⟩ :=
    RhoUnaryDelivery.private_delivery_accounted guarded world seed returned fresh frame
  refine ⟨⟨.nm :: Γ, .bind .nil, world.extendAt seed returned fresh,
    image ++ frame.map (Activity.rename (fun _ name => Var.succ name)),
    RhoUnaryInventoryScope.delivered_prefix guarded seed returned fresh inventory initial balanced,
    fun _ => rfl, Nat.le_refl _, 0, ?_, .inl ⟨rfl, sourceEq⟩, targetEq⟩, rfl⟩
  simp only [total_append, total_cons, credit, total_rename]
  rw [credited]
  omega

/-- Forget the administrative charge while retaining the supplied phase result. -/
theorem install {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (seed : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world (.install channel body guarded :: .reply seed :: frame)) :
    Nonempty (Result world (.install channel body guarded :: .reply seed :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (installBody channel guarded world.world).term (seedCode seed) ::
          (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _⟩ := install_administrative world channel guarded seed frame inventory
  exact ⟨result⟩

theorem rearm {Γ : Ctx sig} (world : SeedWorld Γ)
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (self : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world
      (.rearm channel body guarded self :: .sendCode channel body guarded self :: frame)) :
    Nonempty (Result world
      (.rearm channel body guarded self :: .sendCode channel body guarded self :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst
          (GuardedReplication.body (allocatedName self) (world.world channel).term
            (RhoUnaryActive.ordinary guarded world.world).term)
          (stored channel guarded world.world self) :: (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _⟩ := rearm_administrative world channel guarded self frame inventory
  exact ⟨result⟩

theorem allocator_request {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ))
    (inventory : Inventory world (.allocatorReady :: .request :: frame)) :
    Nonempty (Result world (.allocatorReady :: .request :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst ((Activity.allocatorReady : Activity Γ).header world.world).content
          ((Activity.request : Activity Γ).header world.world).content ::
            (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _⟩ := allocator_request_administrative world frame inventory
  exact ⟨result⟩

theorem allocator_rearm {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ))
    (inventory : Inventory world (.allocatorRearm :: .allocatorSendCode :: frame)) :
    Nonempty (Result world (.allocatorRearm :: .allocatorSendCode :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst ((Activity.allocatorRearm : Activity Γ).header world.world).content
          ((Activity.allocatorSendCode : Activity Γ).header world.world).content ::
            (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _⟩ := allocator_rearm_administrative world frame inventory
  exact ⟨result⟩

theorem token {Γ : Ctx sig} (world : SeedWorld Γ) (frame : List (Activity Γ))
    (inventory : Inventory world (.seedInput :: .token world.available :: frame)) :
    Nonempty (Result world (.seedInput :: .token world.available :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst ((Activity.seedInput : Activity Γ).header world.world).content
          ((Activity.token world.available : Activity Γ).header world.world).content ::
            (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _⟩ := token_administrative world frame inventory
  exact ⟨result⟩

theorem private_scope {Γ : Ctx sig} (world : SeedWorld Γ)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    (seed : Nat) (frame : List (Activity Γ))
    (inventory : Inventory world (.privateScope body guarded :: .reply seed :: frame)) :
    Nonempty (Result world (.privateScope body guarded :: .reply seed :: frame)
      (RhoScopedServers.parallel
        (semanticCommSubst (RhoUnaryActive.ordinary guarded world.world).term (seedCode seed) ::
          (headers world.world frame).map Header.pattern))) := by
  obtain ⟨result, _⟩ := private_scope_administrative world guarded seed frame inventory
  exact ⟨result⟩

/-- The actual semantic COMM contractum at the supplied activity pair. -/
noncomputable def contractum {Γ : Ctx sig} (world : SeedWorld Γ)
    (input output : Activity Γ) (frame : List (Activity Γ)) : Pattern :=
  RhoScopedServers.parallel
    (semanticCommSubst (input.header world.world).content (output.header world.world).content ::
      (headers world.world frame).map Header.pattern)

/-- Every matcher-classified pair has another valid actual implementation
image. Rearming metadata is recovered from concrete owner incidence. -/
theorem pair {Γ : Ctx sig} (world : SeedWorld Γ) (input output : Activity Γ)
    (frame : List (Activity Γ)) (classified : Pair input output)
    (inventory : Inventory world (input :: output :: frame)) :
    Nonempty (Result world (input :: output :: frame) (contractum world input output frame)) := by
  cases classified with
  | ordinary channel datum body guarded =>
      simpa only [contractum, Activity.header, Header.content] using
        ordinary world channel datum guarded frame inventory
  | persistent channel datum body guarded self =>
      simpa only [contractum, Activity.header, Header.content] using
        persistent world channel datum guarded self frame inventory
  | privateScope body guarded seed =>
      simpa only [contractum, Activity.header, Header.content] using
        private_scope world guarded seed frame inventory
  | install channel body guarded seed =>
      simpa only [contractum, Activity.header, Header.content] using
        install world channel guarded seed frame inventory
  | rearm channel suppliedChannel body suppliedBody guarded suppliedGuarded self =>
      have same := inventory.rearm_owner channel suppliedChannel body suppliedBody guarded suppliedGuarded self
        (by simp) (by simp)
      cases same.1
      cases same.2
      simpa only [contractum, Activity.header, Header.content] using
        rearm world channel guarded self frame inventory
  | allocatorRequest => exact allocator_request world frame inventory
  | allocatorRearm => exact allocator_rearm world frame inventory
  | token seed =>
      have member : seed ∈ tokens (.seedInput :: .token seed :: frame) := by
        simp [tokens, tokenSeed]
      rw [inventory.token_unique] at member
      have same : seed = world.available := by simpa using member
      subst seed
      exact token world frame inventory

private theorem source_step_precompose {Γ : Ctx sig} {before middle after : Proc Γ}
    (equal : StructuralEq before middle) (step : StepModulo middle after) : StepModulo before after := by
  obtain ⟨source, target, beforeEq, firing, afterEq⟩ := step
  exact ⟨source, target, .trans equal beforeEq, firing, afterEq⟩

/-- Re-exposing the selected source occurrences changes no endpoint or world. -/
def Result.precompose {Γ : Ctx sig} {world : SeedWorld Γ}
    {before exposed : List (Activity Γ)} {target : Pattern}
    (result : Result world exposed target)
    (equal : StructuralEq (RhoUnaryActive.source before) (RhoUnaryActive.source exposed))
    (credited : total before = total exposed) : Result world before target :=
  { result with
    credit := by rw [credited]; exact result.credit
    status := (result.status.elim
      (fun unchanged => .inl ⟨unchanged.1, .trans equal unchanged.2⟩)
      (fun firing => .inr ⟨firing.1, source_step_precompose equal firing.2⟩)) }

/-- A supplied original-occurrence selection reflects its own contractum,
with every duplicate frame occurrence and nominal interpretation retained. -/
theorem selection {Γ : Ctx sig} (world : SeedWorld Γ) (activities : List (Activity Γ))
    (inventory : Inventory world activities)
    (selected : Selection (headers world.world activities)) :
    Nonempty (Result world activities selected.contractum) := by
  have classified : Pair (input selected) (output selected) :=
    selected_pair world activities inventory.ports_fresh selected
  have exposedInventory := inventory.perm (permutation selected)
  obtain ⟨result⟩ := pair world (input selected) (output selected) (residue selected)
    classified exposedInventory
  have endpoint : selected.contractum =
      contractum world (input selected) (output selected) (residue selected) :=
    contractum_content selected
  rw [← endpoint] at result
  exact ⟨result.precompose (source_permutation selected) (total_perm (permutation selected))⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadbackStep
