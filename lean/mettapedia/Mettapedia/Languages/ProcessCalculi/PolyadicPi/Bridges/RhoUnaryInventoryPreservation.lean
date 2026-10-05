import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventory
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReindex

/-!
# Preservation of the concrete implementation inventory

These lemmas read the actual phase replacement lists. They preserve the
allocator token, distinct issued replies and persistent-owner incidence.
Actual core firing and substitution are proved separately by the phase
inversion and endpoint modules; no scheduler is part of the inventory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryPreservation

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryInventory
open RhoUnaryImage

@[simp] theorem clientCount_cons {Γ : Ctx sig} (activity : Activity Γ)
    (activities : List (Activity Γ)) :
    clientCount (activity :: activities) = pendingWeight activity + clientCount activities := rfl

@[simp] theorem requestCount_cons {Γ : Ctx sig} (activity : Activity Γ)
    (activities : List (Activity Γ)) :
    requestCount (activity :: activities) = requestWeight activity + requestCount activities := rfl

@[simp] theorem clientCount_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    clientCount (first ++ second) = clientCount first + clientCount second := by
  simp [clientCount, List.sum_append]

@[simp] theorem requestCount_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    requestCount (first ++ second) = requestCount first + requestCount second := by
  simp [requestCount, List.sum_append]

/-- Activating a supplied balanced compiler image contributes no live
implementation names, replies or allocator token of its own. -/
theorem initial_prefix {Γ : Ctx sig} {world : SeedWorld Γ}
    {added frame : List (Activity Γ)}
    (initial : ∀ activity ∈ added, Initial activity)
    (balanced : clientCount added = requestCount added)
    (inventory : Inventory world frame) : Inventory world (added ++ frame) := by
  obtain ⟨noListeners, noRearms, noCodes, noReplies, noTokens,
    noSeedInputs, noAllocator, noRearm, noCode⟩ := initial_extractions initial
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [tokens_append, noTokens, List.nil_append] using inventory.token_unique
  · simpa only [listeners_append, noListeners, List.nil_append] using inventory.owner_unique
  · simpa only [rearms_append, noRearms, codes_append, noCodes, List.nil_append] using inventory.rearm_code
  · simpa only [listeners_append, noListeners, List.nil_append] using inventory.owner_below
  · simpa only [listeners_append, noListeners, List.nil_append] using inventory.owner_fresh
  · simpa only [replies_append, noReplies, List.nil_append] using inventory.reply_unique
  · simpa only [replies_append, noReplies, List.nil_append] using inventory.reply_below
  · simpa only [replies_append, noReplies, List.nil_append] using inventory.reply_fresh
  · simpa only [replies_append, noReplies, listeners_append, noListeners, List.nil_append]
      using inventory.reply_owner
  · simpa only [count_append, noAllocator, noRearm, Nat.zero_add] using inventory.allocator_phase
  · simpa only [count_append, noCode, noRearm, Nat.zero_add] using inventory.allocator_code
  · rw [clientCount_append, requestCount_append, count_append, replies_append,
      noReplies, List.nil_append, noSeedInputs, Nat.zero_add, balanced]
    have pending := inventory.pending_balance
    omega

/-- Consuming an ordinary source input and output removes no allocator or
server ownership. The subsequently activated body is handled by initial_prefix. -/
theorem ordinary_remove {Γ : Ctx sig} {world : SeedWorld Γ}
    (channel datum : Var Γ .nm) {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body)
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.input channel body guarded :: .output channel datum :: frame)) :
    Inventory world frame := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
      replies, replySeed, List.filterMap_cons, count_cons, contribution,
      clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add] at *
  all_goals assumption

/-- A persistent source communication retains its exact owner in the
rearming listener and stored-code output. -/
theorem persistent_release {Γ : Ctx sig} {world : SeedWorld Γ}
    (channel datum : Var Γ .nm) {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (self : Nat) {frame : List (Activity Γ)}
    (inventory : Inventory world (.ready channel body guarded self :: .output channel datum :: frame)) :
    Inventory world (.sendCode channel body guarded self :: .rearm channel body guarded self :: frame) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
      replies, replySeed, List.filterMap_cons, List.map_cons, count_cons, contribution,
      clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add] at *
  all_goals first | assumption | exact code.cons _

/-- Coherent stored-code receipt restores the same listener. -/
theorem persistent_rearm {Γ : Ctx sig} {world : SeedWorld Γ}
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (self : Nat) {frame : List (Activity Γ)}
    (inventory : Inventory world (.rearm channel body guarded self :: .sendCode channel body guarded self :: frame)) :
    Inventory world (.ready channel body guarded self :: frame) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
      replies, replySeed, List.filterMap_cons, List.map_cons, count_cons, contribution,
      clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add] at *
  all_goals first | assumption | exact code.cons_inv

/-- A delivered seed can become a server's self channel because the
issued-reply invariant excludes every source name and earlier owner. -/
theorem install_reply {Γ : Ctx sig} {world : SeedWorld Γ}
    (channel : Var Γ .nm) {body : Proc (.nm :: Γ)}
    (guarded : GuardedUnary body) (seed : Nat) {frame : List (Activity Γ)}
    (inventory : Inventory world (.install channel body guarded :: .reply seed :: frame)) :
    Inventory world (.ready channel body guarded seed :: frame) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
      replies, replySeed, List.filterMap_cons, List.map_cons, count_cons, contribution,
      clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add,
      List.length_cons] at *
  · exact token
  · apply List.nodup_cons.mpr
    refine ⟨?_, ownerUnique⟩
    intro member
    obtain ⟨owner, ownerMember, same⟩ := List.mem_map.mp member
    exact replyOwner seed (List.mem_cons_self) owner ownerMember same.symm
  · exact code
  · intro owner member
    rcases List.mem_cons.mp member with rfl | old
    · exact replyBound seed (List.mem_cons_self)
    · exact ownerBound owner old
  · intro owner member name
    rcases List.mem_cons.mp member with rfl | old
    · exact replyFresh seed (List.mem_cons_self) name
    · exact ownerFresh owner old name
  · exact replyUnique.of_cons
  · intro other member
    exact replyBound other (List.mem_cons_of_mem seed member)
  · intro other member name
    exact replyFresh other (List.mem_cons_of_mem seed member) name
  · intro other member owner ownerMember
    rcases List.mem_cons.mp ownerMember with rfl | old
    · have different := (List.nodup_cons.mp replyUnique).1
      intro same
      change other = seed at same
      subst other
      exact different member
    · exact replyOwner other (List.mem_cons_of_mem seed member) owner old
  · exact allocator
  · exact allocatorCode
  · omega

/-- Starting an allocator request replaces its one request occurrence by
one waiting seed receiver and temporarily rearming allocator code. -/
theorem allocator_request {Γ : Ctx sig} {world : SeedWorld Γ}
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.allocatorReady :: .request :: frame)) :
    Inventory world (.allocatorSendCode :: .allocatorRearm :: .seedInput :: frame) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
    replies, replySeed, List.filterMap_cons, count_cons, contribution,
    clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add] at *
  all_goals first | assumption | omega

/-- Code rearming restores the one ready allocator without issuing a seed. -/
theorem allocator_rearm {Γ : Ctx sig} {world : SeedWorld Γ}
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.allocatorRearm :: .allocatorSendCode :: frame)) :
    Inventory world (.allocatorReady :: frame) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
    replies, replySeed, List.filterMap_cons, count_cons, contribution,
    clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add] at *
  all_goals first | assumption | omega

/-- Issuing the current seed advances the actual cursor. The new reply
cannot duplicate any live reply or installed implementation owner. -/
theorem issue_seed {Γ : Ctx sig} {world : SeedWorld Γ}
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.seedInput :: .token world.available :: frame)) :
    Inventory world.advance (.reply world.available :: .token (world.available + 1) :: frame) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  constructor <;>
    simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
    replies, replySeed, List.filterMap_cons,
    count_cons, contribution, clientCount_cons, requestCount_cons,
    pendingWeight, requestWeight, Nat.zero_add, List.cons.injEq,
    List.length_cons] at *
  · simp [token, SeedWorld.advance]
  · exact ownerUnique
  · exact code
  · intro owner member
    have bound := ownerBound owner member
    change owner.self < world.available + 1
    omega
  · exact ownerFresh
  · apply List.nodup_cons.mpr
    refine ⟨?_, replyUnique⟩
    intro member
    have bound := replyBound world.available member
    omega
  · intro seed member
    rcases List.mem_cons.mp member with rfl | old
    · change world.available < world.available + 1
      omega
    · have bound := replyBound seed old
      change seed < world.available + 1
      omega
  · intro seed member name
    rcases List.mem_cons.mp member with rfl | old
    · have bound := world.below name
      change world.available ≠ world.index name
      omega
    · exact replyFresh seed old name
  · intro seed member owner ownerMember
    rcases List.mem_cons.mp member with rfl | old
    · have bound := ownerBound owner ownerMember
      omega
    · exact replyOwner seed old owner ownerMember
  · exact allocator
  · exact allocatorCode
  · omega

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryPreservation
