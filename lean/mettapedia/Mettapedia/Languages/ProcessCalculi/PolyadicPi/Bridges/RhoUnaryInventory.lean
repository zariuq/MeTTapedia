import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryRoles
import Mathlib.Data.List.Nodup

/-!
# Occurrence inventory of the concrete unary compiler

The inventory reads the actual active-list constructors. It records the one
allocator token, issued but undelivered replies, and persistent-server owners.
Each rearming listener has exactly its own stored-code message; duplicate
source messages are unaffected. The conditions are invariant under list
permutation and exclude cross-owner communication through an implementation
channel. They do not define or assume a target transition relation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventory

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryWorld RhoUnaryActive RhoUnaryRoles

/-- The owner keeps the actual source listener, not just its private channel. -/
structure Owner (Γ : Ctx sig) where
  self : Nat
  channel : Var Γ .nm
  body : Proc (.nm :: Γ)

def listener {Γ : Ctx sig} : Activity Γ → Option (Owner Γ)
  | .ready channel body _ self | .rearm channel body _ self => some ⟨self, channel, body⟩
  | _ => none

def rearming {Γ : Ctx sig} : Activity Γ → Option (Owner Γ)
  | .rearm channel body _ self => some ⟨self, channel, body⟩
  | _ => none

def storedCode {Γ : Ctx sig} : Activity Γ → Option (Owner Γ)
  | .sendCode channel body _ self => some ⟨self, channel, body⟩
  | _ => none

def replySeed {Γ : Ctx sig} : Activity Γ → Option Nat
  | .reply seed => some seed
  | _ => none

def tokenSeed {Γ : Ctx sig} : Activity Γ → Option Nat
  | .token seed => some seed
  | _ => none

inductive CountKind where
  | seedInput | allocatorReady | allocatorRearm | allocatorSendCode
  deriving DecidableEq

def contribution {Γ : Ctx sig} : CountKind → Activity Γ → Nat
  | .seedInput, .seedInput | .allocatorReady, .allocatorReady |
    .allocatorRearm, .allocatorRearm | .allocatorSendCode, .allocatorSendCode => 1
  | _, _ => 0

def count {Γ : Ctx sig} (kind : CountKind) (activities : List (Activity Γ)) : Nat :=
  (activities.map (contribution kind)).sum

@[simp] theorem count_nil {Γ : Ctx sig} (kind : CountKind) :
    count kind ([] : List (Activity Γ)) = 0 := rfl

@[simp] theorem count_cons {Γ : Ctx sig} (kind : CountKind) (activity : Activity Γ)
    (activities : List (Activity Γ)) :
    count kind (activity :: activities) = contribution kind activity + count kind activities := rfl

@[simp] theorem count_append {Γ : Ctx sig} (kind : CountKind)
    (first second : List (Activity Γ)) :
    count kind (first ++ second) = count kind first + count kind second := by
  simp [count, List.sum_append]

theorem count_perm {Γ : Ctx sig} (kind : CountKind)
    {first second : List (Activity Γ)} (permutation : first.Perm second) :
    count kind first = count kind second :=
  (permutation.map (contribution kind)).sum_eq

def listeners {Γ : Ctx sig} (activities : List (Activity Γ)) : List (Owner Γ) :=
  activities.filterMap listener

def rearms {Γ : Ctx sig} (activities : List (Activity Γ)) : List (Owner Γ) :=
  activities.filterMap rearming

def codes {Γ : Ctx sig} (activities : List (Activity Γ)) : List (Owner Γ) :=
  activities.filterMap storedCode

def replies {Γ : Ctx sig} (activities : List (Activity Γ)) : List Nat :=
  activities.filterMap replySeed

def tokens {Γ : Ctx sig} (activities : List (Activity Γ)) : List Nat :=
  activities.filterMap tokenSeed

@[simp] theorem listeners_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    listeners (first ++ second) = listeners first ++ listeners second := List.filterMap_append

@[simp] theorem rearms_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    rearms (first ++ second) = rearms first ++ rearms second := List.filterMap_append

@[simp] theorem codes_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    codes (first ++ second) = codes first ++ codes second := List.filterMap_append

@[simp] theorem replies_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    replies (first ++ second) = replies first ++ replies second := List.filterMap_append

@[simp] theorem tokens_append {Γ : Ctx sig} (first second : List (Activity Γ)) :
    tokens (first ++ second) = tokens first ++ tokens second := List.filterMap_append

theorem rearm_mem_listener {Γ : Ctx sig} {activities : List (Activity Γ)}
    {owner : Owner Γ} (member : owner ∈ rearms activities) : owner ∈ listeners activities := by
  obtain ⟨activity, member, same⟩ := List.mem_filterMap.mp member
  apply List.mem_filterMap.mpr
  refine ⟨activity, member, ?_⟩
  cases activity <;> simp_all [rearming, listener]

/-- All components are read from concrete occurrences. The token is linear,
and a reply is not assigned to a client until the actual receipt occurs. -/
structure Inventory {Γ : Ctx sig} (world : SeedWorld Γ) (activities : List (Activity Γ)) : Prop where
  token_unique : tokens activities = [world.available]
  owner_unique : ((listeners activities).map Owner.self).Nodup
  rearm_code : (rearms activities).Perm (codes activities)
  owner_below : ∀ owner ∈ listeners activities, owner.self < world.available
  owner_fresh : ∀ owner ∈ listeners activities, ∀ name, owner.self ≠ world.index name
  reply_unique : (replies activities).Nodup
  reply_below : ∀ seed ∈ replies activities, seed < world.available
  reply_fresh : ∀ seed ∈ replies activities, ∀ name, seed ≠ world.index name
  reply_owner : ∀ seed ∈ replies activities, ∀ owner ∈ listeners activities, seed ≠ owner.self
  allocator_phase : count .allocatorReady activities + count .allocatorRearm activities = 1
  allocator_code : count .allocatorSendCode activities = count .allocatorRearm activities
  pending_balance : RhoUnaryImage.clientCount activities =
    RhoUnaryImage.requestCount activities + count .seedInput activities + (replies activities).length

theorem Inventory.code_mem_listener {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    {owner : Owner Γ} (member : owner ∈ codes activities) : owner ∈ listeners activities :=
  rearm_mem_listener (inventory.rearm_code.mem_iff.mpr member)

/-- Actual self-channel matches cannot combine different stored handlers. -/
theorem Inventory.owner_coherent {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    {first second : Owner Γ} (firstMember : first ∈ listeners activities)
    (secondMember : second ∈ listeners activities) (same : first.self = second.self) :
    first = second := by
  exact List.inj_on_of_nodup_map inventory.owner_unique firstMember secondMember same

theorem Inventory.rearm_owner {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities)
    (channel suppliedChannel : Var Γ .nm) (body suppliedBody : Proc (.nm :: Γ))
    (guarded : GuardedUnary body) (suppliedGuarded : GuardedUnary suppliedBody) (self : Nat)
    (inputMember : Activity.rearm channel body guarded self ∈ activities)
    (outputMember : Activity.sendCode suppliedChannel suppliedBody suppliedGuarded self ∈ activities) :
    channel = suppliedChannel ∧ body = suppliedBody := by
  have first : (⟨self, channel, body⟩ : Owner Γ) ∈ listeners activities :=
    List.mem_filterMap.mpr ⟨_, inputMember, rfl⟩
  have second : (⟨self, suppliedChannel, suppliedBody⟩ : Owner Γ) ∈ codes activities :=
    List.mem_filterMap.mpr ⟨_, outputMember, rfl⟩
  have same := inventory.owner_coherent first (inventory.code_mem_listener second) rfl
  exact ⟨congrArg Owner.channel same, congrArg Owner.body same⟩

/-- The port-separation hypothesis used by actual matcher inversion is
derived from ownership; it is not a further compiler correctness premise. -/
theorem Inventory.ports_fresh {Γ : Ctx sig} {world : SeedWorld Γ}
    {activities : List (Activity Γ)} (inventory : Inventory world activities) :
    ∀ activity ∈ activities, activity.port.Fresh world := by
  intro activity member
  cases activity with
  | rearm channel body guarded self =>
      exact inventory.owner_fresh ⟨self, channel, body⟩
        (List.mem_filterMap.mpr ⟨_, member, rfl⟩)
  | sendCode channel body guarded self =>
      exact inventory.owner_fresh ⟨self, channel, body⟩
        (inventory.code_mem_listener (List.mem_filterMap.mpr ⟨_, member, rfl⟩))
  | output channel datum => trivial
  | input channel body guarded => trivial
  | privateScope body guarded => trivial
  | install channel body guarded => trivial
  | ready channel body guarded self => trivial
  | request => trivial
  | reply seed => trivial
  | allocatorReady => trivial
  | allocatorRearm => trivial
  | allocatorSendCode => trivial
  | seedInput => trivial
  | token seed => trivial

/-- Reordering occurrences preserves the complete inventory. -/
theorem Inventory.perm {Γ : Ctx sig} {world : SeedWorld Γ}
    {first second : List (Activity Γ)} (inventory : Inventory world first)
    (permutation : first.Perm second) : Inventory world second := by
  have listenerPerm : (listeners first).Perm (listeners second) := permutation.filterMap listener
  have replyPerm : (replies first).Perm (replies second) := permutation.filterMap replySeed
  have tokenPerm : (tokens first).Perm (tokens second) := permutation.filterMap tokenSeed
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.perm_singleton.mp (tokenPerm.symm.trans (List.Perm.of_eq inventory.token_unique))
  · exact (listenerPerm.map Owner.self).nodup_iff.mp inventory.owner_unique
  · exact (permutation.filterMap rearming).symm.trans
      (inventory.rearm_code.trans (permutation.filterMap storedCode))
  · intro owner member
    exact inventory.owner_below owner (listenerPerm.mem_iff.mpr member)
  · intro owner member
    exact inventory.owner_fresh owner (listenerPerm.mem_iff.mpr member)
  · exact replyPerm.nodup_iff.mp inventory.reply_unique
  · intro seed member
    exact inventory.reply_below seed (replyPerm.mem_iff.mpr member)
  · intro seed member
    exact inventory.reply_fresh seed (replyPerm.mem_iff.mpr member)
  · intro seed member owner ownerMember
    exact inventory.reply_owner seed (replyPerm.mem_iff.mpr member)
      owner (listenerPerm.mem_iff.mpr ownerMember)
  · rw [← count_perm _ permutation, ← count_perm _ permutation]
    exact inventory.allocator_phase
  · rw [← count_perm _ permutation, ← count_perm _ permutation]
    exact inventory.allocator_code
  · have clients : RhoUnaryImage.clientCount first = RhoUnaryImage.clientCount second :=
      (permutation.map RhoUnaryImage.pendingWeight).sum_eq
    have requests : RhoUnaryImage.requestCount first = RhoUnaryImage.requestCount second :=
      (permutation.map RhoUnaryImage.requestWeight).sum_eq
    rw [← clients, ← requests, ← count_perm _ permutation, ← replyPerm.length_eq]
    exact inventory.pending_balance

theorem initial_extractions {Γ : Ctx sig} {activities : List (Activity Γ)}
    (initial : ∀ activity ∈ activities, RhoUnaryImage.Initial activity) :
    listeners activities = [] ∧ rearms activities = [] ∧ codes activities = [] ∧
      replies activities = [] ∧ tokens activities = [] ∧
      count .seedInput activities = 0 ∧ count .allocatorReady activities = 0 ∧
      count .allocatorRearm activities = 0 ∧ count .allocatorSendCode activities = 0 := by
  have excluded : ∀ activity ∈ activities,
      listener activity = none ∧ rearming activity = none ∧ storedCode activity = none ∧
      replySeed activity = none ∧ tokenSeed activity = none ∧
      contribution .seedInput activity = 0 ∧ contribution .allocatorReady activity = 0 ∧
      contribution .allocatorRearm activity = 0 ∧ contribution .allocatorSendCode activity = 0 := by
    intro activity member
    have entry := initial activity member
    cases activity <;> simp_all [RhoUnaryImage.Initial, listener, rearming, storedCode,
      replySeed, tokenSeed, contribution]
  have countZero (kind : CountKind) : count kind activities = 0 := by
    unfold count
    apply List.sum_eq_zero
    intro amount sumMember
    obtain ⟨activity, activityMember, amountEq⟩ := List.mem_map.mp sumMember
    subst amount
    have all := excluded activity activityMember
    cases kind <;> tauto
  refine ⟨?_, ?_, ?_, ?_, ?_, countZero _, countZero _, countZero _, countZero _⟩
  all_goals apply List.filterMap_eq_nil_iff.mpr
  all_goals intro activity member
  all_goals have all := excluded activity member
  all_goals tauto

/-- Every compiled initial frontier can be placed beside the actual one
allocator and token. The new instance contains that token, not an empty
or constant runtime used to satisfy the laws. -/
theorem initial_inventory {Γ : Ctx sig} (world : SeedWorld Γ)
    {activities : List (Activity Γ)}
    (initial : ∀ activity ∈ activities, RhoUnaryImage.Initial activity)
    (balanced : RhoUnaryImage.clientCount activities = RhoUnaryImage.requestCount activities) :
    Inventory world (activities ++ [.allocatorReady, .token world.available]) := by
  obtain ⟨noListeners, noRearms, noCodes, noReplies, noTokens,
    noSeedInputs, noAllocator, noRearm, noCode⟩ := initial_extractions initial
  have noRuntimeListeners : listeners (activities ++ [.allocatorReady, .token world.available]) = [] := by
    rw [listeners_append, noListeners]
    rfl
  have noRuntimeRearms : rearms (activities ++ [.allocatorReady, .token world.available]) = [] := by
    rw [rearms_append, noRearms]
    rfl
  have noRuntimeCodes : codes (activities ++ [.allocatorReady, .token world.available]) = [] := by
    rw [codes_append, noCodes]
    rfl
  have noRuntimeReplies : replies (activities ++ [.allocatorReady, .token world.available]) = [] := by
    rw [replies_append, noReplies]
    rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tokens_append, noTokens]
    rfl
  · simp only [noRuntimeListeners, List.map_nil, List.nodup_nil]
  · rw [noRuntimeRearms, noRuntimeCodes]
  · simp only [noRuntimeListeners, List.not_mem_nil, false_implies, implies_true]
  · simp only [noRuntimeListeners, List.not_mem_nil, false_implies, implies_true]
  · simp only [noRuntimeReplies, List.nodup_nil]
  · simp only [noRuntimeReplies, List.not_mem_nil, false_implies, implies_true]
  · simp only [noRuntimeReplies, List.not_mem_nil, false_implies, implies_true]
  · simp only [noRuntimeReplies, List.not_mem_nil, false_implies, implies_true]
  · simp [noAllocator, noRearm, contribution]
  · simp [noCode, noRearm, contribution]
  · simp only [RhoUnaryImage.clientCount, RhoUnaryImage.requestCount, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      RhoUnaryImage.pendingWeight, RhoUnaryImage.requestWeight, Nat.add_zero]
    rw [← RhoUnaryImage.clientCount, ← RhoUnaryImage.requestCount, balanced,
      count_append, noSeedInputs, noRuntimeReplies]
    rfl

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventory
