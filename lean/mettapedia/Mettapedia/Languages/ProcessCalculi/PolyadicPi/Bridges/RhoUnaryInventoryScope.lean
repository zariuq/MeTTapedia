import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryPreservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryDelivery
import Mettapedia.OSLF.Syntax.Strengthening

/-!
# Inventory preservation when an actual private reply binds a source name

The received seed is read from the concrete reply occurrence. The existing
inventory proves that it was issued, is fresh for all source names and live
server owners, and differs from every remaining reply. Extending the source
scope reindexes every untouched activity without changing its runtime header.
The activated body contributes its actual balanced initial compiler image.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryScope

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCode RhoUnaryCompiler RhoUnaryExecution RhoUnaryWorld RhoUnaryActive RhoUnaryInventory
open RhoUnaryInventoryPreservation RhoUnaryImage RhoUnaryReindex
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges
open RhoScopedAllocation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

def _root_.Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventory.Owner.rename
    {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (owner : Owner Γ) : Owner Δ where
  self := owner.self
  channel := environment _ owner.channel
  body := Mettapedia.OSLF.Binding.rename (liftRen environment [.nm]) owner.body

/-- The computed partial inverse reflects both the source channel and its
guarded handler, including the handler's bound request variable. -/
theorem owner_rename_injective {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (inverse : Strengthener environment) : Function.Injective (Owner.rename environment) := by
  rintro ⟨firstSelf, firstChannel, firstBody⟩ ⟨secondSelf, secondChannel, secondBody⟩ same
  have sameSelf := congrArg Owner.self same
  have sameChannel := congrArg Owner.channel same
  have sameBody := congrArg Owner.body same
  change firstSelf = secondSelf at sameSelf
  change environment Srt.nm firstChannel = environment Srt.nm secondChannel at sameChannel
  change rename (liftRen environment [.nm]) firstBody =
    rename (liftRen environment [.nm]) secondBody at sameBody
  have originalChannel : firstChannel = secondChannel := by
    have found := inverse.un_rho Srt.nm firstChannel
    rw [sameChannel, inverse.un_rho] at found
    exact (Option.some.inj found).symm
  have originalBody := Mettapedia.OSLF.Binding.rename_injective (inverse.liftS [.nm]) sameBody
  cases sameSelf
  cases originalChannel
  cases originalBody
  rfl

theorem owner_weaken_injective {Γ : Ctx sig} :
    Function.Injective (Owner.rename (Γ := Γ) (fun _ name => Var.succ name : Ren sig Γ (.nm :: Γ))) :=
  owner_rename_injective _ (Strengthener.ofWeaken sig Srt.nm)

@[simp] theorem listener_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    listener (activity.rename environment) = (listener activity).map (Owner.rename environment) := by
  cases activity <;> rfl

@[simp] theorem rearming_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    rearming (activity.rename environment) = (rearming activity).map (Owner.rename environment) := by
  cases activity <;> rfl

@[simp] theorem storedCode_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    storedCode (activity.rename environment) = (storedCode activity).map (Owner.rename environment) := by
  cases activity <;> rfl

@[simp] theorem replySeed_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    replySeed (activity.rename environment) = replySeed activity := by cases activity <;> rfl

@[simp] theorem tokenSeed_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    tokenSeed (activity.rename environment) = tokenSeed activity := by cases activity <;> rfl

theorem listeners_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    listeners (activities.map (Activity.rename environment)) =
      (listeners activities).map (Owner.rename environment) := by
  unfold listeners
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext activity
  exact listener_rename environment activity

theorem rearms_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    rearms (activities.map (Activity.rename environment)) =
      (rearms activities).map (Owner.rename environment) := by
  unfold rearms
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext activity
  exact rearming_rename environment activity

theorem codes_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    codes (activities.map (Activity.rename environment)) =
      (codes activities).map (Owner.rename environment) := by
  unfold codes
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext activity
  exact storedCode_rename environment activity

theorem replies_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    replies (activities.map (Activity.rename environment)) = replies activities := by
  unfold replies
  rw [List.filterMap_map]
  congr 1
  funext activity
  exact replySeed_rename environment activity

theorem tokens_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    tokens (activities.map (Activity.rename environment)) = tokens activities := by
  unfold tokens
  rw [List.filterMap_map]
  congr 1
  funext activity
  exact tokenSeed_rename environment activity

@[simp] theorem contribution_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (kind : CountKind) (activity : Activity Γ) :
    contribution kind (activity.rename environment) = contribution kind activity := by
  cases kind <;> cases activity <;> rfl

theorem count_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (kind : CountKind) (activities : List (Activity Γ)) :
    count kind (activities.map (Activity.rename environment)) = count kind activities := by
  unfold count
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun activity _ => contribution_rename environment kind activity))

@[simp] theorem pendingWeight_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    pendingWeight (activity.rename environment) = pendingWeight activity := by cases activity <;> rfl

@[simp] theorem requestWeight_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activity : Activity Γ) :
    requestWeight (activity.rename environment) = requestWeight activity := by cases activity <;> rfl

theorem clientCount_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    clientCount (activities.map (Activity.rename environment)) = clientCount activities := by
  unfold clientCount
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun activity _ => pendingWeight_rename environment activity))

theorem requestCount_rename {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ) (activities : List (Activity Γ)) :
    requestCount (activities.map (Activity.rename environment)) = requestCount activities := by
  unfold requestCount
  rw [List.map_map]
  exact congrArg List.sum (List.map_congr_left (fun activity _ => requestWeight_rename environment activity))

/-- The exact returned reply has the required facts to extend the source
world. They are consequences of the original inventory, not new premises. -/
theorem private_reply_facts {Γ : Ctx sig} {world : SeedWorld Γ}
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (seed : Nat)
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.privateScope body guarded :: .reply seed :: frame)) :
    seed < world.available ∧ ∀ name, seed ≠ world.index name := by
  have member : seed ∈ replies (.privateScope body guarded :: .reply seed :: frame) := by
    simp only [replies, List.filterMap_cons, replySeed, List.mem_cons_self]
  exact ⟨inventory.reply_below seed member, inventory.reply_fresh seed member⟩

/-- Removing the delivered client/reply and extending by that actual seed
preserves every existing owner, reply, allocator phase and pending balance. -/
theorem private_frame {Γ : Ctx sig} {world : SeedWorld Γ}
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.privateScope body guarded :: .reply seed :: frame)) :
    Inventory (world.extendAt seed returned fresh)
      (frame.map (Activity.rename (fun _ name => Var.succ name))) := by
  rcases inventory with ⟨token, ownerUnique, code, ownerBound, ownerFresh,
    replyUnique, replyBound, replyFresh, replyOwner, allocator, allocatorCode, pending⟩
  simp only [tokens, tokenSeed, listeners, listener, rearms, rearming, codes, RhoUnaryInventory.storedCode,
    replies, replySeed, List.filterMap_cons, count_cons, contribution,
    clientCount_cons, requestCount_cons, pendingWeight, requestWeight, Nat.zero_add,
    List.length_cons] at *
  constructor
  · rw [tokens_rename]
    exact token
  · rw [listeners_rename, List.map_map]
    exact ownerUnique
  · rw [rearms_rename, codes_rename]
    exact code.map _
  · intro owner member
    rw [listeners_rename] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ownerBound original present
  · intro owner member name
    rw [listeners_rename] at member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    cases name with
    | zero =>
        intro same
        exact replyOwner seed (List.mem_cons_self) original present same.symm
    | succ old => exact ownerFresh original present old
  · rw [replies_rename]
    exact replyUnique.of_cons
  · intro other member
    rw [replies_rename] at member
    exact replyBound other (List.mem_cons_of_mem seed member)
  · intro other member name
    rw [replies_rename] at member
    cases name with
    | zero =>
        intro same
        change other = seed at same
        have distinct := (List.nodup_cons.mp replyUnique).1
        exact distinct (same ▸ member)
    | succ old => exact replyFresh other (List.mem_cons_of_mem seed member) old
  · intro other member owner ownerMember
    rw [replies_rename] at member
    rw [listeners_rename] at ownerMember
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp ownerMember
    exact replyOwner other (List.mem_cons_of_mem seed member) original present
  · rw [count_rename, count_rename]
    exact allocator
  · rw [count_rename, count_rename]
    exact allocatorCode
  · rw [clientCount_rename, requestCount_rename, count_rename, replies_rename]
    change clientCount frame = requestCount frame + count .seedInput frame +
      (List.filterMap replySeed frame).length
    omega

/-- The activated body may contain further private scopes and servers. Its
real initial image is balanced, and therefore preserves the delivered frame's
complete inventory. -/
theorem delivered_prefix {Γ : Ctx sig} {world : SeedWorld Γ}
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    {frame : List (Activity Γ)}
    (inventory : Inventory world (.privateScope body guarded :: .reply seed :: frame))
    {image : List (Activity (.nm :: Γ))}
    (initial : ∀ activity ∈ image, Initial activity)
    (balanced : clientCount image = requestCount image) :
    Inventory (world.extendAt seed returned fresh)
      (image ++ frame.map (Activity.rename (fun _ name => Var.succ name))) :=
  initial_prefix initial balanced (private_frame guarded seed returned fresh inventory)

/-- The same actual private-delivery endpoint has the existing source-scope
comparison, the actual compiled rho image, and the preserved inventory. -/
theorem private_delivery_inventory {Γ : Ctx sig} (world : SeedWorld Γ)
    {body : Proc (.nm :: Γ)} (guarded : GuardedUnary body) (seed : Nat)
    (returned : seed < world.available) (fresh : ∀ name, seed ≠ world.index name)
    (frame : List (Activity Γ))
    (inventory : Inventory world (.privateScope body guarded :: .reply seed :: frame)) :
    ∃ image : List (Activity (.nm :: Γ)),
      (∀ activity ∈ image, Initial activity) ∧
      StructuralEq (source (.privateScope body guarded :: .reply seed :: frame))
        (nu (source (image ++ frame.map (Activity.rename (fun _ name => Var.succ name))))) ∧
      StructuralCongruence
        (RhoScopedServers.parallel
          (semanticCommSubst (ordinary guarded world.world).term (seedCode seed) ::
            (headers world.world frame).map Header.pattern))
        (actual (world.extendAt seed returned fresh).world
          (image ++ frame.map (Activity.rename (fun _ name => Var.succ name)))) ∧
      Inventory (world.extendAt seed returned fresh)
        (image ++ frame.map (Activity.rename (fun _ name => Var.succ name))) := by
  obtain ⟨image, initial, sourceEq, targetEq, balanced⟩ :=
    RhoUnaryDelivery.private_delivery_balanced guarded world seed returned fresh frame
  exact ⟨image, initial, sourceEq, targetEq,
    delivered_prefix guarded seed returned fresh inventory initial balanced⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInventoryScope
