import Mettapedia.GSLT.Distinction.RelocationRelation
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Dynamics.CacheCoherence

/-!
# Controls for relocation as a relation

* **A missed saved completion-bank root** (`missed_bank_root`).  Collection is
  a relocation session for the registered roots, yet a saved bank that no root
  field registers is gone after collection; registering it keeps it.
* **Garbage removal is many-to-one** (`garbage_many_to_one`): two different
  heaps collect to the same lookup, and both are related to it.
* **One shared world split into two** (`split_world_has_two_images`,
  `split_world_duplicates_work`).  A copy that gives one shared world two
  images breaks the aliasing of the branches that share it, is no relocation
  session, and duplicates the future admission work: an extra effect in the
  ordered observation, while the answer bags agree.  Two independent copies
  of a choice resample it (`split_world_resamples`).
* **One common session across carriers** (`common_session_keeps_cross_carrier_aliases`):
  payload, world, receipt and grade roots relocated by one injective copy keep
  their cross-carrier aliases and their first-encounter order.
* **Identifier reuse seen by an old holder** (`identifier_reuse_old_holder`):
  after a reset reuses an address, a stamped view is refused, while a raw
  address read observes the new object.
* **A live owner is not currency** (`retained_program_after_revision`): the
  program's bytes are still readable through its owner, while the answer
  cached before an equation revision may not be published.
* **Commit retires the source; refusal rolls back** (`commit_retires_source`,
  `refusal_rolls_back`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.RelocationControls

open Mettapedia.Machines
open Mettapedia.Machines.ResourceOwnership
open Mettapedia.GSLT.Distinction
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open Mettapedia.GSLT.Dynamics.OrderedDemand (Event answerBag lazyTrace resampledTrace
  lazyTrace_eq_resampledTrace_iff)

theorem valid_of_univ {Address : Type} [DecidableEq Address] [Fintype Address]
    (heap : Heap Address ℕ) (univ : heap.allocated = Finset.univ) (roots : Roots ℕ Address) :
    ValidRoots heap roots := by
  intro pair _
  rw [univ]
  exact Finset.mem_univ _

/-! ## A missed saved completion-bank root -/

/-- A frame's cell at `0` and its saved completion bank at `1`. -/
def bankHeap : Heap (Fin 2) ℕ where
  lookup a := some ⟨a.val, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

/-- The frame's root fields without the bank. -/
def frameOnly : Roots ℕ (Fin 2) := {(7, 0)}

/-- The frame's root fields with the bank. -/
def frameWithBank : Roots ℕ (Fin 2) := {(7, 0), (7, 1)}

/-- Collection is a relocation session for the registered roots. -/
noncomputable def frameCollection : LiveRelocation bankHeap frameOnly (collect bankHeap frameOnly) frameOnly :=
  LiveRelocation.ofCollect bankHeap frameOnly

/-- **A missed saved completion-bank root**: the session exists, and the bank is
gone; registering it keeps it. -/
theorem missed_bank_root :
    (collect bankHeap frameOnly).lookup 1 = none ∧ bankHeap.lookup 1 ≠ none ∧
      (collect bankHeap frameWithBank).lookup 1 = bankHeap.lookup 1 := by
  have unreached : ¬ Live bankHeap frameOnly 1 := by
    rw [← mem_census_iff_live bankHeap frameOnly (valid_of_univ bankHeap rfl frameOnly)]
    decide
  refine ⟨lookup_collect_of_not_live bankHeap frameOnly unreached, by simp [bankHeap], ?_⟩
  exact lookup_collect_of_live bankHeap frameWithBank
    (live_of_root bankHeap frameWithBank (owner := 7) (a := 1) (by decide) (by decide))

/-! ## Garbage removal is many-to-one -/

def cleanHeap : Heap (Fin 2) ℕ where
  lookup a := if a = 0 then some ⟨0, ∅, 8⟩ else none
  allocated := {0}
  allocated_iff a := by fin_cases a <;> simp
  closed := by
    intro a cell found b member
    by_cases zero : a = 0
    · simp only [zero, if_true, Option.some.injEq] at found
      subst found
      simp at member
    · simp [zero] at found

def garbageHeap : Heap (Fin 2) ℕ where
  lookup a := some ⟨if a = 0 then 0 else 5, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

def onlyZero : Roots ℕ (Fin 2) := {(0, 0)}

/-- **Two different heaps collect to the same lookup**, and both are related to
it by collection sessions. -/
theorem garbage_many_to_one :
    cleanHeap ≠ garbageHeap ∧
      ∀ a, (collect cleanHeap onlyZero).lookup a = (collect garbageHeap onlyZero).lookup a := by
  refine ⟨fun same => absurd (congrArg Heap.allocated same) (by decide), ?_⟩
  intro a
  have cleanLive : ∀ a, Live cleanHeap onlyZero a ↔ a = 0 := by
    intro a
    rw [← mem_census_iff_live cleanHeap onlyZero (by
      intro pair member
      simp only [onlyZero, Finset.mem_singleton] at member
      subst member
      decide)]
    fin_cases a <;> decide
  have garbageLive : ∀ a, Live garbageHeap onlyZero a ↔ a = 0 := by
    intro a
    rw [← mem_census_iff_live garbageHeap onlyZero (valid_of_univ garbageHeap rfl onlyZero)]
    fin_cases a <;> decide
  by_cases zero : a = 0
  · subst zero
    rw [lookup_collect_of_live _ _ ((cleanLive 0).mpr rfl),
      lookup_collect_of_live _ _ ((garbageLive 0).mpr rfl)]
    rfl
  · rw [lookup_collect_of_not_live _ _ (fun live => zero ((cleanLive a).mp live)),
      lookup_collect_of_not_live _ _ (fun live => zero ((garbageLive a).mp live))]

/-! ## One shared world split into two -/

/-- One world shared by two branches. -/
def worldHeap : Heap (Fin 1) ℕ where
  lookup _ := some ⟨42, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

def branches : Roots ℕ (Fin 1) := {(1, 0), (2, 0)}

/-- Two independent copies of it, one per branch. -/
def splitHeap : Heap (Fin 2) ℕ where
  lookup _ := some ⟨42, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

def splitRoots : Roots ℕ (Fin 2) := {(1, 0), (2, 1)}

/-- **A shared world with two images**: the branches alias in the source and
not in the copy, and no relocation session relates them. -/
theorem split_world_has_two_images :
    Aliases worldHeap 0 [] 0 [] ∧ ¬ Aliases splitHeap 0 [] 1 [] ∧
      IsEmpty (LiveRelocation worldHeap branches splitHeap splitRoots) := by
  refine ⟨⟨0, by decide, by decide⟩, ?_, ⟨fun session => ?_⟩⟩
  · rintro ⟨endpoint, left, right⟩
    simp [walk, splitHeap] at left right
    rw [← left] at right
    exact absurd right (by decide)
  · have image : ∀ pair ∈ splitRoots, pair ∈ branches.image fun pair => (pair.1, session.address pair.2) := by
      intro pair member
      rw [← session.roots_eq]
      exact member
    obtain ⟨first, _, firstSame⟩ := Finset.mem_image.mp (image (1, 0) (by decide))
    obtain ⟨second, _, secondSame⟩ := Finset.mem_image.mp (image (2, 1) (by decide))
    have firstAddress : session.address 0 = 0 := by
      have := congrArg Prod.snd firstSame
      rwa [Subsingleton.elim first.2 0] at this
    have secondAddress : session.address 0 = 1 := by
      have := congrArg Prod.snd secondSame
      rwa [Subsingleton.elim second.2 0] at this
    exact absurd (firstAddress.symm.trans secondAddress) (by decide)

abbrev WorldEvent := Event ℕ String Unit

/-- A shared world: the first branch admits and caches, later branches read the
cache.  The state records whether the cache is filled and the branches left. -/
def memoWorld : Machine (Bool × ℕ) WorldEvent Unit Empty where
  step
    | (_, 0) => some (.finish ())
    | (false, n + 1) => some (.publish [.effect "admit", .answer 7] (true, n))
    | (true, n + 1) => some (.publish [.answer 7] (true, n))

/-- **Splitting the world duplicates future admission work**: one more effect in
the ordered observation, while the answer bags agree. -/
theorem split_world_duplicates_work :
    (memoWorld.run 3 (false, 2)).1 = [.effect "admit", .answer 7, .answer 7] ∧
      (memoWorld.run 2 (false, 1)).1 ++ (memoWorld.run 2 (false, 1)).1 =
        [.effect "admit", .answer 7, .effect "admit", .answer 7] ∧
      answerBag (memoWorld.run 3 (false, 2)).1 =
        answerBag ((memoWorld.run 2 (false, 1)).1 ++ (memoWorld.run 2 (false, 1)).1) ∧
      (memoWorld.run 3 (false, 2)).1 ≠
        (memoWorld.run 2 (false, 1)).1 ++ (memoWorld.run 2 (false, 1)).1 :=
  ⟨rfl, rfl, by decide, by decide⟩

/-- **Two independent copies of a choice resample it**: sharing a coin between
two uses differs from drawing it in each copy. -/
theorem split_world_resamples :
    lazyTrace 2 ([.answer 0, .answer 1] : List WorldEvent) ≠
      resampledTrace 2 ([.answer 0, .answer 1] : List WorldEvent) := by
  rw [Ne, lazyTrace_eq_resampledTrace_iff]
  rintro (impossible | none | ⟨value, equal⟩)
  · omega
  · simp [Mettapedia.GSLT.Dynamics.OrderedDemand.answers,
      Mettapedia.GSLT.Dynamics.OrderedDemand.Event.answer?] at none
  · simp at equal

/-! ## One common session across carriers -/

open Examples in
/-- Payload (`0`), world (`1`), receipt (`2`) and grade (`3`) roots of one
cyclic graph. -/
def carriers : Roots ℕ (Fin 3) := {(0, 0), (1, 2), (2, 1), (3, 0)}

open Examples in
/-- **One common session keeps cross-carrier aliases and first-encounter
order**: the receipt's path through `2` and the world's root meet, before and
after the copy. -/
theorem common_session_keeps_cross_carrier_aliases :
    Aliases cyclicHeap 1 [2] 2 [] ∧
      Aliases copiedHeap (relocationAddress 1) ([2].map relocationAddress)
        (relocationAddress 2) (([] : List (Fin 3)).map relocationAddress) ∧
      ([0, 1, 2, 1, 0].map relocationAddress).eraseDups = [0, 1, 2].map relocationAddress := by
  have source : Aliases cyclicHeap 1 [2] 2 [] := ⟨2, by decide, by decide⟩
  have liveOne : Live cyclicHeap carriers 1 :=
    live_of_root cyclicHeap carriers (owner := 2) (a := 1) (by decide) (by decide)
  have liveTwo : Live cyclicHeap carriers 2 :=
    live_of_root cyclicHeap carriers (owner := 1) (a := 2) (by decide) (by decide)
  refine ⟨source, ?_, ?_⟩
  · exact ((LiveRelocation.ofRelocation shiftedCopy carriers).aliases_iff liveOne liveTwo _ _).mpr
      ⟨[2], [], rfl, rfl, source⟩
  · exact (Relocation.first_seen_address_order shiftedCopy [0, 1, 2, 1, 0]).trans (by decide)

/-! ## Identifier reuse seen by an old holder -/

def oldHeap : Heap (Fin 1) ℕ where
  lookup _ := some ⟨1, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

/-- The same address, reused for a different object after a reset. -/
def reusedHeap : Heap (Fin 1) ℕ where
  lookup _ := some ⟨2, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

def region : RequestBorrow.Region ℕ (Fin 1) ℕ := ⟨⟨5, 0⟩, oldHeap⟩

def oldHolder : RequestBorrow.View ℕ (Fin 1) := ⟨⟨5, 0⟩, [(0, [])]⟩

/-- **Identifier reuse**: the stamped holder reads the old object before the
reset and is refused after it; a raw address read after the reset observes the
new object. -/
theorem identifier_reuse_old_holder :
    RequestBorrow.read region oldHolder = some (RequestBorrow.observe oldHeap oldHolder.paths) ∧
      RequestBorrow.read (RequestBorrow.reset region reusedHeap) oldHolder = none ∧
      RequestBorrow.observe reusedHeap oldHolder.paths ≠ RequestBorrow.observe oldHeap oldHolder.paths := by
  refine ⟨rfl, RequestBorrow.read_reset_rejected region reusedHeap oldHolder rfl, by decide⟩

/-! ## A live owner is not currency -/

open Mettapedia.GSLT.Dynamics.CacheCoherence

/-- The retained program's answer depends on the equations' revision. -/
def programAnswer (live : RevisionEnvironment Unit ℕ) (_ : Unit) : ℕ := live.current () * 10

def consultsEquations (_ : RevisionEnvironment Unit ℕ) (_ : Unit) : List Unit := [()]

theorem equations_determine : ReadsDetermine programAnswer consultsEquations := by
  intro captured live query agrees
  have same := agrees () (by simp [consultsEquations])
  simp [programAnswer, same]

def beforeRevision : RevisionEnvironment Unit ℕ := ⟨fun _ => 1⟩

def afterRevision : RevisionEnvironment Unit ℕ := ⟨fun _ => 2⟩

def programRegion : RequestBorrow.Region ℕ (Fin 1) ℕ := ⟨⟨9, 0⟩, oldHeap⟩

def programView : RequestBorrow.View ℕ (Fin 1) := ⟨⟨9, 0⟩, [(0, [])]⟩

/-- **A live owner is not currency**: the retained program's bytes are still
readable through its owner, while the answer cached before the equation
revision is stale and may not be published. -/
theorem retained_program_after_revision :
    RequestBorrow.read programRegion programView =
        some (RequestBorrow.observe oldHeap programView.paths) ∧
      (record programAnswer consultsEquations beforeRevision ()).answer = 10 ∧
      programAnswer afterRevision () = 20 ∧
      ¬ (record programAnswer consultsEquations beforeRevision ()).view.CanPublish afterRevision := by
  refine ⟨rfl, rfl, rfl, fun publish => ?_⟩
  have current := (recorded_record equations_determine beforeRevision ()).answer_of_canPublish publish
  exact absurd current (by decide)

/-! ## Commit retires the source; refusal rolls back -/

/-- The source copy at `0`, owned by `0`; the destination copy at `1`, owned by
`1`, during a session. -/
def sessionHeap : Heap (Fin 2) ℕ where
  lookup _ := some ⟨42, ∅, 8⟩
  allocated := Finset.univ
  allocated_iff a := ⟨fun _ => ⟨_, rfl⟩, fun _ => Finset.mem_univ a⟩
  closed _ _ _ b _ := Finset.mem_univ b

def sessionRoots : Roots ℕ (Fin 2) := {(0, 0), (1, 1)}

/-- **Commit retires the source**: releasing the source owner keeps every
destination path and reclaims the source copy. -/
theorem commit_retires_source (path : List (Fin 2)) :
    walk (collect sessionHeap (release sessionRoots 0)) 1 path = walk sessionHeap 1 path ∧
      (collect sessionHeap (release sessionRoots 0)).lookup 0 = none := by
  have valid : ValidRoots sessionHeap (release sessionRoots 0) :=
    valid_of_univ sessionHeap rfl _
  refine ⟨walk_collect sessionHeap _ ((mem_census_iff_live sessionHeap _ valid 1).mp (by decide)) path, ?_⟩
  apply lookup_collect_of_not_live
  rw [← mem_census_iff_live sessionHeap _ valid]
  decide

/-- **Refusal rolls back**: releasing the destination owner keeps every source
path and reclaims the destination copy. -/
theorem refusal_rolls_back (path : List (Fin 2)) :
    walk (collect sessionHeap (release sessionRoots 1)) 0 path = walk sessionHeap 0 path ∧
      (collect sessionHeap (release sessionRoots 1)).lookup 1 = none := by
  have valid : ValidRoots sessionHeap (release sessionRoots 1) :=
    valid_of_univ sessionHeap rfl _
  refine ⟨walk_collect sessionHeap _ ((mem_census_iff_live sessionHeap _ valid 0).mp (by decide)) path, ?_⟩
  apply lookup_collect_of_not_live
  rw [← mem_census_iff_live sessionHeap _ valid]
  decide

end Mettapedia.GSLT.Distinction.RelocationControls
