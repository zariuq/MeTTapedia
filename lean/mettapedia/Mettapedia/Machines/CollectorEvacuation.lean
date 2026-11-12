import Mettapedia.Logic.Relation.FiniteReachability
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Sort

/-!
# Finite graph evacuation with separate tracing and relocation

Tracing computes the reachable source set.  Copying starts with empty relocation
storage, reserves a fresh target before exposing a node's children to the
worklist, and finishes target edges only after the frontier is exhausted.
Spelled symbols and variables use side-table entries; their payloads are never
interpreted as forwarding fields.  Numbered symbols and expressions may use
inline entries.  The two representations implement one logical partial map.

The development proves preservation, sharing, injectivity, totality, and finite
progress for finite graphs with sufficient target capacity.  Allocation failure
publishes no target graph.  These are abstract collector contracts, not a
verification claim about a particular memory allocator or C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CollectorEvacuation

open Mettapedia.Logic.Relation

universe u v w

/-- Semantic atom payloads whose physical forwarding disciplines differ. -/
inductive AtomPayload where
  | numberedSymbol (number : Nat)
  | spelledSymbol (spelling : String)
  | variable (identity : Nat)
  | expression
  deriving DecidableEq, Repr

/-- Whether the atom has a non-payload field available for inline forwarding. -/
def inlineAvailable : AtomPayload → Bool
  | .numberedSymbol _ | .expression => true
  | .spelledSymbol _ | .variable _ => false

inductive ForwardingStorage where
  | inline | sideTable
  deriving DecidableEq, Repr

def requiredStorage (payload : AtomPayload) : ForwardingStorage :=
  if inlineAvailable payload then .inline else .sideTable

structure SourceNode (Source : Type u) (Label : Type v) where
  payload : AtomPayload
  children : List (Label × Source)

structure SourceGraph (Source : Type u) (Label : Type v) where
  node : Source → SourceNode Source Label

structure Target where
  index : Nat
  deriving DecidableEq, Repr

structure Entry (Source : Type u) where
  source : Source
  target : Target
  storage : ForwardingStorage
  deriving DecidableEq, Repr

/-- The logical copy map ignores the physical forwarding representation. -/
def lookup {Source : Type u} [DecidableEq Source] (source : Source) :
    List (Entry Source) → Option Target
  | [] => none
  | entry :: rest =>
      if entry.source = source then some entry.target else lookup source rest

def reset {Source : Type u} (_entries : List (Entry Source)) : List (Entry Source) := []

@[simp] theorem lookup_reset {Source : Type u} [DecidableEq Source]
    (entries : List (Entry Source)) (source : Source) :
    lookup source (reset entries) = none := rfl

theorem lookup_none_not_mem_keys {Source : Type u} [DecidableEq Source]
    {source : Source} {entries : List (Entry Source)}
    (missing : lookup source entries = none) : source ∉ entries.map Entry.source := by
  induction entries with
  | nil => simp
  | cons entry rest ih =>
      simp only [lookup, List.map_cons, List.mem_cons] at missing ⊢
      split at missing
      next same => contradiction
      next different =>
        rintro (same | old)
        · exact different same.symm
        · exact ih missing old

theorem lookup_some_mem_entries {Source : Type u} [DecidableEq Source]
    {source : Source} {target : Target} {entries : List (Entry Source)}
    (found : lookup source entries = some target) :
    ∃ entry ∈ entries, entry.source = source ∧ entry.target = target := by
  induction entries with
  | nil => contradiction
  | cons entry rest ih =>
      simp only [lookup] at found
      split at found
      next same =>
        cases found
        exact ⟨entry, by simp, same, rfl⟩
      next different =>
          obtain ⟨foundEntry, member, key, image⟩ := ih found
          exact ⟨foundEntry, List.mem_cons_of_mem entry member, key, image⟩

/-- Old entries survive insertion for a previously missing key. -/
theorem lookup_insert_old {Source : Type u} [DecidableEq Source]
    {source other : Source} {target otherTarget : Target}
    {entries : List (Entry Source)} {storage : ForwardingStorage}
    (missing : lookup source entries = none)
    (found : lookup other entries = some otherTarget) :
    lookup other (⟨source, target, storage⟩ :: entries) = some otherTarget := by
  have different : source ≠ other := by
    intro same
    subst other
    rw [missing] at found
    contradiction
  simp [lookup, different, found]

@[simp] theorem lookup_insert_same {Source : Type u} [DecidableEq Source]
    (source : Source) (target : Target) (storage : ForwardingStorage)
    (entries : List (Entry Source)) :
    lookup source (⟨source, target, storage⟩ :: entries) = some target := by
  simp [lookup]

variable {Source : Type u} {Label : Type v}
  [Fintype Source] [LinearOrder Source]

def successors (graph : SourceGraph Source Label) (source : Source) : Finset Source :=
  ((graph.node source).children.map Prod.snd).toFinset

/-- The independent meaning of tracing: finite reflexive-transitive reachability. -/
def live (graph : SourceGraph Source Label) (roots : List Source) : Finset Source :=
  reachSet (successors graph) roots.toFinset

theorem mem_live_iff (graph : SourceGraph Source Label) (roots : List Source) (source : Source) :
    source ∈ live graph roots ↔
      ∃ root ∈ roots.toFinset,
        Relation.ReflTransGen (fun a b => b ∈ successors graph a) root source :=
  mem_reachSet_iff

theorem root_live (graph : SourceGraph Source Label) {roots : List Source}
    {root : Source} (member : root ∈ roots) : root ∈ live graph roots := by
  exact subset_reachSet (next := successors graph) roots.toFinset
    (List.mem_toFinset.mpr member)

theorem child_live (graph : SourceGraph Source Label) {roots : List Source}
    {source child : Source} (sourceLive : source ∈ live graph roots)
    (edge : child ∈ successors graph source) : child ∈ live graph roots := by
  have exposed := mem_saturateStep.mpr (Or.inr ⟨source, sourceLive, edge⟩)
  have closed : saturateStep (successors graph) (live graph roots) = live graph roots :=
    saturateStep_reachSet roots.toFinset
  rwa [closed] at exposed

structure CopyState (Source : Type u) where
  entries : List (Entry Source)
  pending : Finset Source
  nextTarget : Nat

def Mapped {Source : Type u} [DecidableEq Source]
    (state : CopyState Source) (source : Source) : Prop :=
  ∃ target, lookup source state.entries = some target

def StorageValid (graph : SourceGraph Source Label) (state : CopyState Source) : Prop :=
  ∀ entry ∈ state.entries,
    entry.storage = requiredStorage (graph.node entry.source).payload

/-- Reachable-state invariant.  In particular, a reserved source has already
exposed every child to the map-or-frontier boundary. -/
structure Invariant (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source) : Prop where
  mapped_live : ∀ {source target}, lookup source state.entries = some target →
    source ∈ live graph roots
  pending_live : ∀ source ∈ state.pending, source ∈ live graph roots
  roots_covered : ∀ root ∈ roots, Mapped state root ∨ root ∈ state.pending
  edges_covered : ∀ {source target}, lookup source state.entries = some target →
    ∀ {child}, child ∈ successors graph source → Mapped state child ∨ child ∈ state.pending
  keys_unique : (state.entries.map Entry.source).Nodup
  targets_unique : (state.entries.map Entry.target).Nodup
  target_bound : ∀ entry ∈ state.entries, entry.target.index < state.nextTarget
  next_eq_length : state.nextTarget = state.entries.length
  storage_valid : StorageValid graph state

def initialCopy (roots : List Source) : CopyState Source :=
  ⟨[], roots.toFinset, 0⟩

theorem initialCopy_invariant (graph : SourceGraph Source Label) (roots : List Source) :
    Invariant graph roots (initialCopy roots) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro source target found
    contradiction
  · intro source member
    exact root_live graph (List.mem_toFinset.mp member)
  · intro root member
    exact Or.inr (List.mem_toFinset.mpr member)
  · intro source target found
    contradiction
  · exact List.nodup_nil
  · exact List.nodup_nil
  · intro entry member
    contradiction
  · rfl
  · intro entry member
    contradiction

/-- Remove one selected occurrence from the abstract frontier. -/
def skip {Source : Type u} [DecidableEq Source]
    (state : CopyState Source) (source : Source) : CopyState Source :=
  { state with pending := state.pending.erase source }

/-- Reserve before exposing children.  The target is fresh according to the
monotonic allocator index; storage is selected from payload ownership. -/
def allocate (graph : SourceGraph Source Label)
    (state : CopyState Source) (source : Source) : CopyState Source :=
  let entry : Entry Source :=
    ⟨source, ⟨state.nextTarget⟩, requiredStorage (graph.node source).payload⟩
  ⟨entry :: state.entries, (state.pending.erase source) ∪ successors graph source,
    state.nextTarget + 1⟩

/-- One worklist round.  The selected source is removed from the frontier.  An
unmapped source receives its target before its children join the frontier. -/
def reserveLoop (graph : SourceGraph Source Label) (capacity : Nat)
    (state : CopyState Source) : Option (CopyState Source) :=
  if nonempty : state.pending.Nonempty then
    let source := state.pending.min' nonempty
    match _found : lookup source state.entries with
    | some _ => reserveLoop graph capacity (skip state source)
    | none =>
        if _available : state.nextTarget < capacity ∧
            state.entries.length < Fintype.card Source then
          reserveLoop graph capacity (allocate graph state source)
        else none
  else some state
termination_by (Fintype.card Source - state.entries.length, state.pending.card)
decreasing_by
  · apply Prod.Lex.right
    exact Finset.card_erase_lt_of_mem (Finset.min'_mem _ nonempty)
  · apply Prod.Lex.left
    simp only [allocate, List.length_cons]
    omega

theorem covered_erase {Source : Type u} [DecidableEq Source]
    {state : CopyState Source} {selected source : Source}
    (selectedMapped : Mapped state selected)
    (covered : Mapped state source ∨ source ∈ state.pending) :
    Mapped state source ∨ source ∈ state.pending.erase selected := by
  rcases covered with mapped | pending
  · exact Or.inl mapped
  · by_cases same : source = selected
    · subst source
      exact Or.inl selectedMapped
    · exact Or.inr (Finset.mem_erase.mpr ⟨same, pending⟩)

theorem skip_invariant (graph : SourceGraph Source Label) (roots : List Source)
    {state : CopyState Source} {source : Source}
    (invariant : Invariant graph roots state) (mapped : Mapped state source) :
    Invariant graph roots (skip state source) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact invariant.mapped_live
  · intro child member
    exact invariant.pending_live child (Finset.mem_of_mem_erase member)
  · intro root member
    exact covered_erase mapped (invariant.roots_covered root member)
  · intro parent target found child edge
    exact covered_erase mapped (invariant.edges_covered found edge)
  · exact invariant.keys_unique
  · exact invariant.targets_unique
  · exact invariant.target_bound
  · exact invariant.next_eq_length
  · exact invariant.storage_valid

theorem allocate_invariant (graph : SourceGraph Source Label) (roots : List Source)
    {state : CopyState Source} {source : Source}
    (invariant : Invariant graph roots state) (sourceLive : source ∈ live graph roots)
    (missing : lookup source state.entries = none) :
    Invariant graph roots (allocate graph state source) := by
  have newMapped : Mapped (allocate graph state source) source := by
    refine ⟨⟨state.nextTarget⟩, ?_⟩
    simp [allocate]
  have preserve : ∀ {other : Source} {target : Target},
      lookup other state.entries = some target →
        lookup other (allocate graph state source).entries = some target := by
    intro other target found
    exact lookup_insert_old missing found
  have newTargetFresh : (⟨state.nextTarget⟩ : Target) ∉
      state.entries.map Entry.target := by
    intro member
    obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp member
    have bound := invariant.target_bound entry entryMember
    have index := congrArg Target.index equal
    simp only at index
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro other target found
    by_cases same : source = other
    · subst other
      exact sourceLive
    · have old : lookup other state.entries = some target := by
        simpa [allocate, lookup, same] using found
      exact invariant.mapped_live old
  · intro child member
    simp only [allocate, Finset.mem_union, Finset.mem_erase] at member
    rcases member with ⟨_, old⟩ | edge
    · exact invariant.pending_live child old
    · exact child_live graph sourceLive edge
  · intro root member
    rcases invariant.roots_covered root member with mapped | pending
    · obtain ⟨target, found⟩ := mapped
      exact Or.inl ⟨target, preserve found⟩
    · by_cases same : source = root
      · subst root
        exact Or.inl newMapped
      · exact Or.inr (by simp [allocate, Ne.symm same, pending])
  · intro parent target found child edge
    by_cases same : source = parent
    · subst parent
      exact Or.inr (by simp [allocate, edge])
    · have old : lookup parent state.entries = some target := by
        simpa [allocate, lookup, same] using found
      rcases invariant.edges_covered old edge with mapped | pending
      · obtain ⟨childTarget, childFound⟩ := mapped
        exact Or.inl ⟨childTarget, preserve childFound⟩
      · by_cases childSame : source = child
        · subst child
          exact Or.inl newMapped
        · exact Or.inr (by simp [allocate, Ne.symm childSame, pending])
  · simp only [allocate, List.map_cons, List.nodup_cons]
    exact ⟨lookup_none_not_mem_keys missing, invariant.keys_unique⟩
  · simp only [allocate, List.map_cons, List.nodup_cons]
    exact ⟨newTargetFresh, invariant.targets_unique⟩
  · intro entry member
    change entry.target.index < state.nextTarget + 1
    simp only [allocate, List.mem_cons] at member
    rcases member with rfl | old
    · simp
    · have bound := invariant.target_bound entry old
      omega
  · simp only [allocate, List.length_cons]
    have length := invariant.next_eq_length
    omega
  · intro entry member
    simp only [allocate, List.mem_cons] at member
    rcases member with rfl | old
    · rfl
    · exact invariant.storage_valid entry old

theorem reserveLoop_invariant (graph : SourceGraph Source Label) (roots : List Source)
    (capacity : Nat) (state : CopyState Source) :
    Invariant graph roots state →
      ∀ final, reserveLoop graph capacity state = some final →
        Invariant graph roots final := by
  induction state using reserveLoop.induct (graph := graph) (capacity := capacity) with
  | case1 state nonempty source target found ih =>
      intro invariant final result
      rw [reserveLoop.eq_def, dif_pos nonempty] at result
      dsimp only at result
      rw [found] at result
      exact ih (skip_invariant graph roots invariant ⟨target, found⟩) final result
  | case2 state nonempty source missing available ih =>
      intro invariant final result
      rw [reserveLoop.eq_def, dif_pos nonempty] at result
      dsimp only at result
      rw [missing, dif_pos available] at result
      have selectedLive := invariant.pending_live _ (Finset.min'_mem _ nonempty)
      exact ih (allocate_invariant graph roots invariant selectedLive missing) final result
  | case3 state nonempty source missing unavailable =>
      intro invariant final result
      rw [reserveLoop.eq_def, dif_pos nonempty] at result
      dsimp only at result
      rw [missing, dif_neg unavailable] at result
      contradiction
  | case4 state empty =>
      intro invariant final result
      rw [reserveLoop.eq_def, dif_neg empty] at result
      cases result
      exact invariant

theorem reserveLoop_pending_empty (graph : SourceGraph Source Label)
    (capacity : Nat) (state : CopyState Source) :
    ∀ final, reserveLoop graph capacity state = some final → final.pending = ∅ := by
  induction state using reserveLoop.induct (graph := graph) (capacity := capacity) with
  | case1 state nonempty source target found ih =>
      intro final result
      rw [reserveLoop.eq_def, dif_pos nonempty] at result
      dsimp only at result
      rw [found] at result
      exact ih final result
  | case2 state nonempty source missing available ih =>
      intro final result
      rw [reserveLoop.eq_def, dif_pos nonempty] at result
      dsimp only at result
      rw [missing, dif_pos available] at result
      exact ih final result
  | case3 state nonempty source missing unavailable =>
      intro final result
      rw [reserveLoop.eq_def, dif_pos nonempty] at result
      dsimp only at result
      rw [missing, dif_neg unavailable] at result
      contradiction
  | case4 state empty =>
      intro final result
      rw [reserveLoop.eq_def, dif_neg empty] at result
      cases result
      exact Finset.not_nonempty_iff_eq_empty.mp empty

theorem mapped_total_of_exhausted (graph : SourceGraph Source Label) (roots : List Source)
    {state : CopyState Source} (invariant : Invariant graph roots state)
    (empty : state.pending = ∅) {source : Source} (sourceLive : source ∈ live graph roots) :
    Mapped state source := by
  obtain ⟨root, rootMember, path⟩ := (mem_live_iff graph roots source).mp sourceLive
  have rootMapped : Mapped state root := by
    rcases invariant.roots_covered root (List.mem_toFinset.mp rootMember) with mapped | pending
    · exact mapped
    · rw [empty] at pending
      contradiction
  induction path with
  | refl => exact rootMapped
  | @tail middle target path edge ih =>
      have middleLive : middle ∈ live graph roots :=
        (mem_live_iff graph roots middle).mpr ⟨root, rootMember, path⟩
      obtain ⟨middleTarget, found⟩ := ih middleLive
      rcases invariant.edges_covered found edge with mapped | pending
      · exact mapped
      · rw [empty] at pending
        contradiction

theorem lookup_of_mem_entries {Source : Type u} [DecidableEq Source]
    {entries : List (Entry Source)} {entry : Entry Source} (member : entry ∈ entries) :
    ∃ target, lookup entry.source entries = some target := by
  induction entries with
  | nil => contradiction
  | cons head rest ih =>
      rcases List.mem_cons.mp member with same | old
      · subst head
        exact ⟨entry.target, by simp [lookup]⟩
      · by_cases same : head.source = entry.source
        · exact ⟨head.target, by simp [lookup, same]⟩
        · obtain ⟨target, found⟩ := ih old
          exact ⟨target, by simp [lookup, same, found]⟩

theorem entries_length_lt_live_of_missing (graph : SourceGraph Source Label)
    (roots : List Source) {state : CopyState Source}
    (invariant : Invariant graph roots state) {source : Source}
    (sourceLive : source ∈ live graph roots)
    (missing : lookup source state.entries = none) :
    state.entries.length < (live graph roots).card := by
  have absent := lookup_none_not_mem_keys missing
  have unique : (source :: state.entries.map Entry.source).Nodup :=
    List.nodup_cons.mpr ⟨absent, invariant.keys_unique⟩
  have subset : (source :: state.entries.map Entry.source).toFinset ⊆ live graph roots := by
    intro other member
    simp only [List.toFinset_cons, Finset.mem_insert, List.mem_toFinset] at member
    rcases member with rfl | old
    · exact sourceLive
    · obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp old
      subst other
      obtain ⟨target, found⟩ := lookup_of_mem_entries entryMember
      exact invariant.mapped_live found
  have bound := Finset.card_le_card subset
  rw [List.toFinset_card_of_nodup unique] at bound
  simp only [List.length_cons, List.length_map] at bound
  omega

theorem reserveLoop_succeeds (graph : SourceGraph Source Label) (roots : List Source)
    (capacity : Nat) (state : CopyState Source) :
    Invariant graph roots state → (live graph roots).card ≤ capacity →
      ∃ final, reserveLoop graph capacity state = some final := by
  induction state using reserveLoop.induct (graph := graph) (capacity := capacity) with
  | case1 state nonempty source target found ih =>
      intro invariant enough
      obtain ⟨final, result⟩ := ih (skip_invariant graph roots invariant ⟨target, found⟩) enough
      refine ⟨final, ?_⟩
      rw [reserveLoop.eq_def, dif_pos nonempty]
      dsimp only
      rw [found]
      exact result
  | case2 state nonempty source missing available ih =>
      intro invariant enough
      have selectedLive := invariant.pending_live _ (Finset.min'_mem _ nonempty)
      obtain ⟨final, result⟩ :=
        ih (allocate_invariant graph roots invariant selectedLive missing) enough
      refine ⟨final, ?_⟩
      rw [reserveLoop.eq_def, dif_pos nonempty]
      dsimp only
      rw [missing, dif_pos available]
      exact result
  | case3 state nonempty source missing unavailable =>
      intro invariant enough
      have selectedLive := invariant.pending_live _ (Finset.min'_mem _ nonempty)
      have bound := entries_length_lt_live_of_missing graph roots invariant selectedLive missing
      have universeBound : (live graph roots).card ≤ Fintype.card Source :=
        Finset.card_le_univ _
      have nextLength := invariant.next_eq_length
      exfalso
      apply unavailable
      omega
  | case4 state empty =>
      intro invariant enough
      exact ⟨state, by rw [reserveLoop.eq_def, dif_neg empty]⟩

/-- Unique allocated images make the logical relocation injective on its domain. -/
theorem lookup_injective {Source : Type u} [DecidableEq Source]
    {entries : List (Entry Source)} (unique : (entries.map Entry.target).Nodup)
    {source other : Source} {target : Target}
    (sourceFound : lookup source entries = some target)
    (otherFound : lookup other entries = some target) : source = other := by
  induction entries with
  | nil => contradiction
  | cons entry rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      simp only [lookup] at sourceFound otherFound
      split at sourceFound <;> split at otherFound
      next sameSource sameOther => exact sameSource.symm.trans sameOther
      next sameSource differentOther =>
          cases sourceFound
          obtain ⟨old, oldMember, _, image⟩ := lookup_some_mem_entries otherFound
          exact False.elim (unique.1 (List.mem_map.mpr ⟨old, oldMember, image⟩))
      next differentSource sameOther =>
          cases otherFound
          obtain ⟨old, oldMember, _, image⟩ := lookup_some_mem_entries sourceFound
          exact False.elim (unique.1 (List.mem_map.mpr ⟨old, oldMember, image⟩))
      next differentSource differentOther => exact ih unique.2 sourceFound otherFound

/-- Boolean validation that every stored source belongs to the traced live set. -/
def entriesLiveOn (graph : SourceGraph Source Label) (roots : List Source)
    (entries : List (Entry Source)) : Bool :=
  entries.all fun entry => decide (entry.source ∈ live graph roots)

theorem entriesLiveOn_sound (graph : SourceGraph Source Label) (roots : List Source)
    {entries : List (Entry Source)} (checked : entriesLiveOn graph roots entries = true) :
    ∀ entry ∈ entries, entry.source ∈ live graph roots := by
  intro entry member
  have checkedEntry := List.all_eq_true.mp checked entry member
  exact of_decide_eq_true checkedEntry

/-- Boolean totality check used by the executable publication boundary. -/
def totalOn {Source : Type u} [LinearOrder Source]
    (sources : Finset Source) (entries : List (Entry Source)) : Bool :=
  (sources.sort (· ≤ ·)).all fun source => (lookup source entries).isSome

theorem totalOn_sound {Source : Type u} [LinearOrder Source]
    {sources : Finset Source} {entries : List (Entry Source)}
    (total : totalOn sources entries = true) {source : Source} (member : source ∈ sources) :
    ∃ target, lookup source entries = some target := by
  have present := List.all_eq_true.mp total source ((Finset.mem_sort _).mpr member)
  exact Option.isSome_iff_exists.mp present

/-- Look up the reservation using its totality proof.  The proof is irrelevant
to execution; `Option.get` uses the actual stored target. -/
def relocationTarget (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    (source : Source) (sourceLive : source ∈ live graph roots) : Target :=
  (lookup source state.entries).get (Option.isSome_iff_exists.mpr (total source sourceLive))

/-- A proof-independent view of the same relocation map.  Under `total`, every
live source is present, so the default is never observed in the contract. -/
def relocatedOrZero (state : CopyState Source) (source : Source) : Target :=
  (lookup source state.entries).getD ⟨0⟩

theorem lookup_relocationTarget (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    {source : Source} (sourceLive : source ∈ live graph roots) :
    lookup source state.entries = some (relocationTarget graph roots state total source sourceLive) :=
  (Option.some_get _).symm

theorem relocationTarget_eq_relocatedOrZero (graph : SourceGraph Source Label)
    (roots : List Source) (state : CopyState Source)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    {source : Source} (sourceLive : source ∈ live graph roots) :
    relocationTarget graph roots state total source sourceLive = relocatedOrZero state source := by
  unfold relocatedOrZero
  rw [lookup_relocationTarget graph roots state total sourceLive]
  rfl

omit [Fintype Source] in
theorem mem_successors_of_mem_children (graph : SourceGraph Source Label)
    {source child : Source} {label : Label}
    (member : (label, child) ∈ (graph.node source).children) :
    child ∈ successors graph source := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(label, child), member, rfl⟩)

structure TargetNode (Label : Type v) where
  payload : AtomPayload
  children : List (Label × Target)
  deriving DecidableEq, Repr

structure TargetGraph (Label : Type v) where
  nodes : List (Target × TargetNode Label)
  roots : List Target

/-- Finish one reserved node after all reachable children have targets. -/
def completeNode (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    (entry : Entry Source) (entryMember : entry ∈ state.entries) : TargetNode Label :=
  { payload := (graph.node entry.source).payload
    children := (graph.node entry.source).children.attach.map fun edge =>
      (edge.val.1, relocationTarget graph roots state total edge.val.2
        (child_live graph (sourcesLive entry entryMember)
          (mem_successors_of_mem_children graph edge.property))) }

/-- Finish all incomplete edges and transport each root occurrence. -/
def complete (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source) : TargetGraph Label :=
  { nodes := state.entries.attach.map fun entry =>
      (entry.val.target, completeNode graph roots state sourcesLive total entry.val entry.property)
    roots := roots.attach.map fun root =>
      relocationTarget graph roots state total root.val (root_live graph root.property) }

def lookupNode {Label : Type v} (target : Target) :
    List (Target × TargetNode Label) → Option (TargetNode Label)
  | [] => none
  | (key, node) :: rest => if key = target then some node else lookupNode target rest

theorem lookupNode_of_mem_unique {Label : Type v}
    {nodes : List (Target × TargetNode Label)} (unique : (nodes.map Prod.fst).Nodup)
    {pair : Target × TargetNode Label} (member : pair ∈ nodes) :
    lookupNode pair.1 nodes = some pair.2 := by
  induction nodes with
  | nil => contradiction
  | cons head rest ih =>
      simp only [List.map_cons, List.nodup_cons] at unique
      rcases List.mem_cons.mp member with same | old
      · subst head
        simp [lookupNode]
      · by_cases same : head.1 = pair.1
        · exfalso
          apply unique.1
          apply List.mem_map.mpr
          exact ⟨pair, old, same.symm⟩
        · simp only [lookupNode, same, ↓reduceIte]
          exact ih unique.2 old

theorem complete_roots (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    {root : Source} (member : root ∈ roots) :
    ∃ target, lookup root state.entries = some target ∧
      target ∈ (complete graph roots state sourcesLive total).roots := by
  let rootLive := root_live graph member
  refine ⟨relocationTarget graph roots state total root rootLive,
    lookup_relocationTarget graph roots state total rootLive, ?_⟩
  simp only [complete, List.mem_map]
  exact ⟨⟨root, member⟩, List.mem_attach _ _, rfl⟩

/-- The completed target node has the source payload and every ordered labelled
edge, with each child resolved through the same logical relocation map. -/
theorem complete_lookup_relocated (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    (unique : (state.entries.map Entry.target).Nodup)
    {source : Source} {target : Target}
    (found : lookup source state.entries = some target) :
    ∃ node, lookupNode target (complete graph roots state sourcesLive total).nodes = some node ∧
      node.payload = (graph.node source).payload ∧
      ∀ {label : Label} {child : Source}, (label, child) ∈ (graph.node source).children →
        ∃ childTarget, lookup child state.entries = some childTarget ∧
          (label, childTarget) ∈ node.children := by
  obtain ⟨entry, entryMember, sourceEqual, targetEqual⟩ := lookup_some_mem_entries found
  cases sourceEqual
  cases targetEqual
  have keys : (complete graph roots state sourcesLive total).nodes.map Prod.fst =
      state.entries.map Entry.target := by
    simp only [complete, List.map_map]
    change List.map (fun entry : {x // x ∈ state.entries} => entry.val.target)
      state.entries.attach = List.map Entry.target state.entries
    exact List.attach_map_val
  have nodesUnique : (complete graph roots state sourcesLive total).nodes.map Prod.fst |>.Nodup := by
    rw [keys]
    exact unique
  have pairMember :
      (entry.target, completeNode graph roots state sourcesLive total entry entryMember) ∈
        (complete graph roots state sourcesLive total).nodes := by
    simp only [complete, List.mem_map]
    exact ⟨⟨entry, entryMember⟩, List.mem_attach _ _, rfl⟩
  refine ⟨completeNode graph roots state sourcesLive total entry entryMember,
    lookupNode_of_mem_unique nodesUnique pairMember, rfl, ?_⟩
  intro label child childMember
  let childLive : child ∈ live graph roots := child_live graph
    (sourcesLive entry entryMember) (mem_successors_of_mem_children graph childMember)
  refine ⟨relocationTarget graph roots state total child childLive,
    lookup_relocationTarget graph roots state total childLive, ?_⟩
  simp only [completeNode, List.mem_map]
  exact ⟨⟨(label, child), childMember⟩, List.mem_attach _ _, rfl⟩

theorem entries_length_le_live (graph : SourceGraph Source Label) (roots : List Source)
    {state : CopyState Source} (invariant : Invariant graph roots state) :
    state.entries.length ≤ (live graph roots).card := by
  have subset : (state.entries.map Entry.source).toFinset ⊆ live graph roots := by
    intro source member
    obtain ⟨entry, entryMember, equal⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    subst source
    obtain ⟨target, found⟩ := lookup_of_mem_entries entryMember
    exact invariant.mapped_live found
  have bound := Finset.card_le_card subset
  rw [List.toFinset_card_of_nodup invariant.keys_unique] at bound
  simpa only [List.length_map] using bound

theorem lookup_deterministic {Source : Type u} [DecidableEq Source]
    {entries : List (Entry Source)} {source : Source} {first second : Target}
    (firstFound : lookup source entries = some first)
    (secondFound : lookup source entries = some second) : first = second := by
  rw [firstFound] at secondFound
  cases secondFound
  rfl

@[simp] theorem complete_roots_length (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source) :
    (complete graph roots state sourcesLive total).roots.length = roots.length := by
  simp [complete]

@[simp] theorem completeNode_children_length (graph : SourceGraph Source Label)
    (roots : List Source) (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    (entry : Entry Source) (entryMember : entry ∈ state.entries) :
    (completeNode graph roots state sourcesLive total entry entryMember).children.length =
      (graph.node entry.source).children.length := by
  simp [completeNode]

/-- Exact ordered root transport, including duplicate root occurrences. -/
theorem complete_roots_ordered (graph : SourceGraph Source Label) (roots : List Source)
    (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source) :
    (complete graph roots state sourcesLive total).roots = roots.attach.map fun root =>
      relocationTarget graph roots state total root.val (root_live graph root.property) := rfl

/-- Exact ordered child transport.  The source occurrence list is mapped once,
in order; sharing does not deduplicate equal child occurrences. -/
theorem completeNode_ordered_children (graph : SourceGraph Source Label)
    (roots : List Source) (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    (entry : Entry Source) (entryMember : entry ∈ state.entries) :
    (completeNode graph roots state sourcesLive total entry entryMember).children =
      (graph.node entry.source).children.attach.map fun edge =>
        (edge.val.1, relocationTarget graph roots state total edge.val.2
          (child_live graph (sourcesLive entry entryMember)
            (mem_successors_of_mem_children graph edge.property))) := rfl

private theorem attach_map_eq_map {A : Type u} {B : Type v} (items : List A)
    (f : ∀ item, item ∈ items → B) (g : A → B)
    (pointwise : ∀ item member, f item member = g item) :
    items.attach.map (fun item => f item.val item.property) = items.map g := by
  apply List.ext_getElem
  · simp
  · intro index rootsLength mappedLength
    simp only [List.getElem_map, List.getElem_attach]
    exact pointwise _ _

theorem complete_roots_map_relocatedOrZero (graph : SourceGraph Source Label)
    (roots : List Source) (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source) :
    (complete graph roots state sourcesLive total).roots = roots.map (relocatedOrZero state) := by
  rw [complete_roots_ordered]
  apply attach_map_eq_map roots
    (fun root member => relocationTarget graph roots state total root (root_live graph member))
  intro root member
  exact relocationTarget_eq_relocatedOrZero graph roots state total (root_live graph member)

theorem completeNode_children_map_relocatedOrZero (graph : SourceGraph Source Label)
    (roots : List Source) (state : CopyState Source)
    (sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots)
    (total : ∀ source ∈ live graph roots, Mapped state source)
    (entry : Entry Source) (entryMember : entry ∈ state.entries) :
    (completeNode graph roots state sourcesLive total entry entryMember).children =
      (graph.node entry.source).children.map fun edge =>
        (edge.1, relocatedOrZero state edge.2) := by
  rw [completeNode_ordered_children]
  apply attach_map_eq_map (graph.node entry.source).children
    (fun edge member => (edge.1, relocationTarget graph roots state total edge.2
      (child_live graph (sourcesLive entry entryMember)
        (mem_successors_of_mem_children graph member))))
  intro edge member
  rw [relocationTarget_eq_relocatedOrZero graph roots state total
    (child_live graph (sourcesLive entry entryMember)
      (mem_successors_of_mem_children graph member))]

inductive EvacuationFailure where
  | allocation | incompleteRelocation
  deriving DecidableEq, Repr

inductive EvacuationResult (Source : Type u) (Label : Type v) where
  | failed (failure : EvacuationFailure)
  | published (state : CopyState Source) (graph : TargetGraph Label)

/-- Trace semantics determine `live`; copying begins from empty entries.  No
trace-side mark is reused as copy authority.  Failure never returns a graph. -/
def evacuate (graph : SourceGraph Source Label) (roots : List Source) (capacity : Nat) :
    EvacuationResult Source Label :=
  match reserveLoop graph capacity (initialCopy roots) with
  | none => .failed .allocation
  | some state =>
      if sourcesLive : entriesLiveOn graph roots state.entries = true then
        if total : totalOn (live graph roots) state.entries = true then
          .published state (complete graph roots state
            (entriesLiveOn_sound graph roots sourcesLive)
            (fun _source member => totalOn_sound total member))
        else .failed .incompleteRelocation
      else .failed .incompleteRelocation

/-- Observable successful-evacuation contract.  Root and child transport are
exact list equations: order, labels, sharing, and every duplicate occurrence
are preserved by the same lookup-based relocation map. -/
structure PublishedContract (graph : SourceGraph Source Label) (roots : List Source)
    (capacity : Nat) (state : CopyState Source) (target : TargetGraph Label) : Prop where
  exhausted : state.pending = ∅
  total : ∀ source ∈ live graph roots, Mapped state source
  injective : ∀ {source other image},
    lookup source state.entries = some image → lookup other state.entries = some image →
      source = other
  keys_unique : (state.entries.map Entry.source).Nodup
  storage_valid : StorageValid graph state
  targets_bounded : ∀ entry ∈ state.entries, entry.target.index < capacity
  roots_ordered : target.roots = roots.map (relocatedOrZero state)
  nodes_preserved : ∀ {source image}, lookup source state.entries = some image →
    ∃ node, lookupNode image target.nodes = some node ∧
      node.payload = (graph.node source).payload ∧
      node.children = (graph.node source).children.map fun edge =>
        (edge.1, relocatedOrZero state edge.2)

/-- The former exported interface is retained solely for its counterexample:
support plus cardinality does not determine order or per-root multiplicity. -/
structure LegacyPublishedContract (graph : SourceGraph Source Label) (roots : List Source)
    (capacity : Nat) (state : CopyState Source) (target : TargetGraph Label) : Prop where
  exhausted : state.pending = ∅
  total : ∀ source ∈ live graph roots, Mapped state source
  injective : ∀ {source other image},
    lookup source state.entries = some image → lookup other state.entries = some image →
      source = other
  keys_unique : (state.entries.map Entry.source).Nodup
  storage_valid : StorageValid graph state
  targets_bounded : ∀ entry ∈ state.entries, entry.target.index < capacity
  roots_preserved : ∀ root ∈ roots, ∃ image,
    lookup root state.entries = some image ∧ image ∈ target.roots
  root_count : target.roots.length = roots.length
  nodes_preserved : ∀ {source image}, lookup source state.entries = some image →
    ∃ node, lookupNode image target.nodes = some node ∧
      node.payload = (graph.node source).payload ∧
      node.children.length = (graph.node source).children.length ∧
      ∀ {label : Label} {child : Source}, (label, child) ∈ (graph.node source).children →
        ∃ childImage, lookup child state.entries = some childImage ∧
          (label, childImage) ∈ node.children

/-- Composed finite collector theorem.  Sufficient capacity yields an actual
published graph, total injective relocation, storage discipline, and exact
ordered root and labelled-child transport, including duplicate occurrences. -/
theorem trace_reset_evacuate_composes (graph : SourceGraph Source Label)
    (roots : List Source) {capacity : Nat} (enough : (live graph roots).card ≤ capacity) :
    ∃ state target, evacuate graph roots capacity = .published state target ∧
      PublishedContract graph roots capacity state target := by
  obtain ⟨state, reserved⟩ := reserveLoop_succeeds graph roots capacity (initialCopy roots)
    (initialCopy_invariant graph roots) enough
  have invariant : Invariant graph roots state :=
    reserveLoop_invariant graph roots capacity (initialCopy roots)
      (initialCopy_invariant graph roots) state reserved
  have exhausted : state.pending = ∅ :=
    reserveLoop_pending_empty graph capacity (initialCopy roots) state reserved
  have total : ∀ source ∈ live graph roots, Mapped state source := fun source sourceLive =>
    mapped_total_of_exhausted graph roots invariant exhausted sourceLive
  have sourcesLive : ∀ entry ∈ state.entries, entry.source ∈ live graph roots := by
    intro entry entryMember
    obtain ⟨image, found⟩ := lookup_of_mem_entries entryMember
    exact invariant.mapped_live found
  have sourcesLiveCheck : entriesLiveOn graph roots state.entries = true := by
    apply List.all_eq_true.mpr
    intro entry entryMember
    exact decide_eq_true (sourcesLive entry entryMember)
  have totalCheck : totalOn (live graph roots) state.entries = true := by
    apply List.all_eq_true.mpr
    intro source member
    obtain ⟨image, found⟩ := total source ((Finset.mem_sort _).mp member)
    simp [found]
  have nextBound : state.nextTarget ≤ capacity := by
    have lengthBound := entries_length_le_live graph roots invariant
    have nextLength := invariant.next_eq_length
    omega
  refine ⟨state, complete graph roots state sourcesLive total, ?_, ?_⟩
  · unfold evacuate
    rw [reserved]
    dsimp only
    rw [dif_pos sourcesLiveCheck, dif_pos totalCheck]
  · refine ⟨exhausted, total, ?_, invariant.keys_unique, invariant.storage_valid, ?_, ?_, ?_⟩
    · intro source other image sourceFound otherFound
      exact lookup_injective invariant.targets_unique sourceFound otherFound
    · intro entry entryMember
      exact (invariant.target_bound entry entryMember).trans_le nextBound
    · exact complete_roots_map_relocatedOrZero graph roots state sourcesLive total
    · intro source image found
      obtain ⟨node, nodeFound, payload, _⟩ :=
        complete_lookup_relocated graph roots state sourcesLive total invariant.targets_unique found
      refine ⟨node, nodeFound, payload, ?_⟩
      obtain ⟨entry, entryMember, sourceEqual, targetEqual⟩ := lookup_some_mem_entries found
      cases sourceEqual
      cases targetEqual
      have nodeEqual : node = completeNode graph roots state sourcesLive total entry entryMember := by
        have lookupAgain := lookupNode_of_mem_unique (nodes := (complete graph roots state
          sourcesLive total).nodes) (pair := (entry.target,
            completeNode graph roots state sourcesLive total entry entryMember)) ?_ ?_
        · rw [nodeFound] at lookupAgain
          cases lookupAgain
          rfl
        · have keys : (complete graph roots state sourcesLive total).nodes.map Prod.fst =
              state.entries.map Entry.target := by
            simp only [complete, List.map_map]
            change List.map (fun item : {x // x ∈ state.entries} => item.val.target)
              state.entries.attach = List.map Entry.target state.entries
            exact List.attach_map_val
          rw [keys]
          exact invariant.targets_unique
        · simp only [complete, List.mem_map]
          exact ⟨⟨entry, entryMember⟩, List.mem_attach _ _, rfl⟩
      rw [nodeEqual]
      exact completeNode_children_map_relocatedOrZero graph roots state sourcesLive total entry entryMember

theorem reserve_failure_publishes_no_graph (graph : SourceGraph Source Label)
    (roots : List Source) (capacity : Nat)
    (failed : reserveLoop graph capacity (initialCopy roots) = none) :
    evacuate graph roots capacity = .failed .allocation := by
  unfold evacuate
  rw [failed]

namespace Controls

/-- Historical storage mistake: use the inline field even when it owns spelling. -/
def oldEntry (source : Nat) (target : Target) (_payload : AtomPayload) : Entry Nat :=
  ⟨source, target, .inline⟩

theorem old_spelled_symbol_uses_payload_field :
    (oldEntry 0 ⟨99⟩ (.spelledSymbol "alpha")).storage = .inline ∧
      requiredStorage (.spelledSymbol "alpha") = .sideTable := by
  exact ⟨rfl, rfl⟩

def updateExisting {Source : Type u} [DecidableEq Source]
    (source : Source) (target : Target) : List (Entry Source) → Option (List (Entry Source))
  | [] => none
  | entry :: rest =>
      if entry.source = source then
        some (⟨source, target, entry.storage⟩ :: rest)
      else
        Option.map (fun tail => entry :: tail) (updateExisting source target rest)

theorem update_existing_fails_after_reset {Source : Type u} [DecidableEq Source]
    (entries : List (Entry Source)) (source : Source) (target : Target) :
    updateExisting source target (reset entries) = none := rfl

def nonemptyTable : List (Entry Nat) := [⟨0, ⟨0⟩, .sideTable⟩]

theorem lookup_missing_in_nonempty_table :
    nonemptyTable ≠ [] ∧ lookup 1 nonemptyTable = none := by
  exact ⟨by simp [nonemptyTable], rfl⟩

/-- Root 0 has a repeated reference to 1, references to two different spelled
symbols 1 and 2, and shared edges to 3.  Node 3 closes a cycle back to 0. -/
def regressionGraph : SourceGraph (Fin 5) String where
  node source :=
    match source.val with
    | 0 => ⟨.expression,
        [("repeat-first", 1), ("repeat-second", 1), ("second-spelled", 2),
          ("shared-first", 3), ("numbered", 4)]⟩
    | 1 => ⟨.spelledSymbol "alpha", [("shared-second", 3)]⟩
    | 2 => ⟨.spelledSymbol "beta", []⟩
    | 3 => ⟨.variable 7, [("cycle", 0)]⟩
    | _ => ⟨.numberedSymbol 42, [("shared-third", 3)]⟩

theorem regression_live_all : live regressionGraph [0] = Finset.univ := by
  decide

theorem reset_does_not_copy_live_mark :
    (0 : Fin 5) ∈ live regressionGraph [0] ∧
      lookup (0 : Nat) (reset nonemptyTable) = none := by
  constructor
  · rw [regression_live_all]
    exact Finset.mem_univ _
  · rfl

theorem two_distinct_spelled_symbols_are_live :
    (regressionGraph.node 1).payload = .spelledSymbol "alpha" ∧
      (regressionGraph.node 2).payload = .spelledSymbol "beta" ∧
      (1 : Fin 5) ∈ live regressionGraph [0] ∧ (2 : Fin 5) ∈ live regressionGraph [0] := by
  rw [regression_live_all]
  exact ⟨rfl, rfl, Finset.mem_univ _, Finset.mem_univ _⟩

theorem repaired_regression_publishes :
    ∃ state target, evacuate regressionGraph [0] 5 = .published state target ∧
      PublishedContract regressionGraph [0] 5 state target := by
  apply trace_reset_evacuate_composes
  rw [regression_live_all]
  decide

theorem empty_roots_publish_empty_relocation :
    ∃ state target, evacuate regressionGraph [] 0 = .published state target ∧
      state.entries = [] ∧ target.roots = [] := by
  obtain ⟨state, target, published, contract⟩ :=
    trace_reset_evacuate_composes regressionGraph [] (capacity := 0) (by decide)
  refine ⟨state, target, published, ?_, by simpa using contract.roots_ordered⟩
  cases stateEntries : state.entries with
  | nil => rfl
  | cons entry rest =>
      have bound := contract.targets_bounded entry (by simp [stateEntries])
      omega

theorem zero_capacity_allocation_failure :
    evacuate regressionGraph [0] 0 = .failed .allocation := by
  apply reserve_failure_publishes_no_graph
  rw [reserveLoop.eq_def]
  simp [initialCopy]
  rfl

end Controls

#print axioms reserveLoop_succeeds
#print axioms mapped_total_of_exhausted
#print axioms lookup_injective
#print axioms complete_lookup_relocated
#print axioms complete_roots_ordered
#print axioms completeNode_ordered_children
#print axioms complete_roots_map_relocatedOrZero
#print axioms completeNode_children_map_relocatedOrZero
#print axioms trace_reset_evacuate_composes
#print axioms reserve_failure_publishes_no_graph
#print axioms Controls.repaired_regression_publishes
#print axioms Controls.zero_capacity_allocation_failure

end Mettapedia.Machines.CollectorEvacuation
