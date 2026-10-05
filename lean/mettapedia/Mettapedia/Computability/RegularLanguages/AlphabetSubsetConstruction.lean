import Mettapedia.Computability.RegularLanguages.IntervalClasses

/-!
# State-relative observations of a membership alphabet

An interval NFA has two independent views of its consuming edges: direct
pointwise membership, and execution over a vector of membership bits. The
second preserves the ordered enabled-edge list, not merely the set of target
states. Consequently annotations and their first conflict are preserved too.

A reusable observation is keyed by both the active state and the membership
vector. The controls show why omitting either state, literal refinement or
annotations is unsound. These laws do not certify the native event sweep,
allocator, hash table, epsilon closure or bounded DFA worklist.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.RegularLanguages.AlphabetSubsetConstruction

open IntervalClasses

structure Edge where
  id : Nat
  source : Nat
  target : Nat
  annotation : Nat
  ranges : List Interval
  deriving DecidableEq, Repr

def memberBit (ranges : List Interval) (point : Nat) : Bool :=
  ranges.any fun range => decide (range.low ≤ point ∧ point ≤ range.high)

theorem memberBit_spec (ranges : List Interval) (point : Nat) :
    memberBit ranges point = true ↔ Contains ranges point := by
  simp [memberBit, Contains, Interval.Contains]

def profile (edges : List Edge) (point : Nat) : List Bool :=
  edges.map fun edge => memberBit edge.ranges point

def enabledAt (active : List Nat) (edges : List Edge) (point : Nat) : List Edge :=
  edges.filter fun edge => active.contains edge.source && memberBit edge.ranges point

def enabledByBits (active : List Nat) : List Edge → List Bool → List Edge
  | edge :: edges, bit :: bits =>
    if active.contains edge.source && bit then
      edge :: enabledByBits active edges bits
    else enabledByBits active edges bits
  | _, _ => []

theorem enabledByBits_profile (active : List Nat) (edges : List Edge) (point : Nat) :
    enabledByBits active edges (profile edges point) = enabledAt active edges point := by
  induction edges with
  | nil => rfl
  | cons edge edges ih =>
    simp only [profile, List.map_cons, enabledByBits, enabledAt, List.filter_cons]
    split <;> simp_all [enabledAt, profile]

inductive AnnotationResult where
  | empty
  | action (annotation : Nat)
  | conflict (previousEdge previousAnnotation nextEdge nextAnnotation : Nat)
  deriving DecidableEq, Repr

def scanAnnotations : Option (Nat × Nat) → List Edge → AnnotationResult
  | none, [] => .empty
  | some previous, [] => .action previous.2
  | none, edge :: edges => scanAnnotations (some (edge.id, edge.annotation)) edges
  | some previous, edge :: edges =>
    if previous.2 = edge.annotation then
      scanAnnotations (some (edge.id, edge.annotation)) edges
    else .conflict previous.1 previous.2 edge.id edge.annotation

structure Observation where
  targets : List Nat
  annotations : AnnotationResult
  deriving DecidableEq, Repr

def observeEdges (edges : List Edge) : Observation :=
  ⟨edges.map Edge.target, scanAnnotations none edges⟩

def observeAt (active : List Nat) (edges : List Edge) (point : Nat) : Observation :=
  observeEdges (enabledAt active edges point)

def observeBits (active : List Nat) (edges : List Edge) (bits : List Bool) : Observation :=
  observeEdges (enabledByBits active edges bits)

theorem observeBits_profile (active : List Nat) (edges : List Edge) (point : Nat) :
    observeBits active edges (profile edges point) = observeAt active edges point := by
  rw [observeBits, enabledByBits_profile]
  rfl

theorem same_profile_same_observation (active : List Nat) (edges : List Edge)
    (left right : Nat) (same : profile edges left = profile edges right) :
    observeAt active edges left = observeAt active edges right := by
  rw [← observeBits_profile active edges left, ← observeBits_profile active edges right, same]

/-- Applying the same epsilon-closure computation to the preserved targets
keeps its result. This does not assume or prove correctness of that closure. -/
theorem closed_targets_agree {State : Type} (close : List Nat → State)
    (active : List Nat) (edges : List Edge) (point : Nat) :
    close (observeBits active edges (profile edges point)).targets =
      close (observeAt active edges point).targets := by
  rw [observeBits_profile]

def subsetWordCount (states : Nat) : Nat :=
  states / 64 + if states % 64 = 0 then 0 else 1

theorem subsetWordCount_covers (states : Nat) : states ≤ 64 * subsetWordCount states := by
  have remainder := Nat.mod_lt states (by decide : 0 < 64)
  have decomposition := Nat.mod_add_div states 64
  simp only [subsetWordCount]
  split_ifs <;> omega

theorem subsetWordCount_least (states words : Nat) (covers : states ≤ 64 * words) :
    subsetWordCount states ≤ words := by
  have remainder := Nat.mod_lt states (by decide : 0 < 64)
  have decomposition := Nat.mod_add_div states 64
  simp only [subsetWordCount]
  split_ifs <;> omega

theorem subsetWordCount_positive (states : Nat) (nonempty : 0 < states) :
    0 < subsetWordCount states := by
  have covers := subsetWordCount_covers states
  omega

theorem subsetWordCount_uint32_max : subsetWordCount 4294967295 = 67108864 := by decide

abbrev Key := List Nat × List Bool

def key (active : List Nat) (edges : List Edge) (point : Nat) : Key :=
  (active, profile edges point)

theorem key_sound (edges : List Edge) (leftActive rightActive : List Nat)
    (left right : Nat) (same : key leftActive edges left = key rightActive edges right) :
    observeAt leftActive edges left = observeAt rightActive edges right := by
  obtain ⟨states, letters⟩ := Prod.mk.inj same
  subst rightActive
  exact same_profile_same_observation leftActive edges left right letters

abbrev Cache := List (Key × Observation)

def Coherent (edges : List Edge) (cache : Cache) : Prop :=
  ∀ entry ∈ cache, ∀ active point,
    entry.1 = key active edges point → entry.2 = observeAt active edges point

theorem empty_cache_coherent (edges : List Edge) : Coherent edges [] := by
  simp [Coherent]

def insert (active : List Nat) (edges : List Edge) (point : Nat) (cache : Cache) : Cache :=
  (key active edges point, observeBits active edges (profile edges point)) :: cache

theorem insert_coherent (edges : List Edge) (cache : Cache) (coherent : Coherent edges cache)
    (active : List Nat) (point : Nat) : Coherent edges (insert active edges point cache) := by
  intro entry member otherActive otherPoint same
  rcases List.mem_cons.mp member with inserted | old
  · subst entry
    rw [observeBits_profile]
    exact key_sound edges active otherActive point otherPoint same
  · exact coherent entry old otherActive otherPoint same

private def broad : Edge := ⟨0, 0, 1, 7, [⟨97, 98⟩]⟩
private def literal : Edge := ⟨1, 0, 2, 7, [⟨97, 97⟩]⟩

theorem broad_profile_coalesces : profile [broad] 97 = profile [broad] 98 := by decide

theorem literal_refines : profile [broad, literal] 97 ≠ profile [broad, literal] 98 := by decide

theorem omitted_literal_changes_observation :
    observeAt [0] [broad, literal] 97 ≠ observeAt [0] [broad, literal] 98 := by decide

theorem state_is_required :
    profile [broad] 97 = profile [broad] 98 ∧
      observeAt [0] [broad] 97 ≠ observeAt [1] [broad] 98 := by decide

theorem first_annotation_conflict :
    scanAnnotations none [broad, {literal with annotation := 8}, {literal with id := 2}] =
      .conflict 0 7 1 8 := by decide

theorem target_equivalence_does_not_preserve_annotations :
    (observeAt [0] [broad] 97).targets =
      (observeAt [0] [{broad with annotation := 8}] 97).targets ∧
    (observeAt [0] [broad] 97).annotations ≠
      (observeAt [0] [{broad with annotation := 8}] 97).annotations := by decide

theorem repeated_targets_are_preserved :
    (observeAt [0] [broad, {broad with id := 1}] 97).targets = [1, 1] := by decide

end Mettapedia.Computability.RegularLanguages.AlphabetSubsetConstruction
