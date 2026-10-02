import Mettapedia.Logic.Saturation.RecursiveSynthesis
import Mathlib.Combinatorics.Quiver.Path
import Mathlib.Data.List.Basic
import Mathlib.Data.List.Nodup

/-!
# Witness-producing recursion over an ordered finite rule frontier

Finite outgoing rule inventories generate actual quiver paths, retaining
each intermediate goal and each chosen rule witness. The recursion uses the
public primitive-recursion program and list `flatMap`/`map`, preserving order
and duplicate occurrences rather than quotienting answers by their endpoint.

This is the ground path/chaining fragment of bounded proof production.
Universally sound outputs follow from local rule interpretation, whereas
coverage of every rule and absence of pruning are separate completeness
conditions. Multiplicity is exact: when no inventory lists a rule twice the
frontier lists each supported path of the given length once, and a repeated
inventory entry repeats its witnesses. Neither a native encoding of the
extension branch nor a CeTTa execution comparison is asserted here.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Saturation.RecursivePathSynthesis

open Quiver

universe u v w

variable {Goal : Type u} [Quiver.{v} Goal]

/-- A finite ordered inventory can contain distinct rules with the same
endpoint and repeated occurrences of the same rule. -/
abbrev Inventory (Goal : Type u) [Quiver.{v} Goal] :=
  (source : Goal) → List ((target : Goal) × (source ⟶ target))

/-- Mathlib's path retains every selected rule; the endpoint is its index. -/
abbrev Witness (root : Goal) := (target : Goal) × Path root target

def extend (rules : Inventory Goal) {root : Goal} (frontier : List (Witness root)) :
    List (Witness root) :=
  frontier.flatMap fun earlier =>
    (rules earlier.1).map fun rule => ⟨rule.1, earlier.2.cons rule.2⟩

/-- Exact-depth production, with no implicit endpoint deduplication. -/
def produce (rules : Inventory Goal) (root : Goal) : Nat → List (Witness root) :=
  RecursiveSynthesis.primitiveRecursion [⟨root, .nil⟩]
    (fun _ frontier => extend rules frontier)

@[simp] theorem produce_zero (rules : Inventory Goal) (root : Goal) :
    produce rules root 0 = [⟨root, .nil⟩] := rfl

@[simp] theorem produce_succ (rules : Inventory Goal) (root : Goal) (depth : Nat) :
    produce rules root (depth + 1) = extend rules (produce rules root depth) := rfl

/-- Every path edge must occur in the actual outgoing rule inventory. -/
inductive Supported (rules : Inventory Goal) (root : Goal) :
    {target : Goal} → Path root target → Prop where
  | nil : Supported rules root .nil
  | cons {middle target : Goal} {earlier : Path root middle} {rule : middle ⟶ target}
      (previous : Supported rules root earlier)
      (listed : (⟨target, rule⟩ : (target : Goal) × (middle ⟶ target)) ∈ rules middle) :
      Supported rules root (earlier.cons rule)

/-- Induction certifies the actual output of the recursive producer. The
specification is not supplied as a premise for the completed program. -/
theorem produce_supported (rules : Inventory Goal) (root : Goal) :
    ∀ depth, ∀ witness ∈ produce rules root depth,
      Supported rules root witness.2 ∧ witness.2.length = depth := by
  unfold produce
  apply RecursiveSynthesis.primitiveRecursion_correct
    (fun depth (frontier : List (Witness root)) => ∀ witness ∈ frontier,
      Supported rules root witness.2 ∧ witness.2.length = depth)
  · intro witness member
    have same : witness = ⟨root, .nil⟩ := by simpa only [List.mem_singleton] using member
    subst witness
    exact ⟨.nil, rfl⟩
  · intro depth frontier certified witness member
    obtain ⟨earlier, earlierListed, ruleMember⟩ := List.mem_flatMap.mp member
    obtain ⟨rule, listed, rfl⟩ := List.mem_map.mp ruleMember
    obtain ⟨previous, length⟩ := certified earlier earlierListed
    exact ⟨.cons previous listed, congrArg Nat.succ length⟩

/-- Every supported path is generated at its own finite length. Cycles do
not compromise this bounded statement. -/
theorem supported_generated (rules : Inventory Goal) (root : Goal)
    {target : Goal} {path : Path root target} (supported : Supported rules root path) :
    (⟨target, path⟩ : Witness root) ∈ produce rules root path.length := by
  induction supported with
  | nil => simp only [Path.length_nil, produce_zero, List.mem_singleton]
  | @cons middle target earlier rule previous listed ih =>
      apply List.mem_flatMap.mpr
      exact ⟨⟨middle, earlier⟩, ih, List.mem_map.mpr ⟨⟨target, rule⟩, listed, rfl⟩⟩

theorem generated_iff (rules : Inventory Goal) (root : Goal) (depth : Nat)
    {target : Goal} (path : Path root target) :
    (⟨target, path⟩ : Witness root) ∈ produce rules root depth ↔
      Supported rules root path ∧ path.length = depth := by
  constructor
  · exact produce_supported rules root depth _
  · rintro ⟨supported, rfl⟩
    exact supported_generated rules root supported

/-- Completeness for all quiver paths needs an independently complete
inventory; merely sound rule implementations are insufficient. -/
theorem all_paths_supported (rules : Inventory Goal)
    (covers : ∀ source target (rule : source ⟶ target),
      (⟨target, rule⟩ : (target : Goal) × (source ⟶ target)) ∈ rules source)
    {root target : Goal} (path : Path root target) : Supported rules root path := by
  induction path with
  | nil => exact .nil
  | cons earlier rule ih => exact .cons ih (covers _ _ rule)

theorem produce_complete (rules : Inventory Goal)
    (covers : ∀ source target (rule : source ⟶ target),
      (⟨target, rule⟩ : (target : Goal) × (source ⟶ target)) ∈ rules source)
    {root target : Goal} (path : Path root target) :
    (⟨target, path⟩ : Witness root) ∈ produce rules root path.length :=
  supported_generated rules root (all_paths_supported rules covers path)

/-- An extended witness determines the witness it extends and the rule used. -/
theorem extension_injective {root : Goal} {first second : Witness root}
    {firstRule : (target : Goal) × (first.1 ⟶ target)}
    {secondRule : (target : Goal) × (second.1 ⟶ target)}
    (same : (⟨firstRule.1, first.2.cons firstRule.2⟩ : Witness root) =
      ⟨secondRule.1, second.2.cons secondRule.2⟩) :
    first = second ∧ HEq firstRule secondRule := by
  obtain ⟨firstMiddle, firstPath⟩ := first
  obtain ⟨secondMiddle, secondPath⟩ := second
  obtain ⟨firstTarget, firstEdge⟩ := firstRule
  obtain ⟨secondTarget, secondEdge⟩ := secondRule
  obtain ⟨rfl, paths⟩ := Sigma.mk.inj same
  have paths := eq_of_heq paths
  obtain rfl := Path.obj_eq_of_cons_eq_cons paths
  obtain rfl := eq_of_heq (Path.heq_of_cons_eq_cons paths)
  obtain rfl := eq_of_heq (Path.hom_heq_of_cons_eq_cons paths)
  exact ⟨rfl, HEq.rfl⟩

/-- Extending a frontier without repetitions by inventories without
repetitions gives a frontier without repetitions. -/
theorem extend_nodup (rules : Inventory Goal)
    (duplicateFree : ∀ source, (rules source).Nodup) {root : Goal}
    {frontier : List (Witness root)} (distinct : frontier.Nodup) :
    (extend rules frontier).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun earlier _ => ?_, distinct.imp ?_⟩
  · refine (duplicateFree earlier.1).map fun firstRule secondRule same => ?_
    exact eq_of_heq (extension_injective same).2
  · intro first second different
    refine List.disjoint_left.mpr fun witness fromFirst fromSecond => different ?_
    obtain ⟨firstRule, _, rfl⟩ := List.mem_map.mp fromFirst
    obtain ⟨secondRule, _, same⟩ := List.mem_map.mp fromSecond
    exact ((extension_injective same).1).symm

/-- **Exact multiplicity.**  When no inventory lists a rule twice, no witness
is produced twice.  With `generated_iff`, the frontier at a depth lists each
supported path of that length exactly once. -/
theorem produce_nodup (rules : Inventory Goal)
    (duplicateFree : ∀ source, (rules source).Nodup) (root : Goal) :
    ∀ depth, (produce rules root depth).Nodup
  | 0 => List.nodup_singleton _
  | depth + 1 => extend_nodup rules duplicateFree (produce_nodup rules duplicateFree root depth)

/-- **The frontier enumerates the paths.**  When the inventories list every
rule and list none twice, the frontier at a depth is a list without
repetitions of exactly the paths of that length. -/
theorem produce_enumerates (rules : Inventory Goal)
    (covers : ∀ source target (rule : source ⟶ target),
      (⟨target, rule⟩ : (target : Goal) × (source ⟶ target)) ∈ rules source)
    (duplicateFree : ∀ source, (rules source).Nodup) (root : Goal) (depth : Nat) :
    (produce rules root depth).Nodup ∧
      ∀ {target : Goal} (path : Path root target),
        (⟨target, path⟩ : Witness root) ∈ produce rules root depth ↔ path.length = depth :=
  ⟨produce_nodup rules duplicateFree root depth, fun path =>
    (generated_iff rules root depth path).trans
      ⟨fun supported => supported.2,
        fun length => ⟨all_paths_supported rules covers path, length⟩⟩⟩

variable {Meaning : Type w} (denote : Goal → Meaning) (relation : Meaning → Meaning → Prop)

/-- Local rule correctness composes into the semantic meaning of an actual
retained path, with every intermediate state still available. -/
theorem path_sound
    (ruleSound : ∀ source target (_rule : source ⟶ target),
      relation (denote source) (denote target))
    {root target : Goal} (path : Path root target) :
    Relation.ReflTransGen relation (denote root) (denote target) := by
  induction path with
  | nil => exact .refl
  | cons earlier rule ih => exact ih.tail (ruleSound _ _ rule)

/-- Only inventoried rule occurrences need a semantic certificate. An
unused arrow in the ambient quiver imposes no interpretation obligation. -/
theorem supported_sound (rules : Inventory Goal)
    (ruleSound : ∀ source target (rule : source ⟶ target),
      (⟨target, rule⟩ : (target : Goal) × (source ⟶ target)) ∈ rules source →
        relation (denote source) (denote target))
    {root target : Goal} {path : Path root target}
    (supported : Supported rules root path) :
    Relation.ReflTransGen relation (denote root) (denote target) := by
  induction supported with
  | nil => exact .refl
  | cons _ listed ih => exact ih.tail (ruleSound _ _ _ listed)

theorem produced_sound (rules : Inventory Goal)
    (ruleSound : ∀ source target (rule : source ⟶ target),
      (⟨target, rule⟩ : (target : Goal) × (source ⟶ target)) ∈ rules source →
        relation (denote source) (denote target))
    (root : Goal) (depth : Nat) (witness : Witness root)
    (generated : witness ∈ produce rules root depth) :
    Supported rules root witness.2 ∧ witness.2.length = depth ∧
      Relation.ReflTransGen relation (denote root) (denote witness.1) :=
  ⟨(produce_supported rules root depth witness generated).1,
    (produce_supported rules root depth witness generated).2,
    supported_sound denote relation rules ruleSound
      (produce_supported rules root depth witness generated).1⟩

/-- Filtering only removes produced occurrences, so it preserves soundness.
This statement intentionally supplies no completeness or multiplicity law. -/
theorem filtered_sound (rules : Inventory Goal)
    (ruleSound : ∀ source target (rule : source ⟶ target),
      (⟨target, rule⟩ : (target : Goal) × (source ⟶ target)) ∈ rules source →
        relation (denote source) (denote target))
    (root : Goal) (depth : Nat) (keep : Witness root → Bool) (witness : Witness root)
    (retained : witness ∈ (produce rules root depth).filter keep) :
    Supported rules root witness.2 ∧ witness.2.length = depth ∧
      Relation.ReflTransGen relation (denote root) (denote witness.1) :=
  produced_sound denote relation rules ruleSound root depth witness (List.mem_filter.mp retained).1

namespace CalendarControl

inductive Month | january | february | march
  deriving DecidableEq, Repr

/-- Different rule witnesses may establish the same month relation. -/
inductive Rule : Month → Month → Type where
  | janFeb (label : Bool) : Rule .january .february
  | febMar : Rule .february .march

instance : Quiver Month where Hom := Rule

def rules : Inventory Month
  | .january => [⟨.february, .janFeb false⟩, ⟨.february, .janFeb true⟩]
  | .february => [⟨.march, .febMar⟩]
  | .march => []

def proof (label : Bool) : Path Month.january Month.march :=
  (Path.nil.cons (Rule.janFeb label)).cons Rule.febMar

theorem inventory_covers : ∀ source target (rule : source ⟶ target),
    (⟨target, rule⟩ : (target : Month) × (source ⟶ target)) ∈ rules source := by
  intro source target rule
  cases rule with
  | janFeb label => cases label <;> simp [rules]
  | febMar => simp [rules]

def ordinal : Month → Nat
  | .january => 0
  | .february => 1
  | .march => 2

theorem rules_meaning (source target : Month) (rule : source ⟶ target) :
    ordinal source ≤ ordinal target := by
  cases rule <;> decide

/-- Every generated proof establishes the intended month precedence, from
every root and at every depth, not just the two-step examples below.  From
January the precedence holds of every month, so it is the other roots that
constrain the endpoint: see `january_not_produced_from_february`. -/
theorem calendar_sound (root : Month) (depth : Nat) (witness : Witness root)
    (generated : witness ∈ produce rules root depth) :
    Supported rules root witness.2 ∧ witness.2.length = depth ∧
      Relation.ReflTransGen (· ≤ ·) (ordinal root) (ordinal witness.1) :=
  produced_sound ordinal (· ≤ ·) rules (fun source target rule _ => rules_meaning source target rule)
    root depth witness generated

private theorem le_of_precedence {first last : Nat}
    (chain : Relation.ReflTransGen (· ≤ ·) first last) : first ≤ last := by
  induction chain with
  | refl => exact Nat.le_refl _
  | tail _ step earlier => exact Nat.le_trans earlier step

/-- Soundness excludes an endpoint: no proof produced from February, at any
depth, ends in January. -/
theorem january_not_produced_from_february (depth : Nat) (witness : Witness Month.february)
    (generated : witness ∈ produce rules .february depth) : witness.1 ≠ .january := by
  intro same
  have precedes : ordinal Month.february ≤ ordinal witness.1 :=
    le_of_precedence (calendar_sound .february depth witness generated).2.2
  rw [same] at precedes
  exact absurd precedes (by decide)

theorem inventory_duplicateFree : ∀ source, (rules source).Nodup := by
  intro source
  cases source
  · refine List.nodup_cons.mpr ⟨fun member => ?_, List.nodup_singleton _⟩
    cases eq_of_heq (Sigma.mk.inj (List.mem_singleton.mp member)).2
  · exact List.nodup_singleton _
  · exact List.nodup_nil

theorem actual_frontier : produce rules .january 2 =
    [⟨.march, proof false⟩, ⟨.march, proof true⟩] := rfl

theorem proofs_distinct : proof false ≠ proof true := by
  intro same
  have prefixes := eq_of_heq (Path.heq_of_cons_eq_cons same)
  have edges := eq_of_heq (Path.hom_heq_of_cons_eq_cons prefixes)
  cases edges

/-- Collapsing to endpoints loses the distinction between the two proofs. -/
theorem endpoints_coincide :
    (produce rules .january 2).map Sigma.fst = [.march, .march] := rfl

def duplicateRules : Inventory Month
  | .january => [⟨.february, .janFeb false⟩, ⟨.february, .janFeb false⟩]
  | .february => [⟨.march, .febMar⟩]
  | .march => []

theorem duplicate_occurrences_retained :
    produce duplicateRules .january 2 = [⟨.march, proof false⟩, ⟨.march, proof false⟩] := rfl

/-- The calendar inventory lists every rule once, so at every depth and from
every root the frontier lists each proof of that length once. -/
theorem calendar_enumerates (root : Month) (depth : Nat) :
    (produce rules root depth).Nodup ∧
      ∀ {target : Month} (path : Path root target),
        (⟨target, path⟩ : Witness root) ∈ produce rules root depth ↔ path.length = depth :=
  produce_enumerates rules inventory_covers inventory_duplicateFree root depth

/-- The hypothesis of `produce_nodup` is needed: an inventory that lists a
rule twice produces its proof twice. -/
theorem duplicated_inventory_repeats_proofs :
    ¬ (∀ source, (duplicateRules source).Nodup) ∧
      ¬ (produce duplicateRules .january 2).Nodup := by
  constructor
  · intro distinct
    exact absurd (distinct .january) (by simp [duplicateRules])
  · rw [duplicate_occurrences_retained]
    simp

def pathLabel : {source target : Month} → Path source target → Bool
  | _, _, .nil => false
  | _, _, .cons earlier rule =>
      match rule with
      | .janFeb label => label
      | .febMar => pathLabel earlier

def selectTrue (witness : Witness Month.january) : Bool := pathLabel witness.2

theorem selective_pruning :
    (produce rules .january 2).filter selectTrue = [⟨.march, proof true⟩] := by
  have falseLabel : selectTrue ⟨.march, proof false⟩ = false := by
    simp only [selectTrue, proof, pathLabel]
  have trueLabel : selectTrue ⟨.march, proof true⟩ = true := by
    simp only [selectTrue, proof, pathLabel]
  rw [actual_frontier]
  simp only [List.filter_cons, falseLabel, trueLabel, List.filter_nil,
    Bool.false_eq_true, if_false, if_true]

/-- Endpoint support can survive pruning while witness multiplicity changes. -/
theorem pruning_preserves_endpoints (target : Month) :
    (∃ witness ∈ (produce rules .january 2).filter selectTrue, witness.1 = target) ↔
      ∃ witness ∈ produce rules .january 2, witness.1 = target := by
  rw [selective_pruning, actual_frontier]
  simp

theorem pruning_changes_multiplicity :
    ((produce rules .january 2).filter selectTrue).length = 1 ∧
      (produce rules .january 2).length = 2 := by
  rw [selective_pruning, actual_frontier]
  exact ⟨rfl, rfl⟩

theorem pruning_can_lose_completeness :
    (⟨.march, proof false⟩ : Witness .january) ∈ produce rules .january 2 ∧
      (produce rules .january 2).filter (fun _ => false) = [] := by
  rw [actual_frontier]
  constructor
  · exact List.mem_cons_self
  · simp

/-- The selective filter keeps the endpoint and loses a supported proof of
it: completeness for proofs fails while completeness for endpoints holds. -/
theorem selective_pruning_loses_a_proof :
    Supported rules .january (proof false) ∧
      (⟨.march, proof false⟩ : Witness .january) ∉
        (produce rules .january 2).filter selectTrue := by
  constructor
  · exact ((generated_iff rules .january 2 (proof false)).mp
      (by rw [actual_frontier]; exact List.mem_cons_self)).1
  · rw [selective_pruning]
    intro member
    exact proofs_distinct (eq_of_heq (Sigma.mk.inj (List.mem_singleton.mp member)).2)

end CalendarControl

end Mettapedia.Logic.Saturation.RecursivePathSynthesis
