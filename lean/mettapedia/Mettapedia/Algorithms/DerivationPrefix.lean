import Mettapedia.Algorithms.LazyRankFamilies
import Mathlib.Data.List.Perm.Basic

/-!
# Finite derivation prefixes and truncating child caches

A certified prefix is sound, distinct and ordered. If an independent source
derivation is omitted, the cache has its full requested size and every cached
derivation is no dearer. The source is a predicate, not an enumeration passed
to the implementation.

Two child caches of size at most k suffice for selecting k binary parent
derivations with additive costs. An omitted child supplies k distinct cheap
replacements. This dominance argument is the reason child caches may be
truncated; it is not assumed as an algorithm's optimality condition.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.DerivationPrefix

variable {Value Left Right : Type*}

structure Correct (requested : Nat) (cost : Value → Nat) (source : Value → Prop)
    (cached : List Value) : Prop where
  distinct : cached.Nodup
  sound : ∀ value ∈ cached, source value
  ordered : cached.Pairwise (fun first second => cost first ≤ cost second)
  bounded : cached.length ≤ requested
  omitted : ∀ value, source value → value ∉ cached →
    cached.length = requested ∧ ∀ selected ∈ cached, cost selected ≤ cost value

theorem graph_prefix_correct {Node : Type} [DecidableEq Node]
    (graph : MonotoneRankEnumeration.Graph Node)
    (increasing : MonotoneRankEnumeration.Monotone graph) (roots : List Node)
    (allReachable : ∀ node, MonotoneRankEnumeration.Source graph roots node)
    (requested : Nat) :
    Correct requested graph.cost (fun _ => True)
      ((MonotoneRankEnumeration.demandMachine graph requested).runSlice requested
        (MonotoneRankEnumeration.initial roots)).1.published := by
  classical
  let result := (MonotoneRankEnumeration.demandMachine graph requested).runSlice requested
    (MonotoneRankEnumeration.initial roots)
  have projection := congrArg Prod.fst
    (MonotoneRankEnumeration.demand_is_prefix graph requested requested
      (MonotoneRankEnumeration.initial roots))
  change result.1 = MonotoneRankEnumeration.run graph result.2
    (MonotoneRankEnumeration.initial roots) at projection
  have valid := MonotoneRankEnumeration.run_invariant graph roots result.2 _
    (MonotoneRankEnumeration.initial_invariant graph roots)
  have best := MonotoneRankEnumeration.run_best graph increasing roots result.2
  have closedOrFull := MonotoneRankEnumeration.demand_allowance_suffices graph requested
    requested (MonotoneRankEnumeration.initial roots)
    (by simp [MonotoneRankEnumeration.initial])
    (by simp [MonotoneRankEnumeration.initial])
  change result.1.published.length = requested ∨ result.1.frontier = [] at closedOrFull
  refine ⟨?_, fun _ _ => trivial, ?_, ?_, ?_⟩
  · rw [projection]
    exact (List.nodup_append.mp valid.distinct).1
  · rw [projection]
    exact best.1
  · exact MonotoneRankEnumeration.demand_no_overshoot graph requested requested _
      (by simp [MonotoneRankEnumeration.initial])
  · intro node _ absent
    refine ⟨?_, ?_⟩
    · rcases closedOrFull with full | closed
      · exact full
      · have present := (MonotoneRankEnumeration.closed_complete graph increasing roots
            _ valid (by rw [← projection]; exact closed) node).mpr (allReachable node)
        rw [← projection] at present
        exact False.elim (absent present)
    · intro selected member
      rw [projection] at member absent
      exact best.2 selected member node (allReachable node) absent

theorem zero_correct (cost : Value → Nat) (source : Value → Prop) :
    Correct 0 cost source [] := by
  refine ⟨List.nodup_nil, ?_, List.Pairwise.nil, le_rfl, ?_⟩
  · simp
  · intro _ _ _; exact ⟨rfl, by simp⟩

theorem empty_correct (requested : Nat) (cost : Value → Nat) (source : Value → Prop)
    (empty : ∀ value, ¬ source value) : Correct requested cost source [] := by
  refine ⟨List.nodup_nil, ?_, List.Pairwise.nil, Nat.zero_le _, ?_⟩
  · simp
  · intro value allowed _; exact False.elim (empty value allowed)

theorem member_or_full (requested : Nat) (cost : Value → Nat) (source : Value → Prop)
    (cached : List Value) (valid : Correct requested cost source cached)
    {value : Value} (allowed : source value) :
    value ∈ cached ∨ cached.length = requested := by
  classical
  by_cases member : value ∈ cached
  · exact Or.inl member
  · exact Or.inr (valid.omitted value allowed member).1

theorem cheap_member (requested : Nat) (positive : 0 < requested)
    (cost : Value → Nat) (source : Value → Prop) (cached : List Value)
    (valid : Correct requested cost source cached) {value : Value} (allowed : source value) :
    ∃ selected ∈ cached, cost selected ≤ cost value := by
  classical
  by_cases member : value ∈ cached
  · exact ⟨value, member, le_rfl⟩
  · have full := valid.omitted value allowed member
    cases cached with
    | nil => simp only [List.length_nil] at full; omega
    | cons first rest => exact ⟨first, List.mem_cons_self, full.2 first List.mem_cons_self⟩

def product (left : List Left) (right : List Right) : List (Left × Right) :=
  left.flatMap fun first => right.map (first, ·)

@[simp] theorem mem_product (left : List Left) (right : List Right) (pair : Left × Right) :
    pair ∈ product left right ↔ pair.1 ∈ left ∧ pair.2 ∈ right := by
  simp [product, List.mem_flatMap, List.mem_map, Prod.ext_iff]

def pairCost (leftCost : Left → Nat) (rightCost : Right → Nat) (pair : Left × Right) : Nat :=
  leftCost pair.1 + rightCost pair.2

/-- Omission from the truncated Cartesian family yields k distinct retained
parents that cost no more than the omitted independently valid parent. -/
theorem product_dominates (requested : Nat) (positive : 0 < requested)
    (leftCost : Left → Nat) (rightCost : Right → Nat)
    (leftSource : Left → Prop) (rightSource : Right → Prop)
    (left : List Left) (right : List Right)
    (leftValid : Correct requested leftCost leftSource left)
    (rightValid : Correct requested rightCost rightSource right)
    (pair : Left × Right) (allowed : leftSource pair.1 ∧ rightSource pair.2)
    (omitted : pair ∉ product left right) :
    ∃ witnesses : List (Left × Right), witnesses.Nodup ∧ witnesses.length = requested ∧
      witnesses ⊆ product left right ∧
      ∀ witness ∈ witnesses, pairCost leftCost rightCost witness ≤
        pairCost leftCost rightCost pair := by
  classical
  by_cases leftPresent : pair.1 ∈ left
  · have rightMissing : pair.2 ∉ right := fun rightPresent =>
      omitted ((mem_product left right pair).mpr ⟨leftPresent, rightPresent⟩)
    have full := rightValid.omitted pair.2 allowed.2 rightMissing
    refine ⟨right.map (pair.1, ·), ?_, by simpa using full.1, ?_, ?_⟩
    · exact rightValid.distinct.map (fun first second same => congrArg Prod.snd same)
    · intro witness member
      obtain ⟨other, present, same⟩ := List.mem_map.mp member
      subst witness
      exact (mem_product left right _).mpr ⟨leftPresent, present⟩
    · intro witness member
      obtain ⟨other, present, same⟩ := List.mem_map.mp member
      subst witness
      exact Nat.add_le_add_left (full.2 other present) _
  · have full := leftValid.omitted pair.1 allowed.1 leftPresent
    obtain ⟨other, rightPresent, cheaper⟩ :=
      cheap_member requested positive rightCost rightSource right rightValid allowed.2
    refine ⟨left.map (·, other), ?_, by simpa using full.1, ?_, ?_⟩
    · exact leftValid.distinct.map (fun first second same => congrArg Prod.fst same)
    · intro witness member
      obtain ⟨first, present, same⟩ := List.mem_map.mp member
      subst witness
      exact (mem_product left right _).mpr ⟨present, rightPresent⟩
    · intro witness member
      obtain ⟨first, present, same⟩ := List.mem_map.mp member
      subst witness
      exact Nat.add_le_add (full.2 first present) cheaper

/-- A minimum prefix of a retained finite family remains a minimum prefix of
the independent larger source when omitted source members have k cheap
retained witnesses. This is used after lazy rank extraction, not as a premise
that the lazy algorithm is optimal. -/
theorem extend_by_dominance (requested : Nat) (cost : Value → Nat)
    (source retained : Value → Prop) (cached : List Value)
    (valid : Correct requested cost retained cached)
    (retainedSound : ∀ value, retained value → source value)
    (domination : ∀ value, source value → ¬ retained value →
      ∃ witnesses : List Value, witnesses.Nodup ∧ witnesses.length = requested ∧
        (∀ witness ∈ witnesses, retained witness) ∧
        ∀ witness ∈ witnesses, cost witness ≤ cost value) :
    Correct requested cost source cached := by
  classical
  refine ⟨valid.distinct, fun value member => retainedSound value (valid.sound value member),
    valid.ordered, valid.bounded, ?_⟩
  intro value allowed missing
  by_cases retainedValue : retained value
  · exact valid.omitted value retainedValue missing
  · obtain ⟨witnesses, distinct, count, witnessesRetained, witnessesCheap⟩ :=
      domination value allowed retainedValue
    by_cases allSeen : witnesses ⊆ cached
    · have lower := distinct.length_le_of_subset allSeen
      have upper := valid.bounded
      have full : cached.length = requested := by omega
      have same := (List.subperm_of_subset distinct allSeen).perm_of_length_le
        (by omega)
      refine ⟨full, ?_⟩
      intro selected member
      exact witnessesCheap selected (same.mem_iff.mpr member)
    · have someMissing : ∃ witness ∈ witnesses, witness ∉ cached := by
        simpa only [List.subset_def, not_forall, exists_prop] using allSeen
      obtain ⟨witness, present, notSeen⟩ := someMissing
      have full := valid.omitted witness (witnessesRetained witness present) notSeen
      refine ⟨full.1, ?_⟩
      intro selected member
      exact (full.2 selected member).trans (witnessesCheap witness present)

/-- The lazy family algorithm itself constructs a correct complete prefix
over the independently specified rank combinations. -/
theorem rank_prefix_correct (families : List LazyRankFamilies.Family) (requested : Nat) :
    Correct requested (LazyRankFamilies.cost families) (fun _ => True)
      (LazyRankFamilies.completePrefix families requested) := by
  have best := LazyRankFamilies.extract_best families requested requested
  refine ⟨best.1, fun _ _ => trivial, best.2.1,
    LazyRankFamilies.completePrefix_bound families requested, ?_⟩
  intro candidate _ omitted
  exact LazyRankFamilies.omitted_completePrefix families requested candidate omitted

/-- Injective reconstruction changes representation without identifying
distinct derivations. The cost equality is checked separately. -/
theorem map_correct {Other : Type*} (requested : Nat)
    (cost : Value → Nat) (otherCost : Other → Nat) (source : Value → Prop)
    (cached : List Value) (valid : Correct requested cost source cached)
    (reconstruct : Value → Other) (faithful : Function.Injective reconstruct)
    (sameCost : ∀ value, otherCost (reconstruct value) = cost value) :
    Correct requested otherCost
      (fun other => ∃ value, source value ∧ reconstruct value = other)
      (cached.map reconstruct) := by
  classical
  refine ⟨valid.distinct.map faithful, ?_, ?_, by simpa using valid.bounded, ?_⟩
  · intro other member
    obtain ⟨value, present, same⟩ := List.mem_map.mp member
    exact ⟨value, valid.sound value present, same⟩
  · simpa only [List.pairwise_map, sameCost] using valid.ordered
  · intro other allowed omitted
    obtain ⟨value, permitted, same⟩ := allowed
    subst other
    have absent : value ∉ cached := fun member =>
      omitted (List.mem_map.mpr ⟨value, member, rfl⟩)
    have full := valid.omitted value permitted absent
    refine ⟨by simpa using full.1, ?_⟩
    intro selected member
    obtain ⟨original, present, equal⟩ := List.mem_map.mp member
    subst selected
    simpa only [sameCost] using full.2 original present

/-- Reconstruction needs injectivity on authorized source values. This
permits merging physically disjoint family caches without imposing an
irrelevant injectivity condition on malformed trees. -/
theorem map_correct_on {Other : Type*} (requested : Nat)
    (cost : Value → Nat) (otherCost : Other → Nat) (source : Value → Prop)
    (cached : List Value) (valid : Correct requested cost source cached)
    (reconstruct : Value → Other)
    (faithful : ∀ first, source first → ∀ second, source second →
      reconstruct first = reconstruct second → first = second)
    (sameCost : ∀ value, otherCost (reconstruct value) = cost value) :
    Correct requested otherCost
      (fun other => ∃ value, source value ∧ reconstruct value = other)
      (cached.map reconstruct) := by
  classical
  refine ⟨?_, ?_, ?_, by simpa using valid.bounded, ?_⟩
  · exact valid.distinct.map_on fun first presentFirst second presentSecond same =>
      faithful first (valid.sound first presentFirst) second (valid.sound second presentSecond) same
  · intro other member
    obtain ⟨value, present, same⟩ := List.mem_map.mp member
    exact ⟨value, valid.sound value present, same⟩
  · simpa only [List.pairwise_map, sameCost] using valid.ordered
  · intro other allowed omitted
    obtain ⟨value, permitted, same⟩ := allowed
    subst other
    have absent : value ∉ cached := fun member =>
      omitted (List.mem_map.mpr ⟨value, member, rfl⟩)
    have full := valid.omitted value permitted absent
    refine ⟨by simpa using full.1, ?_⟩
    intro selected member
    obtain ⟨original, present, equal⟩ := List.mem_map.mp member
    subst selected
    simpa only [sameCost] using full.2 original present

namespace Controls

def small : List Nat := [0, 1]

theorem smallCorrect : Correct 2 id (fun value => value < 3) small := by
  constructor
  · decide
  · intro value member; simp [small] at member; omega
  · decide
  · decide
  · intro value allowed omitted
    have valueTwo : value = 2 := by simp [small] at omitted; omega
    subst value
    refine ⟨rfl, ?_⟩
    intro selected member
    simp [small] at member
    change selected ≤ 2
    omega

example : ∃ witnesses : List (Nat × Nat), witnesses.Nodup ∧ witnesses.length = 2 ∧
    witnesses ⊆ product small small ∧
    ∀ witness ∈ witnesses, pairCost id id witness ≤ pairCost id id (2, 2) :=
  product_dominates 2 (by decide) id id (fun value => value < 3) (fun value => value < 3)
    small small smallCorrect smallCorrect (2, 2) ⟨by decide, by decide⟩ (by decide)

/-- Parent extraction must retain physical derivations even if their costs
and answer values coincide. -/
example : product [0, 1] [0] = [(0, 0), (1, 0)] := rfl

end Controls

end Mettapedia.Algorithms.DerivationPrefix
