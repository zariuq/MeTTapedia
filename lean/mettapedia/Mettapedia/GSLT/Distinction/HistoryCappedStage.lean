import Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver

/-!
# A justified stage certificate for the history grammar, and why capping the observation fails

The stage lifts of `GradedTwoSidedObservation` take a stabilization certificate
of the two-sided system.  `HistoryTwoSidedObserver.observer_not_stabilizes`
refutes one on the whole history grammar.  This module proves where a
certificate exists and where it does not.

* **Finite systems over the integer scale stabilize** (`finite_stabilizes`).  If
  the terms of a presented system over `Scale.integers unit` are listed, some
  stage at most `n · n · unit` stabilizes, where `n` is the length of the list.
  The sum of all depth bounds rises by at least one at every stage that does not
  stabilize, and is at most `n · n · unit`.  The stage is found by a bounded
  search; no choice of stage is assumed.
* **The history grammar with a capacity** (`Bounded`, `boundedPresented`,
  `boundedPast`).  Configurations with at most `capacity` copies of every node,
  with the history steps between them.  Over a listed node set its configurations
  are listed (`mem_boundedTerms`), so the two-sided system has a certificate
  (`bounded_stabilizes`) and the bridge's stage lifts, pullbacks and native
  comparisons apply (`bounded_stage_lifts`, `bounded_native_future_iff`,
  `bounded_native_predecessor_box_iff`).  With event labels the system is
  faithful (`bounded_gradedBisimilar_iff_eq`), so the certified classes are
  single configurations (`bounded_classes_exact`).
* **Kind labels give a coarser certified quotient** (`boundedKindPresented`,
  `boundedKind_stage_lifts`).  The same certificate holds when the bounded steps
  are labelled by the kind of event only; then the certified classes can
  identify different configurations (`HistoryCoverageControls.certified_quotient`).
* **The capacity cuts only at the boundary** (`boundedSuccessors_val`,
  `boundedPredecessors_val`, `capacity_cuts_fork`).  Away from the capacity the
  authored lists of the bounded system are those of the history grammar; at
  the capacity a copy is cut.
* **Capping the observation is not enough** (`capped_cost_reading`,
  `capped_not_stabilizes`).  On one node, the cost reading with unit potential on
  the integer scale of unit `cap` reads the number of copies capped at `cap`.
  The two-sided history observer with these readings has no certificate at any
  depth: the readings agree from `cap` copies on, and erasures separate every
  two sizes, so the depth-`n` approximants identify `n + cap + 1` and
  `n + cap + 2` copies while the faithful observer does not.

**Where choice enters.**  The history grammar's firing relation uses Mathlib's
multiset erase and subtraction, which carry `Classical.choice`, and so does
everything about the bounded history system.  The finite stabilization theorem
(`finite_stabilizes` and the lemmas before it) is stated for any presented
system and is choice-free: its sums use the integer lemmas of the core
library, because Mathlib's ordered-ring instance of the integers carries
choice.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.HistoryCappedStage

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.Distinction.HistoryGrammar
open Mettapedia.GSLT.Distinction.HistoryObserver
open Mettapedia.GSLT.Distinction.HistoryObserverControls
open Mettapedia.GSLT.Distinction.HistoryTwoSidedObserver
open Mettapedia.GSLT.Distinction.Constructive
open Mettapedia.GSLT.GradedTwoSidedObservation
open Mettapedia.GSLT.GradedValueObserver
open Mettapedia.Cybernetics.DistinctionCalculus.History
open Mettapedia.OSLF.Framework.DerivedModalities
open Mettapedia.OSLF.Bridges.TypeTheory.GradedValueNativeDescent
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.TypeTheory.MaterialSets.Hypersets.PowerClassFamilyDescent
open Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-! ## Finite systems over the integer scale stabilize -/

section Finite

/-! Integer sums, proved from the integer lemmas of the core library. -/

theorem sum_le_sum_int {ι : Type*} (f g : ι → ℤ) :
    ∀ (list : List ι), (∀ i ∈ list, f i ≤ g i) → (list.map f).sum ≤ (list.map g).sum
  | [], _ => Int.le_refl 0
  | i :: rest, le => by
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      exact Int.add_le_add (le i (List.mem_cons_self ..))
        (sum_le_sum_int f g rest fun j member => le j (List.mem_cons_of_mem _ member))

theorem sum_lt_sum_int {ι : Type*} (f g : ι → ℤ) :
    ∀ (list : List ι), (∀ i ∈ list, f i ≤ g i) → (∃ i ∈ list, f i < g i) →
      (list.map f).sum < (list.map g).sum
  | [], _, ⟨_, member, _⟩ => absurd member List.not_mem_nil
  | i :: rest, le, ⟨j, member, lt⟩ => by
      rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons]
      have restLe : ∀ k ∈ rest, f k ≤ g k := fun k member' => le k (List.mem_cons_of_mem _ member')
      rcases List.mem_cons.mp member with rfl | memberRest
      · exact Int.add_lt_add_of_lt_of_le lt (sum_le_sum_int f g rest restLe)
      · exact Int.add_lt_add_of_le_of_lt (le i (List.mem_cons_self ..))
          (sum_lt_sum_int f g rest restLe ⟨j, memberRest, lt⟩)

theorem sum_nonneg_int {ι : Type*} (f : ι → ℤ) :
    ∀ (list : List ι), (∀ i ∈ list, 0 ≤ f i) → 0 ≤ (list.map f).sum
  | [], _ => Int.le_refl 0
  | i :: rest, nonneg => by
      rw [List.map_cons, List.sum_cons]
      exact Int.add_nonneg (nonneg i (List.mem_cons_self ..))
        (sum_nonneg_int f rest fun j member => nonneg j (List.mem_cons_of_mem _ member))

theorem sum_le_length_mul_int {ι : Type*} (f : ι → ℤ) (bound : ℤ) :
    ∀ (list : List ι), (∀ i ∈ list, f i ≤ bound) → (list.map f).sum ≤ list.length * bound
  | [], _ => Int.le_of_eq (by
      rw [List.map_nil, List.sum_nil, List.length_nil, Int.natCast_zero, Int.zero_mul])
  | i :: rest, le => by
      rw [List.map_cons, List.sum_cons, List.length_cons, Int.natCast_succ, Int.add_mul, Int.one_mul,
        Int.add_comm _ bound]
      exact Int.add_le_add (le i (List.mem_cons_self ..))
        (sum_le_length_mul_int f bound rest fun j member => le j (List.mem_cons_of_mem _ member))

/-- **A non-decreasing integer sequence is flat somewhere or climbs.** -/
theorem flat_or_climbs {total : ℕ → ℤ} (mono : ∀ depth, total depth ≤ total (depth + 1)) :
    ∀ steps : ℕ, (∃ depth < steps, total (depth + 1) = total depth) ∨ total 0 + steps ≤ total steps
  | 0 => Or.inr (Int.le_of_eq (Int.add_zero _))
  | steps + 1 => by
      rcases flat_or_climbs mono steps with ⟨depth, below, flat⟩ | climbs
      · exact Or.inl ⟨depth, Nat.lt_succ_of_lt below, flat⟩
      · rcases Int.lt_or_eq_of_le (mono steps) with rises | flat
        · exact Or.inr (by push_cast; omega)
        · exact Or.inl ⟨steps, Nat.lt_succ_self steps, flat.symm⟩

/-- **A bounded non-decreasing integer sequence is flat below its bound.** -/
theorem exists_flat {total : ℕ → ℤ} (mono : ∀ depth, total depth ≤ total (depth + 1))
    (lower : 0 ≤ total 0) (bound : ℕ) (upper : ∀ depth, total depth ≤ bound) :
    ∃ depth ≤ bound, total (depth + 1) = total depth := by
  rcases flat_or_climbs mono (bound + 1) with ⟨depth, below, flat⟩ | climbs
  · exact ⟨depth, Nat.lt_succ_iff.mp below, flat⟩
  · have := upper (bound + 1)
    push_cast at climbs
    omega

/-- Equal sums of pointwise-smaller integers are pointwise equal. -/
theorem eq_of_sum_eq {ι : Type*} (list : List ι) (f g : ι → ℤ) (le : ∀ i ∈ list, f i ≤ g i)
    (same : (list.map f).sum = (list.map g).sum) : ∀ i ∈ list, f i = g i := by
  intro i member
  rcases Int.lt_or_eq_of_le (le i member) with lt | eq
  · have strict := sum_lt_sum_int f g list le ⟨i, member, lt⟩
    rw [same] at strict
    exact absurd strict (Int.lt_irrefl _)
  · exact eq

universe uS uAtom uLabel uObs

variable {S : GSLT.{uS}} {unit : ℤ} {positive : 0 < unit}
variable (Q : PresentedSystem.{uS, uAtom, uLabel, uObs} S (Scale.integers unit positive))
variable (W : Q.Vocabulary) (terms : List S.Term)

/-- The sum of all depth bounds between listed terms. -/
def total (depth : ℕ) : ℤ :=
  (terms.map fun left => (terms.map fun right => Q.depthBound W depth left right).sum).sum

theorem total_mono (depth : ℕ) : total Q W terms depth ≤ total Q W terms (depth + 1) :=
  sum_le_sum_int _ _ terms fun left _ => sum_le_sum_int _ _ terms fun right _ =>
    Q.depthBound_mono W (Nat.le_succ depth) left right

theorem total_nonneg (depth : ℕ) : 0 ≤ total Q W terms depth :=
  sum_nonneg_int _ terms fun left _ => sum_nonneg_int _ terms fun right _ =>
    Q.depthBound_nonneg W depth left right

theorem total_le (depth : ℕ) :
    total Q W terms depth ≤ terms.length * (terms.length * unit) :=
  sum_le_length_mul_int _ _ terms fun left _ =>
    sum_le_length_mul_int _ _ terms fun right _ => Q.depthBound_le_one W depth left right

variable {terms}

/-- **A flat total is a stabilization stage**, when every term is listed. -/
theorem stabilizes_of_total_eq (complete : ∀ term, term ∈ terms) (depth : ℕ)
    (flat : total Q W terms (depth + 1) = total Q W terms depth) : Q.Stabilizes W depth := by
  intro left right
  have rows := eq_of_sum_eq terms
    (fun left => (terms.map fun right => Q.depthBound W depth left right).sum)
    (fun left => (terms.map fun right => Q.depthBound W (depth + 1) left right).sum)
    (fun left _ => sum_le_sum_int _ _ terms fun right _ =>
      Q.depthBound_mono W (Nat.le_succ depth) left right)
    flat.symm left (complete left)
  exact (eq_of_sum_eq terms (fun right => Q.depthBound W depth left right)
    (fun right => Q.depthBound W (depth + 1) left right)
    (fun right _ => Q.depthBound_mono W (Nat.le_succ depth) left right) rows right
    (complete right)).symm

/-- **Every finite presented system over the integer scale stabilizes**, at a
stage at most `n · n · unit` for a list of `n` terms. -/
theorem finite_stabilizes (complete : ∀ term, term ∈ terms) :
    ∃ stage ≤ terms.length * (terms.length * unit.toNat), Q.Stabilizes W stage := by
  have unitEq : ((unit.toNat : ℕ) : ℤ) = unit := Int.toNat_of_nonneg (Int.le_of_lt positive)
  have upper : ∀ depth, total Q W terms depth ≤ ((terms.length * (terms.length * unit.toNat) : ℕ) : ℤ) := by
    intro depth
    rw [Int.natCast_mul, Int.natCast_mul, unitEq]
    exact total_le Q W terms depth
  obtain ⟨stage, below, flat⟩ := exists_flat (total_mono Q W terms) (total_nonneg Q W terms 0) _ upper
  exact ⟨stage, below, stabilizes_of_total_eq Q W complete stage flat⟩

end Finite

section Classes

universe uS' uAtom' uLabel' uObs' uV'

variable {W' : Type uV'} [AddCommGroup W'] [LinearOrder W'] [IsOrderedAddMonoid W'] {K' : Scale W'}
variable {S' : GSLT.{uS'}} (Q' : PresentedSystem.{uS', uAtom', uLabel', uObs'} S' K')

/-- Graded bisimilar terms are in one stage class at every depth. -/
theorem stateOf_eq_of_gradedBisimilar (depth : ℕ) {left right : S'.Term}
    (bisimilar : Q'.GradedBisimilar left right) : stateOf Q' depth left = stateOf Q' depth right :=
  (classOf_eq_iff _ left right).mpr (funext fun formula => Q'.val_eq_of_gradedBisimilar bisimilar formula.1)

end Classes

/-! ## The history grammar with a capacity -/

section Capacity

variable {V : Type} [DecidableEq V] (G : Grammar V) (L : Listing V) (capacity : ℕ)

/-- A configuration within capacity: at most `capacity` copies of every node. -/
abbrev Bounded (V : Type) [DecidableEq V] (capacity : ℕ) :=
  {live : Multiset V // ∀ x, live.count x ≤ capacity}

/-- **The history grammar with a capacity**: bounded configurations and the
history steps between them. -/
abbrev boundedGSLT : GSLT.{0} where
  Term := Bounded V capacity
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites source target := ∃ event, Fires G event source.1 target.1
  rewrites_resp_left := by
    intro _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  rewrites_resp_right := by
    intro _ _ _ step equal
    exact equal ▸ step

/-- Events label the bounded steps. -/
abbrev boundedSystem : HennessyMilner.System.{0, 0} (boundedGSLT G capacity) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := Event V
  act event source target := Fires G event source.1 target.1
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

theorem within_iff (live : Multiset V) :
    (∀ x ∈ L.nodes, live.count x ≤ capacity) ↔ ∀ x, live.count x ≤ capacity :=
  ⟨fun within x => within x (L.complete x), fun within x _ => within x⟩

/-- Keep a configuration when it is within capacity. -/
def bound (live : Multiset V) : Option (Bounded V capacity) :=
  if within : ∀ x ∈ L.nodes, live.count x ≤ capacity then
    some ⟨live, (within_iff L capacity live).mp within⟩
  else none

theorem bound_eq_some_iff (live : Multiset V) (bounded : Bounded V capacity) :
    bound L capacity live = some bounded ↔ live = bounded.1 := by
  unfold bound
  split_ifs with within
  · constructor
    · intro same
      exact congrArg Subtype.val (Option.some.inj same)
    · intro same
      exact congrArg some (Subtype.ext same)
  · constructor
    · intro impossible
      cases impossible
    · intro same
      exact absurd ((within_iff L capacity live).mpr (same ▸ bounded.2)) within

/-- The authored successor lists of the bounded system. -/
def boundedSuccessors (event : Event V) (source : Bounded V capacity) : List (Bounded V capacity) :=
  ((step G event source.1).bind (bound L capacity)).toList

/-- The authored predecessor lists of the bounded system. -/
def boundedPredecessors (event : Event V) (target : Bounded V capacity) : List (Bounded V capacity) :=
  ((unstep G event target.1).bind (bound L capacity)).toList

theorem mem_boundedSuccessors {event : Event V} {source target : Bounded V capacity} :
    target ∈ boundedSuccessors G L capacity event source ↔ Fires G event source.1 target.1 := by
  unfold boundedSuccessors
  rw [mem_toList_iff, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨live, fired, bounded⟩
    rw [(bound_eq_some_iff L capacity live target).mp bounded] at fired
    exact (step_eq_some_iff G event _ _).mp fired
  · intro fires
    exact ⟨target.1, (step_eq_some_iff G event _ _).mpr fires,
      (bound_eq_some_iff L capacity _ target).mpr rfl⟩

theorem mem_boundedPredecessors {event : Event V} {source target : Bounded V capacity} :
    source ∈ boundedPredecessors G L capacity event target ↔ Fires G event source.1 target.1 := by
  unfold boundedPredecessors
  rw [mem_toList_iff, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨live, undone, bounded⟩
    rw [(bound_eq_some_iff L capacity live source).mp bounded] at undone
    exact (unstep_eq_some_iff G event _ _).mp undone
  · intro fires
    exact ⟨source.1, (unstep_eq_some_iff G event _ _).mpr fires,
      (bound_eq_some_iff L capacity _ source).mpr rfl⟩

section Presented

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- **The bounded history system**: the bounded steps, the history readings and
the authored successor lists. -/
def boundedPresented (R : NodeReadings K V) : PresentedSystem (boundedGSLT G capacity) K where
  dynamics := boundedSystem G capacity
  Obs := Reading
  value observation live := reading K R observation live.1
  value_nonneg _ _ := reading_nonneg R _ _
  value_le_one _ _ := reading_le_one R _ _
  value_resp _ _ _ same := by cases same; rfl
  successors := boundedSuccessors G L capacity
  successors_act member := (mem_boundedSuccessors G L capacity).mp member
  successors_cover action := ⟨_, (mem_boundedSuccessors G L capacity).mpr action, rfl⟩

/-- The authored predecessor lists of the bounded system. -/
def boundedPast (R : NodeReadings K V) : Predecessors (boundedPresented G L capacity K R) where
  list := boundedPredecessors G L capacity
  sound member := (mem_boundedPredecessors G L capacity).mp member
  cover action := ⟨_, (mem_boundedPredecessors G L capacity).mpr action, rfl⟩

/-- Over a listed node set the vocabulary is finite. -/
def boundedVocabulary (R : NodeReadings K V) : (boundedPresented G L capacity K R).Vocabulary where
  observations := [.result, .fault, .cost]
  observations_complete := Reading.mem_all
  labels := L.events
  labels_complete := L.mem_events

/-- The labelled bounded steps as authored events. -/
def boundedEvents (R : NodeReadings K V) : AuthoredEvents (boundedPresented G L capacity K R) where
  span := {
    Edge := {step : Event V × Bounded V capacity × Bounded V capacity //
      Fires G step.1 step.2.1.1 step.2.2.1}
    source := fun step => step.1.2.1
    target := fun step => step.1.2.2 }
  label step := step.1.1
  sound step := step.2
  cover label source target action := ⟨⟨(label, source, target), action⟩, rfl, rfl, rfl⟩

end Presented

/-! ### Listing the bounded configurations -/

/-- The configurations over a list of nodes with at most `capacity` copies of
each. -/
def configsOver : List V → List (Multiset V)
  | [] => [0]
  | x :: rest => (List.range (capacity + 1)).flatMap fun copies =>
      (configsOver rest).map fun live => Multiset.replicate copies x + live

theorem mem_configsOver : ∀ (nodes : List V), nodes.Nodup → ∀ (live : Multiset V),
    (∀ x, live.count x ≤ capacity) → (∀ x, x ∉ nodes → live.count x = 0) →
      live ∈ configsOver capacity nodes
  | [], _, live, _, outside => by
      have empty : live = 0 := Multiset.eq_zero_of_forall_notMem fun x member =>
        absurd (outside x List.not_mem_nil) (Nat.pos_iff_ne_zero.mp (Multiset.count_pos.mpr member))
      rw [empty]
      exact List.mem_singleton_self _
  | x :: rest, distinct, live, bounded, outside => by
      have rest_distinct := (List.nodup_cons.mp distinct)
      let others := live.filter (fun y => ¬ y = x)
      have split : Multiset.replicate (live.count x) x + others = live := by
        rw [← Multiset.filter_eq' live x]
        exact Multiset.filter_add_not (fun y => y = x) live
      have othersBounded : ∀ y, others.count y ≤ capacity := fun y =>
        (Multiset.count_le_of_le y (Multiset.filter_le _ _)).trans (bounded y)
      have othersOutside : ∀ y, y ∉ rest → others.count y = 0 := by
        intro y notRest
        rw [Multiset.count_filter]
        by_cases same : y = x
        · simp [same]
        · rw [if_pos same]
          exact outside y (by simp [same, notRest])
      have member := mem_configsOver rest rest_distinct.2 others othersBounded othersOutside
      refine List.mem_flatMap.mpr ⟨live.count x, List.mem_range.mpr (Nat.lt_succ_of_le (bounded x)), ?_⟩
      exact List.mem_map.mpr ⟨others, member, split⟩

/-- The bounded configurations over a listed node set. -/
def boundedTerms : List (Bounded V capacity) :=
  (configsOver capacity L.nodes.dedup).filterMap (bound L capacity)

/-- **Every bounded configuration is listed.** -/
theorem mem_boundedTerms (live : Bounded V capacity) : live ∈ boundedTerms L capacity := by
  refine List.mem_filterMap.mpr ⟨live.1, ?_, (bound_eq_some_iff L capacity _ live).mpr rfl⟩
  exact mem_configsOver capacity L.nodes.dedup (List.nodup_dedup _) live.1 live.2
    fun x outside => absurd (List.mem_dedup.mpr (L.complete x)) outside

/-! ### The certificate and the stage lifts -/

section Certificate

variable (unit : ℤ) (positive : 0 < unit)

/-- **The two-sided bounded system has a stabilization certificate.** -/
theorem bounded_stabilizes (R : NodeReadings (Scale.integers unit positive) V) :
    ∃ stage, (twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R)).Stabilizes
      (twoSidedVocabulary _ (boundedPast G L capacity _ R) (boundedVocabulary G L capacity _ R)) stage :=
  let ⟨stage, _, stable⟩ := finite_stabilizes
    (twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R))
    (twoSidedVocabulary _ (boundedPast G L capacity _ R) (boundedVocabulary G L capacity _ R))
    (mem_boundedTerms L capacity)
  ⟨stage, stable⟩

/-- **The bridge's stage lifts apply to the bounded history**: at a certified
stage both endpoint lifts hold for every authored event span, and the future
diamond and the predecessor box commute with the stage classes. -/
theorem bounded_stage_lifts (R : NodeReadings (Scale.integers unit positive) V)
    (events : AuthoredEvents (boundedPresented G L capacity _ R)) :
    ∃ stage,
      (stageMap _ (boundedPast G L capacity _ R) events stage).SourceLifts ∧
      (stageMap _ (boundedPast G L capacity _ R) events stage).TargetLifts ∧
      (∀ predicate (source : Bounded V capacity),
        derivedDiamond (stageSpan _ (boundedPast G L capacity _ R) events stage) predicate
            (stateOf (twoSided _ (boundedPast G L capacity _ R)) stage source) ↔
          derivedDiamond events.span
            (predicate ∘ stateOf (twoSided _ (boundedPast G L capacity _ R)) stage) source) ∧
      (∀ predicate (target : Bounded V capacity),
        derivedBox (stageSpan _ (boundedPast G L capacity _ R) events stage) predicate
            (stateOf (twoSided _ (boundedPast G L capacity _ R)) stage target) ↔
          derivedBox events.span
            (predicate ∘ stateOf (twoSided _ (boundedPast G L capacity _ R)) stage) target) := by
  obtain ⟨stage, stable⟩ := bounded_stabilizes G L capacity unit positive R
  have positive' : (Scale.integers unit positive).Positive := Scale.integers_positive unit positive
  exact ⟨stage,
    source_lifts _ _ events (boundedVocabulary G L capacity _ R) stage positive' stable,
    target_lifts _ _ events (boundedVocabulary G L capacity _ R) stage positive' stable,
    future_pullback _ _ events (boundedVocabulary G L capacity _ R) stage positive' stable,
    predecessor_box_pullback _ _ events (boundedVocabulary G L capacity _ R) stage positive' stable⟩

/-- **Native future comparison on the bounded history**: at a certified stage
the native image of every two-sided formula commutes with the future diamond. -/
theorem bounded_native_future_iff (R : NodeReadings (Scale.integers unit positive) V)
    (events : AuthoredEvents (boundedPresented G L capacity _ R)) :
    ∃ stage, ∀ (formula : Formula (valueSystem (twoSided _ (boundedPast G L capacity _ R))).Atom
        (twoSided _ (boundedPast G L capacity _ R)).dynamics.Label) (source : Bounded V capacity),
      derivedDiamond (stageSpan _ (boundedPast G L capacity _ R) events stage)
          (nativeImage (twoSided _ (boundedPast G L capacity _ R)) stage
            (formulaPredicate (valueSystem (twoSided _ (boundedPast G L capacity _ R))) formula))
          (stateOf (twoSided _ (boundedPast G L capacity _ R)) stage source) ↔
        (futurePredicate _ events
          (formulaPredicate (valueSystem (twoSided _ (boundedPast G L capacity _ R))) formula)).1 source := by
  obtain ⟨stage, stable⟩ := bounded_stabilizes G L capacity unit positive R
  exact ⟨stage, fun formula source => formula_future_native_iff _ _ events
    (boundedVocabulary G L capacity _ R) stage (Scale.integers_positive unit positive) stable formula source⟩

/-- **Native predecessor-box comparison on the bounded history.** -/
theorem bounded_native_predecessor_box_iff (R : NodeReadings (Scale.integers unit positive) V)
    (events : AuthoredEvents (boundedPresented G L capacity _ R)) :
    ∃ stage, ∀ (formula : Formula (valueSystem (twoSided _ (boundedPast G L capacity _ R))).Atom
        (twoSided _ (boundedPast G L capacity _ R)).dynamics.Label) (target : Bounded V capacity),
      derivedBox (stageSpan _ (boundedPast G L capacity _ R) events stage)
          (nativeImage (twoSided _ (boundedPast G L capacity _ R)) stage
            (formulaPredicate (valueSystem (twoSided _ (boundedPast G L capacity _ R))) formula))
          (stateOf (twoSided _ (boundedPast G L capacity _ R)) stage target) ↔
        (predecessorBoxPredicate _ events
          (formulaPredicate (valueSystem (twoSided _ (boundedPast G L capacity _ R))) formula)).1 target := by
  obtain ⟨stage, stable⟩ := bounded_stabilizes G L capacity unit positive R
  exact ⟨stage, fun formula target => formula_predecessor_box_native_iff _ _ events
    (boundedVocabulary G L capacity _ R) stage (Scale.integers_positive unit positive) stable formula target⟩

/-- **With event labels the two-sided bounded system is faithful**: erasures
count every node, and an erasure never leaves the capacity. -/
theorem bounded_gradedBisimilar_iff_eq (R : NodeReadings (Scale.integers unit positive) V)
    (left right : Bounded V capacity) :
    (twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R)).GradedBisimilar
      left right ↔ left = right := by
  constructor
  · rintro ⟨relation, ⟨forth, back, _⟩, related⟩
    let lifted : Multiset V → Multiset V → Prop := fun first second =>
      ∃ boundedFirst boundedSecond : Bounded V capacity, boundedFirst.1 = first ∧
        boundedSecond.1 = second ∧ relation boundedFirst boundedSecond
    have erased : ∀ (live : Bounded V capacity) (x : V), ∀ y, (live.1.erase x).count y ≤ capacity :=
      fun live x y => (Multiset.count_le_of_le y (Multiset.erase_le x live.1)).trans (live.2 y)
    have forthErasures : MatchesErasures (G := G) lifted := by
      rintro _ _ ⟨boundedFirst, boundedSecond, rfl, rfl, related'⟩ x member
      obtain ⟨second', action, related''⟩ := forth related' (.forward, .erase x)
        (left' := ⟨boundedFirst.1.erase x, erased boundedFirst x⟩) (Fires.erase member)
      exact ⟨second'.1, action, _, second', rfl, rfl, related''⟩
    have backErasures : MatchesErasures (G := G) (fun first second => lifted second first) := by
      rintro _ _ ⟨boundedFirst, boundedSecond, rfl, rfl, related'⟩ x member
      obtain ⟨first', action, related''⟩ := back related' (.forward, .erase x)
        (right' := ⟨boundedSecond.1.erase x, erased boundedSecond x⟩) (Fires.erase member)
      exact ⟨first'.1, action, first', _, rfl, rfl, related''⟩
    exact Subtype.ext (eq_of_matchesErasures (G := G) forthErasures backErasures
      ⟨left, right, rfl, rfl, related⟩)
  · rintro rfl
    exact ⟨_, (twoSided (boundedPresented G L capacity _ R)
      (boundedPast G L capacity _ R)).isGradedBisimulation_equiv, rfl⟩

/-- **At a certified stage the event-labelled classes are single
configurations.** -/
theorem bounded_classes_exact (R : NodeReadings (Scale.integers unit positive) V) {stage : ℕ}
    (stable : (twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R)).Stabilizes
      (twoSidedVocabulary _ (boundedPast G L capacity _ R) (boundedVocabulary G L capacity _ R)) stage)
    (left right : Bounded V capacity) :
    stateOf (twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R)) stage left =
        stateOf (twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R)) stage right ↔
      left = right :=
  (classOf_eq_iff _ left right).trans
    ((ObservedGradedFamilyDescent.readout_eq_iff _
      (twoSidedVocabulary _ (boundedPast G L capacity _ R) (boundedVocabulary G L capacity _ R))
      stage left right).trans
    ((((twoSided (boundedPresented G L capacity _ R) (boundedPast G L capacity _ R)).gradedBisimilar_iff_of_stabilizes
      _ (Scale.integers_positive unit positive) stable left right).2).symm.trans
      (bounded_gradedBisimilar_iff_eq G L capacity unit positive R left right)))

end Certificate

/-! ### Kind labels: a certified stage with a coarser quotient

With event labels the bounded system is faithful, so its certified classes are
single configurations.  With labels that record only the kind of an event the
same construction certifies a stage whose classes can identify different
configurations. -/

section Kinds

/-- Kinds of events label the bounded steps. -/
abbrev boundedKindSystem : HennessyMilner.System.{0, 0} (boundedGSLT G capacity) where
  Atom := Empty
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := EventKind
  act kind source target := ∃ event, kindOf event = kind ∧ Fires G event source.1 target.1
  act_resp_left := by
    intro _ _ _ target equal step
    exact ⟨target, equal ▸ step, rfl⟩
  act_resp_right := by
    intro _ _ _ _ step equal
    exact equal ▸ step

/-- The successors of one kind: those of every listed event of that kind. -/
def boundedKindSuccessors (kind : EventKind) (source : Bounded V capacity) : List (Bounded V capacity) :=
  (L.events.filter fun event => decide (kindOf event = kind)).flatMap fun event =>
    boundedSuccessors G L capacity event source

/-- The predecessors of one kind. -/
def boundedKindPredecessors (kind : EventKind) (target : Bounded V capacity) :
    List (Bounded V capacity) :=
  (L.events.filter fun event => decide (kindOf event = kind)).flatMap fun event =>
    boundedPredecessors G L capacity event target

theorem mem_boundedKindSuccessors {kind : EventKind} {source target : Bounded V capacity} :
    target ∈ boundedKindSuccessors G L capacity kind source ↔
      ∃ event, kindOf event = kind ∧ Fires G event source.1 target.1 := by
  unfold boundedKindSuccessors
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨event, member, listed⟩
    exact ⟨event, of_decide_eq_true (List.mem_filter.mp member).2,
      (mem_boundedSuccessors G L capacity).mp listed⟩
  · rintro ⟨event, kindEq, fires⟩
    exact ⟨event, List.mem_filter.mpr ⟨L.mem_events event, decide_eq_true kindEq⟩,
      (mem_boundedSuccessors G L capacity).mpr fires⟩

theorem mem_boundedKindPredecessors {kind : EventKind} {source target : Bounded V capacity} :
    source ∈ boundedKindPredecessors G L capacity kind target ↔
      ∃ event, kindOf event = kind ∧ Fires G event source.1 target.1 := by
  unfold boundedKindPredecessors
  rw [List.mem_flatMap]
  constructor
  · rintro ⟨event, member, listed⟩
    exact ⟨event, of_decide_eq_true (List.mem_filter.mp member).2,
      (mem_boundedPredecessors G L capacity).mp listed⟩
  · rintro ⟨event, kindEq, fires⟩
    exact ⟨event, List.mem_filter.mpr ⟨L.mem_events event, decide_eq_true kindEq⟩,
      (mem_boundedPredecessors G L capacity).mpr fires⟩

omit [DecidableEq V] in
theorem kind_mem_all (kind : EventKind) : kind ∈ [EventKind.evolve, .fork, .merge, .erase] := by
  cases kind <;> simp

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] (K : Scale W)

/-- **The kind-labelled bounded history system.** -/
def boundedKindPresented (R : NodeReadings K V) : PresentedSystem (boundedGSLT G capacity) K where
  dynamics := boundedKindSystem G capacity
  Obs := Reading
  value observation live := reading K R observation live.1
  value_nonneg _ _ := reading_nonneg R _ _
  value_le_one _ _ := reading_le_one R _ _
  value_resp _ _ _ same := by cases same; rfl
  successors := boundedKindSuccessors G L capacity
  successors_act member := (mem_boundedKindSuccessors G L capacity).mp member
  successors_cover action := ⟨_, (mem_boundedKindSuccessors G L capacity).mpr action, rfl⟩

/-- The authored kind-labelled predecessor lists. -/
def boundedKindPast (R : NodeReadings K V) : Predecessors (boundedKindPresented G L capacity K R) where
  list := boundedKindPredecessors G L capacity
  sound member := (mem_boundedKindPredecessors G L capacity).mp member
  cover action := ⟨_, (mem_boundedKindPredecessors G L capacity).mpr action, rfl⟩

/-- The kind-labelled vocabulary. -/
def boundedKindVocabulary (R : NodeReadings K V) : (boundedKindPresented G L capacity K R).Vocabulary where
  observations := [.result, .fault, .cost]
  observations_complete := Reading.mem_all
  labels := [.evolve, .fork, .merge, .erase]
  labels_complete := kind_mem_all

/-- Labelled bounded steps, read by their kinds, as authored events: each
retains its full event. -/
def boundedKindEvents (R : NodeReadings K V) : AuthoredEvents (boundedKindPresented G L capacity K R) where
  span := {
    Edge := {step : Event V × Bounded V capacity × Bounded V capacity //
      Fires G step.1 step.2.1.1 step.2.2.1}
    source := fun step => step.1.2.1
    target := fun step => step.1.2.2 }
  label step := kindOf step.1.1
  sound step := ⟨step.1.1, rfl, step.2⟩
  cover kind source target action := by
    obtain ⟨event, kindEq, fires⟩ := action
    exact ⟨⟨(event, source, target), fires⟩, kindEq, rfl, rfl⟩

end Kinds

section KindCertificate

variable (unit : ℤ) (positive : 0 < unit)

/-- **The two-sided kind-labelled bounded system has a certificate.** -/
theorem boundedKind_stabilizes (R : NodeReadings (Scale.integers unit positive) V) :
    ∃ stage, (twoSided (boundedKindPresented G L capacity _ R) (boundedKindPast G L capacity _ R)).Stabilizes
      (twoSidedVocabulary _ (boundedKindPast G L capacity _ R) (boundedKindVocabulary G L capacity _ R))
      stage :=
  let ⟨stage, _, stable⟩ := finite_stabilizes
    (twoSided (boundedKindPresented G L capacity _ R) (boundedKindPast G L capacity _ R))
    (twoSidedVocabulary _ (boundedKindPast G L capacity _ R) (boundedKindVocabulary G L capacity _ R))
    (mem_boundedTerms L capacity)
  ⟨stage, stable⟩

/-- **The bridge's stage lifts apply to the kind-labelled bounded history.** -/
theorem boundedKind_stage_lifts (R : NodeReadings (Scale.integers unit positive) V)
    (events : AuthoredEvents (boundedKindPresented G L capacity _ R)) :
    ∃ stage,
      (twoSided (boundedKindPresented G L capacity _ R) (boundedKindPast G L capacity _ R)).Stabilizes
        (twoSidedVocabulary _ (boundedKindPast G L capacity _ R) (boundedKindVocabulary G L capacity _ R))
        stage ∧
      (stageMap _ (boundedKindPast G L capacity _ R) events stage).SourceLifts ∧
      (stageMap _ (boundedKindPast G L capacity _ R) events stage).TargetLifts := by
  obtain ⟨stage, stable⟩ := boundedKind_stabilizes G L capacity unit positive R
  have positive' : (Scale.integers unit positive).Positive := Scale.integers_positive unit positive
  exact ⟨stage, stable,
    source_lifts _ _ events (boundedKindVocabulary G L capacity _ R) stage positive' stable,
    target_lifts _ _ events (boundedKindVocabulary G L capacity _ R) stage positive' stable⟩

end KindCertificate

/-! ### The capacity cuts only at the boundary -/

theorem count_cons_le (y head : V) (rest : Multiset V) :
    (head ::ₘ rest).count y ≤ rest.count y + 1 := by
  rw [Multiset.count_cons]
  split <;> omega

/-- A step adds at most one copy of each node. -/
theorem count_le_of_fires {event : Event V} {source target : Multiset V}
    (fires : Fires G event source target) (y : V) : target.count y ≤ source.count y + 1 := by
  cases fires with
  | evolve member =>
      exact (count_cons_le y _ _).trans
        (Nat.add_le_add_right (Multiset.count_le_of_le y (Multiset.erase_le _ _)) 1)
  | fork member => exact count_cons_le y _ _
  | merge enabled =>
      exact (count_cons_le y _ _).trans
        (Nat.add_le_add_right (Multiset.count_le_of_le y (Multiset.sub_le_self _ _)) 1)
  | erase member => exact (Multiset.count_le_of_le y (Multiset.erase_le _ _)).trans (Nat.le_succ _)

/-- An undone step adds at most two copies of each node. -/
theorem count_le_of_unfires {event : Event V} {source target : Multiset V}
    (fires : Fires G event source target) (y : V) : source.count y ≤ target.count y + 2 := by
  obtain ⟨_, resultEq⟩ := (HistoryIndependence.fires_iff G event source target).mp fires
  have consumed : (HistoryIndependence.consumed event).count y ≤ 2 := by
    cases event <;> simp only [HistoryIndependence.consumed, pair, Multiset.count_cons,
      Multiset.count_singleton, Multiset.count_zero] <;> (try split_ifs) <;> omega
  have kept : source.count y ≤ (source - HistoryIndependence.consumed event).count y +
      (HistoryIndependence.consumed event).count y := by
    rw [Multiset.count_sub]
    omega
  rw [resultEq, Multiset.count_add]
  omega

/-- **Away from the capacity the forward lists are the history grammar's.** -/
theorem boundedSuccessors_val (event : Event V) (source : Bounded V capacity)
    (margin : ∀ y, source.1.count y + 1 ≤ capacity) :
    (boundedSuccessors G L capacity event source).map Subtype.val = successors G event source.1 := by
  unfold boundedSuccessors successors
  cases fired : step G event source.1 with
  | none => rfl
  | some target =>
      have within : ∀ y, target.count y ≤ capacity := fun y =>
        (count_le_of_fires G ((step_eq_some_iff G event _ _).mp fired) y).trans (margin y)
      rw [Option.bind_some, (bound_eq_some_iff L capacity target ⟨target, within⟩).mpr rfl]
      rfl

/-- **Away from the capacity the backward lists are the history grammar's.** -/
theorem boundedPredecessors_val (event : Event V) (target : Bounded V capacity)
    (margin : ∀ y, target.1.count y + 2 ≤ capacity) :
    (boundedPredecessors G L capacity event target).map Subtype.val = predecessors G event target.1 := by
  unfold boundedPredecessors predecessors
  cases undone : unstep G event target.1 with
  | none => rfl
  | some source =>
      have within : ∀ y, source.count y ≤ capacity := fun y =>
        (count_le_of_unfires G ((unstep_eq_some_iff G event _ _).mp undone) y).trans (margin y)
      rw [Option.bind_some, (bound_eq_some_iff L capacity source ⟨source, within⟩).mpr rfl]
      rfl

/-- **At the capacity a copy is cut**: copying a node held `capacity` times is a
step of the history grammar and not of the bounded system. -/
theorem capacity_cuts_fork (source : Bounded V capacity) {x : V} (full : source.1.count x = capacity)
    (positiveCapacity : 0 < capacity) :
    boundedSuccessors G L capacity (.fork x) source = [] ∧
      successors G (.fork x) source.1 = [x ::ₘ source.1] := by
  have member : x ∈ source.1 := Multiset.count_pos.mp (by rw [full]; exact positiveCapacity)
  have stepped : step G (.fork x) source.1 = some (x ::ₘ source.1) := by
    simp [step, member]
  refine ⟨?_, by unfold successors; rw [stepped]; rfl⟩
  unfold boundedSuccessors
  rw [stepped, Option.bind_some]
  have overCapacity : ¬ (∀ y ∈ L.nodes, (x ::ₘ source.1).count y ≤ capacity) := by
    intro within
    have := within x (L.complete x)
    rw [Multiset.count_cons_self, full] at this
    omega
  simp [bound, overCapacity]

end Capacity

/-! ## Capping the observation is not enough -/

section Capped

/-- A presented system on the one-node grammar whose steps are determined by
sizes and whose readings agree from `threshold` copies on. -/
structure SizeDeterminedAbove {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W]
    {K : Scale W} (Q : PresentedSystem (historyGSLT unitGrammar) K) where
  threshold : ℕ
  need : Q.dynamics.Label → ℕ
  shift : Q.dynamics.Label → ℕ → ℕ
  need_le : ∀ label, need label ≤ 2
  shift_ge : ∀ label size, size ≤ shift label size + 1
  act_iff : ∀ label source target, Q.dynamics.act label source target ↔
    need label ≤ Multiset.card source ∧ Multiset.card target = shift label (Multiset.card source)
  value_agree : ∀ observation (left right : Multiset Unit), threshold ≤ Multiset.card left →
    threshold ≤ Multiset.card right → Q.value observation left = Q.value observation right

namespace SizeDeterminedAbove

variable {W : Type} [AddCommGroup W] [LinearOrder W] [IsOrderedAddMonoid W] {K : Scale W}
variable {Q : PresentedSystem (historyGSLT unitGrammar) K}

/-- **Configurations of at least `depth + threshold + 2` copies agree to depth
`depth`.** -/
theorem approx (sized : SizeDeterminedAbove Q) : ∀ (depth : ℕ) (left right : Multiset Unit),
    depth + sized.threshold + 2 ≤ Multiset.card left →
      depth + sized.threshold + 2 ≤ Multiset.card right → Q.Approx depth left right
  | 0, left, right, leftSize, rightSize => by
      simp only [PresentedSystem.Approx]
      exact fun observation => sized.value_agree observation left right (by omega) (by omega)
  | depth + 1, left, right, leftSize, rightSize => by
      simp only [PresentedSystem.Approx]
      refine ⟨fun observation => sized.value_agree observation left right (by omega) (by omega),
        ?_, ?_⟩
      · intro label left' action
        obtain ⟨_, size⟩ := (sized.act_iff label left left').mp action
        have needed := sized.need_le label
        have lower := sized.shift_ge label (Multiset.card left)
        have lower' := sized.shift_ge label (Multiset.card right)
        refine ⟨Multiset.replicate (sized.shift label (Multiset.card right)) (),
          (sized.act_iff label right _).mpr ⟨by omega, by simp⟩, ?_⟩
        exact approx sized depth _ _ (by omega) (by simp only [Multiset.card_replicate]; omega)
      · intro label right' action
        obtain ⟨_, size⟩ := (sized.act_iff label right right').mp action
        have needed := sized.need_le label
        have lower := sized.shift_ge label (Multiset.card left)
        have lower' := sized.shift_ge label (Multiset.card right)
        refine ⟨Multiset.replicate (sized.shift label (Multiset.card left)) (),
          (sized.act_iff label left _).mpr ⟨by omega, by simp⟩, ?_⟩
        exact approx sized depth _ _ (by simp only [Multiset.card_replicate]; omega) (by omega)

/-- At every depth two different sizes agree. -/
theorem separated (sized : SizeDeterminedAbove Q) (depth : ℕ) :
    ∃ left right : Multiset Unit, ¬ (historyGSLT unitGrammar).Equiv left right ∧
      Q.Approx depth left right := by
  refine ⟨Multiset.replicate (depth + sized.threshold + 2) (),
    Multiset.replicate (depth + sized.threshold + 3) (), ?_,
    sized.approx depth _ _ (by simp only [Multiset.card_replicate]; omega)
      (by simp only [Multiset.card_replicate]; omega)⟩
  intro same
  have sizes := congrArg Multiset.card (show Multiset.replicate (depth + sized.threshold + 2) () =
    Multiset.replicate (depth + sized.threshold + 3) () from same)
  simp at sizes

end SizeDeterminedAbove

variable (cap : ℕ) (positive : (0 : ℤ) < cap)

/-- **Capped multiplicity readings on one node**: no result, no fault, and one
unit of potential per copy on the integer scale of unit `cap`. -/
def cappedReadings : NodeReadings (Scale.integers cap positive) Unit where
  result _ := 0
  result_nonneg _ := le_rfl
  result_le_one _ := le_of_lt positive
  faulty _ := false
  potential _ := 1

/-- **The cost reading counts copies, capped at `cap`.** -/
theorem capped_cost_reading (live : Multiset Unit) :
    reading (Scale.integers cap positive) (cappedReadings cap positive) .cost live =
      min (cap : ℤ) (Multiset.card live) := by
  change max 0 (min (cap : ℤ) (potentialSum (fun _ => (1 : ℤ)) live)) = _
  have sum : potentialSum (fun _ : Unit => (1 : ℤ)) live = Multiset.card live := by
    simp [potentialSum]
  rw [sum, max_eq_right (le_min (le_of_lt positive) (Int.natCast_nonneg _))]

theorem capped_readings_agree (observation : Reading) (left right : Multiset Unit)
    (leftSize : cap ≤ Multiset.card left) (rightSize : cap ≤ Multiset.card right) :
    reading (Scale.integers cap positive) (cappedReadings cap positive) observation left =
      reading (Scale.integers cap positive) (cappedReadings cap positive) observation right := by
  have nonempty : ∀ live : Multiset Unit, 1 ≤ Multiset.card live →
      live = Multiset.replicate (Multiset.card live - 1 + 1) () := by
    intro live size
    rw [Nat.sub_add_cancel size]
    exact unit_eq_replicate live
  cases observation with
  | result =>
      change best (cappedReadings cap positive).result left = best (cappedReadings cap positive).result right
      rw [nonempty left (by omega), nonempty right (by omega),
        best_replicate_succ (cappedReadings cap positive).result () le_rfl,
        best_replicate_succ (cappedReadings cap positive).result () le_rfl]
  | fault =>
      change best (faultIndicator _ (cappedReadings cap positive)) left =
        best (faultIndicator _ (cappedReadings cap positive)) right
      rw [nonempty left (by omega), nonempty right (by omega),
        best_replicate_succ _ _ (faultIndicator_nonneg _ ()),
        best_replicate_succ _ _ (faultIndicator_nonneg _ ())]
  | cost =>
      rw [capped_cost_reading, capped_cost_reading, min_eq_left (by exact_mod_cast leftSize),
        min_eq_left (by exact_mod_cast rightSize)]

/-- The two-sided capped observer on one node is size-determined from `cap`
copies on. -/
def cappedSized :
    SizeDeterminedAbove (observer unitGrammar (Scale.integers cap positive) (cappedReadings cap positive)) where
  threshold := cap
  need := twoSidedNeed
  shift := twoSidedShift
  need_le := by
    rintro ⟨direction, event⟩
    cases direction <;> cases event <;> simp [twoSidedNeed, need, backNeed]
  shift_ge := by
    rintro ⟨direction, event⟩ size
    cases direction <;> cases event <;> simp only [twoSidedShift, shift, backShift] <;> omega
  act_iff := by
    rintro ⟨direction, event⟩ source target
    cases direction
    · exact unit_fires_iff event source target
    · exact unit_backward_iff event source target
  value_agree observation left right leftSize rightSize :=
    capped_readings_agree cap positive observation left right leftSize rightSize

/-- **Capping the observation does not certify a stage**: the two-sided history
observer with capped multiplicity readings has no stabilization certificate at
any depth. -/
theorem capped_not_stabilizes (depth : ℕ) :
    ¬ (observer unitGrammar (Scale.integers cap positive) (cappedReadings cap positive)).Stabilizes
      (observerVocabulary unitGrammar _ (cappedReadings cap positive) unitListing) depth :=
  not_stabilizes_of_faithful _ _ (Scale.integers_positive cap positive)
    (fun left right => (observer_gradedBisimilar_iff_eq unitGrammar _ _ left right).mp)
    (cappedSized cap positive).separated depth

/-- **Capping the dynamics does**: with the same capped readings, the history
grammar on one node with capacity `cap` has a certified stage. -/
theorem capped_bounded_stabilizes :
    ∃ stage, (twoSided (boundedPresented unitGrammar unitListing cap _ (cappedReadings cap positive))
      (boundedPast unitGrammar unitListing cap _ (cappedReadings cap positive))).Stabilizes
      (twoSidedVocabulary _ (boundedPast unitGrammar unitListing cap _ (cappedReadings cap positive))
        (boundedVocabulary unitGrammar unitListing cap _ (cappedReadings cap positive))) stage :=
  bounded_stabilizes unitGrammar unitListing cap cap positive (cappedReadings cap positive)

end Capped

end Mettapedia.GSLT.Distinction.HistoryCappedStage
