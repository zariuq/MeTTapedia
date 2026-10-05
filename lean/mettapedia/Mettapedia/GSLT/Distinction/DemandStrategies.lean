import Mettapedia.GSLT.Distinction.RouteGrades
import Mettapedia.GSLT.Dynamics.DemandAgreement

/-!
# A distinction graph of demand strategies, with its observers as data

Three options for when a discarded or copied computation runs: eager
evaluation, lazy evaluation with sharing, and resampling (call by name).  Each
option is a node; its observer compares test programs by what they do; routes
between options are interpretations of one option in another; examples that
separate two options are witnesses.

* **What a program does** (`answers`, `draws`).  A computation draws a bag of
  outcomes, each an answer or a fault, possibly none and possibly repeated.
  Discarding (`k a b`) runs `b` eagerly, so each outcome of `b` gives one `a`
  or one fault, and does not run it lazily or under resampling.  Copying
  (`let x = b in (x, x)`) uses one outcome twice with sharing and draws twice
  under resampling.  The number of draws of `b` is recorded as an effect.
* **The generic laws apply** (`answers_discard`, `answers_copy`).  Discarding
  is the bound computation used zero times and copying is it used twice; on a
  computation without faults each strategy returns the generic answers of
  eager sharing, lazy sharing and resampling.  So the agreement facts are the
  generic laws: discarding agrees over bags exactly at one answer and over sets
  exactly at some answer (`discard_bags_iff`, `discard_supports_iff`), copying
  agrees over bags exactly at most one answer and over sets exactly at a set of
  at most one answer (`copy_bags_iff`, `copy_supports_iff`).  A fault is not in
  the generic carriers; discarding keeps it (`none_mem_dropped`).
* **The observer is data** (`Weights`, `observer`).  Five readings of what a
  program does: its outcome bag, its outcome set, its number of outcomes,
  whether it faults, and its number of draws.  A choice of nonnegative weights
  summing to one makes the share of weighted readings that separate two
  programs a distance satisfying the metric law (`observer_metric`).
* **Defects derived from the laws.**  A reading on which two strategies agree
  contributes nothing to the defect of the default interpretation (the same
  program under the other strategy) (`expandsAtMost_of_agreement`).  On
  computations that answer and do not fault, eager and lazy evaluation agree
  on outcome sets and faults (`eager_lazy_agreement`), so the defect is at most
  the weight of bags, counts and draws, and any computation with other than
  one answer attains it (`eager_lazy_defect`).  With exactly one answer the
  outcomes agree too and the defect is the weight of draws alone
  (`deterministic_eager_lazy`).
* **The number depends on the observer; the agreement does not**
  (`weights_control`).  With equal weight on bags and sets the defect is
  `1/2`; with weight `1/4` on bags it is `1/4`; with sets alone it is `0`;
  the agreement proposition is the same in every case.  An observer that
  ignores bags certifies an interpretation that changes multiplicities.
* **Absent answers, faults and duplicates are observed per reading**
  (`absent_and_fault_witnesses`, `copy_witnesses`).
* **Exact interpretations preserve everything** (`exact_translations`):
  forcing, dropping, pairing and sharing preserve outcomes, faults and draws,
  so they have zero distortion for every choice of weights, and they compose.
* **Purity is a hypothesis** (`sharing_requires_purity`): replacing the
  resampled copy by sharing keeps outcomes exactly when the computation has at
  most one outcome, and it always changes the number of draws.

The weighted readings are the observation; the defects are relative to it.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Distinction.DemandStrategies

open Mettapedia.Cybernetics.DistinctionCalculus
open Mettapedia.GSLT.Distinction.RouteGrades
open Mettapedia.GSLT.Dynamics.DemandAgreement
  (eagerShared lazyShared resampledUses shareTuple resampledUses_succ resampledUses_zero
    eagerShared_eq_lazyShared_iff lazyShared_eq_resampledUses_iff
    eagerShared_lazyShared_support_iff lazyShared_resampledUses_support_iff)

/-- The three options. -/
inductive Strategy where
  | eager
  | lazy
  | resample
  deriving DecidableEq

/-- Test programs over a type of computations. -/
inductive Program (Computation : Type) where
  /-- `k a b`: return `a`, with `b` as the discarded argument. -/
  | discard (computation : Computation)
  /-- `let x = b in (x, x)`. -/
  | copy (computation : Computation)
  /-- Return `a`. -/
  | unit
  /-- Run `b` and return `a` for each outcome. -/
  | forceThen (computation : Computation)
  /-- Two independent draws of `b`. -/
  | pairUp (computation : Computation)
  /-- One draw of `b`, used twice. -/
  | shareUp (computation : Computation)
  deriving DecidableEq

/-- An outcome: an answer (`a` is the empty list, a pair has two entries) or a
fault (`none`). -/
abbrev Outcome := Option (List Bool)

variable {Computation : Type} (draw : Computation → Multiset (Option Bool))

/-- One `a` for each answer; a fault stays a fault. -/
def dropped (bag : Multiset (Option Bool)) : Multiset Outcome :=
  bag.map (Option.map fun _ => [])

/-- One draw, used twice. -/
def shared (bag : Multiset (Option Bool)) : Multiset Outcome :=
  bag.map (Option.map fun value => [value, value])

/-- Two independent draws; a fault in either draw faults. -/
def pairs (bag : Multiset (Option Bool)) : Multiset Outcome :=
  bag.bind fun first => bag.map fun second =>
    first.bind fun left => second.map fun right => [left, right]

/-- **The outcomes of a program under a strategy.** -/
def answers : Strategy → Program Computation → Multiset Outcome
  | .eager, .discard computation => dropped (draw computation)
  | .lazy, .discard _ => {some []}
  | .resample, .discard _ => {some []}
  | .eager, .copy computation => shared (draw computation)
  | .lazy, .copy computation => shared (draw computation)
  | .resample, .copy computation => pairs (draw computation)
  | _, .unit => {some []}
  | _, .forceThen computation => dropped (draw computation)
  | _, .pairUp computation => pairs (draw computation)
  | _, .shareUp computation => shared (draw computation)

/-- **The number of draws of the computation**, an effect outside the
outcomes. -/
def draws : Strategy → Program Computation → ℕ
  | .eager, .discard _ => 1
  | .lazy, .discard _ => 0
  | .resample, .discard _ => 0
  | .eager, .copy _ => 1
  | .lazy, .copy _ => 1
  | .resample, .copy _ => 2
  | _, .unit => 0
  | _, .forceThen _ => 1
  | _, .pairUp _ => 2
  | _, .shareUp _ => 1

/-! ## Observers as data -/

/-- The readings of what a program does. -/
inductive Reading where
  | bag
  | support
  | count
  | fault
  | effects
  deriving DecidableEq

/-- **A weighted observer family**: nonnegative weights on the readings,
summing to one. -/
structure Weights where
  weight : Reading → ℚ
  nonneg : ∀ reading, 0 ≤ weight reading
  total : weight .bag + weight .support + weight .count + weight .fault + weight .effects = 1

/-- One reading's verdict: `0` when it reads two programs alike. -/
def separates {W : Type} [DecidableEq W] (reading : Program Computation → W)
    (first second : Program Computation) : ℚ :=
  if reading first = reading second then 0 else 1

omit draw in
theorem separates_triangle {W : Type} [DecidableEq W] (reading : Program Computation → W)
    (first second third : Program Computation) :
    separates reading first third ≤ separates reading first second + separates reading second third := by
  unfold separates
  by_cases firstSecond : reading first = reading second
  · rw [if_pos firstSecond, firstSecond]
    split_ifs <;> norm_num
  · rw [if_neg firstSecond]
    split_ifs <;> norm_num

omit draw in
theorem separates_mem {W : Type} [DecidableEq W] (reading : Program Computation → W)
    (first second : Program Computation) :
    0 ≤ separates reading first second ∧ separates reading first second ≤ 1 := by
  unfold separates
  split_ifs <;> norm_num

omit draw in
theorem separates_symm {W : Type} [DecidableEq W] (reading : Program Computation → W)
    (first second : Program Computation) :
    separates reading first second = separates reading second first := by
  unfold separates
  simp only [eq_comm]

omit draw in
theorem separates_of_eq {W : Type} [DecidableEq W] {reading : Program Computation → W}
    {first second : Program Computation} (same : reading first = reading second) :
    separates reading first second = 0 := by
  simp [separates, same]

omit draw in
theorem separates_of_ne {W : Type} [DecidableEq W] {reading : Program Computation → W}
    {first second : Program Computation} (different : reading first ≠ reading second) :
    separates reading first second = 1 := by
  simp [separates, different]

/-- The five readings of a strategy. -/
def bagReading (strategy : Strategy) : Program Computation → Multiset Outcome :=
  answers draw strategy

def supportReading (strategy : Strategy) : Program Computation → Finset Outcome :=
  fun program => (answers draw strategy program).toFinset

def countReading (strategy : Strategy) : Program Computation → ℕ :=
  fun program => Multiset.card (answers draw strategy program)

def faultReading (strategy : Strategy) : Program Computation → Bool :=
  fun program => decide (none ∈ answers draw strategy program)

def effectsReading (strategy : Strategy) : Program Computation → ℕ :=
  draws strategy

/-- **The weighted distance** of two programs under a strategy. -/
def answerDistance (weights : Weights) (strategy : Strategy)
    (first second : Program Computation) : ℚ :=
  weights.weight .bag * separates (bagReading draw strategy) first second +
    weights.weight .support * separates (supportReading draw strategy) first second +
    weights.weight .count * separates (countReading draw strategy) first second +
    weights.weight .fault * separates (faultReading draw strategy) first second +
    weights.weight .effects * separates (effectsReading strategy) first second

theorem answerDistance_mem (weights : Weights) (strategy : Strategy)
    (first second : Program Computation) :
    0 ≤ answerDistance draw weights strategy first second ∧
      answerDistance draw weights strategy first second ≤ 1 := by
  unfold answerDistance
  have b := separates_mem (bagReading draw strategy) first second
  have s := separates_mem (supportReading draw strategy) first second
  have c := separates_mem (countReading draw strategy) first second
  have f := separates_mem (faultReading draw strategy) first second
  have e := separates_mem (effectsReading (Computation := Computation) strategy) first second
  have wb := weights.nonneg .bag
  have ws := weights.nonneg .support
  have wc := weights.nonneg .count
  have wf := weights.nonneg .fault
  have we := weights.nonneg .effects
  have total := weights.total
  constructor
  · exact add_nonneg (add_nonneg (add_nonneg (add_nonneg (mul_nonneg wb b.1) (mul_nonneg ws s.1))
      (mul_nonneg wc c.1)) (mul_nonneg wf f.1)) (mul_nonneg we e.1)
  · nlinarith [mul_le_mul_of_nonneg_left b.2 wb, mul_le_mul_of_nonneg_left s.2 ws,
      mul_le_mul_of_nonneg_left c.2 wc, mul_le_mul_of_nonneg_left f.2 wf,
      mul_le_mul_of_nonneg_left e.2 we]

/-- **The observer of an option** under a choice of weights. -/
def observer (weights : Weights) (strategy : Strategy) : Tolerance (Program Computation) where
  similarity first second := 1 - answerDistance draw weights strategy first second
  nonnegative first second := by linarith [(answerDistance_mem draw weights strategy first second).2]
  bounded first second := by linarith [(answerDistance_mem draw weights strategy first second).1]
  reflexive program := by simp [answerDistance, separates]
  symmetric first second := by
    unfold answerDistance
    rw [separates_symm (bagReading draw strategy), separates_symm (supportReading draw strategy),
      separates_symm (countReading draw strategy), separates_symm (faultReading draw strategy),
      separates_symm (effectsReading strategy)]

theorem observer_distance (weights : Weights) (strategy : Strategy)
    (first second : Program Computation) :
    (observer draw weights strategy).distance first second =
      answerDistance draw weights strategy first second := by
  simp [Tolerance.distance, observer]

/-- Every observer of the family satisfies the metric law. -/
theorem observer_metric (weights : Weights) (strategy : Strategy) :
    (observer draw weights strategy).Metric := by
  intro first second third
  rw [observer_distance, observer_distance, observer_distance]
  unfold answerDistance
  have b := separates_triangle (bagReading draw strategy) first second third
  have s := separates_triangle (supportReading draw strategy) first second third
  have c := separates_triangle (countReading draw strategy) first second third
  have f := separates_triangle (faultReading draw strategy) first second third
  have e := separates_triangle (effectsReading (Computation := Computation) strategy) first second third
  nlinarith [mul_le_mul_of_nonneg_left b (weights.nonneg .bag),
    mul_le_mul_of_nonneg_left s (weights.nonneg .support),
    mul_le_mul_of_nonneg_left c (weights.nonneg .count),
    mul_le_mul_of_nonneg_left f (weights.nonneg .fault),
    mul_le_mul_of_nonneg_left e (weights.nonneg .effects)]

/-- The default interpretation compares distances program by program. -/
theorem expandsAtMost_identity_iff (weights : Weights) (source target : Strategy) (δ : ℚ) :
    ExpandsAtMost (observer draw weights source) (observer draw weights target)
        (Route.identity _) δ ↔
      ∀ first second : Program Computation,
        answerDistance draw weights target first second ≤
          answerDistance draw weights source first second + δ := by
  constructor
  · intro bound first second
    have := bound (rfl : first = first) (rfl : second = second)
    rwa [observer_distance, observer_distance] at this
  · rintro bound first second _ _ rfl rfl
    rw [observer_distance, observer_distance]
    exact bound first second

/-- Two programs with the same outcomes and the same draws are at distance zero
for every choice of weights. -/
theorem answerDistance_eq_zero_of_same (weights : Weights) {strategy : Strategy}
    {first second : Program Computation}
    (outcomes : answers draw strategy first = answers draw strategy second)
    (effects : draws strategy first = draws strategy second) :
    answerDistance draw weights strategy first second = 0 := by
  unfold answerDistance
  rw [separates_of_eq (reading := bagReading draw strategy) (first := first) (second := second)
      outcomes,
    separates_of_eq (reading := supportReading draw strategy) (first := first) (second := second)
      (congrArg Multiset.toFinset outcomes),
    separates_of_eq (reading := countReading draw strategy) (first := first) (second := second)
      (congrArg Multiset.card outcomes),
    separates_of_eq (reading := faultReading draw strategy) (first := first) (second := second)
      (congrArg (fun bag => decide (none ∈ bag)) outcomes),
    separates_of_eq (reading := effectsReading strategy) (first := first) (second := second)
      effects]
  ring

/-! ## The generic agreement laws in this semantics -/

/-- The generic answers of a computation bound once and used `n` times, under a
strategy: eager sharing, lazy sharing, or resampling. -/
def uses : Strategy → ℕ → Multiset Bool → Multiset (List Bool)
  | .eager => eagerShared
  | .lazy => lazyShared
  | .resample => resampledUses

/-- The answers in a bag of outcomes, faults left out. -/
def answersOf (bag : Multiset (Option Bool)) : Multiset Bool :=
  bag.filterMap id

/-- A bag without faults is the bag of its answers. -/
theorem eq_map_some_answersOf {bag : Multiset (Option Bool)} (faultFree : none ∉ bag) :
    bag = (answersOf bag).map some := by
  induction bag using Multiset.induction_on with
  | empty => simp [answersOf]
  | cons outcome bag ih =>
      rw [Multiset.mem_cons, not_or] at faultFree
      obtain ⟨value, rfl⟩ := Option.ne_none_iff_exists'.mp (Ne.symm faultFree.1)
      rw [answersOf, Multiset.filterMap_cons_some id _ _ rfl, Multiset.map_cons, ← answersOf,
        ← ih faultFree.2]

/-- Discarding keeps a fault. -/
theorem none_mem_dropped (bag : Multiset (Option Bool)) : none ∈ dropped bag ↔ none ∈ bag := by
  simp [dropped]

theorem none_not_mem_map_some (outcomes : Multiset (List Bool)) : none ∉ outcomes.map some := by
  simp

theorem dropped_map_some (values : Multiset Bool) :
    dropped (values.map some) = (eagerShared 0 values).map some := by
  simp [dropped, eagerShared, shareTuple, Multiset.map_map]

theorem shared_map_some (values : Multiset Bool) :
    shared (values.map some) = (eagerShared 2 values).map some := by
  simp [shared, eagerShared, shareTuple, Multiset.map_map]

theorem pairs_map_some (values : Multiset Bool) :
    pairs (values.map some) = (resampledUses 2 values).map some := by
  simp [pairs, resampledUses_succ, resampledUses_zero, Multiset.bind_map, Multiset.map_bind,
    Multiset.map_map]

/-- **Discarding is the bound computation used zero times.** On a computation
without faults, each strategy returns the generic answers. -/
theorem answers_discard (strategy : Strategy) {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    answers draw strategy (.discard computation) = (uses strategy 0 values).map some := by
  cases strategy with
  | eager =>
      change dropped (draw computation) = (eagerShared 0 values).map some
      rw [pure, dropped_map_some]
  | lazy =>
      change ({some []} : Multiset Outcome) = (lazyShared 0 values).map some
      simp [lazyShared]
  | resample =>
      change ({some []} : Multiset Outcome) = (resampledUses 0 values).map some
      simp [resampledUses_zero]

/-- **Copying is the bound computation used twice.** On a computation without
faults, each strategy returns the generic answers. -/
theorem answers_copy (strategy : Strategy) {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    answers draw strategy (.copy computation) = (uses strategy 2 values).map some := by
  cases strategy with
  | eager =>
      change shared (draw computation) = (eagerShared 2 values).map some
      rw [pure, shared_map_some]
  | lazy =>
      change shared (draw computation) = (lazyShared 2 values).map some
      rw [pure, shared_map_some]
      simp [lazyShared, eagerShared]
  | resample =>
      change pairs (draw computation) = (resampledUses 2 values).map some
      rw [pure, pairs_map_some]

/-- **Discarding, over bags**: eager and lazy evaluation give the same outcomes
exactly when the computation has one answer. -/
theorem discard_bags_iff {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    answers draw .eager (.discard computation) = answers draw .lazy (.discard computation) ↔
      Multiset.card values = 1 := by
  rw [answers_discard draw .eager pure, answers_discard draw .lazy pure,
    (Multiset.map_injective (Option.some_injective _)).eq_iff]
  exact (eagerShared_eq_lazyShared_iff 0 values).trans (by simp)

/-- **Discarding, over sets**: eager and lazy evaluation give the same outcome
set exactly when the computation has an answer. -/
theorem discard_supports_iff {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    supportReading draw .eager (.discard computation) =
        supportReading draw .lazy (.discard computation) ↔ values ≠ 0 := by
  unfold supportReading
  rw [answers_discard draw .eager pure, answers_discard draw .lazy pure, Multiset.toFinset_map,
    Multiset.toFinset_map, Finset.image_inj (Option.some_injective _)]
  exact (eagerShared_lazyShared_support_iff 0 values).trans (by simp)

/-- **Copying, over bags**: sharing and resampling give the same outcomes
exactly when the computation has at most one answer. -/
theorem copy_bags_iff {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    answers draw .lazy (.copy computation) = answers draw .resample (.copy computation) ↔
      Multiset.card values ≤ 1 := by
  rw [answers_copy draw .lazy pure, answers_copy draw .resample pure,
    (Multiset.map_injective (Option.some_injective _)).eq_iff]
  exact (lazyShared_eq_resampledUses_iff 2 values).trans (by simp)

/-- **Copying, over sets**: sharing and resampling give the same outcome set
exactly when the computation has at most one distinct answer. -/
theorem copy_supports_iff {computation : Computation} {values : Multiset Bool}
    (pure : draw computation = values.map some) :
    supportReading draw .lazy (.copy computation) =
        supportReading draw .resample (.copy computation) ↔ values.toFinset.card ≤ 1 := by
  unfold supportReading
  rw [answers_copy draw .lazy pure, answers_copy draw .resample pure, Multiset.toFinset_map,
    Multiset.toFinset_map, Finset.image_inj (Option.some_injective _)]
  exact (lazyShared_resampledUses_support_iff 2 values).trans (by simp)

/-! ## Defects derived from agreement laws -/

/-- **A reading on which two strategies agree contributes nothing to the
defect.** If the two strategies give every program the same outcome set and
the same fault verdict, the default interpretation expands distances by at
most the weight of bags, counts and draws. -/
theorem expandsAtMost_of_agreement (weights : Weights) {source target : Strategy}
    (supportAgrees : ∀ program : Program Computation,
      supportReading draw target program = supportReading draw source program)
    (faultAgrees : ∀ program : Program Computation,
      faultReading draw target program = faultReading draw source program) :
    ExpandsAtMost (observer draw weights source) (observer draw weights target) (Route.identity _)
      (weights.weight .bag + weights.weight .count + weights.weight .effects) := by
  rw [expandsAtMost_identity_iff]
  intro first second
  have supportSame : separates (supportReading draw target) first second =
      separates (supportReading draw source) first second := by
    unfold separates
    rw [supportAgrees first, supportAgrees second]
  have faultSame : separates (faultReading draw target) first second =
      separates (faultReading draw source) first second := by
    unfold separates
    rw [faultAgrees first, faultAgrees second]
  unfold answerDistance
  rw [supportSame, faultSame]
  have bTarget := (separates_mem (bagReading draw target) first second).2
  have bSource := (separates_mem (bagReading draw source) first second).1
  have cTarget := (separates_mem (countReading draw target) first second).2
  have cSource := (separates_mem (countReading draw source) first second).1
  have eTarget := (separates_mem (effectsReading (Computation := Computation) target) first second).2
  have eSource := (separates_mem (effectsReading (Computation := Computation) source) first second).1
  nlinarith [mul_le_mul_of_nonneg_left bTarget (weights.nonneg .bag),
    mul_nonneg (weights.nonneg .bag) bSource,
    mul_le_mul_of_nonneg_left cTarget (weights.nonneg .count),
    mul_nonneg (weights.nonneg .count) cSource,
    mul_le_mul_of_nonneg_left eTarget (weights.nonneg .effects),
    mul_nonneg (weights.nonneg .effects) eSource]

/-- **When two strategies give every program the same outcomes**, only draws can
separate programs differently, so the default interpretation expands distances
by at most the weight of draws. -/
theorem expandsAtMost_of_bag_agreement (weights : Weights) {source target : Strategy}
    (bagAgrees : ∀ program : Program Computation,
      answers draw target program = answers draw source program) :
    ExpandsAtMost (observer draw weights source) (observer draw weights target) (Route.identity _)
      (weights.weight .effects) := by
  rw [expandsAtMost_identity_iff]
  intro first second
  have bagSame : separates (bagReading draw target) first second =
      separates (bagReading draw source) first second := by
    unfold separates bagReading
    rw [bagAgrees first, bagAgrees second]
  have supportSame : separates (supportReading draw target) first second =
      separates (supportReading draw source) first second := by
    unfold separates supportReading
    rw [bagAgrees first, bagAgrees second]
  have countSame : separates (countReading draw target) first second =
      separates (countReading draw source) first second := by
    unfold separates countReading
    rw [bagAgrees first, bagAgrees second]
  have faultSame : separates (faultReading draw target) first second =
      separates (faultReading draw source) first second := by
    unfold separates faultReading
    rw [bagAgrees first, bagAgrees second]
  unfold answerDistance
  rw [bagSame, supportSame, countSame, faultSame]
  have eTarget := (separates_mem (effectsReading (Computation := Computation) target) first second).2
  have eSource := (separates_mem (effectsReading (Computation := Computation) source) first second).1
  nlinarith [mul_le_mul_of_nonneg_left eTarget (weights.nonneg .effects),
    mul_nonneg (weights.nonneg .effects) eSource]

/-- **An interpretation that preserves outcomes and draws preserves every
distance**, for every choice of weights. -/
theorem distortsAtMost_zero_of_preserved (weights : Weights) {source target : Strategy}
    (translate : Program Computation → Program Computation)
    (outcomes : ∀ program, answers draw target (translate program) = answers draw source program)
    (effects : ∀ program, draws target (translate program) = draws source program) :
    DistortsAtMost (observer draw weights source) (observer draw weights target)
      (Route.graph translate) 0 := by
  rintro first second _ _ rfl rfl
  rw [observer_distance, observer_distance]
  unfold answerDistance separates bagReading supportReading countReading faultReading
    effectsReading
  simp only [outcomes, effects, sub_self, abs_zero, le_refl]

/-- **The agreement law of eager and lazy evaluation, from the generic laws.**
On computations that answer and do not fault, eager and lazy evaluation give
every program the same outcome set and the same fault verdict. -/
theorem eager_lazy_agreement
    (answering : ∀ computation, draw computation ≠ 0)
    (faultFree : ∀ computation, none ∉ draw computation) :
    (∀ program : Program Computation,
      supportReading draw .lazy program = supportReading draw .eager program) ∧
      (∀ program : Program Computation,
        faultReading draw .lazy program = faultReading draw .eager program) := by
  constructor
  · intro program
    cases program with
    | discard computation =>
        have pure := eq_map_some_answersOf (faultFree computation)
        refine ((discard_supports_iff draw pure).mpr fun noAnswer => ?_).symm
        exact answering computation (by rw [pure, noAnswer, Multiset.map_zero])
    | copy _ => rfl
    | unit => rfl
    | forceThen _ => rfl
    | pairUp _ => rfl
    | shareUp _ => rfl
  · intro program
    cases program with
    | discard computation =>
        have pure := eq_map_some_answersOf (faultFree computation)
        simp only [faultReading, answers_discard draw .lazy pure, answers_discard draw .eager pure,
          none_not_mem_map_some]
    | copy _ => rfl
    | unit => rfl
    | forceThen _ => rfl
    | pairUp _ => rfl
    | shareUp _ => rfl

/-- **The witness, for every computation that answers, does not fault and has
other than one answer.** Discarding it and forcing it are alike under eager
evaluation; under lazy evaluation they differ in bags, counts and draws, and
agree in sets and faults. -/
theorem discard_witness (weights : Weights) {computation : Computation}
    (answering : draw computation ≠ 0) (faultFree : none ∉ draw computation)
    (notOne : Multiset.card (draw computation) ≠ 1) :
    answerDistance draw weights .eager (.discard computation) (.forceThen computation) = 0 ∧
      answerDistance draw weights .lazy (.discard computation) (.forceThen computation) =
        weights.weight .bag + weights.weight .count + weights.weight .effects := by
  have pure := eq_map_some_answersOf faultFree
  have someAnswer : answersOf (draw computation) ≠ 0 := fun noAnswer =>
    answering (by rw [pure, noAnswer, Multiset.map_zero])
  have notOneAnswer : Multiset.card (answersOf (draw computation)) ≠ 1 := by
    rwa [pure, Multiset.card_map] at notOne
  constructor
  · exact answerDistance_eq_zero_of_same draw weights rfl rfl
  · have bag : separates (bagReading draw .lazy) (.discard computation) (.forceThen computation) = 1 :=
      separates_of_ne fun same => notOneAnswer ((discard_bags_iff draw pure).mp same.symm)
    have support : separates (supportReading draw .lazy) (.discard computation)
        (.forceThen computation) = 0 :=
      separates_of_eq ((discard_supports_iff draw pure).mpr someAnswer).symm
    have count : separates (countReading draw .lazy) (.discard computation)
        (.forceThen computation) = 1 :=
      separates_of_ne fun same => notOne (by simpa [countReading, answers, dropped] using same.symm)
    have fault : separates (faultReading draw .lazy) (.discard computation)
        (.forceThen computation) = 0 :=
      separates_of_eq (by simp [faultReading, answers, none_mem_dropped, faultFree])
    have effects : separates (effectsReading (Computation := Computation) .lazy) (.discard computation)
        (.forceThen computation) = 1 :=
      separates_of_ne (by simp [effectsReading, draws])
    unfold answerDistance
    rw [bag, support, count, fault, effects]
    ring

/-- **Eager into lazy by the default interpretation: the defect is exactly the
weight of bags, counts and draws**, on computations that answer and do not
fault, as soon as one of them has other than one answer. -/
theorem eager_lazy_defect (weights : Weights)
    (answering : ∀ computation, draw computation ≠ 0)
    (faultFree : ∀ computation, none ∉ draw computation)
    {witness : Computation} (notOne : Multiset.card (draw witness) ≠ 1) :
    ExpandsAtMost (observer draw weights .eager) (observer draw weights .lazy)
        (Route.identity _) (weights.weight .bag + weights.weight .count + weights.weight .effects) ∧
      ∀ δ < weights.weight .bag + weights.weight .count + weights.weight .effects,
        ¬ ExpandsAtMost (observer draw weights .eager)
          (observer draw weights .lazy) (Route.identity _) δ := by
  obtain ⟨supportAgrees, faultAgrees⟩ := eager_lazy_agreement draw answering faultFree
  refine ⟨expandsAtMost_of_agreement draw weights supportAgrees faultAgrees,
    fun δ small bound => ?_⟩
  have separated := (expandsAtMost_identity_iff draw weights .eager .lazy δ).mp bound
    (.discard witness) (.forceThen witness)
  obtain ⟨eagerZero, lazyValue⟩ :=
    discard_witness draw weights (answering witness) (faultFree witness) notOne
  rw [eagerZero, lazyValue] at separated
  linarith

/-- **With exactly one answer, eager and lazy evaluation give every program the
same outcomes** (the generic discarding law at one answer), so only draws
separate them: the defect is exactly the weight of draws. -/
theorem deterministic_eager_lazy (weights : Weights)
    (deterministic : ∀ computation, ∃ value, draw computation = {some value})
    (computation : Computation) :
    ExpandsAtMost (observer draw weights .eager) (observer draw weights .lazy)
        (Route.identity _) (weights.weight .effects) ∧
      ∀ δ < weights.weight .effects, ¬ ExpandsAtMost (observer draw weights .eager)
        (observer draw weights .lazy) (Route.identity _) δ := by
  have bagAgrees : ∀ program : Program Computation,
      answers draw .lazy program = answers draw .eager program := by
    intro program
    cases program with
    | discard computation =>
        obtain ⟨value, single⟩ := deterministic computation
        have pure : draw computation = ({value} : Multiset Bool).map some := by
          rw [single, Multiset.map_singleton]
        exact ((discard_bags_iff draw pure).mpr (Multiset.card_singleton value)).symm
    | copy _ => rfl
    | unit => rfl
    | forceThen _ => rfl
    | pairUp _ => rfl
    | shareUp _ => rfl
  refine ⟨expandsAtMost_of_bag_agreement draw weights bagAgrees, fun δ small bound => ?_⟩
  have separated := (expandsAtMost_identity_iff draw weights .eager .lazy δ).mp bound
    (.discard computation) (.forceThen computation)
  have same := bagAgrees (.discard computation)
  have eagerZero : answerDistance draw weights .eager (.discard computation)
      (.forceThen computation) = 0 :=
    answerDistance_eq_zero_of_same draw weights rfl rfl
  have lazyEffects : answerDistance draw weights .lazy (.discard computation)
      (.forceThen computation) = weights.weight .effects := by
    unfold answerDistance
    rw [separates_of_eq (reading := bagReading draw .lazy) (first := .discard computation)
        (second := .forceThen computation) same,
      separates_of_eq (reading := supportReading draw .lazy) (first := .discard computation)
        (second := .forceThen computation) (congrArg Multiset.toFinset same),
      separates_of_eq (reading := countReading draw .lazy) (first := .discard computation)
        (second := .forceThen computation) (congrArg Multiset.card same),
      separates_of_eq (reading := faultReading draw .lazy) (first := .discard computation)
        (second := .forceThen computation) (congrArg (fun bag => decide (none ∈ bag)) same),
      separates_of_ne (reading := effectsReading (Computation := Computation) .lazy)
        (first := .discard computation) (second := .forceThen computation)
        (by simp [effectsReading, draws])]
    ring
  rw [eagerZero, lazyEffects] at separated
  linarith

/-! ## Answering computations -/

/-- One answer, or a coin with two. -/
inductive Answering where
  | heads
  | coin
  deriving DecidableEq

def answeringDraw : Answering → Multiset (Option Bool)
  | .heads => {some true}
  | .coin => {some true, some false}

/-- Every program over answering computations, listed. -/
def answeringPrograms : List (Program Answering) :=
  [.discard .heads, .discard .coin, .copy .heads, .copy .coin, .unit, .forceThen .heads,
    .forceThen .coin, .pairUp .heads, .pairUp .coin, .shareUp .heads, .shareUp .coin]

theorem mem_answeringPrograms (program : Program Answering) : program ∈ answeringPrograms := by
  cases program with
  | discard computation => cases computation <;> decide
  | copy computation => cases computation <;> decide
  | unit => decide
  | forceThen computation => cases computation <;> decide
  | pairUp computation => cases computation <;> decide
  | shareUp computation => cases computation <;> decide

theorem answeringDraw_coin : answeringDraw .coin = ({true, false} : Multiset Bool).map some :=
  rfl

theorem answeringDraw_ne_zero (computation : Answering) : answeringDraw computation ≠ 0 := by
  cases computation <;> simp [answeringDraw]

theorem answeringDraw_faultFree (computation : Answering) : none ∉ answeringDraw computation := by
  cases computation <;> simp [answeringDraw]

/-- **The agreement law, on answering computations**, from the generic laws:
eager and lazy evaluation give every program the same outcome set and the same
fault verdict. -/
theorem answering_agreement :
    (∀ program : Program Answering,
      supportReading answeringDraw .lazy program = supportReading answeringDraw .eager program) ∧
      (∀ program : Program Answering,
        faultReading answeringDraw .lazy program = faultReading answeringDraw .eager program) :=
  eager_lazy_agreement answeringDraw answeringDraw_ne_zero answeringDraw_faultFree

/-- The same proposition by checking every program: it agrees with the law. -/
theorem answering_agreement_check :
    (∀ program : Program Answering,
      supportReading answeringDraw .lazy program = supportReading answeringDraw .eager program) ∧
      (∀ program : Program Answering,
        faultReading answeringDraw .lazy program = faultReading answeringDraw .eager program) := by
  have support : ∀ program ∈ answeringPrograms,
      supportReading answeringDraw .lazy program = supportReading answeringDraw .eager program := by
    decide +kernel
  have fault : ∀ program ∈ answeringPrograms,
      faultReading answeringDraw .lazy program = faultReading answeringDraw .eager program := by
    decide +kernel
  exact ⟨fun program => support program (mem_answeringPrograms program),
    fun program => fault program (mem_answeringPrograms program)⟩

theorem coin_card_ne_one : Multiset.card (answeringDraw .coin) ≠ 1 := by
  simp [answeringDraw]

/-- The witness: discarding a coin against forcing it. -/
theorem coin_witness (weights : Weights) :
    answerDistance answeringDraw weights .eager (.discard .coin) (.forceThen .coin) = 0 ∧
      answerDistance answeringDraw weights .lazy (.discard .coin) (.forceThen .coin) =
        weights.weight .bag + weights.weight .count + weights.weight .effects :=
  discard_witness answeringDraw weights (answeringDraw_ne_zero .coin)
    (answeringDraw_faultFree .coin) coin_card_ne_one

/-- **Eager into lazy by the default interpretation, on answering
computations: the defect is exactly the weight of bags, counts and draws.** It
is derived from the agreement on sets and faults, and attained by a coin. -/
theorem answering_eager_lazy (weights : Weights) :
    ExpandsAtMost (observer answeringDraw weights .eager) (observer answeringDraw weights .lazy)
        (Route.identity _) (weights.weight .bag + weights.weight .count + weights.weight .effects) ∧
      ∀ δ < weights.weight .bag + weights.weight .count + weights.weight .effects,
        ¬ ExpandsAtMost (observer answeringDraw weights .eager)
          (observer answeringDraw weights .lazy) (Route.identity _) δ :=
  eager_lazy_defect answeringDraw weights answeringDraw_ne_zero answeringDraw_faultFree
    coin_card_ne_one

/-! ## Computations with one answer -/

/-- A computation that returns its value. -/
def fixedDraw : Bool → Multiset (Option Bool) :=
  fun value => {some value}

/-- **With one answer per computation the defect is the weight of draws**: the
bag, set, count and fault readings agree, so an observer without draws
certifies eager in lazy with zero defect. -/
theorem fixed_eager_lazy (weights : Weights) :
    ExpandsAtMost (observer fixedDraw weights .eager) (observer fixedDraw weights .lazy)
        (Route.identity _) (weights.weight .effects) ∧
      ∀ δ < weights.weight .effects, ¬ ExpandsAtMost (observer fixedDraw weights .eager)
        (observer fixedDraw weights .lazy) (Route.identity _) δ :=
  deterministic_eager_lazy fixedDraw weights (fun value => ⟨value, rfl⟩) true

/-! ## The number depends on the observer, the agreement does not -/

/-- Equal weight on outcome bags and outcome sets. -/
def bagsAndSets : Weights where
  weight
    | .bag => 1 / 2
    | .support => 1 / 2
    | _ => 0
  nonneg reading := by cases reading <;> norm_num
  total := by norm_num

/-- Weight `1/4` on outcome bags, the rest on outcome sets. -/
def quarterBags : Weights where
  weight
    | .bag => 1 / 4
    | .support => 3 / 4
    | _ => 0
  nonneg reading := by cases reading <;> norm_num
  total := by norm_num

/-- Outcome sets alone. -/
def setsOnly : Weights where
  weight
    | .support => 1
    | _ => 0
  nonneg reading := by cases reading <;> norm_num
  total := by norm_num

/-- **Changing the observer changes the defect, not the agreement.** The
agreement on outcome sets and faults is one proposition, independent of any
weights; the defect of the default interpretation of eager in lazy is `1/2`,
`1/4` and `0` under three observers.  The observer that reads sets alone
certifies an interpretation that changes the multiplicity of outcomes. -/
theorem weights_control :
    (∀ program : Program Answering,
      supportReading answeringDraw .lazy program = supportReading answeringDraw .eager program) ∧
      bagsAndSets.weight .bag + bagsAndSets.weight .count + bagsAndSets.weight .effects = 1 / 2 ∧
      quarterBags.weight .bag + quarterBags.weight .count + quarterBags.weight .effects = 1 / 4 ∧
      setsOnly.weight .bag + setsOnly.weight .count + setsOnly.weight .effects = 0 ∧
      ExpandsAtMost (observer answeringDraw setsOnly .eager) (observer answeringDraw setsOnly .lazy)
        (Route.identity _) 0 ∧
      answers answeringDraw .eager (.discard .coin) ≠ answers answeringDraw .lazy (.discard .coin) := by
  refine ⟨answering_agreement.1, by norm_num [bagsAndSets], by norm_num [quarterBags],
    by norm_num [setsOnly], ?_, fun same => ?_⟩
  · have bound := (answering_eager_lazy setsOnly).1
    have zero : setsOnly.weight .bag + setsOnly.weight .count + setsOnly.weight .effects = 0 := by
      norm_num [setsOnly]
    rwa [zero] at bound
  · have one := (discard_bags_iff answeringDraw answeringDraw_coin).mp same
    simp at one

/-! ## Absent answers, faults and duplicates -/

/-- No outcome, one answer, a coin, a fault, or one answer twice. -/
inductive Full where
  | absent
  | heads
  | coin
  | fault
  | twice
  deriving DecidableEq

def fullDraw : Full → Multiset (Option Bool)
  | .absent => 0
  | .heads => {some true}
  | .coin => {some true, some false}
  | .fault => {none}
  | .twice => {some true, some true}

theorem fullDraw_absent : fullDraw .absent = (0 : Multiset Bool).map some :=
  rfl

theorem fullDraw_heads : fullDraw .heads = ({true} : Multiset Bool).map some :=
  rfl

theorem fullDraw_coin : fullDraw .coin = ({true, false} : Multiset Bool).map some :=
  rfl

theorem fullDraw_twice : fullDraw .twice = ({true, true} : Multiset Bool).map some :=
  rfl

/-- **Absent answers and faults are observed per reading.** Discarding a
computation without outcomes separates sets and counts between eager and lazy
evaluation; discarding a faulting one separates the fault verdict; repeated
outcomes separate bags and counts but not sets.  The set and bag facts are the
generic discarding laws; the count and fault facts are this semantics' own. -/
theorem absent_and_fault_witnesses :
    supportReading fullDraw .eager (.discard .absent) ≠ supportReading fullDraw .lazy (.discard .absent) ∧
      countReading fullDraw .eager (.discard .absent) ≠ countReading fullDraw .lazy (.discard .absent) ∧
      faultReading fullDraw .eager (.discard .fault) ≠ faultReading fullDraw .lazy (.discard .fault) ∧
      bagReading fullDraw .eager (.discard .twice) ≠ bagReading fullDraw .lazy (.discard .twice) ∧
      supportReading fullDraw .eager (.discard .twice) = supportReading fullDraw .lazy (.discard .twice) := by
  refine ⟨fun same => (discard_supports_iff fullDraw fullDraw_absent).mp same rfl,
    by decide +kernel, by decide +kernel, fun same => ?_,
    (discard_supports_iff fullDraw fullDraw_twice).mpr (by simp)⟩
  have one := (discard_bags_iff fullDraw fullDraw_twice).mp same
  simp at one

/-- **Duplicates under copying**, from the generic copying laws: two copies of
one answer are shared and resampled into different bags with the same set; a
coin's differ even as sets. -/
theorem copy_witnesses :
    answers fullDraw .lazy (.copy .twice) ≠ answers fullDraw .resample (.copy .twice) ∧
      supportReading fullDraw .lazy (.copy .twice) =
        supportReading fullDraw .resample (.copy .twice) ∧
      supportReading fullDraw .lazy (.copy .coin) ≠
        supportReading fullDraw .resample (.copy .coin) := by
  refine ⟨fun same => ?_, (copy_supports_iff fullDraw fullDraw_twice).mpr (by simp),
    fun same => ?_⟩
  · have atMostOne := (copy_bags_iff fullDraw fullDraw_twice).mp same
    simp at atMostOne
  · have atMostOne := (copy_supports_iff fullDraw fullDraw_coin).mp same
    simp at atMostOne

/-! ## Exact interpretations and purity -/

/-- Eager in lazy: force the discarded argument. -/
def eagerInLazy {C : Type} : Program C → Program C
  | .discard computation => .forceThen computation
  | program => program

/-- Lazy in eager: drop the discarded argument. -/
def lazyInEager {C : Type} : Program C → Program C
  | .discard _ => .unit
  | program => program

/-- Resampling in lazy: draw twice. -/
def resampleInLazy {C : Type} : Program C → Program C
  | .copy computation => .pairUp computation
  | program => program

/-- Lazy in resampling: draw once and share. -/
def lazyInResample {C : Type} : Program C → Program C
  | .copy computation => .shareUp computation
  | program => program

/-- **Every option is interpretable in every other without loss**, for every
computation type and every choice of weights: forcing, dropping, pairing and
sharing return the same outcomes, faults, absent and repeated answers included,
and the same draws. -/
theorem exact_translations (weights : Weights) :
    DistortsAtMost (observer draw weights .eager) (observer draw weights .lazy)
        (Route.graph eagerInLazy) 0 ∧
      DistortsAtMost (observer draw weights .lazy) (observer draw weights .eager)
        (Route.graph lazyInEager) 0 ∧
      DistortsAtMost (observer draw weights .resample) (observer draw weights .lazy)
        (Route.graph resampleInLazy) 0 ∧
      DistortsAtMost (observer draw weights .lazy) (observer draw weights .resample)
        (Route.graph lazyInResample) 0 :=
  ⟨distortsAtMost_zero_of_preserved draw weights _ (fun program => by cases program <;> rfl)
      (fun program => by cases program <;> rfl),
    distortsAtMost_zero_of_preserved draw weights _ (fun program => by cases program <;> rfl)
      (fun program => by cases program <;> rfl),
    distortsAtMost_zero_of_preserved draw weights _ (fun program => by cases program <;> rfl)
      (fun program => by cases program <;> rfl),
    distortsAtMost_zero_of_preserved draw weights _ (fun program => by cases program <;> rfl)
      (fun program => by cases program <;> rfl)⟩

/-- **Exact routes compose to an exact route**, by graded functoriality. -/
theorem eager_through_lazy_to_resample (weights : Weights) :
    DistortsAtMost (observer draw weights .eager) (observer draw weights .resample)
      (Route.graph (lazyInResample ∘ eagerInLazy)) 0 := by
  have composite :=
    (exact_translations draw weights).1.comp (exact_translations draw weights).2.2.2
  rw [Route.graph_comp, add_zero] at composite
  exact composite

/-- **Purity is a hypothesis.** Replacing a resampled copy by sharing keeps the
outcomes when the computation has at most one outcome, not for a coin, and it
always halves the number of draws.  The answering cases are the generic copying
law; a fault is outside its carriers and is checked directly. -/
theorem sharing_requires_purity :
    (∀ computation : Full, Multiset.card (fullDraw computation) ≤ 1 →
      answers fullDraw .resample (.copy computation) =
        answers fullDraw .resample (.shareUp computation)) ∧
      answers fullDraw .resample (.copy .coin) ≠ answers fullDraw .resample (.shareUp .coin) ∧
      ∀ computation : Full,
        draws .resample (.copy computation) ≠ draws .resample (.shareUp computation) := by
  refine ⟨?_, fun same => ?_, fun computation => by cases computation <;> decide⟩
  · intro computation pure
    cases computation with
    | absent => exact ((copy_bags_iff fullDraw fullDraw_absent).mpr (by simp)).symm
    | heads => exact ((copy_bags_iff fullDraw fullDraw_heads).mpr (by simp)).symm
    | coin => exact absurd pure (by simp [fullDraw])
    | fault => decide +kernel
    | twice => exact absurd pure (by simp [fullDraw])
  · have atMostOne := (copy_bags_iff fullDraw fullDraw_coin).mp same.symm
    simp at atMostOne

end Mettapedia.GSLT.Distinction.DemandStrategies
