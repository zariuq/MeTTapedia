import Mettapedia.GSLT.Core.WeightedMuScheduler

/-!
# Value grading is irreducible to crisp guards

## Background and attribution

The framing formalized here is due to L. G. Meredith (F1R3FLY.io).  In
*Observation Disciplines* an observation discipline over a term language is
presented as `L(Σ, R, S, V)`: a signature of nameable shapes, a rewrite
system of visible steps, a container in which witnesses are collected, and
a value algebra in which an observation returns.  The first two components
are read off the presentation; the last two are genuine parameters.  `V`,
the value dial, is the component this module concerns.

That work also supplies the placement at issue.  A formula may be used as a
specification, as a test, or as a *guard* written on a binder — the
where-clause of a for-comprehension, evaluated at the moment a
communication is about to occur, whose value resolves the system's own
non-determinism.  Grading that guard, rather than keeping it crisp, is the
change whose consequences are studied here.

The statement proved below is the formal counterpart of the principle
Meredith states as **"weighing is not selecting"** — that assigning weights
and choosing a winner are distinct operations, identified there with the
quantifier and selection monads respectively.  This module gives one
direction of that separation a machine-checked form at guard granularity,
against the graded-clause language actually used by this project's
scheduler.  The companion observation that weight maps are graded clauses
in disjunctive normal form is likewise Meredith's.

* L. G. Meredith, *Observation Disciplines: How logics are generated from
  term structure, and why graded where-clauses are the mortal scientist's
  instrument*, F1R3FLY.io.  `rho-mind/observation-disciplines` in
  `github.com/F1R3FLY-io/publications`; read at commit `64bf45a`
  (2026-08-14).  Slogan 0.3.1 and Figure 1 give the four components;
  Part 0 §0.4 gives the three placements; Part V ("Price") opens with
  "Weighing is not selecting" and its Principle (Division of labour);
  Part VIII §"What is shown" item 8 records the monad identification.
* L. G. Meredith, *graded where-clauses*, `fuzzyware/graded-where` in the
  same repository, for weight maps and the graded for-comprehension.

Nothing below is claimed as a restatement of a theorem of that work: the
separation there is drawn between monads, whereas the theorem here is a
non-existence statement about Boolean guards acting on candidate bags.

## What this module proves

The value dial has two directions.  One is conservative and already
recorded: the crisp discipline is the `Bool` instance of the graded one
(`WeighClause.crisp_true_conservative`,
`WeighClause.crisp_false_rejects`), so grading extends crisp guarding
without changing it.  This module addresses the other direction, and
separates two obstructions that are easy to conflate:

* **Locality.**  A crisp clause acts on a candidate bag by pointwise
  filtration, and selection is not filtration
  (`no_crispClause_isMaxSelection`).  This is about the guard's *arity*:
  the control `boolBagTest_isMaxSelection` shows a Boolean test that sees
  the whole bag succeeds, so the value algebra is not what fails here.
* **Resolution.**  Holding the arity at the real placement --- one
  observation per candidate, an arbitrary aggregator over the results ---
  candidates sharing an observation are indistinguishable to every
  aggregator, so a two-valued observation cannot carry a three-level
  ranking (`no_boolObservation_isMaxSelection`), while a weight-valued one
  can (`weightObservation_supportsMaxSelection`).  **This** is the value-dial
  statement.

Both are needed, and only the second is evidence that `V` is a component
in its own right.  Neither says a five-field language cannot *compute*
maxima: it can, by encoding weights as terms and comparisons as rewrite
steps.  The distinction that survives is where the accounting lives ---
in the language's semantics, or in a program written in the language.

A crisp guard is one Boolean observation evaluated per candidate.  Its
action on a candidate bag is therefore pointwise filtration: whether a
candidate survives depends on that candidate alone.  Graded selection is
not pointwise: keeping a weight-maximal candidate requires comparing it
against the *other* members of the same bag.  The two are separated by a
two-candidate witness, and the separation applies verbatim to the graded
scheduler's clause language: no `WeighClause Bool` guard has a bag action
that performs maximum selection over candidates of distinct weights.

Scope: this is irreducibility of the value dial *at fixed
observation granularity* — one guard evaluation per candidate over one
shared candidate bag.  It does not claim that a five-field language cannot
*simulate* selection globally; it can, by enlarging the signature and the
rewrite system (encoding weights as terms and comparisons as steps).  That
is precisely the point: any such simulation pays in the signature and
rewrite dials, so the value dial buys, in one evaluation, something the
crisp discipline must buy with new syntax and new steps.  The converse
irreducibility — that a signature-level cost wrapping is not expressible
as any value readout — is witnessed separately by the cost lane's
two-colour continuation retyping and is not formalized in this module.

Delivery-level companions (below) complete the picture at result
granularity.  The conservative direction is made exact: a crisp
where-clause delivers *identically* to an `if` at the head of the transform
with an `(empty)` failure branch (`whereDeliver_eq_ifDeliver`), and that
identity is the `Bool` corner of graded delivery
(`gradedDeliver_bool_corner`).  What escapes sugarhood arrives with
normalization: a normalized (Gillespie / sampled) discipline needs the
race total in addition to each candidate's weight — sufficient
(`raceShare_eq_of_total_eq`) and necessary
(`normalizedShare_not_candidatewise`).  Finally, firing is two-axis:
semiring annihilation gates the zero grade (`zero_grade_never_fires`),
but affordability lives outside the value algebra
(`grade_annihilation_cannot_gate`).
-/

namespace Mettapedia.GSLT.Core

open Mettapedia.GSLT.Core.WeightedMuScheduler

universe uCandidate uResult

variable {Candidate : Type uCandidate}

/-- A bag transformer is pointwise when one per-candidate Boolean test
decides survival, independently of the rest of the bag.  This is exactly
the action available to a crisp where-clause in the sense of Meredith's
guard placement: the formula is evaluated against the candidate message,
and nothing else. -/
def PointwiseSelection
    (select : Multiset Candidate → Multiset Candidate) : Prop :=
  ∃ keep : Candidate → Bool,
    ∀ bag : Multiset Candidate, select bag = bag.filter (keep · = true)

/-- Bag-level maximum selection, as a membership specification: a candidate
survives exactly when it belongs to the bag and no member of the same bag
strictly outweighs it. -/
def IsMaxSelection (weight : Candidate → ℕ)
    (select : Multiset Candidate → Multiset Candidate) : Prop :=
  ∀ (bag : Multiset Candidate) (candidate : Candidate),
    candidate ∈ select bag ↔
      candidate ∈ bag ∧ ∀ other ∈ bag, weight other ≤ weight candidate

/-- The canonical maximum selector.  Naming it lets the positive and
negative halves below refer to one construction rather than merely to an
existential witness. -/
noncomputable def maxSelector (weight : Candidate → ℕ)
    (bag : Multiset Candidate) : Multiset Candidate :=
  bag.filter
    (fun candidate => ∀ other ∈ bag, weight other ≤ weight candidate)

theorem maxSelector_isMaxSelection (weight : Candidate → ℕ) :
    IsMaxSelection weight (maxSelector weight) := by
  classical
  intro bag candidate
  simp [maxSelector, Multiset.mem_filter]

/-- Maximum selection is realizable, so the specification below is not
refuted vacuously: filtering by bag-relative maximality inhabits it. -/
theorem exists_isMaxSelection (weight : Candidate → ℕ) :
    ∃ select : Multiset Candidate → Multiset Candidate,
      IsMaxSelection weight select :=
  ⟨maxSelector weight, maxSelector_isMaxSelection weight⟩

/-- **Selection is not filtration.**  As soon as two candidates have
distinct weights, no per-candidate Boolean test computes maximum
selection: the low candidate must be kept when alone and dropped when the
high candidate joins the bag, and a pointwise test cannot tell the two
bags apart.

This is the bag-level form of Meredith's "weighing is not selecting":
there the two operations are separated as the quantifier and selection
monads, here as a non-existence statement about pointwise transformers. -/
theorem not_pointwiseSelection_of_isMaxSelection
    (weight : Candidate → ℕ) {low high : Candidate}
    (outweighed : weight low < weight high)
    {select : Multiset Candidate → Multiset Candidate}
    (maximal : IsMaxSelection weight select) :
    ¬ PointwiseSelection select := by
  rintro ⟨keep, pointwise⟩
  have lowAlone : low ∈ select {low} := by
    rw [maximal]
    refine ⟨Multiset.mem_singleton_self low, ?_⟩
    intro other membership
    rw [Multiset.mem_singleton] at membership
    subst membership
    exact le_refl _
  have keepLow : keep low = true := by
    have := lowAlone
    rw [pointwise, Multiset.mem_filter] at this
    exact this.2
  have lowInPair : low ∈ ({low, high} : Multiset Candidate) := by
    simp
  have lowSurvivesPair : low ∈ select {low, high} := by
    rw [pointwise, Multiset.mem_filter]
    exact ⟨lowInPair, by simp [keepLow]⟩
  have lowMaximalPair := (maximal {low, high} low).mp lowSurvivesPair
  have highLe : weight high ≤ weight low := by
    refine lowMaximalPair.2 high ?_
    simp
  exact absurd highLe (not_le.mpr outweighed)

/-! ## The separation lands on the scheduler's clause language -/

/-- The bag action of a crisp clause: evaluate the Boolean grade at each
candidate and keep the accepted ones.  This is the crisp where-clause of
the graded scheduler, acting on one candidate bag. -/
def crispClauseBagAction (clause : WeighClause Bool Candidate)
    (bag : Multiset Candidate) : Multiset Candidate :=
  bag.filter (fun candidate => WeighClause.eval candidate clause = true)

/-- Every crisp clause acts pointwise: its grade at a candidate never
consults the rest of the bag. -/
theorem crispClauseBagAction_pointwise
    (clause : WeighClause Bool Candidate) :
    PointwiseSelection (crispClauseBagAction clause) :=
  ⟨fun candidate => WeighClause.eval candidate clause,
    fun _ => rfl⟩

/-- **No crisp where-clause performs graded maximum selection.**  For any
two candidates of distinct weights, no `WeighClause Bool` guard has a bag
action satisfying the maximum-selection specification.  The value dial is
therefore irreducible to the crisp discipline at guard granularity: the
graded scheduler's selection genuinely uses the value algebra.

Scope, stated exactly: this obstruction is one of **arity**, not of the
value algebra.  A Boolean test with access to the whole bag does perform
maximum selection (`boolBagTest_isMaxSelection`), so what defeats the
crisp guard here is bag-blindness.  The statement that separates value
algebras is `no_boolObservation_isMaxSelection` below, which holds the
arity fixed and varies only what the observation returns. -/
theorem no_crispClause_isMaxSelection
    (weight : Candidate → ℕ) {low high : Candidate}
    (outweighed : weight low < weight high)
    (clause : WeighClause Bool Candidate) :
    ¬ IsMaxSelection weight (crispClauseBagAction clause) :=
  fun maximal =>
    not_pointwiseSelection_of_isMaxSelection weight outweighed maximal
      (crispClauseBagAction_pointwise clause)

/-! ## The value dial proper: observation resolution

The separation above is about *locality*, not about values: a Boolean test
with access to the whole bag performs maximum selection perfectly
(`boolBagTest_isMaxSelection`), so bag-blindness rather than the value
algebra is what defeats a crisp guard there.

The statement that genuinely concerns the value dial holds the guard's
arity fixed at the real placement — one observation per candidate — and
lets an arbitrary aggregator do the bag-level work.  Then the only channel
from a candidate to the decision is its observed value, so candidates
sharing an observation are indistinguishable to *every* aggregator.  A
value algebra can therefore support ranking only if it has room to carry
the ranking, and `Bool` does not. -/

/-- A Boolean test that may consult the whole bag does perform maximum
selection.  This control isolates the locality result: it is what
shows that the earlier obstruction is arity, not value. -/
theorem boolBagTest_isMaxSelection (weight : Candidate → ℕ) :
    IsMaxSelection weight
      (fun bag => bag.filter
        (fun candidate => ∀ other ∈ bag, weight other ≤ weight candidate)) := by
  classical
  intro bag candidate
  simp [Multiset.mem_filter]

/-- An aggregator's only channel from a candidate is its observed value.
Candidates of one bag sharing an observation must therefore share a fate.
This is exactly the guard placement: the clause is evaluated against the
candidate, and the scheduler sees the resulting values. -/
def AggregatorRespects {Value : Type uValue} (observe : Candidate → Value)
    (select : Multiset Candidate → Multiset Candidate) : Prop :=
  ∀ (bag : Multiset Candidate) (first second : Candidate),
    first ∈ bag → second ∈ bag → observe first = observe second →
    (first ∈ select bag ↔ second ∈ select bag)

/-- **A collision in the observation destroys selection.**  If two
candidates of distinct weight receive the same observed value, no
aggregator over those observations can perform maximum selection --- no
matter how rich the aggregator is, because the two candidates are
indistinguishable to it. -/
theorem no_isMaxSelection_of_observation_collision
    {Value : Type uValue} (weight : Candidate → ℕ)
    (observe : Candidate → Value) {low high : Candidate}
    (outweighed : weight low < weight high)
    (collision : observe low = observe high)
    {select : Multiset Candidate → Multiset Candidate}
    (respects : AggregatorRespects observe select)
    (maximal : IsMaxSelection weight select) : False := by
  have lowMember : low ∈ ({low, high} : Multiset Candidate) := by simp
  have highMember : high ∈ ({low, high} : Multiset Candidate) := by simp
  have highSurvives : high ∈ select {low, high} := by
    rw [maximal]
    refine ⟨highMember, ?_⟩
    intro other membership
    have : other = low ∨ other = high := by
      simpa [Multiset.insert_eq_cons] using membership
    rcases this with rfl | rfl
    · exact le_of_lt outweighed
    · exact le_refl _
  have lowSurvives : low ∈ select {low, high} :=
    (respects {low, high} low high lowMember highMember collision).mpr
      highSurvives
  have lowMaximal := (maximal {low, high} low).mp lowSurvives
  have highLe : weight high ≤ weight low := lowMaximal.2 high highMember
  exact absurd highLe (not_le.mpr outweighed)

/-- **A two-valued observation cannot carry a three-level ranking.**  Given
three candidates of strictly increasing weight, every `Bool`-valued
observation collides on two of them, so no aggregator over a crisp guard
performs maximum selection.

This is the value-dial statement: the guard's arity is fixed at one
observation per candidate and the aggregator is arbitrary, so the only
thing varying is what the observation returns.  `Bool` fails for a reason
of resolution --- two values, three levels --- and a weight-valued
observation succeeds (`weightObservation_supportsMaxSelection`). -/
theorem no_boolObservation_isMaxSelection
    (weight : Candidate → ℕ) (observe : Candidate → Bool)
    {small middle large : Candidate}
    (smallLtMiddle : weight small < weight middle)
    (middleLtLarge : weight middle < weight large)
    {select : Multiset Candidate → Multiset Candidate}
    (respects : AggregatorRespects observe select)
    (maximal : IsMaxSelection weight select) : False := by
  have collide : ∃ low high : Candidate,
      weight low < weight high ∧ observe low = observe high := by
    rcases Bool.eq_false_or_eq_true (observe small) with smallObs | smallObs <;>
      rcases Bool.eq_false_or_eq_true (observe middle) with middleObs | middleObs <;>
        rcases Bool.eq_false_or_eq_true (observe large) with largeObs | largeObs
    · exact ⟨small, middle, smallLtMiddle, by rw [smallObs, middleObs]⟩
    · exact ⟨small, middle, smallLtMiddle, by rw [smallObs, middleObs]⟩
    · exact ⟨small, large, smallLtMiddle.trans middleLtLarge,
        by rw [smallObs, largeObs]⟩
    · exact ⟨middle, large, middleLtLarge, by rw [middleObs, largeObs]⟩
    · exact ⟨middle, large, middleLtLarge, by rw [middleObs, largeObs]⟩
    · exact ⟨small, large, smallLtMiddle.trans middleLtLarge,
        by rw [smallObs, largeObs]⟩
    · exact ⟨small, middle, smallLtMiddle, by rw [smallObs, middleObs]⟩
    · exact ⟨small, middle, smallLtMiddle, by rw [smallObs, middleObs]⟩
  obtain ⟨low, high, outweighed, collision⟩ := collide
  exact no_isMaxSelection_of_observation_collision weight observe outweighed
    collision respects maximal

/-- The exact information criterion for an observation to support ranking:
equal observations must imply equal weights.  This is deliberately weaker
than injectivity of `observe`; candidates may remain indistinguishable when
their weights agree. -/
def WeightFactorsThrough {Value : Type uValue}
    (observe : Candidate → Value) (weight : Candidate → ℕ) : Prop :=
  ∀ ⦃first second : Candidate⦄,
    observe first = observe second → weight first = weight second

/-- The canonical maximum selector respects an observation exactly when
the weight factors through that observation.  This is the value-resolution
criterion: neither cardinality alone nor injectivity is the right condition. -/
theorem maxSelector_respects_iff {Value : Type uValue}
    (observe : Candidate → Value) (weight : Candidate → ℕ) :
    AggregatorRespects observe (maxSelector weight) ↔
      WeightFactorsThrough observe weight := by
  classical
  constructor
  · intro respects first second observed
    apply le_antisymm
    · by_contra notLe
      have outweighed : weight second < weight first := Nat.lt_of_not_ge notLe
      exact no_isMaxSelection_of_observation_collision weight observe outweighed
        observed.symm respects (maxSelector_isMaxSelection weight)
    · by_contra notLe
      have outweighed : weight first < weight second := Nat.lt_of_not_ge notLe
      exact no_isMaxSelection_of_observation_collision weight observe outweighed
        observed respects (maxSelector_isMaxSelection weight)
  · intro factors bag first second firstMember secondMember observed
    have sameWeight : weight first = weight second := factors observed
    simp only [maxSelector, Multiset.mem_filter]
    constructor
    · rintro ⟨_, maximalFirst⟩
      refine ⟨secondMember, ?_⟩
      intro other membership
      rw [← sameWeight]
      exact maximalFirst other membership
    · rintro ⟨_, maximalSecond⟩
      refine ⟨firstMember, ?_⟩
      intro other membership
      rw [sameWeight]
      exact maximalSecond other membership

/-- An observation supports maximum selection when some bag aggregator both
uses candidates only through their observations and realizes the maximum
specification. -/
def ObservationSupportsMaxSelection {Value : Type uValue}
    (observe : Candidate → Value) (weight : Candidate → ℕ) : Prop :=
  ∃ select : Multiset Candidate → Multiset Candidate,
    AggregatorRespects observe select ∧ IsMaxSelection weight select

/-- **Exact value-resolution theorem.**  An observation supports maximum
selection if and only if the target weight factors through it.  Thus the
necessary information is precisely the ranking quotient, not an arbitrary
choice of a large carrier. -/
theorem observationSupportsMaxSelection_iff {Value : Type uValue}
    (observe : Candidate → Value) (weight : Candidate → ℕ) :
    ObservationSupportsMaxSelection observe weight ↔
      WeightFactorsThrough observe weight := by
  constructor
  · rintro ⟨select, respects, maximal⟩ first second observed
    apply le_antisymm
    · by_contra notLe
      have outweighed : weight second < weight first := Nat.lt_of_not_ge notLe
      exact no_isMaxSelection_of_observation_collision weight observe outweighed
        observed.symm respects maximal
    · by_contra notLe
      have outweighed : weight first < weight second := Nat.lt_of_not_ge notLe
      exact no_isMaxSelection_of_observation_collision weight observe outweighed
        observed respects maximal
  · intro factors
    exact ⟨maxSelector weight,
      (maxSelector_respects_iff observe weight).2 factors,
      maxSelector_isMaxSelection weight⟩

/-- The positive half: observing the weight itself carries exactly the
information required for maximum selection. -/
theorem weightObservation_supportsMaxSelection (weight : Candidate → ℕ) :
    ObservationSupportsMaxSelection weight weight := by
  rw [observationSupportsMaxSelection_iff]
  intro first second observed
  exact observed

/-! ## Positive and negative examples -/

-- Positive: the specification is genuinely inhabited over concrete
-- candidates, so the refutations above are about a real selector.
example : ∃ select : Multiset ℕ → Multiset ℕ, IsMaxSelection id select :=
  exists_isMaxSelection id

-- Negative: with candidates 1 and 2 at their own weights, no crisp clause
-- selects maxima.
example (clause : WeighClause Bool ℕ) :
    ¬ IsMaxSelection id (crispClauseBagAction clause) :=
  no_crispClause_isMaxSelection id (low := 1) (high := 2)
    (by norm_num) clause

-- Negative control for the separation itself: pointwise selection is not
-- refuted for free — the identity filter is pointwise, so the refutation
-- genuinely uses maximality rather than holding of every transformer.
example : PointwiseSelection (fun bag : Multiset ℕ => bag.filter (fun _ => True)) := by
  refine ⟨fun _ => true, ?_⟩
  intro bag
  simp

/-- Conditioning on a **fixed threshold** stays within the crisp
discipline: `θ ≤ w(candidate)` is an ordinary per-candidate Boolean
test.  The genuinely irreducible ingredient of weighted selection is
therefore the comparison *between candidates of one bag*
(`no_crispClause_isMaxSelection`), never the mere use of an ordered or
interval-valued codomain. -/
theorem thresholdSelection_pointwise
    (weight : Candidate → ℕ) (threshold : ℕ) :
    PointwiseSelection
      (fun bag : Multiset Candidate =>
        bag.filter (fun candidate => threshold ≤ weight candidate)) := by
  refine ⟨fun candidate => decide (threshold ≤ weight candidate),
    fun bag => ?_⟩
  simp

/-! ## Delivery: the crisp where-clause is exactly an if-guarded transform

The guard-granularity results above say what a crisp *guard* cannot do.
At *delivery* granularity the complementary exactness holds: the two
MeTTa surface forms `(= $p $t $w)` (crisp guard) and
`(= $p (if $w $t (empty)))` (an `if` at the head of the transform)
deliver the same result bag.  Under the usual evaluation order the
`if`'s condition is evaluated before either branch, so not even the
evaluation-order argument separates the forms: the crisp where-clause is
a semantic reshuffling, provably.  What the graded generalization changes
is recorded by `gradedDeliver` and its `Bool` corner. -/

section Delivery

variable {Result : Type uResult} (w : Candidate → Bool) (t : Candidate → Result)

/-- Crisp where-clause delivery: keep the rows the guard admits, then apply
the transform.  This is `(= $p $t $w)` read as a bag producer. -/
def whereDeliver (bag : Multiset Candidate) : Multiset Result :=
  (bag.filter (fun σ => w σ = true)).map t

/-- If-guarded transform delivery: every row runs the head-`if` of
`(= $p (if $w $t (empty)))`; admitted rows yield the transformed result,
rejected rows yield `(empty)` — no result at all. -/
def ifDeliver (bag : Multiset Candidate) : Multiset Result :=
  bag.filterMap (fun σ => if w σ = true then some (t σ) else none)

variable {w t}

/-- **The crisp equivalence.**  For a Boolean guard the two forms produce
identical result bags: the crisp where-clause is exactly an `if` at the
head of the transform with `(empty)` in the failure branch.  Positive
example: the sugar direction. -/
theorem whereDeliver_eq_ifDeliver (bag : Multiset Candidate) :
    whereDeliver w t bag = ifDeliver w t bag := by
  unfold whereDeliver ifDeliver
  induction bag using Multiset.induction_on with
  | empty => rfl
  | cons σ rest ih =>
      cases hσ : w σ <;> simp [hσ, ih]

/-- Graded delivery: every row survives, annotated with its value — the
result bag becomes a weighted bag, a `V`-valued support with
coefficients. -/
def gradedDeliver {V : Type*} [CommSemiring V]
    (weight : Candidate → V) (t : Candidate → Result)
    (bag : Multiset Candidate) : Multiset (V × Result) :=
  bag.map fun σ => (weight σ, t σ)

/-- **The Bool corner.**  Filtering a `Bool`-graded delivery down to its
admitted projections recovers the crisp where-clause: the graded form
specializes to the crisp form exactly, so the equivalence above is the
degenerate `V = Bool` case rather than an accidental identity. -/
theorem gradedDeliver_bool_corner (w : Candidate → Bool) (t : Candidate → Result)
    (bag : Multiset Candidate) :
    (gradedDeliver w t bag).filterMap
        (fun p : Bool × Result => if p.1 = true then some p.2 else none) =
      whereDeliver w t bag := by
  unfold gradedDeliver whereDeliver
  induction bag using Multiset.induction_on with
  | empty => rfl
  | cons σ rest ih =>
      cases hσ : w σ <;> simp [hσ, ih]

end Delivery

/-! ## Normalized readings need the race total

A normalized (Gillespie / sampled) discipline assigns each candidate the
share `weight / raceTotal`.  The total is the *only* race-set information
such a discipline adds to a candidate's own weight — it suffices
(`raceShare_eq_of_total_eq`) and it is necessary
(`normalizedShare_not_candidatewise`).  Over a finite, fully enumerated
race set the total exists by construction; over a stream it must be
declared as a window. -/

/-- The total weight a race aggregates: the denominator of every
normalized (Gillespie / sampled) discipline. -/
noncomputable def raceTotal (bag : Multiset ℝ) : ℝ :=
  bag.sum

/-- The normalized share of one candidate: its weight over the race
total. -/
noncomputable def raceShare (w : Candidate → ℝ) (bag : Multiset Candidate)
    (σ : Candidate) : ℝ :=
  w σ / raceTotal (bag.map w)

/-- **The total suffices.**  Two race sets with the same aggregate weight
assign the candidate the same share. -/
theorem raceShare_eq_of_total_eq (w : Candidate → ℝ) (σ : Candidate)
    (b₁ b₂ : Multiset Candidate)
    (h : raceTotal (b₁.map w) = raceTotal (b₂.map w)) :
    raceShare w b₁ σ = raceShare w b₂ σ := by
  unfold raceShare
  rw [h]

/-- **The total is necessary.**  Two bags in which one candidate carries
the same weight can assign it different shares — here a singleton race
versus a two-candidate race at uniform positive weight — so no
per-candidate computation realizes a normalized discipline.  Negative
example: what candidate-local data cannot see, formalized. -/
theorem normalizedShare_not_candidatewise :
    ∃ w : Bool → ℝ, ∃ σ : Bool, ∃ b₁ b₂ : Multiset Bool,
      σ ∈ b₁ ∧ σ ∈ b₂ ∧ (∀ τ ∈ b₁, 0 < w τ) ∧ (∀ τ ∈ b₂, 0 < w τ) ∧
        raceShare w b₁ σ ≠ raceShare w b₂ σ := by
  have singleton_share :
      raceShare (fun _ : Bool => (1 : ℝ)) ({true} : Multiset Bool) true = 1 := by
    simp [raceShare, raceTotal, Multiset.map_singleton, Multiset.sum_singleton]
  have pair_share :
      raceShare (fun _ : Bool => (1 : ℝ)) ({true, false} : Multiset Bool) true =
        1 / 2 := by
    simp [raceShare, raceTotal, Multiset.insert_eq_cons, Multiset.map_singleton,
      Multiset.sum_singleton, one_add_one_eq_two]
  refine ⟨fun _ => 1, true, {true}, {true, false}, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · simp
  · intro τ _
    norm_num
  · intro τ _
    norm_num
  · rw [singleton_share, pair_share]
    norm_num

/-! ## Firing: value and cost are two axes -/

/-- A candidate fires exactly when its grade is nonzero *and* its price
is affordable.  The first conjunct belongs to the value semiring; the
second to the cost ledger's order. -/
def fires (value price purse : ℝ) : Prop :=
  value ≠ 0 ∧ price ≤ purse

/-- Positive example: grade and budget together license firing. -/
theorem fires_of_grade_and_budget {value price purse : ℝ}
    (hv : value ≠ 0) (hc : price ≤ purse) : fires value price purse :=
  ⟨hv, hc⟩

/-- Negative example: the value semiring's zero gates firing — its
annihilation law is exactly this conjunct. -/
theorem zero_grade_never_fires (price purse : ℝ) : ¬ fires 0 price purse := by
  norm_num [fires]

/-- Negative example: no value-algebra condition expresses affordability.
A candidate with a nonzero grade and an unaffordable price does not fire,
yet every condition of the pure value fragment `value ≠ 0` already
holds — the purse is invisible to the semiring's multiplication, so cost
cannot be folded into the guard's algebra. -/
theorem grade_annihilation_cannot_gate :
    ∃ value purse price : ℝ, value ≠ 0 ∧ ¬ fires value price purse := by
  refine ⟨1, 0, 1, by norm_num, ?_⟩
  norm_num [fires]

/-! ## Axiom audit for the delivery-level companions -/

#print axioms whereDeliver_eq_ifDeliver
#print axioms gradedDeliver_bool_corner
#print axioms raceShare_eq_of_total_eq
#print axioms normalizedShare_not_candidatewise
#print axioms zero_grade_never_fires
#print axioms grade_annihilation_cannot_gate

end Mettapedia.GSLT.Core
