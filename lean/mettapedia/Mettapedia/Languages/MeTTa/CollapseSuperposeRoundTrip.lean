import Mettapedia.Languages.MeTTa.EmptinessTaxonomy

/-!
# When `superpose (collapse e) = e`

Two round trips are often written as though they were one law.  They are not,
and only one of them is generally available.

```
   data  --superpose-->  computation  --collapse-->  data        (a section)
   computation --collapse--> data --superpose--> computation     (a retraction)
```

The **section** direction is cheap: superposing a collection creates a
computation whose whole content came from that collection, so collapsing it
back returns what was put in.  It needs only that the datum really was a
collection, which is proved here and fails, as it should, on a datum that is
not one.

The **retraction** direction — the one asked about — is where the assumptions
live.  Collapsing reifies the *value* coordinate of an outcome.  An outcome
in a real engine carries more than values: whether the search was complete,
what faults occurred, and whatever else the design records.  Superposing the
values back manufactures a fresh outcome, and the manufactured one claims
complete coverage and no faults whether or not that was true.

The main results:

* `superpose_collapse_eq_iff` — the retraction holds **exactly** on outcomes
  that are complete and fault-free.  A biconditional, so this is the full
  characterization rather than a sufficient condition.
* `no_restoration_of_outcome` — off that fragment the failure is not a
  property of this particular `superpose`.  **No function whatsoever** inverts
  `collapse`, because the information is gone.  So one cannot repair the law
  by choosing a cleverer interpretation of collections.
* `roundTrip_launders_incompleteness` — the failure is not merely lossy, it
  is unsound in a specific direction: a search that did not finish comes back
  reporting that it did.

The last result is the one with operational teeth, and it also suggests the
repair.  `boundedObserve_honest` shows that an observer which reports its own
truncation cannot launder: whenever it claims completeness, it really did
return everything.  That is the precise sense in which incompleteness belongs
to the *observation* rather than to the answers.
-/

namespace Mettapedia.Languages.MeTTa.RoundTrip

open Mettapedia.Languages.MeTTa.Emptiness
open Mettapedia.GSLT.Core.NonFactorization

/-! ## Outcomes carry more than values -/

/-- Whether a search covered its scope. -/
inductive Coverage where
  /-- The scope was exhausted; absence of an answer is a negative result. -/
  | complete
  /-- The scope was not exhausted; absence of an answer means nothing. -/
  | incomplete (reason : String)
deriving DecidableEq, Repr

/-- What a computation reports.  Values are one coordinate among several;
treating the whole outcome as its value bag is precisely the error this
module measures. -/
structure Outcome where
  /-- The answers found. -/
  values : List Datum
  /-- Whether the search finished. -/
  coverage : Coverage
  /-- Faults raised along the way. -/
  faults : List String
deriving DecidableEq, Repr

/-! ## The two directions -/

/-- Read a collection datum back as a bag.  A datum that is not a collection
contributes no branches. -/
def decode : Datum → List Datum
  | .nil => []
  | .cons head tail => head :: decode tail
  | _ => []

/-- Reify an outcome as one datum.  Only the values survive — this is the
whole point, and the whole problem. -/
def collapseValues (outcome : Outcome) : Datum := encode outcome.values

/-- Interpret a collection datum as a computation: one branch per element.
The result necessarily claims complete coverage and no faults, because a
collection literal carries no such information. -/
def superpose (datum : Datum) : Outcome :=
  { values := decode datum, coverage := .complete, faults := [] }

/-- Encoding a bag and reading it back is the identity: order and
multiplicity are preserved. -/
theorem decode_encode (bag : List Datum) : decode (encode bag) = bag := by
  induction bag with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp [encode, decode, inductionHypothesis]

/-! ## The retraction: `superpose (collapse e) = e`

This is the direction with assumptions.  They turn out to be exactly two. -/

/-- **The characterization.**  The retraction holds precisely for outcomes
that are complete and fault-free.  Nothing about the values matters: order,
multiplicity and content always survive.  What does not survive is everything
that is not a value. -/
theorem superpose_collapse_eq_iff (outcome : Outcome) :
    superpose (collapseValues outcome) = outcome ↔
      outcome.coverage = .complete ∧ outcome.faults = [] := by
  constructor
  · intro roundTrips
    refine ⟨?_, ?_⟩
    · exact (congrArg Outcome.coverage roundTrips).symm
    · exact (congrArg Outcome.faults roundTrips).symm
  · rintro ⟨complete, noFaults⟩
    obtain ⟨values, coverage, faults⟩ := outcome
    simp only at complete noFaults
    subst complete
    subst noFaults
    simp [superpose, collapseValues, decode_encode]

/-- On the pure fragment the law holds. -/
theorem superpose_collapse_of_pure (values : List Datum) :
    superpose (collapseValues ⟨values, .complete, []⟩) = ⟨values, .complete, []⟩ :=
  superpose_collapse_eq_iff _ |>.mpr ⟨rfl, rfl⟩

/-! ## Off the pure fragment, no interpretation can repair it

The failure above is stated for one definition of `superpose`.  The following
is stronger and is the reason the law cannot be recovered by redesigning the
collection interpretation: two outcomes differing only outside their values
collapse to the *same* datum, so nothing downstream can tell them apart. -/

/-- Two outcomes with the same answers and different coverage.  The observer
identifies them. -/
def coverageFiber : NonTrivialFiber collapseValues (id : Outcome → Outcome) where
  left := ⟨[.unit], .complete, []⟩
  right := ⟨[.unit], .incomplete "budget", []⟩
  sameShadow := rfl
  differentValue := by decide

/-- **No function inverts the value observer.**  Since collapse keeps only
the values, no interpretation of collections — however clever — restores the
outcome it came from.  The retraction is therefore genuinely partial, not
merely awkwardly defined. -/
theorem no_restoration_of_outcome :
    ¬ ∃ restore : Datum → Outcome, ∀ outcome, restore (collapseValues outcome) = outcome :=
  coverageFiber.not_factors

/-- The same for faults. -/
def faultFiber : NonTrivialFiber collapseValues (id : Outcome → Outcome) where
  left := ⟨[.unit], .complete, []⟩
  right := ⟨[.unit], .complete, ["divide by zero"]⟩
  sameShadow := rfl
  differentValue := by decide

/-! ## The failure has a direction

Losing information would be tolerable.  What actually happens is worse: the
manufactured outcome asserts the good case. -/

/-- **The round trip launders incompleteness into completeness.**  A search
that ran out of budget returns claiming it exhausted its scope — so a
subsequent "not found" reads as a negative result rather than as ignorance. -/
theorem roundTrip_launders_incompleteness (values : List Datum) (reason : String) :
    (superpose (collapseValues ⟨values, .incomplete reason, []⟩)).coverage = .complete :=
  rfl

/-- And it discards faults, so a broken question comes back as a clean one. -/
theorem roundTrip_drops_faults (values : List Datum) (message : String) :
    (superpose (collapseValues ⟨values, .complete, [message]⟩)).faults = [] :=
  rfl

/-! ## The section: `collapse (superpose d) = d`

The other direction, for contrast.  It needs only well-formedness of the
datum, because superposing supplies exactly the coordinates collapse reads
back. -/

/-- A datum that really is a collection. -/
inductive IsCollection : Datum → Prop
  | nil : IsCollection .nil
  | cons (head : Datum) {tail : Datum} :
      IsCollection tail → IsCollection (.cons head tail)

theorem encode_decode {datum : Datum} (collection : IsCollection datum) :
    encode (decode datum) = datum := by
  induction collection with
  | nil => rfl
  | cons head _ inductionHypothesis =>
      simp [decode, encode, inductionHypothesis]

/-- **The section holds for every collection**, with no purity assumption at
all — superposing cannot introduce incompleteness or faults, so there is
nothing for collapse to lose. -/
theorem collapse_superpose {datum : Datum} (collection : IsCollection datum) :
    collapseValues (superpose datum) = datum := by
  simp [collapseValues, superpose, encode_decode collection]

/-- Well-formedness is genuinely needed: a datum that is not a collection is
not recovered. -/
theorem collapse_superpose_needs_collection :
    collapseValues (superpose (.sym "x")) ≠ .sym "x" := by
  decide

/-! ## The repair

An observer that reports its own truncation cannot launder.  This is the
precise sense in which incompleteness belongs to the observation rather than
to the answers: it is produced where the bound is applied, not carried by the
values. -/

/-- A bounded observer that records whether its bound bit. -/
def boundedObserve (budget : Nat) (outcome : Outcome) : Outcome where
  values := outcome.values.take budget
  coverage :=
    if outcome.values.length ≤ budget then outcome.coverage else .incomplete "budget"
  faults := outcome.faults

/-- **An honest bounded observer never launders.**  Whenever it reports
completeness it really did return every answer — so the precondition of the
retraction is met exactly when it is truthfully claimed. -/
theorem boundedObserve_honest (budget : Nat) (outcome : Outcome)
    (claimsComplete : (boundedObserve budget outcome).coverage = .complete) :
    (boundedObserve budget outcome).values = outcome.values := by
  by_cases withinBudget : outcome.values.length ≤ budget
  · simp [boundedObserve, List.take_of_length_le withinBudget]
  · simp [boundedObserve, withinBudget] at claimsComplete

/-- A bound that bites is reported, rather than silently truncating. -/
theorem boundedObserve_reports_truncation (budget : Nat) (outcome : Outcome)
    (overBudget : ¬ outcome.values.length ≤ budget) :
    (boundedObserve budget outcome).coverage = .incomplete "budget" := by
  simp [boundedObserve, overBudget]

end Mettapedia.Languages.MeTTa.RoundTrip
