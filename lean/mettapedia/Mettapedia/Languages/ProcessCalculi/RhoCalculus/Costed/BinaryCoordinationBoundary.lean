import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.AtomicResourceJoinExamples
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ParallelWave

/-!
# Binary-coordination boundary for atomic cost joins

One core rho `COMM` consumes exactly two top-level endpoint occurrences.  A
split cost event funded by two selected purse occurrences consumes four source
occurrences atomically.  Consequently that event has no occurrence-cardinality
preserving implementation as one core binary `COMM`.  A binary implementation
must introduce administrative reductions or target a genuine multiway join.

This local theorem does not claim that every weak multi-step encoding is
impossible.  It isolates the precise one-step coordination mismatch that such
an encoding must account for.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction

namespace CoreBinary

/-- Count the primitive `COMM` rules inside one contextual core-rho step.  The
other constructors only transport a single underlying communication through
structural or parallel context. -/
def primitiveCommCount {source target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} :
    Reduces source target → Nat
  | .comm => 1
  | .equiv _ step _ => primitiveCommCount step
  | .par step => primitiveCommCount step
  | .par_any step => primitiveCommCount step
  | .par_set step => primitiveCommCount step
  | .par_set_any step => primitiveCommCount step

/-- Every core one-step derivation contains exactly one primitive binary
communication, even when it is transported through context. -/
theorem primitiveCommCount_eq_one
    {source target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (step : Reduces source target) : primitiveCommCount step = 1 := by
  induction step <;> simp [primitiveCommCount, *]

/-- Count primitive communications along an exactly indexed core trace. -/
def tracePrimitiveCommCount :
    {depth : Nat} → {source target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern} →
      ReducesN depth source target → Nat
  | 0, _, _, .zero _ => 0
  | _ + 1, _, _, .succ step rest =>
      primitiveCommCount step + tracePrimitiveCommCount rest

/-- The exact-step index is also the exact number of primitive binary
communications in the derivation. -/
theorem tracePrimitiveCommCount_eq_depth
    {depth : Nat} {source target : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    (trace : ReducesN depth source target) :
    tracePrimitiveCommCount trace = depth := by
  induction trace with
  | zero => rfl
  | succ step rest ih =>
      simp [tracePrimitiveCommCount, primitiveCommCount_eq_one, ih]
      omega

end CoreBinary

/-- Every core binary communication claim owns exactly two endpoint
occurrences. -/
theorem commClaim_endpoints_length_two (claim : CommClaim) :
    claim.endpoints.length = 2 := rfl

/-- The closed split example owns two signed endpoints and two selected purse
occurrences in one atomic cost event. -/
theorem AtomicResourceJoinExamples.split_consumed_card_four :
    AtomicResourceJoinExamples.splitEvent.consumed.card = 4 := by
  decide

/-- No single core binary communication can preserve the consumed-occurrence
cardinality of the four-way split funded event. -/
theorem no_single_comm_occurrence_cardinality_preservation :
    ¬∃ claim : CommClaim,
      claim.endpoints.length =
        AtomicResourceJoinExamples.splitEvent.consumed.card := by
  intro alleged
  obtain ⟨claim, equality⟩ := alleged
  rw [commClaim_endpoints_length_two claim,
    AtomicResourceJoinExamples.split_consumed_card_four] at equality
  omega

/-- The obstruction is genuinely about the compound event: a core claim's own
endpoint family has the expected binary cardinality. -/
theorem binary_claim_cardinality_is_realized (claim : CommClaim) :
    ∃ endpoints : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern,
      endpoints = claim.endpoints ∧ endpoints.length = 2 :=
  ⟨claim.endpoints, rfl, commClaim_endpoints_length_two claim⟩

/-- A global one-step occurrence-preserving compiler would have to map every
cost event to one binary claim with exactly the same consumed cardinality. -/
def OneStepOccurrencePreservingEncoding (Ground : Type) : Prop :=
  ∃ encode : CostedEvent Ground → CommClaim,
    ∀ event, (encode event).endpoints.length = event.consumed.card

/-- The four-way split example refutes a global occurrence-preserving
one-step compiler into core binary communication. -/
theorem no_global_oneStep_occurrencePreservingEncoding :
    ¬OneStepOccurrencePreservingEncoding
      ParallelExamples.ExampleGround := by
  rintro ⟨encode, preserves⟩
  have impossible := preserves AtomicResourceJoinExamples.splitEvent
  rw [commClaim_endpoints_length_two,
    AtomicResourceJoinExamples.split_consumed_card_four] at impossible
  omega

/-- Total endpoint capacity of a finite sequence of binary claims. -/
def binaryPlanEndpointCount (claims : List CommClaim) : Nat :=
  (claims.map fun claim => claim.endpoints.length).sum

/-- Each claim contributes exactly two endpoint occurrences to a binary
plan. -/
theorem binaryPlanEndpointCount_eq_twice_length (claims : List CommClaim) :
    binaryPlanEndpointCount claims = 2 * claims.length := by
  induction claims with
  | nil => rfl
  | cons claim rest ih =>
      change claim.endpoints.length + binaryPlanEndpointCount rest =
        2 * (rest.length + 1)
      rw [commClaim_endpoints_length_two, ih]
      omega

/-- Any binary plan whose endpoint capacity covers the split event requires
at least two primitive communications. -/
theorem split_requires_at_least_two_binary_claims
    (claims : List CommClaim)
    (covers : AtomicResourceJoinExamples.splitEvent.consumed.card ≤
      binaryPlanEndpointCount claims) :
    2 ≤ claims.length := by
  rw [AtomicResourceJoinExamples.split_consumed_card_four,
    binaryPlanEndpointCount_eq_twice_length] at covers
  omega

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
