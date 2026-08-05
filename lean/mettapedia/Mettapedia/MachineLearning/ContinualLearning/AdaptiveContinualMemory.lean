import Mathlib.Tactic

/-!
# Exact-memory boundaries for online nearest-neighbor learning

Prabhu et al., *Online Continual Learning Without the Storage Constraint*
(ICML 2023, arXiv:2305.09253), Section 3, pair a fixed feature extractor
with approximate `k`-nearest-neighbor memory. The source attributes immediate
one-example adaptation, consistency on previously seen examples, and absence
of an optimization stability gap to this architecture.

This file isolates the exact finite core and its missing hypotheses. For the
discrete metric, exact one-nearest-neighbor lookup:

* predicts a newly prepended example immediately;
* continues to recall a stored example after any finite prefix of inserts
  whose features differ from the queried feature;
* can reverse an old prediction after a conflicting duplicate feature is
  prepended.

The source uses majority voting over `k` retrieved neighbors rather than only
one neighbor. A three-neighbor fixture shows that two nonmatching labels can
outvote a newly inserted exact match. A second fixture shows that changing
the feature extractor can reverse recall even though the memory itself is
unchanged.

Thus exact consistency is a conditional property of the encoder, retrieval
semantics, tie policy, neighborhood size, and label consistency. Approximate
retrieval quality, logarithmic complexity, wall-clock cost, test accuracy,
and the source's empirical comparisons remain executable or empirical
obligations.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace AdaptiveContinualMemory

/-- A feature-label packet stored by the online memory. -/
structure Exemplar (Feature Label : Type*) where
  feature : Feature
  label : Label
  deriving DecidableEq, Repr

variable {Feature Label : Type*} [DecidableEq Feature]

/-- Label of the first exact feature match, if one exists. This fixes an
explicit insertion-order tie policy. -/
def firstExactLabel (query : Feature) :
    List (Exemplar Feature Label) → Option Label
  | [] => none
  | exemplar :: memory =>
      if exemplar.feature = query then
        some exemplar.label
      else
        firstExactLabel query memory

@[simp] theorem firstExactLabel_cons_same
    (query : Feature) (label : Label)
    (memory : List (Exemplar Feature Label)) :
    firstExactLabel query
        ({ feature := query, label := label } :: memory) = some label := by
  simp [firstExactLabel]

@[simp] theorem firstExactLabel_cons_of_ne
    (query feature : Feature) (label : Label)
    (memory : List (Exemplar Feature Label))
    (feature_ne : feature ≠ query) :
    firstExactLabel query
        ({ feature := feature, label := label } :: memory) =
      firstExactLabel query memory := by
  simp [firstExactLabel, feature_ne]

/-- Exact one-nearest-neighbor prediction for the discrete metric. Exact
matches have distance zero; if none exists, every stored feature ties at
distance one and insertion order supplies the fallback. -/
def discreteOneNN (query : Feature)
    (memory : List (Exemplar Feature Label)) : Option Label :=
  (firstExactLabel query memory).orElse
    (fun _ => memory.head?.map Exemplar.label)

/-- A single inserted packet is immediately recalled by exact one-nearest
neighbor lookup. -/
theorem inserted_example_is_immediately_recalled
    (query : Feature) (label : Label)
    (memory : List (Exemplar Feature Label)) :
    discreteOneNN query
        ({ feature := query, label := label } :: memory) = some label := by
  simp [discreteOneNN]

/-- Every packet in the list has a feature different from the query. -/
def ExcludesFeature (query : Feature)
    (memory : List (Exemplar Feature Label)) : Prop :=
  ∀ exemplar ∈ memory, exemplar.feature ≠ query

/-- A prefix without the queried feature cannot hide the first exact packet
that follows it. -/
theorem firstExactLabel_append_stored
    (query : Feature) (label : Label)
    (future history : List (Exemplar Feature Label))
    (future_excludes : ExcludesFeature query future) :
    firstExactLabel query
        (future ++ ({ feature := query, label := label } :: history)) =
      some label := by
  induction future with
  | nil =>
      simp
  | cons exemplar future inductionHypothesis =>
      have exemplar_ne : exemplar.feature ≠ query :=
        future_excludes exemplar (by simp)
      have tail_excludes : ExcludesFeature query future := by
        intro candidate candidate_mem
        exact future_excludes candidate (by simp [candidate_mem])
      simp [firstExactLabel, exemplar_ne,
        inductionHypothesis tail_excludes]

/-- Conditional consistency theorem: after storing an example, every finite
sequence of later inserts with different features preserves its exact
one-nearest-neighbor label. -/
theorem distinct_future_inserts_preserve_stored_example
    (query : Feature) (label : Label)
    (future history : List (Exemplar Feature Label))
    (future_excludes : ExcludesFeature query future) :
    discreteOneNN query
        (future ++ ({ feature := query, label := label } :: history)) =
      some label := by
  simp [discreteOneNN,
    firstExactLabel_append_stored query label future history future_excludes]

/-! ## Conflicting labels and larger neighborhoods -/

/-- A conflicting duplicate feature can overwrite the earlier prediction
under the explicit most-recent-first tie policy. -/
theorem conflicting_duplicate_can_reverse_old_prediction :
    discreteOneNN (Feature := ℕ) (Label := Bool) 0
        [{ feature := 0, label := false },
         { feature := 0, label := true }] = some false ∧
      discreteOneNN (Feature := ℕ) (Label := Bool) 0
        [{ feature := 0, label := true }] = some true := by
  decide

/-- Exact matches precede all nonmatches in the discrete-metric ranking,
while insertion order is retained within each part. -/
def discreteRankedNeighbors (query : Feature)
    (memory : List (Exemplar Feature Label)) :
    List (Exemplar Feature Label) :=
  memory.filter (fun exemplar => exemplar.feature = query) ++
    memory.filter (fun exemplar => exemplar.feature ≠ query)

/-- Strict Boolean majority. A tie is classified as `false`, making the tie
policy explicit rather than implicit in an implementation. -/
def strictTrueMajority (labels : List Bool) : Bool :=
  decide (labels.length < 2 * labels.count true)

/-- Discrete `k`-nearest-neighbor classifier with strict majority voting. -/
def discreteKNNBool (query : Feature) (k : ℕ)
    (memory : List (Exemplar Feature Bool)) : Option Bool :=
  let labels :=
    (discreteRankedNeighbors query memory).take k |>.map Exemplar.label
  if labels.isEmpty then none else some (strictTrueMajority labels)

/-- One exact newly inserted `true` label can be outvoted by two `false`
neighbors at `k = 3`, although exact one-nearest-neighbor lookup adapts
immediately. Hence the source's fast-adaptation sentence requires a
neighborhood-vote premise. -/
theorem three_neighbor_majority_can_defeat_exact_insert :
    let memory : List (Exemplar ℕ Bool) :=
      [{ feature := 0, label := true },
       { feature := 1, label := false },
       { feature := 2, label := false }]
    discreteKNNBool 0 3 memory = some false ∧
      discreteOneNN 0 memory = some true := by
  decide

/-! ## Representation identity is load-bearing -/

/-- Query a stored feature memory through a declared encoder. -/
def encodedOneNN (encoder : Bool → Bool) (input : Bool)
    (memory : List (Exemplar Bool Bool)) : Option Bool :=
  discreteOneNN (encoder input) memory

def identityEncoder : Bool → Bool := fun input => input

def flippedEncoder : Bool → Bool := fun input => !input

/-- With an unchanged encoder, the stored packet is recalled. Changing only
the encoder reverses the prediction while the memory remains byte-for-byte
the same. -/
theorem encoder_drift_can_reverse_recall :
    let memory : List (Exemplar Bool Bool) :=
      [{ feature := false, label := true },
       { feature := true, label := false }]
    encodedOneNN identityEncoder false memory = some true ∧
      encodedOneNN flippedEncoder false memory = some false := by
  decide

#print axioms firstExactLabel_append_stored
#print axioms inserted_example_is_immediately_recalled
#print axioms distinct_future_inserts_preserve_stored_example
#print axioms conflicting_duplicate_can_reverse_old_prediction
#print axioms three_neighbor_majority_can_defeat_exact_insert
#print axioms encoder_drift_can_reverse_recall

end AdaptiveContinualMemory

end Mettapedia.MachineLearning.ContinualLearning
