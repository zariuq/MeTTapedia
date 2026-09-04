import Mettapedia.GSLT.LanguageDef.MatchDecisionContract

/-!
# Candidate-superset selection and optional verification

A match-decision index is not a second matcher.  It may remove an authored
occurrence only when a source-derived observation proves that occurrence
cannot match.  The canonical matcher remains the authority for every
survivor.

This module states that boundary for ordered occurrence lists.  An admissible
index predicate is true for every canonical success.  Stable filtering by
such a predicate may be inserted or removed before the canonical matcher
without changing the exact result list: authored order and duplicate
occurrences are preserved definitionally.  The same law applies to an
optional isolated verifier.  Deferring that verifier is therefore a lawful
execution choice, rather than a semantic change.

The cost section gives the exact admission inequality.  Verifying all indexed
survivors early is profitable precisely when verifier work is smaller than
the canonical matching work avoided on candidates it rejects.  In particular,
a verifier that rejects nothing, or costs at least one canonical match per
candidate, cannot improve this local cost model.  This separates a semantic
license from a performance policy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.CandidateSupersetVerificationAlgebra

universe u

variable {Occurrence : Type u}

/-- Ordered canonical matching retains every successful source occurrence. -/
def canonicalRun (canonical : Occurrence → Bool)
    (source : List Occurrence) : List Occurrence :=
  source.filter canonical

/-- A refutation-only predicate is admissible when it retains every canonical
success.  It may also retain candidates about which it knows nothing. -/
def RetainsCanonical
    (canonical mayRetain : Occurrence → Bool) : Prop :=
  ∀ occurrence, canonical occurrence = true →
    mayRetain occurrence = true

/-- A derived index is stable filtering of the authored occurrence family. -/
def indexed (mayRetain : Occurrence → Bool)
    (source : List Occurrence) : List Occurrence :=
  source.filter mayRetain

/-- An index cannot invent an occurrence or change the order of survivors. -/
theorem indexed_sublist (mayRetain : Occurrence → Bool)
    (source : List Occurrence) :
    (indexed mayRetain source).Sublist source :=
  List.filter_sublist

/-- Canonical matching after any admissible candidate-superset index is
exactly canonical matching of the authored source family. -/
theorem canonicalRun_indexed_exact
    (canonical mayRetain : Occurrence → Bool)
    (admissible : RetainsCanonical canonical mayRetain)
    (source : List Occurrence) :
    canonicalRun canonical (indexed mayRetain source) =
      canonicalRun canonical source := by
  have predicateEquality :
      (fun occurrence =>
        canonical occurrence && mayRetain occurrence) = canonical := by
    funext occurrence
    cases matched : canonical occurrence with
    | false => rfl
    | true => exact admissible occurrence matched
  simp only [canonicalRun, indexed, List.filter_filter]
  rw [predicateEquality]

/-- Two independently admissible refutation filters may be composed before
the canonical matcher, and either filter may later be deferred. -/
theorem canonicalRun_two_indices_exact
    (canonical first second : Occurrence → Bool)
    (firstAdmissible : RetainsCanonical canonical first)
    (secondAdmissible : RetainsCanonical canonical second)
    (source : List Occurrence) :
    canonicalRun canonical (indexed second (indexed first source)) =
      canonicalRun canonical source := by
  rw [canonicalRun_indexed_exact canonical second secondAdmissible]
  exact canonicalRun_indexed_exact canonical first firstAdmissible source

/-- Optional exact pre-verification may be removed while retaining the same
ordered canonical results. -/
theorem defer_preverification_exact
    (canonical indexMay preverifyMay : Occurrence → Bool)
    (preverifyAdmissible : RetainsCanonical canonical preverifyMay)
    (source : List Occurrence) :
    canonicalRun canonical
        (indexed preverifyMay (indexed indexMay source)) =
      canonicalRun canonical (indexed indexMay source) := by
  exact canonicalRun_indexed_exact
    canonical preverifyMay preverifyAdmissible (indexed indexMay source)

/-- If a purported index rejects one actual match, canonical results change.
This is the negative boundary that excludes unsound pruning. -/
theorem rejected_canonical_occurrence_changes_result
    [DecidableEq Occurrence]
    (canonical mayRetain : Occurrence → Bool) (occurrence : Occurrence)
    (matched : canonical occurrence = true)
    (rejected : mayRetain occurrence = false) :
    canonicalRun canonical (indexed mayRetain [occurrence]) ≠
      canonicalRun canonical [occurrence] := by
  simp [canonicalRun, indexed, matched, rejected]

/-! ## Exact local cost boundary -/

/-- Cost of deferring exact rejection to the canonical matcher. -/
def deferredCost (indexedCount exactMatchCost : Nat) : Nat :=
  indexedCount * exactMatchCost

/-- Cost of verifying every indexed candidate and then canonically matching
every verifier survivor. -/
def eagerCost (indexedCount survivorCount verifyCost exactMatchCost : Nat) :
    Nat :=
  indexedCount * verifyCost + survivorCount * exactMatchCost

/-- Early verification wins exactly when its total work is smaller than the
canonical matching work saved on rejected indexed candidates. -/
theorem eagerCost_lt_deferredCost_iff
    (indexedCount survivorCount verifyCost exactMatchCost : Nat)
    (survivorsBounded : survivorCount ≤ indexedCount) :
    eagerCost indexedCount survivorCount verifyCost exactMatchCost <
        deferredCost indexedCount exactMatchCost ↔
      indexedCount * verifyCost <
        (indexedCount - survivorCount) * exactMatchCost := by
  have split :
      indexedCount * exactMatchCost =
        (indexedCount - survivorCount) * exactMatchCost +
          survivorCount * exactMatchCost := by
    rw [← Nat.add_mul, Nat.sub_add_cancel survivorsBounded]
  simp only [eagerCost, deferredCost, split]
  omega

/-- A verifier that rejects no indexed candidate cannot reduce work when it
has positive per-candidate cost. -/
theorem eager_not_profitable_without_rejection
    (indexedCount verifyCost exactMatchCost : Nat) :
    ¬ eagerCost indexedCount indexedCount verifyCost exactMatchCost <
        deferredCost indexedCount exactMatchCost := by
  simp [eagerCost, deferredCost]

/-- If verification costs at least one canonical match per candidate, eager
verification cannot improve this local model, regardless of selectivity. -/
theorem eager_not_profitable_when_verify_ge_match
    (indexedCount survivorCount verifyCost exactMatchCost : Nat)
    (verifyDominates : exactMatchCost ≤ verifyCost) :
    ¬ eagerCost indexedCount survivorCount verifyCost exactMatchCost <
        deferredCost indexedCount exactMatchCost := by
  simp only [eagerCost, deferredCost]
  have base : indexedCount * exactMatchCost ≤
      indexedCount * verifyCost :=
    Nat.mul_le_mul_left indexedCount verifyDominates
  omega

/-! ## Positive and negative canaries -/

private def multipleOfFour (value : Nat) : Bool := value % 4 == 0
private def evenCandidate (value : Nat) : Bool := value % 2 == 0
private def rejectFour (value : Nat) : Bool := value != 4

/-- Positive: a coarse even-number index retains exact canonical multiples of
four, including duplicate occurrences and authored order. -/
example :
    canonicalRun multipleOfFour
        (indexed evenCandidate [1, 4, 2, 8, 4, 3]) =
      [4, 8, 4] := by
  decide

/-- Positive cost canary: a cheap selective verifier can win. -/
example : eagerCost 8 1 1 4 < deferredCost 8 4 := by decide

/-- Negative cost canary: a nonselective verifier loses. -/
example : ¬ eagerCost 8 8 1 4 < deferredCost 8 4 := by decide

/-- Negative semantic canary: rejecting a real occurrence changes the exact
ordered result. -/
example :
    canonicalRun multipleOfFour (indexed rejectFour [4, 8, 4]) ≠
      canonicalRun multipleOfFour [4, 8, 4] := by
  decide

#print axioms canonicalRun_indexed_exact
#print axioms canonicalRun_two_indices_exact
#print axioms defer_preverification_exact
#print axioms rejected_canonical_occurrence_changes_result
#print axioms eagerCost_lt_deferredCost_iff
#print axioms eager_not_profitable_without_rejection
#print axioms eager_not_profitable_when_verify_ge_match

end Mettapedia.GSLT.LanguageDef.CandidateSupersetVerificationAlgebra
