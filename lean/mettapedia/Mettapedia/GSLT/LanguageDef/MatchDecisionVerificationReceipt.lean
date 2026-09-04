import Mettapedia.GSLT.LanguageDef.CandidateSupersetVerificationAlgebra

/-!
# Revision-keyed structural-verification receipts

A candidate selector may run a complete structural compatibility predicate on
every survivor before the canonical matcher.  Repeating that same predicate
immediately inside the clause loop cannot change the survivor list.  This
module makes the reuse boundary explicit: the receipt is keyed by both the
mutable-authority revision and the observed query, and becomes unavailable
when either coordinate changes.  The revision coordinate may conservatively
combine every Space or classifier authority consulted by compatibility.

The canonical matcher is deliberately not removed.  A receipt avoids only a
second application of the same refutation-only structural predicate; binding,
occurs checking, rollback, and result construction remain authoritative.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MatchDecisionVerificationReceipt

open CandidateSupersetVerificationAlgebra

universe uRevision uQuery uOccurrence

variable {Revision : Type uRevision} {Query : Type uQuery}
  {Occurrence : Type uOccurrence}

/-- Stable structural verification under one exact authority/query key. -/
def verified (compatible : Revision → Query → Occurrence → Bool)
    (revision : Revision) (query : Query)
    (source : List Occurrence) : List Occurrence :=
  source.filter (compatible revision query)

/-- Proof-erased runtime data plus the proposition that says what was checked.
The source list retains authored order and duplicate occurrences. -/
structure Receipt (compatible : Revision → Query → Occurrence → Bool) where
  revision : Revision
  query : Query
  source : List Occurrence
  survivors : List Occurrence
  exact : survivors = verified compatible revision query source

/-- A receipt may be replayed only at the same revision and query. -/
def replay? [DecidableEq Revision] [DecidableEq Query]
    {compatible : Revision → Query → Occurrence → Bool}
    (receipt : Receipt compatible)
    (revision : Revision) (query : Query) : Option (List Occurrence) :=
  if receipt.revision = revision ∧ receipt.query = query then
    some receipt.survivors
  else
    none

theorem replay?_same [DecidableEq Revision] [DecidableEq Query]
    {compatible : Revision → Query → Occurrence → Bool}
    (receipt : Receipt compatible) :
    replay? receipt receipt.revision receipt.query =
      some receipt.survivors := by
  simp [replay?]

/-- Applying the identical structural verifier to its own survivors is
idempotent.  A same-key receipt therefore removes no additional occurrence
when the second pass is omitted. -/
theorem verified_idempotent
    (compatible : Revision → Query → Occurrence → Bool)
    (revision : Revision) (query : Query) (source : List Occurrence) :
    verified compatible revision query
        (verified compatible revision query source) =
      verified compatible revision query source := by
  simp [verified, List.filter_filter]

theorem receipt_reverification_exact
    {compatible : Revision → Query → Occurrence → Bool}
    (receipt : Receipt compatible) :
    verified compatible receipt.revision receipt.query receipt.survivors =
      receipt.survivors := by
  rw [receipt.exact]
  exact verified_idempotent compatible receipt.revision receipt.query
    receipt.source

/-- Reusing structural survivors leaves the later canonical matcher exact,
provided structural compatibility retains every canonical success. -/
theorem canonicalRun_receipt_exact
    (canonical : Occurrence → Bool)
    (compatible : Revision → Query → Occurrence → Bool)
    (receipt : Receipt compatible)
    (retains : RetainsCanonical canonical
      (compatible receipt.revision receipt.query)) :
    canonicalRun canonical receipt.survivors =
      canonicalRun canonical receipt.source := by
  rw [receipt.exact]
  exact canonicalRun_indexed_exact canonical
    (compatible receipt.revision receipt.query) retains receipt.source

/-! ## Exact local cost consequence -/

/-- The redundant route evaluates compatibility once per verified survivor. -/
def repeatedVerificationChecks
    {compatible : Revision → Query → Occurrence → Bool}
    (receipt : Receipt compatible) : Nat := receipt.survivors.length

/-- Same-key replay reads the receipt and performs no compatibility calls. -/
def receiptReplayChecks
    {compatible : Revision → Query → Occurrence → Bool}
    (_receipt : Receipt compatible) : Nat := 0

theorem receiptReplayChecks_savings
    {compatible : Revision → Query → Occurrence → Bool}
    (receipt : Receipt compatible) :
    repeatedVerificationChecks receipt =
      receiptReplayChecks receipt + receipt.survivors.length := by
  simp [repeatedVerificationChecks, receiptReplayChecks]

/-- Zero compatibility calls is the attainable lower bound once the keyed
receipt is available; this claim is only about the repeated structural pass,
not total matching work. -/
theorem receiptReplayChecks_lower_bound
    {compatible : Revision → Query → Occurrence → Bool}
    (receipt : Receipt compatible) (otherChecks : Nat) :
    receiptReplayChecks receipt ≤ otherChecks := by
  exact Nat.zero_le otherChecks

/-! ## Positive and negative canaries -/

private def parityShape (revision query : Bool) (value : Nat) : Bool :=
  if revision == query then value % 2 == 0 else value % 2 == 1

private def evenReceipt : Receipt parityShape where
  revision := false
  query := false
  source := [1, 2, 2, 3, 4]
  survivors := [2, 2, 4]
  exact := by decide

/-- Same-key reuse retains order and duplicate occurrences. -/
example : replay? evenReceipt false false = some [2, 2, 4] := by
  decide

/-- A changed query refuses the receipt. -/
example : replay? evenReceipt false true = none := by
  decide

/-- Ignoring the key would be observably wrong for this changed query. -/
example : evenReceipt.survivors ≠
    verified parityShape false true evenReceipt.source := by
  decide

/-- A changed revision likewise refuses reuse. -/
example : replay? evenReceipt true false = none := by
  decide

#print axioms replay?_same
#print axioms verified_idempotent
#print axioms receipt_reverification_exact
#print axioms canonicalRun_receipt_exact
#print axioms receiptReplayChecks_savings
#print axioms receiptReplayChecks_lower_bound

end Mettapedia.GSLT.LanguageDef.MatchDecisionVerificationReceipt
