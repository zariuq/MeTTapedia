import Mettapedia.Languages.MeTTa.NativeTypeTheoryDerivation
import Mettapedia.Languages.MeTTa.Prime.DataFibration

/-!
# Prime-internal NIK admission

Admission is a revision-keyed service, not an interior proof replay.  An
authority decides independently stated claims.  Successful decisions are
retained under an authored stable key, so a second request at the same revision
uses the admitted fact directly.  A different revision cannot hit that entry.

The ordinary result contains no receipt.  Receipt publication is a separate
Prime-typed operation over an admitted result, which makes the allocation
boundary explicit in the type.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.InternalAdmission

open Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.DataFibration

universe uRevision uKey uClaim

/-! ## Revision-keyed direct authority -/

/-- A direct NIK authority together with the stable authored identity used by
its admission cache.  Equal keys must preserve meaning; cache soundness must
not rely on collision-prone equality alone. -/
structure RevisionedAuthority
    (Revision : Type uRevision) (Key : Type uKey) (Claim : Type uClaim)
    [DecidableEq Revision] [DecidableEq Key] where
  keyOf : Claim → Key
  Meaning : Revision → Claim → Prop
  key_congruent : ∀ revision {first second : Claim},
    keyOf first = keyOf second →
      (Meaning revision first ↔ Meaning revision second)
  kernel : DecisionKernel (Revision × Claim)
    (fun request => Meaning request.1 request.2)

namespace RevisionedAuthority

variable {Revision : Type uRevision} {Key : Type uKey} {Claim : Type uClaim}
variable [DecidableEq Revision] [DecidableEq Key]

/-- The authority enters the existing four-mode Data admission algebra as a
direct-decision boundary. -/
def entryMode (authority : RevisionedAuthority Revision Key Claim) :
    EntryMode (Revision × Claim) :=
  .directDecision (fun request => authority.Meaning request.1 request.2)
    authority.kernel

@[simp]
theorem entryMode_certificate_free
    (authority : RevisionedAuthority Revision Key Claim) :
    EntryMode.requiresCertificate authority.entryMode = false :=
  rfl

/-- One successful admission, indexed by the exact requested revision and
claim.  Its proof field is erased; the runtime payload is the admitted tag. -/
structure AdmittedAt (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim) where
  marker : PUnit := PUnit.unit
  meaningful : authority.Meaning revision claim

/-- One cache entry retains the representative claim whose stable key was
checked at this revision. -/
structure CacheEntry (authority : RevisionedAuthority Revision Key Claim) where
  revision : Revision
  claim : Claim
  meaningful : authority.Meaning revision claim

/-- The finite admission cache.  Every entry carries the law paid for at its
boundary; no separate Boolean validity table can drift from it. -/
structure Cache (authority : RevisionedAuthority Revision Key Claim) where
  entries : List (CacheEntry authority)

def Cache.empty (authority : RevisionedAuthority Revision Key Claim) :
    Cache authority :=
  ⟨[]⟩

/-- Lookup transfers the retained meaning only through the authority's stable
key law. -/
def Cache.lookup? (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim) :
    Option (AdmittedAt authority revision claim) :=
  lookupEntries cache.entries
where
  lookupEntries : List (CacheEntry authority) →
      Option (AdmittedAt authority revision claim)
    | [] => none
    | entry :: rest =>
        if revisionEq : entry.revision = revision then
          if keyEq : authority.keyOf entry.claim = authority.keyOf claim then
            some ⟨PUnit.unit, (authority.key_congruent revision keyEq).mp
              (revisionEq ▸ entry.meaningful)⟩
          else
            lookupEntries rest
        else
          lookupEntries rest

/-- Extend the cache only with a semantically admitted claim. -/
def Cache.insert (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    (meaningful : authority.Meaning revision claim) : Cache authority :=
  ⟨{ revision := revision, claim := claim, meaningful := meaningful } ::
    cache.entries⟩

@[simp]
theorem Cache.lookup_insert_isSome
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    (meaningful : authority.Meaning revision claim) :
    (Cache.lookup? authority
      (Cache.insert authority cache revision claim meaningful)
      revision claim).isSome =
      true := by
  simp [Cache.lookup?, Cache.lookup?.lookupEntries, Cache.insert]

/-- The ordinary admission result.  It deliberately has no receipt field. -/
inductive Outcome (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim) where
  | admitted (value : AdmittedAt authority revision claim)
  | rejected

/-- Instrumented reference result.  Checker calls and receipt allocations are
observable qualification counters, not semantic evidence. -/
structure Run (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim) where
  cache : Cache authority
  outcome : Outcome authority revision claim
  checkerCalls : Nat
  receiptAllocations : Nat

/-- Admit at most once per revision and stable key.  A cache miss invokes the
direct decision exactly once; rejection leaves the cache unchanged. -/
def run (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim) :
    Run authority revision claim :=
  match Cache.lookup? authority cache revision claim with
  | some admitted =>
      { cache := cache
        outcome := .admitted admitted
        checkerCalls := 0
        receiptAllocations := 0 }
  | none =>
      if accepted : authority.kernel.decide (revision, claim) = true then
        let meaningful := (authority.kernel.correct (revision, claim)).mp accepted
        let updated := Cache.insert authority cache revision claim meaningful
        { cache := updated
          outcome := .admitted ⟨PUnit.unit, meaningful⟩
          checkerCalls := 1
          receiptAllocations := 0 }
      else
        { cache := cache
          outcome := .rejected
          checkerCalls := 1
          receiptAllocations := 0 }

@[simp]
theorem run_receipt_free
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim) :
    (authority.run cache revision claim).receiptAllocations = 0 := by
  unfold run
  split <;> simp
  split <;> simp

theorem run_checkerCalls_le_one
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim) :
    (authority.run cache revision claim).checkerCalls ≤ 1 := by
  unfold run
  split <;> simp
  split <;> simp

theorem cached_run_has_zero_checker_calls
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    {admitted : AdmittedAt authority revision claim}
    (cached : Cache.lookup? authority cache revision claim = some admitted) :
    (authority.run cache revision claim).checkerCalls = 0 := by
  unfold run
  rw [cached]

theorem missed_run_has_one_checker_call
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    (missed : Cache.lookup? authority cache revision claim = none) :
    (authority.run cache revision claim).checkerCalls = 1 := by
  simp only [run, missed]
  split <;> rfl

/-- Every admitted ordinary result satisfies the independently stated
meaning, whether it came from a cache hit or a fresh decision. -/
theorem admitted_sound
    (authority : RevisionedAuthority Revision Key Claim)
    {revision : Revision} {claim : Claim}
    (admitted : AdmittedAt authority revision claim) :
    authority.Meaning revision claim :=
  admitted.meaningful

/-- Every admitted result is retained in its returned cache. -/
theorem run_cache_contains_on_admission
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    (admitted : ∃ value,
      (authority.run cache revision claim).outcome = .admitted value) :
    (Cache.lookup? authority (authority.run cache revision claim).cache
      revision claim).isSome = true := by
  cases cached : Cache.lookup? authority cache revision claim with
  | some value =>
      simp [run, cached]
  | none =>
      cases accepted : authority.kernel.decide (revision, claim) with
      | false =>
          simp [run, cached, accepted] at admitted
      | true =>
          simp only [run, cached, accepted, ↓reduceDIte]
          exact Cache.lookup_insert_isSome authority cache revision claim
            ((authority.kernel.correct (revision, claim)).mp accepted)

/-- Once a request has been admitted, repeating it at the same revision and
stable key performs no checker call. -/
theorem admission_once_per_revision
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    (admitted : ∃ value,
      (authority.run cache revision claim).outcome = .admitted value) :
    (authority.run (authority.run cache revision claim).cache
      revision claim).checkerCalls = 0 := by
  let first := authority.run cache revision claim
  have present :
      (Cache.lookup? authority first.cache revision claim).isSome = true := by
    exact authority.run_cache_contains_on_admission cache revision claim admitted
  cases found : Cache.lookup? authority first.cache revision claim with
  | none => simp [found] at present
  | some value =>
      exact authority.cached_run_has_zero_checker_calls first.cache
        revision claim found

/-- Fail-closed miss: a rejected direct decision leaves the cache unchanged. -/
theorem rejected_miss_preserves_cache
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim)
    (missed : Cache.lookup? authority cache revision claim = none)
    (rejected : authority.kernel.decide (revision, claim) = false) :
    (authority.run cache revision claim).cache = cache ∧
      (authority.run cache revision claim).outcome = .rejected := by
  unfold run
  rw [missed]
  simp [rejected]

/-- An entry admitted at one revision cannot satisfy lookup at a distinct
revision, even when the claim and stable key are unchanged. -/
theorem lookup_insert_different_revision
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) {admittedRevision requestedRevision : Revision}
    (claim : Claim) (meaningful : authority.Meaning admittedRevision claim)
    (different : admittedRevision ≠ requestedRevision) :
    Cache.lookup? authority
      (Cache.insert authority cache admittedRevision claim meaningful)
      requestedRevision claim = Cache.lookup? authority cache requestedRevision claim := by
  simp [Cache.lookup?, Cache.lookup?.lookupEntries, Cache.insert, different]

/-- Starting from an empty cache, changing the revision necessarily crosses
the checker boundary again. -/
theorem different_revision_requires_fresh_check
    (authority : RevisionedAuthority Revision Key Claim)
    {admittedRevision requestedRevision : Revision}
    (claim : Claim) (meaningful : authority.Meaning admittedRevision claim)
    (different : admittedRevision ≠ requestedRevision) :
    (authority.run
      (Cache.insert authority (Cache.empty authority)
        admittedRevision claim meaningful)
      requestedRevision claim).checkerCalls = 1 := by
  apply authority.missed_run_has_one_checker_call
  rw [lookup_insert_different_revision authority (Cache.empty authority)
    claim meaningful different]
  rfl

/-! ## Receipts on explicit demand -/

/-- A published admission receipt is ordinary revision-and-key data.  It is
not needed to use the admitted result internally. -/
structure Receipt
    (Revision : Type uRevision) (Key : Type uKey) where
  revision : Revision
  key : Key
deriving Repr

structure ReceiptResponse
    (Revision : Type uRevision) (Key : Type uKey) where
  receipt : Option (Receipt Revision Key)
  receiptAllocations : Nat

/-- Receipt publication is a separate operation and succeeds only for an
admitted outcome. -/
def requestReceipt (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim)
    (outcome : Outcome authority revision claim) :
    ReceiptResponse Revision Key :=
  match outcome with
  | .admitted _ =>
      { receipt := some ⟨revision, authority.keyOf claim⟩
        receiptAllocations := 1 }
  | .rejected =>
      { receipt := none
        receiptAllocations := 0 }

@[simp]
theorem requestReceipt_admitted
    (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim)
    (admitted : AdmittedAt authority revision claim) :
    authority.requestReceipt revision claim (.admitted admitted) =
      { receipt := some ⟨revision, authority.keyOf claim⟩
        receiptAllocations := 1 } :=
  rfl

@[simp]
theorem requestReceipt_rejected
    (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim) :
    authority.requestReceipt revision claim .rejected =
      { receipt := none, receiptAllocations := 0 } :=
  rfl

/-! ## The operations as terms of Prime's semantic dependent type theory -/

section PrimeTerms

variable {Revision Key Claim : Type}
variable [DecidableEq Revision] [DecidableEq Key]

abbrev PrimeContext := familiesCwF.empty (stageOfNat 0)

def cacheTy (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty PrimeContext :=
  fun _ => Cache authority

abbrev CacheContext (authority : RevisionedAuthority Revision Key Claim) :=
  familiesCwF.ext PrimeContext (cacheTy authority)

def revisionTy (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty (CacheContext authority) :=
  fun _ => Revision

abbrev RevisionContext (authority : RevisionedAuthority Revision Key Claim) :=
  familiesCwF.ext (CacheContext authority) (revisionTy authority)

def claimTy (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty (RevisionContext authority) :=
  fun _ => Claim

abbrev ClaimContext (authority : RevisionedAuthority Revision Key Claim) :=
  familiesCwF.ext (RevisionContext authority) (claimTy authority)

def runTy (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty (ClaimContext authority) :=
  fun context =>
    Run authority context.1.2 context.2

/-- The semantic Prime type

`AdmissionCache → (revision : Revision) → (claim : Claim) →
  AdmissionRun revision claim`.
-/
def internalAdmissionType
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty PrimeContext :=
  familiesCwF.pi (cacheTy authority)
    (familiesCwF.pi (revisionTy authority)
      (familiesCwF.pi (claimTy authority) (runTy authority)))

/-- NIK admission as an ordinary Prime term. -/
def internalAdmission
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Tm PrimeContext (internalAdmissionType authority) :=
  fun _ cache revision claim => authority.run cache revision claim

@[simp]
theorem internalAdmission_apply
    (authority : RevisionedAuthority Revision Key Claim)
    (cache : Cache authority) (revision : Revision) (claim : Claim) :
    internalAdmission authority PUnit.unit cache revision claim =
      authority.run cache revision claim :=
  rfl

def receiptRevisionTy
    (_authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty PrimeContext :=
  fun _ => Revision

abbrev ReceiptRevisionContext
    (authority : RevisionedAuthority Revision Key Claim) :=
  familiesCwF.ext PrimeContext (receiptRevisionTy authority)

def receiptClaimTy
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty (ReceiptRevisionContext authority) :=
  fun _ => Claim

abbrev ReceiptClaimContext
    (authority : RevisionedAuthority Revision Key Claim) :=
  familiesCwF.ext (ReceiptRevisionContext authority) (receiptClaimTy authority)

def admittedOutcomeTy
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty (ReceiptClaimContext authority) :=
  fun context => Outcome authority context.1.2 context.2

abbrev ReceiptOutcomeContext
    (authority : RevisionedAuthority Revision Key Claim) :=
  familiesCwF.ext (ReceiptClaimContext authority) (admittedOutcomeTy authority)

def receiptResponseTy
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty (ReceiptOutcomeContext authority) :=
  fun _ => ReceiptResponse Revision Key

def internalReceiptType
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Ty PrimeContext :=
  familiesCwF.pi (receiptRevisionTy authority)
    (familiesCwF.pi (receiptClaimTy authority)
      (familiesCwF.pi (admittedOutcomeTy authority)
        (receiptResponseTy authority)))

/-- Explicit receipt publication as a second ordinary Prime term. -/
def internalReceipt
    (authority : RevisionedAuthority Revision Key Claim) :
    familiesCwF.Tm PrimeContext (internalReceiptType authority) :=
  fun _ revision claim outcome =>
    authority.requestReceipt revision claim outcome

@[simp]
theorem internalReceipt_apply
    (authority : RevisionedAuthority Revision Key Claim)
    (revision : Revision) (claim : Claim)
    (outcome : Outcome authority revision claim) :
    internalReceipt authority PUnit.unit revision claim outcome =
      authority.requestReceipt revision claim outcome :=
  rfl

end PrimeTerms

/-! ## Executable positive and fail-closed controls -/

def booleanAuthority : RevisionedAuthority Nat Bool Bool where
  keyOf := id
  Meaning := fun _ claim => claim = true
  key_congruent := by
    intro _ first second equal
    have same : first = second := by simpa using equal
    subst second
    rfl
  kernel :=
    { decide := fun request => request.2
      correct := by
        intro request
        cases request.2 <;> simp }

def booleanEmptyCache : Cache booleanAuthority :=
  Cache.empty booleanAuthority

theorem boolean_positive_is_admitted :
    ∃ value,
      (booleanAuthority.run booleanEmptyCache 7 true).outcome =
        .admitted value := by
  let admitted : AdmittedAt booleanAuthority 7 true :=
    ⟨PUnit.unit, rfl⟩
  exact ⟨admitted, rfl⟩

theorem boolean_positive_checks_once :
    (booleanAuthority.run booleanEmptyCache 7 true).checkerCalls = 1 := by
  rfl

theorem boolean_positive_reuses_admission :
    (booleanAuthority.run
      (booleanAuthority.run booleanEmptyCache 7 true).cache
      7 true).checkerCalls = 0 :=
  booleanAuthority.admission_once_per_revision booleanEmptyCache 7 true
    boolean_positive_is_admitted

theorem boolean_revision_change_rechecks :
    (booleanAuthority.run
      (booleanAuthority.run booleanEmptyCache 7 true).cache
      8 true).checkerCalls = 1 := by
  rfl

theorem boolean_negative_is_fail_closed :
    (booleanAuthority.run booleanEmptyCache 7 false).outcome = .rejected ∧
      (booleanAuthority.run booleanEmptyCache 7 false).cache =
        booleanEmptyCache := by
  constructor <;> rfl

theorem boolean_ordinary_path_allocates_no_receipt :
    (booleanAuthority.run booleanEmptyCache 7 true).receiptAllocations = 0 :=
  booleanAuthority.run_receipt_free booleanEmptyCache 7 true

theorem boolean_requested_receipt_is_value :
    ∃ admitted,
      booleanAuthority.requestReceipt 7 true (.admitted admitted) =
        { receipt := some ⟨7, true⟩, receiptAllocations := 1 } := by
  obtain ⟨admitted, _⟩ := boolean_positive_is_admitted
  exact ⟨admitted, rfl⟩

end RevisionedAuthority

/-! ## Existing zero-recheck Need proof flow -/

open Mettapedia.Languages.MeTTa.Prime.Language
open Mettapedia.Languages.MeTTa.NativeTypeTheory.PrimeNeedProofFlow

/-- The retained Need operation really executes as one native derivation node;
there is no hidden checker or receipt argument in the interior application. -/
theorem need_internal_application_is_advance
    (model : Model)
    (rule : OperationalRule (Step model))
    (prior : (Clone model).Hom [] rule.source) :
    applyAdmitted model rule prior =
      OperationalDerivation.advance prior rule.step :=
  applyAdmitted_eq_advance model rule prior

/-- Positive live witness for zero-recheck admitted execution. -/
theorem need_occurrence_flows_without_recheck
    (model : Model) (space : model.Space)
    (subject result : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (occurrence : Nat)
    (copy : occurrence < Multiset.count result
      (model.base.source.occurrences space subject)) :
    Meaning model (answerClaim model space subject result occurrence) :=
  found_flows_without_recheck model space subject result occurrence copy

/-- Fail-closed live witness: a terminal answer cannot fabricate another
admitted interior step. -/
theorem need_answer_cannot_continue
    (model : Model) (space : model.Space)
    (subject result : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern)
    (occurrence : Nat) :
    ¬ ∃ target : Claim model,
      Nonempty (Step model
        (answerClaim model space subject result occurrence) target) :=
  answer_has_no_admitted_successor model space subject result occurrence

#print axioms RevisionedAuthority.admission_once_per_revision
#print axioms RevisionedAuthority.different_revision_requires_fresh_check
#print axioms RevisionedAuthority.internalAdmission_apply
#print axioms need_occurrence_flows_without_recheck

end Mettapedia.Languages.MeTTa.Prime.InternalAdmission
