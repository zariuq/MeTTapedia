import Mettapedia.Languages.MeTTa.Prime.GradualDemandCost
import Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation

/-!
# Gradual evidence for MeTTa-authored native quotations

The proof-producing `native%` quotation and the demand-sensitive execution
plan meet at one source-preserving interface here.

The raw carrier is the exact parsed MeTTa pattern.  Successful native
elaboration can package that same pattern as a `TypedPlan` with its inferred
type and derivation.  A `CheckedPlan` stores the source and a suspended
elaboration obligation; it does not run the elaborator until `demandCheck` is
called.  The Need cell states then have a direct gradual reading:

* `suspended` is unknown evidence;
* `cachedValue` contains an exact native typing package;
* `cachedStableFault` contains a structured source failure.

All three branches execute by erasing to the same authored MeTTa pattern.
Exact evidence may authorize later specialization, but failure and unknown
evidence do not revoke raw execution.

This is an operational evidence boundary, not yet a full gradual dependent
type theory.  In particular, it does not put unknown into kernel conversion
and does not claim the dynamic gradual guarantee for all native types.
-/

namespace Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation

open Mettapedia.GSLT.Dynamics
open Mettapedia.Languages.MeTTa.StagedReflective
open Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
open Mettapedia.Languages.MeTTa.Prime.NativeTypedQuotation
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

/-! ## Source-indexed typing evidence -/

/-- An authored pattern has a native type when proof-producing elaboration
returns a package at exactly that type.  The package itself retains the native
typing derivation. -/
def AuthoredHasType (source : RuntimePattern) (type : StagedReflectiveTm 0 0) : Prop :=
  ∃ result : ClosedTyping,
    elaborate source = .ok result ∧ result.type = type

/-- Exact gradual evidence retains the authored source, the inferred package,
and the equation connecting them. -/
structure TypingEvidence where
  source : RuntimePattern
  result : ClosedTyping
  elaborated : elaborate source = .ok result

/-- Stable gradual blame retains both the source and the structured rejection
returned by native elaboration. -/
structure TypingBlame where
  source : RuntimePattern
  failure : Failure
  rejected : elaborate source = .error failure

/-- The suspended obligation contains only the authored source. -/
structure TypingObligation where
  source : RuntimePattern

/-- Native elaboration has no retry result in the present pure model.  Runtime
authority or guest-service retries belong in a separate effect layer. -/
inductive TypingRetry

/-- Demand-time proof-producing elaboration.  Success and failure both retain
the defining equation, so cached evidence can be used without rerunning the
elaborator. -/
def typingChecker :
    Checker TypingObligation TypingEvidence TypingBlame TypingRetry where
  check obligation :=
    match equation : elaborate obligation.source with
    | .ok result => .value ⟨obligation.source, result, equation⟩
    | .error failure =>
        .stableFault ⟨obligation.source, failure, equation⟩

namespace TypingEvidence

/-- Exact evidence becomes an intrinsically certified plan over the unchanged
authored source. -/
def toTypedPlan (evidence : TypingEvidence) :
    TypedPlan RuntimePattern (StagedReflectiveTm 0 0) AuthoredHasType where
  term := evidence.source
  type := evidence.result.type
  typing := ⟨evidence.result, evidence.elaborated, rfl⟩

end TypingEvidence

/-! ## Exact cache identity -/

/-- The source is part of occurrence identity, so equal cache keys cannot
share evidence between different authored quotations. -/
abbrev TypingKey :=
  CheckKey (Nat × RuntimePattern) Nat String Unit String

/-- One fully discriminated typing key.  The current elaborator infers its
type, so the expected-type coordinate is `Unit`; an expected-type checker must
replace that coordinate rather than smuggling an expectation into authority
or a string label. -/
def key (occurrence revision : Nat) (dialect authority : String)
    (source : RuntimePattern) : TypingKey where
  occurrence := (occurrence, source)
  revision := revision
  dialect := dialect
  expected := ()
  authority := authority

/-- The obligation is a projection of the exact key, not separately supplied
data that could disagree with it. -/
def obligation (typingKey : TypingKey) : TypingObligation :=
  ⟨typingKey.occurrence.2⟩

/-- Equal exact keys necessarily name the same elaboration obligation. -/
theorem key_sharing_preserves_obligation {left right : TypingKey}
    (shares : left = right) : obligation left = obligation right :=
  congrArg obligation shares

/-! ## Raw, exact, and suspended plans -/

abbrev QuotationPlan :=
  Plan RuntimePattern (StagedReflectiveTm 0 0) AuthoredHasType TypingKey
    TypingObligation

/-- The raw plan carries the exact authored pattern and no typing evidence. -/
def rawPlan (source : RuntimePattern) : QuotationPlan :=
  .raw ⟨source⟩

/-- Exact evidence carries a typed accelerator for the same authored pattern. -/
def exactPlan (evidence : TypingEvidence) : QuotationPlan :=
  .typed evidence.toTypedPlan

/-- Prepare a demand-checked plan without invoking native elaboration. -/
def checkedPlan (typingKey : TypingKey) : QuotationPlan :=
  .checked
    { term := typingKey.occurrence.2
      origin := ⟨typingKey, obligation typingKey⟩ }

/-- The checked-plan payload before demand. -/
def suspendedPlan (typingKey : TypingKey) :
    CheckedPlan RuntimePattern TypingKey TypingObligation :=
  { term := typingKey.occurrence.2
    origin := ⟨typingKey, obligation typingKey⟩ }

@[simp] theorem rawPlan_runs_source (source : RuntimePattern) :
    (rawPlan source).run id = source :=
  rfl

@[simp] theorem exactPlan_runs_source (evidence : TypingEvidence) :
    (exactPlan evidence).run id = evidence.source :=
  rfl

@[simp] theorem checkedPlan_runs_source (typingKey : TypingKey) :
    (checkedPlan typingKey).run id = typingKey.occurrence.2 :=
  rfl

/-- Preparing the suspended plan performs no checking work. -/
@[simp] theorem suspendedPlan_noDemandWorkSpan (typingKey : TypingKey)
    (cell : Nat) :
    (suspendedPlan typingKey).noDemandWorkSpan
      (Evidence := TypingEvidence) (Blame := TypingBlame)
      (Retry := TypingRetry) cell = 0 :=
  rfl

/-- The first explicit demand performs exactly one chronological checking
unit, whether elaboration succeeds or produces stable blame. -/
theorem suspendedPlan_demandWorkSpan (typingKey : TypingKey) (cell : Nat) :
    (suspendedPlan typingKey).demandWorkSpan typingChecker cell = ⟨1, 1⟩ :=
  CheckedPlan.demandWorkSpan_eq_unit _ _ _

/-! ## MeTTa-authored protocol example -/

/-- The successful protocol source is authored in PeTTa syntax. -/
def receiptSource : RuntimePattern :=
  metta% petta
    "(native:app
        (native:lam (native:u0) (native:refl (native:var 0)))
        (native:pattern (request ticket-7 (payload datum))))"

/-- Its exact proof-producing elaboration package. -/
def receiptTyping : ClosedTyping := by
  exact native% petta
    "(native:app
        (native:lam (native:u0) (native:refl (native:var 0)))
        (native:pattern (request ticket-7 (payload datum))))"

theorem receipt_elaborates : elaborate receiptSource = .ok receiptTyping :=
  rfl

def receiptEvidence : TypingEvidence :=
  ⟨receiptSource, receiptTyping, receipt_elaborates⟩

def receiptKey : TypingKey :=
  key 7 3 "petta" "native-elaborator-v1" receiptSource

def receiptSuspended :
    CheckedPlan RuntimePattern TypingKey TypingObligation :=
  suspendedPlan receiptKey

/-- Exact, suspended, and raw plans all execute the identical authored source. -/
theorem receipt_all_plans_run_same_source :
    (rawPlan receiptSource).run id =
        (exactPlan receiptEvidence).run id ∧
      (exactPlan receiptEvidence).run id =
        (checkedPlan receiptKey).run id :=
  ⟨rfl, rfl⟩

/-- Before demand, the protocol has unknown evidence and zero checking work. -/
theorem receipt_starts_suspended :
    receiptSuspended.initialState
      (Evidence := TypingEvidence) (Blame := TypingBlame) =
      .suspended receiptSuspended.origin :=
  rfl

/-- On demand, the successful source caches an exact typing package. -/
theorem receipt_demand_caches_exact_typing :
    (receiptSuspended.demandCheck typingChecker (0 : Nat)).1 =
      .cachedValue receiptSuspended.origin receiptEvidence :=
  rfl

/-- The cached exact package has the request-indexed identity type. -/
theorem receipt_cached_type_is_request_indexed :
    receiptEvidence.result.type =
      .id .u0
        (.pattern (metta% petta "(request ticket-7 (payload datum))"))
        (.pattern (metta% petta "(request ticket-7 (payload datum))")) :=
  rfl

/-- Demand adds one checking unit; preparation leaves the raw readout alone. -/
theorem receipt_demand_cost_is_optional :
    receiptSuspended.noDemandWorkSpan
          (Evidence := TypingEvidence) (Blame := TypingBlame)
          (Retry := TypingRetry) (0 : Nat) = 0 ∧
      receiptSuspended.demandWorkSpan typingChecker (0 : Nat) = ⟨1, 1⟩ :=
  ⟨rfl, suspendedPlan_demandWorkSpan receiptKey 0⟩

/-! ## Structured negative example -/

def rejectedSource : RuntimePattern :=
  metta% petta
    "(native:app (native:pattern request) (native:pattern datum))"

def rejectedKey : TypingKey :=
  key 8 3 "petta" "native-elaborator-v1" rejectedSource

def rejectedSuspended :
    CheckedPlan RuntimePattern TypingKey TypingObligation :=
  suspendedPlan rejectedKey

def rejectedFailure : Failure :=
  ⟨[0], .expectedFunction⟩

theorem rejected_source_fails_structurally :
    elaborate rejectedSource = .error rejectedFailure :=
  rfl

def rejectedBlame : TypingBlame :=
  ⟨rejectedSource, rejectedFailure, rejected_source_fails_structurally⟩

/-- Demand caches the named child-path failure rather than fabricating a type. -/
theorem rejected_demand_caches_structured_blame :
    (rejectedSuspended.demandCheck typingChecker (0 : Nat)).1 =
      .cachedStableFault rejectedSuspended.origin rejectedBlame :=
  rfl

/-- Stable rejection still cannot gate the authored raw source. -/
theorem rejected_blame_does_not_gate_raw_execution :
    (checkedPlan rejectedKey).run id = rejectedSource :=
  rfl

/-- Negative control: the rejected source cannot inhabit the exact authored
typing relation at any type. -/
theorem rejected_source_has_no_authored_type (type : StagedReflectiveTm 0 0) :
    ¬ AuthoredHasType rejectedSource type := by
  rintro ⟨result, accepted, resultType⟩
  rw [rejected_source_fails_structurally] at accepted
  cases accepted

end Mettapedia.Languages.MeTTa.Prime.NativeGradualQuotation
