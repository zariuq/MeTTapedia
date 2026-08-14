import Mettapedia.GSLT.Dynamics.ProofRelevantNeedSharing
import Mettapedia.Languages.MeTTa.Prime.NativeInteractionSyntax

/-!
# Gradual execution plans for MeTTa Native

Typing is an accelerator and a source of guarantees, never a prerequisite for
executing a raw MeTTa term.  This module makes that boundary explicit with
three plan forms:

* `RawPlan` contains exactly the raw term;
* `TypedPlan` contains a term, its type, and a derivation;
* `CheckedPlan` contains a raw term and a suspended gradual obligation.

All three erase to the same raw carrier.  The ordinary runner is defined only
from that erasure, so it cannot force a gradual obligation.  A client that
requests the additional guarantee uses `demandCheck`, which realizes the
obligation through the existing proof-relevant call-by-need protocol.  The
first demand performs one evaluation; cached value and cached stable-fault
demands perform no further evaluation.

The resulting cost theorem is a semantic identity in this model.  Establishing
zero machine-code overhead for the raw CeTTa path remains a separate physical
refinement obligation.

The design follows four distinctions from gradual typing:

* kernel definitional equality is not gradual consistency;
* a typed derivation is retained, not reconstructed from a Boolean;
* a failed gradual check is explicit stable blame, not kernel conversion;
* an unknown or unchecked term keeps its raw execution path.
-/

namespace Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan

open Mettapedia.GSLT.Dynamics
open Mettapedia.Languages.MeTTa.NativeTypeTheory
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionInterpretation
open Mettapedia.Languages.MeTTa.Prime.NativeInteractionSyntax
open Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation
open scoped Mettapedia.OSLF.MeTTaIL.MeTTaSyntaxQuotation

universe uRaw uTy uKey uObligation uOutput uCell uEvidence uBlame uRetry
  uOccurrence uRevision uDialect uExpected uAuthority

/-! ## The three plans and their common erasure -/

/-- The dynamic plan contains no typing or checking payload. -/
structure RawPlan (Raw : Type uRaw) where
  term : Raw

/-- An intrinsically certified plan retains the exact term, type, and typing
derivation.  `HasType` is a parameter so the construction applies to the
native DTT as well as future guest calculi. -/
structure TypedPlan (Raw : Type uRaw) (Ty : Type uTy)
    (HasType : Raw → Ty → Prop) where
  term : Raw
  type : Ty
  typing : HasType term type

/-- Every reusable gradual obligation is keyed by all identities that may
change its meaning.  Omitting one of these coordinates requires a separate
semantic proof that the coarser sharing key is sound. -/
structure CheckKey
    (Occurrence : Type uOccurrence) (Revision : Type uRevision)
    (Dialect : Type uDialect) (Expected : Type uExpected)
    (Authority : Type uAuthority) where
  occurrence : Occurrence
  revision : Revision
  dialect : Dialect
  expected : Expected
  authority : Authority
deriving DecidableEq, Repr

/-- The immutable origin of one suspended check. -/
structure CheckOrigin (Key : Type uKey) (Obligation : Type uObligation) where
  key : Key
  obligation : Obligation
deriving DecidableEq, Repr

/-- A checked plan retains a raw fallback and a suspended obligation.  It does
not contain authority to run the checker during ordinary execution. -/
structure CheckedPlan (Raw : Type uRaw) (Key : Type uKey)
    (Obligation : Type uObligation) where
  term : Raw
  origin : CheckOrigin Key Obligation

/-- The common plan family.  The typing relation appears only in the typed
branch; the checking obligation appears only in the checked branch. -/
inductive Plan (Raw : Type uRaw) (Ty : Type uTy)
    (HasType : Raw → Ty → Prop) (Key : Type uKey)
    (Obligation : Type uObligation) where
  | raw (plan : RawPlan Raw)
  | typed (plan : TypedPlan Raw Ty HasType)
  | checked (plan : CheckedPlan Raw Key Obligation)

namespace Plan

variable {Raw : Type uRaw} {Ty : Type uTy} {HasType : Raw → Ty → Prop}
  {Key : Type uKey} {Obligation : Type uObligation}

/-- Forget all optional guarantees and recover the raw term. -/
def erase : Plan Raw Ty HasType Key Obligation → Raw
  | .raw plan => plan.term
  | .typed plan => plan.term
  | .checked plan => plan.term

/-- Ordinary execution is exactly execution of the erased raw term.  In
particular, this function has no checker argument. -/
def run (runRaw : Raw → Output) (plan : Plan Raw Ty HasType Key Obligation) :
    Output :=
  runRaw plan.erase

@[simp] theorem run_raw (runRaw : Raw → Output) (plan : RawPlan Raw) :
    run runRaw (Plan.raw (Ty := Ty) (HasType := HasType) (Key := Key)
      (Obligation := Obligation) plan) = runRaw plan.term :=
  rfl

@[simp] theorem run_typed (runRaw : Raw → Output)
    (plan : TypedPlan Raw Ty HasType) :
    run runRaw (Plan.typed (Key := Key) (Obligation := Obligation) plan) =
      runRaw plan.term :=
  rfl

@[simp] theorem run_checked (runRaw : Raw → Output)
    (plan : CheckedPlan Raw Key Obligation) :
    run runRaw (Plan.checked (Ty := Ty) (HasType := HasType) plan) =
      runRaw plan.term :=
  rfl

/-- A cost observation defined on raw execution is unchanged by plan
selection.  This is the model-level cost identity, not yet a C-code result. -/
def executionCost (rawCost : Raw → Nat)
    (plan : Plan Raw Ty HasType Key Obligation) : Nat :=
  rawCost plan.erase

@[simp] theorem executionCost_raw (rawCost : Raw → Nat)
    (plan : RawPlan Raw) :
    executionCost rawCost
      (Plan.raw (Ty := Ty) (HasType := HasType) (Key := Key)
        (Obligation := Obligation) plan) = rawCost plan.term :=
  rfl

@[simp] theorem executionCost_typed (rawCost : Raw → Nat)
    (plan : TypedPlan Raw Ty HasType) :
    executionCost rawCost
      (Plan.typed (Key := Key) (Obligation := Obligation) plan) =
        rawCost plan.term :=
  rfl

@[simp] theorem executionCost_checked_undemanded (rawCost : Raw → Nat)
    (plan : CheckedPlan Raw Key Obligation) :
    executionCost rawCost
      (Plan.checked (Ty := Ty) (HasType := HasType) plan) =
        rawCost plan.term :=
  rfl

end Plan

/-! ## Exact sharing keys -/

namespace CheckKey

variable {Occurrence : Type uOccurrence} {Revision : Type uRevision}
  {Dialect : Type uDialect} {Expected : Type uExpected}
  {Authority : Type uAuthority}

/-- Exact-key sharing is sound for every declared meaning: equal complete
keys are substitutable without an additional semantic assumption. -/
def exactSharing
    [DecidableEq Occurrence] [DecidableEq Revision] [DecidableEq Dialect]
    [DecidableEq Expected] [DecidableEq Authority] :
    ProofRelevantNeed.SharingScheme
      (CheckKey Occurrence Revision Dialect Expected Authority) where
  Key := CheckKey Occurrence Revision Dialect Expected Authority
  decEq := inferInstance
  key := id

theorem exactSharing_sound
    [DecidableEq Occurrence] [DecidableEq Revision] [DecidableEq Dialect]
    [DecidableEq Expected] [DecidableEq Authority]
    (meaning : CheckKey Occurrence Revision Dialect Expected Authority →
      Output) :
    (exactSharing (Occurrence := Occurrence) (Revision := Revision)
      (Dialect := Dialect) (Expected := Expected)
      (Authority := Authority)).SoundFor meaning := by
  intro left right shares
  exact congrArg meaning shares

end CheckKey

/-! ## Demand semantics through the proof-relevant need protocol -/

/-- A checker returns certified evidence, stable blame, or a retry request.
The three cases have different cache behavior in `ProofRelevantNeed`. -/
structure Checker (Obligation : Type uObligation)
    (Evidence : Type uEvidence) (Blame : Type uBlame)
    (Retry : Type uRetry) where
  check : Obligation → ProofRelevantNeed.Outcome Evidence Blame Retry

abbrev CheckState (Key : Type uKey) (Obligation : Type uObligation)
    (Evidence : Type uEvidence) (Blame : Type uBlame) :=
  ProofRelevantNeed.CellState (CheckOrigin Key Obligation) Evidence Blame

namespace CheckedPlan

variable {Raw : Type uRaw} {Key : Type uKey}
  {Obligation : Type uObligation} {Evidence : Type uEvidence}
  {Blame : Type uBlame} {Retry : Type uRetry} {Cell : Type uCell}

/-- Merely preparing a checked plan suspends its obligation. -/
def initialState (plan : CheckedPlan Raw Key Obligation) :
    CheckState Key Obligation Evidence Blame :=
  .suspended plan.origin

/-- Not demanding a check is the empty chronological trace. -/
def noDemandTrace (cell : Cell) (plan : CheckedPlan Raw Key Obligation) :
    ProofRelevantNeed.Trace Retry cell
      (plan.initialState (Evidence := Evidence) (Blame := Blame))
      (plan.initialState (Evidence := Evidence) (Blame := Blame)) :=
  .refl _

@[simp] theorem noDemandTrace_evaluationCount (cell : Cell)
    (plan : CheckedPlan Raw Key Obligation) :
    (plan.noDemandTrace (Evidence := Evidence) (Blame := Blame)
      (Retry := Retry) cell).evaluationCount = 0 :=
  rfl

@[simp] theorem noDemandTrace_observationCount (cell : Cell)
    (plan : CheckedPlan Raw Key Obligation) :
    (plan.noDemandTrace (Evidence := Evidence) (Blame := Blame)
      (Retry := Retry) cell).outcomeObservationCount = 0 :=
  rfl

/-- Force one suspended obligation.  Successful evidence and stable blame
are cached and observed; a retryable result reopens the suspension. -/
def demandCheck (checker : Checker Obligation Evidence Blame Retry)
    (cell : Cell) (plan : CheckedPlan Raw Key Obligation) :
    Σ target : CheckState Key Obligation Evidence Blame,
      ProofRelevantNeed.Trace Retry cell
        (plan.initialState (Evidence := Evidence) (Blame := Blame)) target :=
  match checker.check plan.origin.obligation with
  | .value evidence =>
      ⟨.cachedValue plan.origin evidence,
        .tail (.beginEvaluation cell plan.origin)
          (.beginEvaluation plan.origin)
          (.tail (.commitValue cell plan.origin evidence)
            (.commitValue plan.origin evidence)
            (.tail (.observeValue cell plan.origin evidence)
              (.observeValue plan.origin evidence) (.refl _)))⟩
  | .stableFault blame =>
      ⟨.cachedStableFault plan.origin blame,
        .tail (.beginEvaluation cell plan.origin)
          (.beginEvaluation plan.origin)
          (.tail (.commitStableFault cell plan.origin blame)
            (.commitStableFault plan.origin blame)
            (.tail (.observeStableFault cell plan.origin blame)
              (.observeStableFault plan.origin blame) (.refl _)))⟩
  | .retryableFault retry =>
      ⟨.suspended plan.origin,
        .tail (.beginEvaluation cell plan.origin)
          (.beginEvaluation plan.origin)
          (.tail (.retry cell plan.origin retry)
            (.retry plan.origin retry) (.refl _))⟩

/-- A first demand claims exactly one evaluation, regardless of its outcome. -/
theorem demandCheck_evaluationCount
    (checker : Checker Obligation Evidence Blame Retry) (cell : Cell)
    (plan : CheckedPlan Raw Key Obligation) :
    (plan.demandCheck checker cell).2.evaluationCount = 1 := by
  unfold demandCheck
  split <;> rfl

/-- Re-observing cached evidence performs no evaluation. -/
def observeCachedValue (cell : Cell) (origin : CheckOrigin Key Obligation)
    (evidence : Evidence) :
    ProofRelevantNeed.Trace Retry cell
      (show CheckState Key Obligation Evidence Blame from
        .cachedValue origin evidence)
      (show CheckState Key Obligation Evidence Blame from
        .cachedValue origin evidence) :=
  .tail (.observeValue cell origin evidence) (.observeValue origin evidence)
    (.refl _)

@[simp] theorem observeCachedValue_evaluationCount (cell : Cell)
    (origin : CheckOrigin Key Obligation) (evidence : Evidence) :
    ((observeCachedValue cell origin evidence :
      ProofRelevantNeed.Trace Retry cell
        (show CheckState Key Obligation Evidence Blame from
          .cachedValue origin evidence)
        (show CheckState Key Obligation Evidence Blame from
          .cachedValue origin evidence))).evaluationCount = 0 :=
  rfl

@[simp] theorem observeCachedValue_observationCount (cell : Cell)
    (origin : CheckOrigin Key Obligation) (evidence : Evidence) :
    ((observeCachedValue cell origin evidence :
      ProofRelevantNeed.Trace Retry cell
        (show CheckState Key Obligation Evidence Blame from
          .cachedValue origin evidence)
        (show CheckState Key Obligation Evidence Blame from
          .cachedValue origin evidence))).outcomeObservationCount = 1 :=
  rfl

/-- Re-observing cached stable blame also performs no evaluation. -/
def observeCachedBlame (cell : Cell) (origin : CheckOrigin Key Obligation)
    (blame : Blame) :
    ProofRelevantNeed.Trace Retry cell
      (show CheckState Key Obligation Evidence Blame from
        .cachedStableFault origin blame)
      (show CheckState Key Obligation Evidence Blame from
        .cachedStableFault origin blame) :=
  .tail (.observeStableFault cell origin blame)
    (.observeStableFault origin blame) (.refl _)

@[simp] theorem observeCachedBlame_evaluationCount (cell : Cell)
    (origin : CheckOrigin Key Obligation) (blame : Blame) :
    ((observeCachedBlame cell origin blame :
      ProofRelevantNeed.Trace Retry cell
        (show CheckState Key Obligation Evidence Blame from
          .cachedStableFault origin blame)
        (show CheckState Key Obligation Evidence Blame from
          .cachedStableFault origin blame))).evaluationCount = 0 :=
  rfl

@[simp] theorem observeCachedBlame_observationCount (cell : Cell)
    (origin : CheckOrigin Key Obligation) (blame : Blame) :
    ((observeCachedBlame cell origin blame :
      ProofRelevantNeed.Trace Retry cell
        (show CheckState Key Obligation Evidence Blame from
          .cachedStableFault origin blame)
        (show CheckState Key Obligation Evidence Blame from
          .cachedStableFault origin blame))).outcomeObservationCount = 1 :=
  rfl

end CheckedPlan

/-! ## MeTTa Native and interaction canaries -/

namespace NativeCanary

abbrev ClosedNativeTyping (term type : NativeRawTm 0 0) : Prop :=
  NativeModalTyping.HasType NativeModalTyping.syntacticConversion .nil term type

inductive ProtocolObligation where
  | requestShape
  | deliberatelyRejected
  | temporarilyUnavailable
deriving DecidableEq, Repr

inductive ProtocolEvidence where
  | requestShape
deriving DecidableEq, Repr

inductive ProtocolBlame where
  | wrongResponseShape
deriving DecidableEq, Repr

inductive ProtocolRetry where
  | authorityRevisionPending
deriving DecidableEq, Repr

def protocolChecker :
    Checker ProtocolObligation ProtocolEvidence ProtocolBlame ProtocolRetry where
  check
    | .requestShape => .value .requestShape
    | .deliberatelyRejected => .stableFault .wrongResponseShape
    | .temporarilyUnavailable => .retryableFault .authorityRevisionPending

abbrev ProtocolKey := CheckKey Nat Nat String String String

def requestKey : ProtocolKey where
  occurrence := 7
  revision := 3
  dialect := "petta"
  expected := "Request(ticket-7)"
  authority := "protocol-v3"

def staleRequestKey : ProtocolKey where
  occurrence := 7
  revision := 2
  dialect := "petta"
  expected := "Request(ticket-7)"
  authority := "protocol-v3"

/-- Negative cache canary: a stale revision is not the current obligation. -/
theorem stale_revision_does_not_share : staleRequestKey ≠ requestKey := by
  decide

/-- The MeTTa-authored request endpoint carries a real native typing
derivation, rather than a Boolean acceptance tag. -/
def typedRequest :
    TypedPlan (NativeRawTm 0 0) (NativeRawTm 0 0) ClosedNativeTyping where
  term := requestEndpoint
  type := .u0
  typing := by
    unfold requestEndpoint
    exact .pattern_intro .nil _

abbrev NativePlan :=
  Plan (NativeRawTm 0 0) (NativeRawTm 0 0) ClosedNativeTyping ProtocolKey
    ProtocolObligation

def typedRequestPlan : NativePlan :=
  .typed typedRequest

/-- Typed execution lowers the exact same authored endpoint as raw
execution. -/
theorem typed_request_executes_by_raw_erasure :
    typedRequestPlan.run rhoInterpretation.lower? =
      some (metta% petta "(request ticket-7 (payload datum))") := by
  rfl

def rejectedRequest :
    CheckedPlan (NativeRawTm 0 0) ProtocolKey ProtocolObligation where
  term := requestEndpoint
  origin := ⟨requestKey, .deliberatelyRejected⟩

def rejectedRequestPlan : NativePlan :=
  .checked rejectedRequest

/-- Negative checking does not revoke the raw request endpoint. -/
theorem rejected_check_does_not_gate_raw_execution :
    rejectedRequestPlan.run rhoInterpretation.lower? =
      some (metta% petta "(request ticket-7 (payload datum))") := by
  rfl

/-- Before demand, the rejected obligation performs no checking work. -/
example :
    (rejectedRequest.noDemandTrace
      (Evidence := ProtocolEvidence) (Blame := ProtocolBlame)
      (Retry := ProtocolRetry) (0 : Nat)).evaluationCount = 0 :=
  rfl

/-- Once demanded, the negative canary is cached as stable blame. -/
example :
    (rejectedRequest.demandCheck protocolChecker (0 : Nat)).1 =
      .cachedStableFault rejectedRequest.origin .wrongResponseShape :=
  rfl

/-- The first negative demand performs one evaluation. -/
example :
    (rejectedRequest.demandCheck protocolChecker
      (0 : Nat)).2.evaluationCount = 1 :=
  CheckedPlan.demandCheck_evaluationCount _ _ _

/-- A later observation of the cached rejection performs no evaluation. -/
example :
    ((CheckedPlan.observeCachedBlame (0 : Nat) rejectedRequest.origin
      ProtocolBlame.wrongResponseShape :
        ProofRelevantNeed.Trace ProtocolRetry (0 : Nat)
          (show CheckState ProtocolKey ProtocolObligation ProtocolEvidence
            ProtocolBlame from .cachedStableFault rejectedRequest.origin
              .wrongResponseShape)
          (show CheckState ProtocolKey ProtocolObligation ProtocolEvidence
            ProtocolBlame from .cachedStableFault rejectedRequest.origin
              .wrongResponseShape))).evaluationCount = 0 :=
  rfl

end NativeCanary

end Mettapedia.Languages.MeTTa.Prime.GradualExecutionPlan
