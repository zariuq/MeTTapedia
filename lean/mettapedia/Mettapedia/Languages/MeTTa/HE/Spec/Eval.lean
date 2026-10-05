import Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-!
# Executable-independent spec evaluator specification

The mutually recursive, fuel-free judgments share the full typed result
continuation with raw/minimal invocation and function completion. The embedded
`metta` fragment includes Atom demand, syntactic errors, and non-error full
results. General embedded-metta failure-priority completeness is not asserted:
its negative all-alternatives test cannot be placed inside an inductive family.
The type, unify, switch, matcher, merger, alpha-renaming, and
equation-query premises are the independent relations from the preceding
modules.  Grounded operations remain an explicitly parameterized host
relation.

The mutual block presents individual raw results.  `EvalRel` below adds the
published top-level success-priority rule: an error is observable only when no
non-error raw result exists for the same configuration.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Eval

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Spec.Match.Merge
open Spec.Type
open Spec.Type.Presentation
open Spec.Eval.Steps

/-! ## Syntax and host boundaries -/

/-- Intrinsic meta-type, stated relationally. -/
inductive MetaTypeRel : Atom → Atom → Prop where
  | symbol (name : String) :
      MetaTypeRel (.symbol name) Atom.symbolType
  | variable (name : String) :
      MetaTypeRel (.var name) Atom.variableType
  | grounded (value : GroundedValue) :
      MetaTypeRel (.grounded value) Atom.groundedType
  | expression (atoms : List Atom) :
      MetaTypeRel (.expression atoms) Atom.expressionType

/-- Intrinsic meta-types are functional.  Evaluator constructor inversions
use this boundary lemma instead of repeating an atom-constructor case split. -/
theorem MetaTypeRel.eq {atom left right : Atom}
    (leftType : MetaTypeRel atom left) (rightType : MetaTypeRel atom right) :
    left = right := by
  cases leftType <;> cases rightType <;> rfl

/-- Syntactic error atom.  The published `(Error ...)` pattern recognizes
every expression headed by `Error`, independently of its tail shape. -/
def IsErrorRel (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "Error" :: tail)

/-- Empty or syntactic error atom. -/
def IsEmptyOrErrorRel (atom : Atom) : Prop :=
  atom = Atom.empty ∨ IsErrorRel atom

namespace Minimal

/-- Host representations used only by the minimal-instruction layer.  The
carrier contains data; injectivity and other properties are separate laws. -/
structure Services where
  /-- Opaque grounded representation of a complete binding set. -/
  bindingPayload : Bindings → GroundedValue
  /-- Opaque grounded handle for the current context space. -/
  contextPayload : Space → GroundedValue
  /-- Behavior of the internal `call-native` instruction. -/
  nativeCall : Atom → Atom → Atom → Bindings → ResultPair → Prop

/-- An ordered enumeration profile for the fuel-free evaluator.  `EvalRel`
describes which individual results are semantically possible; this relation
separately records the order and multiplicity exposed by `collapse-bind`.

The carrier is relational because the published semantics need not choose one
global scheduler.  A concrete operational profile may nevertheless be
functional. -/
structure Enumeration where
  results : Space → Atom → Atom → Bindings → ResultSet → Prop
  /-- Minimal execution has a different result boundary from full typed
  interpretation. Its semantic law is stated after `MinimalResultRel`. -/
  minimalResults : Space → Atom → Bindings → ResultSet → Prop

/-- Representation and ordered collection services configured at the host boundary. -/
structure HostPackage where
  services : Services
  enumeration : Enumeration

end Minimal

/-- Producer provenance distinguishes an ordinary emission from a value
whose interpretation has already completed. It is not inferred from syntax. -/
inductive NativeValueProvenance where
  | emitted
  | completed
  deriving DecidableEq, Repr

/-- Host-grounded operations are genuinely external to the MeTTa semantics.
The evaluator sees only an executable predicate and a relation of possible
host outcomes. -/
structure GroundedDispatch where
  executable : Atom → Prop
  outcome : Atom → List Atom → GroundedResult → Prop
  /-- Opaque minimal services are optional; core instructions do not require them. -/
  minimal : Option Minimal.HostPackage := none
  /-- The producer's completion boundary, shared by raw and full invocation. -/
  valueProvenance : Atom → List Atom → NativeValueProvenance := fun _ _ => .emitted

/-- The equation-query lane is used only when the head is not a host operation
or one of the two structural control instructions. -/
def NonGroundedCallRel (dispatch : GroundedDispatch) (atom : Atom) : Prop :=
  match atom with
  | .expression (operator :: _) =>
      ¬dispatch.executable operator ∧
        operator ≠ .symbol "unify" ∧
        operator ≠ .symbol "switch-minimal"
  | _ => True

namespace Minimal

/-- Encode one semantic result in the exact pair shape consumed by
`superpose-bind`. -/
def encodeResult (services : Services) (result : ResultPair) : Atom :=
  .expression [result.1, .grounded (services.bindingPayload result.2)]

/-- Encode an ordered list of results without changing order or multiplicity. -/
def encodeResults (services : Services) (results : ResultSet) : Atom :=
  .expression (results.map (encodeResult services))

/-- Embedded instructions are interpreted by the minimal machine, not by
ordinary argument evaluation. `return` is a function-body delimiter rather
than an executable instruction. -/
def embeddedInstruction : Atom → Bool
  | .expression (.symbol head :: _) =>
      head ∈ ["eval", "evalc", "chain", "unify", "cons-atom", "decons-atom",
        "function", "collapse-bind", "superpose-bind", "metta",
        "context-space", "call-native"]
  | _ => false

def IsChain (atom : Atom) : Prop :=
  ∃ tail, atom = .expression (.symbol "chain" :: tail)

def IsFunction (atom : Atom) : Prop :=
  ∃ body, atom = .expression [.symbol "function", body]

def HostCall (dispatch : GroundedDispatch) (atom : Atom) : Prop :=
  ∃ operator arguments, atom = .expression (operator :: arguments) ∧
    dispatch.executable operator

/-- Structural substitution of the explicit chain binder. Other caller
variables remain in the carried binding frame. No fixed depth bound is used. -/
def substituteName (name : String) (replacement : Atom) : Atom → Atom
  | .symbol symbol => .symbol symbol
  | .grounded value => .grounded value
  | .var varName => if varName = name then replacement else .var varName
  | .expression atoms => .expression (atoms.map (substituteName name replacement))

/-- Install a concrete minimal host package without changing native dispatch. -/
def withHost (dispatch : GroundedDispatch) (services : Services)
    (enumeration : Enumeration) : GroundedDispatch :=
  { dispatch with minimal := some ⟨services, enumeration⟩ }

end Minimal

/-! ## Type-service boundary and ordered candidate selection -/

/-- One selected function-type policy.  The proof field keeps the argument
and return projections tied to the same arrow presentation; downstream
consumers never reconstruct them independently. -/
structure SelectedTypePolicy where
  functionType : Atom
  argumentTypes : List Atom
  returnType : Atom
  isFunction : FunctionTypeRel functionType argumentTypes returnType

/-- One candidate's applicability result.  A successful candidate supplies
the exact policy that later evaluation consumes as well as the bindings
produced by the applicability check. -/
inductive SelectedTypeApplicabilityOutcome where
  | success (policy : SelectedTypePolicy) (bindings : Bindings)
  | error (errors : List Atom)

/-- Result of the published left-to-right function-candidate scan.  Success
stops the scan immediately and carries one coherent selected policy plus the
bindings produced by applicability.  Exhaustion retains every ordered error
block from every failed function candidate and records whether a non-function
candidate made tuple fallback eligible. -/
inductive FunctionCandidateScanOutcome where
  | success (policy : SelectedTypePolicy) (bindings : Bindings)
  | exhausted (errors : List Atom) (tupleEligible : Bool)

/-- Literal transcription of the candidate loop in `interpret_expression`
(`Specs/he_metta_official_specs.md:172-210`): non-functions enable tuple
fallback, failed functions accumulate errors, and the first applicable
function stops the scan. -/
inductive FunctionCandidateScanRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop)
    (space : Space)
    (expression expectedType : Atom) (bindings : Bindings) :
    List Atom → FunctionCandidateScanOutcome → Prop where
  | nil :
      FunctionCandidateScanRel applicability space expression expectedType bindings
        [] (.exhausted [] false)
  | nonFunctionSuccess {candidate : Atom} {candidates : List Atom}
      {policy : SelectedTypePolicy} {output : Bindings} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | nonFunctionExhausted {candidate : Atom} {candidates errors : List Atom}
      {tupleEligible : Bool} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.exhausted errors true)
  | functionSuccess {candidate : Atom} {candidates argumentTypes : List Atom}
      {returnType : Atom} {policy : SelectedTypePolicy}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes returnType →
      applicability space expression candidate expectedType bindings
        (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | functionFailureThenSuccess
      {candidate : Atom} {candidates argumentTypes : List Atom}
      {candidateReturn : Atom} {candidateErrors : List Atom}
      {policy : SelectedTypePolicy}
      {output : Bindings} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidatePolicy candidateBindings,
        ¬applicability space expression candidate expectedType bindings
          (.success candidatePolicy candidateBindings)) →
      applicability space expression candidate expectedType bindings
        (.error candidateErrors) →
      candidateErrors ≠ [] →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.success policy output) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates) (.success policy output)
  | functionFailureExhausted
      {candidate : Atom} {candidates argumentTypes errors : List Atom}
      {candidateReturn : Atom} {candidateErrors : List Atom}
      {tupleEligible : Bool} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ candidatePolicy candidateBindings,
        ¬applicability space expression candidate expectedType bindings
          (.success candidatePolicy candidateBindings)) →
      applicability space expression candidate expectedType bindings
        (.error candidateErrors) →
      candidateErrors ≠ [] →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        candidates (.exhausted errors tupleEligible) →
      FunctionCandidateScanRel applicability space expression expectedType bindings
        (candidate :: candidates)
        (.exhausted (candidateErrors ++ errors) tupleEligible)

/-! ### Scan boundary algebra -/

/-- Every successful ordered scan is justified by one candidate in the
original list.  Downstream conformance proofs consume this theorem instead of
unfolding the scan recursion. -/
theorem FunctionCandidateScanRel.success_candidate
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : FunctionCandidateScanRel applicability space expression
      expectedType bindings candidates (.success policy output)) :
    ∃ candidate ∈ candidates,
      applicability space expression candidate expectedType bindings
        (.success policy output) := by
  generalize outcomeEq :
      (.success policy output : FunctionCandidateScanOutcome) = outcome at scan
  revert policy output
  induction scan with
  | nil =>
      intro policy output outcomeEq
      cases outcomeEq
  | nonFunctionSuccess _ tail ih =>
      intro policy output outcomeEq
      cases outcomeEq
      obtain ⟨candidate, member, applicable⟩ := ih rfl
      exact ⟨candidate, by simp [member], applicable⟩
  | nonFunctionExhausted =>
      intro policy output outcomeEq
      cases outcomeEq
  | functionSuccess _ applicable =>
      intro policy output outcomeEq
      cases outcomeEq
      exact ⟨_, by simp, applicable⟩
  | functionFailureThenSuccess _ _ _ _ tail ih =>
      intro policy output outcomeEq
      cases outcomeEq
      obtain ⟨candidate, member, applicable⟩ := ih rfl
      exact ⟨candidate, by simp [member], applicable⟩
  | functionFailureExhausted =>
      intro policy output outcomeEq
      cases outcomeEq

/-- An exhausted scan has no successful applicability derivation for any
function candidate in the scanned list.  This is the exact negative boundary
used by tuple fallback and error rules. -/
theorem FunctionCandidateScanRel.exhausted_no_function_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates errors : List Atom} {tupleEligible : Bool}
    (scan : FunctionCandidateScanRel applicability space expression
      expectedType bindings candidates (.exhausted errors tupleEligible)) :
    ∀ candidate ∈ candidates,
      (∃ argumentTypes returnType,
        FunctionTypeRel candidate argumentTypes returnType) →
      ∀ policy output,
        ¬applicability space expression candidate expectedType bindings
          (.success policy output) := by
  generalize outcomeEq :
      (.exhausted errors tupleEligible : FunctionCandidateScanOutcome) =
        outcome at scan
  revert errors tupleEligible
  induction scan with
  | nil =>
      intro errors tupleEligible outcomeEq candidate member
      simp at member
  | nonFunctionSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | nonFunctionExhausted notFunction _ ih =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
      intro candidate member isFunction policy output applicable
      rcases List.mem_cons.mp member with candidateEq | member
      · subst candidate
        exact notFunction isFunction
      · exact ih rfl candidate member isFunction policy output applicable

  | functionSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | functionFailureThenSuccess =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
  | functionFailureExhausted _ noSuccess _ _ _ ih =>
      intro errors tupleEligible outcomeEq
      cases outcomeEq
      intro candidate member isFunction policy output applicable
      rcases List.mem_cons.mp member with candidateEq | member
      · subst candidate
        exact noSuccess policy output applicable
      · exact ih rfl candidate member isFunction policy output applicable

/-! ### Generic exact-scan assembly

The concrete runtime bridge supplies one exact classification per candidate.
The two lemmas below are the only place that classification is threaded into
the published left-to-right scan.  Runtime-specific conformance modules never
reimplement the scan induction. -/

/-- Exact evidence for one candidate that did not stop the scan.  A
non-function enables tuple fallback without contributing an error; a failed
function contributes one nonempty ordered error block and includes the
negative success fact required by `FunctionCandidateScanRel`. -/
inductive FunctionCandidateFailureRel
    (applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop)
    (space : Space) (expression expectedType : Atom)
    (bindings : Bindings) : Atom → (List Atom × Bool) → Prop where
  | nonFunction {candidate : Atom} :
      (¬∃ argumentTypes candidateReturn,
        FunctionTypeRel candidate argumentTypes candidateReturn) →
      FunctionCandidateFailureRel applicability space expression expectedType
        bindings candidate ([], true)
  | functionFailure {candidate : Atom} {argumentTypes : List Atom}
      {candidateReturn : Atom} {errors : List Atom} :
      FunctionTypeRel candidate argumentTypes candidateReturn →
      (∀ policy output,
        ¬applicability space expression candidate expectedType bindings
          (.success policy output)) →
      applicability space expression candidate expectedType bindings
        (.error errors) →
      errors ≠ [] →
      FunctionCandidateFailureRel applicability space expression expectedType
        bindings candidate (errors, false)

/-- Errors contributed by a list of exact failed-candidate summaries, in
source order. -/
def functionCandidateFailureErrors :
    List (List Atom × Bool) → List Atom
  | [] => []
  | (errors, _) :: summaries =>
      errors ++ functionCandidateFailureErrors summaries

/-- The recursive failure readout is exactly row-major flattening of the
per-candidate error blocks. -/
theorem functionCandidateFailureErrors_eq_flatten_map_fst
    (summaries : List (List Atom × Bool)) :
    functionCandidateFailureErrors summaries =
      (summaries.map Prod.fst).flatten := by
  induction summaries with
  | nil => rfl
  | cons summary summaries inductionHypothesis =>
      rcases summary with ⟨errors, eligible⟩
      simp [functionCandidateFailureErrors, inductionHypothesis]

/-- Whether any exact failed-candidate summary enables tuple fallback. -/
def functionCandidateFailureTupleEligible :
    List (List Atom × Bool) → Bool
  | [] => false
  | (_, eligible) :: summaries =>
      eligible || functionCandidateFailureTupleEligible summaries

/-- A pointwise exact failure classification reconstructs the complete
exhausted scan, including error order and tuple eligibility. -/
theorem FunctionCandidateScanRel.of_all_failures
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {summaries : List (List Atom × Bool)}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) candidates summaries) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings candidates
      (.exhausted (functionCandidateFailureErrors summaries)
        (functionCandidateFailureTupleEligible summaries)) := by
  induction failures with
  | nil => exact .nil
  | @cons candidate summary candidates summaries failure _ ih =>
      cases failure with
      | nonFunction notFunction =>
          simpa [functionCandidateFailureErrors,
            functionCandidateFailureTupleEligible] using
            (FunctionCandidateScanRel.nonFunctionExhausted
              notFunction ih)
      | functionFailure isFunction noSuccess errors nonempty =>
          simpa [functionCandidateFailureErrors,
            functionCandidateFailureTupleEligible] using
            (FunctionCandidateScanRel.functionFailureExhausted
              isFunction noSuccess errors nonempty ih)

/-- Exact failures preceding an already-derived success may be prepended
without reopening the scan proof. -/
theorem FunctionCandidateScanRel.prepend_failures_to_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {failedCandidates tail : List Atom}
    {summaries : List (List Atom × Bool)}
    {policy : SelectedTypePolicy} {output : Bindings}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) failedCandidates summaries)
    (tailSuccess : FunctionCandidateScanRel applicability space expression
      expectedType bindings tail (.success policy output)) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings (failedCandidates ++ tail) (.success policy output) := by
  induction failures with
  | nil => simpa using tailSuccess
  | @cons candidate summary candidates summaries failure _ ih =>
      cases failure with
      | nonFunction notFunction =>
          simpa using FunctionCandidateScanRel.nonFunctionSuccess
            notFunction ih
      | functionFailure isFunction noSuccess errors nonempty =>
          simpa using FunctionCandidateScanRel.functionFailureThenSuccess
            isFunction noSuccess errors nonempty ih

/-- Generic first-success assembly: a list of exact failures followed by one
exact successful candidate yields the published ordered-scan result; the
uninspected suffix is intentionally irrelevant. -/
theorem FunctionCandidateScanRel.of_first_success
    {applicability :
      Space → Atom → Atom → Atom → Bindings →
        SelectedTypeApplicabilityOutcome → Prop}
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {failedCandidates suffix : List Atom}
    {summaries : List (List Atom × Bool)}
    {candidate : Atom} {argumentTypes : List Atom} {returnType : Atom}
    {policy : SelectedTypePolicy} {output : Bindings}
    (failures : List.Forall₂
      (FunctionCandidateFailureRel applicability space expression
        expectedType bindings) failedCandidates summaries)
    (isFunction : FunctionTypeRel candidate argumentTypes returnType)
    (success : applicability space expression candidate expectedType bindings
      (.success policy output)) :
    FunctionCandidateScanRel applicability space expression expectedType
      bindings (failedCandidates ++ candidate :: suffix)
        (.success policy output) := by
  apply FunctionCandidateScanRel.prepend_failures_to_success failures
  exact FunctionCandidateScanRel.functionSuccess isFunction success

/-- The exact type interface consumed by the six evaluator judgments.  One
service supplies both positive and negative premises; mixing a permissive
positive layer with a different negative candidate set is unrepresentable.

`candidateScan` is deliberately a single ordered relation rather than a bare
applicability predicate: first-success and all-failed outcomes must quantify
over the same exact candidate sequence.

The published instance below is the specification-textual core.  The repaired
runtime instance is defined in the conformance layer from the exact ordered
package relation. -/
structure EvalTypeService where
  typesOf : Space → Atom → List Atom → Prop
  typeCast : List String → Space → Atom → Atom → Bindings → ResultPair → Prop
  candidateScan :
    Space → Atom → Atom → Bindings →
      List Atom → FunctionCandidateScanOutcome → Prop

/-- Lift one singular published applicability fact into the block-valued
policy-carrying scan interface.  Error blocks assembled from the complete
published argument/return traversal are supplied by the exact service
instance; this constructor remains the reusable singleton brick. -/
inductive PublishedCandidateApplicabilityRel
    (space : Space) (expression candidate expectedType : Atom)
    (bindings : Bindings) : SelectedTypeApplicabilityOutcome → Prop where
  | success {argumentTypes : List Atom} {returnType : Atom}
      {output : Bindings}
      (isFunction : FunctionTypeRel candidate argumentTypes returnType)
      (applicable : ApplicabilityRel space expression candidate expectedType
        bindings (.success output)) :
      PublishedCandidateApplicabilityRel space expression candidate
        expectedType bindings
        (.success ⟨candidate, argumentTypes, returnType, isFunction⟩ output)
  | error {errorAtom : Atom}
      (applicable : ApplicabilityRel space expression candidate expectedType
        bindings (.error errorAtom)) :
      PublishedCandidateApplicabilityRel space expression candidate
        expectedType bindings (.error [errorAtom])

/-- Published-scan success exposes the exact selected arrow and the
spec-threaded applicability bindings.  In particular, the policy witness and
the binding output cannot originate from different candidates. -/
theorem published_scan_success_selected
    {space : Space} {expression expectedType : Atom} {bindings : Bindings}
    {candidates : List Atom} {policy : SelectedTypePolicy}
    {output : Bindings}
    (scan : FunctionCandidateScanRel PublishedCandidateApplicabilityRel
      space expression expectedType bindings candidates
        (.success policy output)) :
    policy.functionType ∈ candidates ∧
      ApplicabilityRel space expression policy.functionType expectedType
        bindings (.success output) := by
  obtain ⟨candidate, member, applicable⟩ := scan.success_candidate
  cases applicable with
  | success _ applicability => exact ⟨member, applicability⟩

/-- The published spec type layer, definitionally, as one coherent evaluator
service. -/
def publishedTypeService : EvalTypeService where
  typesOf := TypesOfRel
  typeCast := fun _ => TypeCastRel
  candidateScan := FunctionCandidateScanRel PublishedCandidateApplicabilityRel

private def scanFailureType : Atom :=
  .expression [.symbol "->", .symbol "A"]

private def scanSuccessType : Atom :=
  .expression [.symbol "->", .symbol "B"]

private def scanSuccessPolicy : SelectedTypePolicy :=
  ⟨scanSuccessType, [], .symbol "B", rfl⟩

private def scanExpression : Atom :=
  .expression [.symbol "scan-target"]

private def scanFailure : Atom :=
  mkError scanExpression (.badType Atom.undefinedType (.symbol "A"))

private def orderedScanCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings)
  (outcome : SelectedTypeApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧ outcome = .error [scanFailure]) ∨
  (functionType = scanSuccessType ∧
    outcome = .success scanSuccessPolicy Bindings.empty)

/-- Positive order canary: a failed first function candidate is recorded and
the second successful candidate is selected. -/
theorem ordered_scan_skips_failed_candidate :
    FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.success scanSuccessPolicy Bindings.empty) := by
  apply FunctionCandidateScanRel.functionFailureThenSuccess
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (candidateErrors := [scanFailure])
  · rfl
  · intro candidatePolicy candidateBindings hsuccess
    simp [orderedScanCanaryApplicability, scanFailureType, scanSuccessType,
      scanSuccessPolicy]
      at hsuccess
  · simp [orderedScanCanaryApplicability]
  · simp
  · apply FunctionCandidateScanRel.functionSuccess
        (argumentTypes := []) (returnType := .symbol "B")
        (policy := scanSuccessPolicy) (output := Bindings.empty)
    · rfl
    · exact Or.inr ⟨rfl, rfl⟩

/-- Negative order canary: once the head function candidate succeeds, the
same candidate list cannot be presented as exhausted, so tuple fallback and
all-failed errors are unavailable. -/
theorem ordered_scan_first_success_excludes_exhaustion
    (candidates errors : List Atom) (tupleEligible : Bool) :
    ¬FunctionCandidateScanRel orderedScanCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      (scanSuccessType :: candidates) (.exhausted errors tupleEligible) := by
  intro hscan
  cases hscan with
  | nonFunctionExhausted hnot _ =>
      exact hnot ⟨[], .symbol "B", rfl⟩
  | functionFailureExhausted _ hnoSuccess _ _ _ =>
      exact hnoSuccess scanSuccessPolicy Bindings.empty (by
        simp [orderedScanCanaryApplicability, scanSuccessPolicy])

private def scanArityFailure : Atom :=
  mkError scanExpression .incorrectNumberOfArguments

private def scanArgumentFailure : Atom :=
  mkError scanExpression
    (.badArgType 1 (.symbol "B") (.symbol "C"))

private def orderedBlockCanaryApplicability
    (_space : Space) (_expression functionType _expectedType : Atom)
    (_bindings : Bindings)
    (outcome : SelectedTypeApplicabilityOutcome) : Prop :=
  (functionType = scanFailureType ∧
    outcome = .error [scanArityFailure]) ∨
  (functionType = scanSuccessType ∧
    outcome = .error [scanArgumentFailure])

/-- W16 order canary: complete failed-candidate blocks are concatenated in
function-candidate scan order and remain contiguous.  This is the
cross-candidate order observed at the HE reference revision used by the
conformance suite. -/
theorem ordered_scan_concatenates_candidate_error_blocks :
    FunctionCandidateScanRel orderedBlockCanaryApplicability Space.empty
      scanExpression Atom.undefinedType Bindings.empty
      [scanFailureType, scanSuccessType]
      (.exhausted [scanArityFailure, scanArgumentFailure] false) := by
  apply FunctionCandidateScanRel.functionFailureExhausted
      (argumentTypes := []) (candidateReturn := .symbol "A")
      (candidateErrors := [scanArityFailure])
  · rfl
  · intro policy output success
    simp [orderedBlockCanaryApplicability] at success
  · exact Or.inl ⟨rfl, rfl⟩
  · simp
  · apply FunctionCandidateScanRel.functionFailureExhausted
        (argumentTypes := []) (candidateReturn := .symbol "B")
        (candidateErrors := [scanArgumentFailure])
    · rfl
    · intro policy output success
      simp [orderedBlockCanaryApplicability] at success
    · exact Or.inr ⟨rfl, rfl⟩
    · simp
    · exact .nil

/-! ## Shared full/minimal evaluator judgments -/

/-- Variables of the complete expected application that remain public while
its operator head is evaluated.  A type service may introduce fresh private
names, but none may collide with this enclosing scope. -/
def expectedApplicationScope (expression expectedType : Atom) : List String :=
  (TypeSubst.typeVars expectedType ++ TypeSubst.typeVars expression).eraseDups

/-- Completed values are held for Undefined demand as well as the ordinary
intrinsic passthrough cases. No call or function syntax is activated here. -/
def CompletedNativeKeepRel (value expectedType : Atom) : Prop :=
  IsEmptyOrErrorRel value ∨ expectedType = Atom.undefinedType ∨
    expectedType = Atom.atomType ∨
    ∃ metaType, MetaTypeRel value metaType ∧
      (expectedType = metaType ∨ metaType = Atom.variableType)

/-- The return judgment for producer-completed values. A required cast is
the existing type service, not recursive interpretation of the value. -/
inductive CompletedNativeReturnRel
    (space : Space) (typing : EvalTypeService) (value expectedType : Atom)
    (bindings : Bindings) : ResultPair → Prop where
  | keep :
      CompletedNativeKeepRel value expectedType →
      CompletedNativeReturnRel space typing value expectedType bindings (value, bindings)
  | cast {result : ResultPair} :
      ¬CompletedNativeKeepRel value expectedType →
      typing.typeCast [] space value expectedType bindings result →
      CompletedNativeReturnRel space typing value expectedType bindings result

open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Minimal

mutual

/-- Evaluate one atom to one raw result. -/
inductive EvalAtomRawRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Bindings → ResultPair →
      (protectedScope : List String := []) →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | emptyOrError (atom expectedType : Atom) (bindings : Bindings) :
      IsEmptyOrErrorRel atom →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope)
        (typing := typing) atom expectedType bindings
        (atom, bindings)
  | typePass (atom expectedType metaType : Atom) (bindings : Bindings) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      (expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope)
        (typing := typing) atom expectedType bindings
        (atom, bindings)
  | cast (atom expectedType metaType : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      ((∃ name, atom = .symbol name) ∨
        (∃ value, atom = .grounded value) ∨ atom = Atom.unit) →
      typing.typeCast protectedScope space atom expectedType bindings result →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope)
        (typing := typing)
        atom expectedType bindings result
  | interpretSuccess (atom expectedType metaType : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      InterpretExpressionRel space dispatch live (typing := typing)
        atom expectedType bindings result →
      ¬IsErrorRel result.1 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope)
        (typing := typing)
        atom expectedType bindings result
  | interpretError (atom expectedType metaType : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬IsEmptyOrErrorRel atom →
      MetaTypeRel atom metaType →
      ¬(expectedType = Atom.atomType ∨
        expectedType = metaType ∨ metaType = Atom.variableType) →
      (∃ head tail, atom = .expression (head :: tail)) →
      InterpretExpressionRel space dispatch live (typing := typing)
        atom expectedType bindings result →
      IsErrorRel result.1 →
      EvalAtomRawRel space dispatch live (protectedScope := protectedScope)
        (typing := typing)
        atom expectedType bindings result

/-- Interpret an expression through a function type, tuple fallback, or
operator-type error. -/
inductive InterpretExpressionRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | functionPath (expression expectedType operator : Atom)
      (arguments types : List Atom)
      (policy : SelectedTypePolicy) (callType : Atom)
      (bindings applicableBindings : Bindings)
      (interpreted callResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator types →
      typing.candidateScan space expression expectedType bindings
        types (.success policy applicableBindings) →
      callType = (if policy.returnType = Atom.expressionType
        then Atom.undefinedType else policy.returnType) →
      InterpretFunctionRel space dispatch live (typing := typing)
        expression policy.functionType expectedType
          applicableBindings interpreted →
      CallRel space dispatch live (typing := typing)
        interpreted.1 callType interpreted.2 callResult →
      InterpretExpressionRel space dispatch live (typing := typing)
        expression expectedType bindings callResult
  | tuplePath (expression expectedType operator : Atom)
      (arguments types errors : List Atom) (bindings : Bindings)
      (tupleResult callResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator types →
      typing.candidateScan space expression expectedType bindings
        types (.exhausted errors true) →
      InterpretTupleRel space dispatch live (typing := typing)
        expression bindings tupleResult →
      CallRel space dispatch live (typing := typing)
        tupleResult.1 expectedType tupleResult.2 callResult →
      InterpretExpressionRel space dispatch live (typing := typing)
        expression expectedType bindings callResult
  | functionError (expression expectedType operator errorAtom : Atom)
      (arguments types errors : List Atom) (tupleEligible : Bool)
      (bindings : Bindings) :
      expression = .expression (operator :: arguments) →
      typing.typesOf space operator types →
      typing.candidateScan space expression expectedType bindings
        types (.exhausted errors tupleEligible) →
      errorAtom ∈ errors →
      InterpretExpressionRel space dispatch live (typing := typing)
        expression expectedType bindings (errorAtom, bindings)

/-- Evaluate a function head, then its arguments. -/
inductive InterpretFunctionRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | headError (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : Bindings)
      (headResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch live
        (protectedScope := expectedApplicationScope expression returnType)
        (typing := typing)
        operator functionType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      InterpretFunctionRel space dispatch live (typing := typing)
        expression functionType
        returnType bindings headResult
  | tailError (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch live
        (protectedScope := expectedApplicationScope expression returnType)
        (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretArgsRel space dispatch live (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      InterpretFunctionRel space dispatch live (typing := typing)
        expression functionType
        returnType bindings tailResult
  | success (expression functionType returnType operator : Atom)
      (declaredReturnType : Atom) (arguments argumentTypes : List Atom)
      (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      expression = .expression (operator :: arguments) →
      FunctionTypeRel functionType argumentTypes declaredReturnType →
      EvalAtomRawRel space dispatch live
        (protectedScope := expectedApplicationScope expression returnType)
        (typing := typing)
        operator functionType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretArgsRel space dispatch live (typing := typing)
        arguments argumentTypes
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      InterpretFunctionRel space dispatch live (typing := typing)
        expression functionType
        returnType bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Evaluate argument lists left to right. -/
inductive InterpretArgsRel :
    Space → GroundedDispatch → List Atom →
    List Atom → List Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | nil (bindings : Bindings) :
      InterpretArgsRel space dispatch live (typing := typing) [] [] bindings
        (Atom.unit, bindings)
  | headChangedError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : Bindings) (headResult : ResultPair) :
      EvalAtomRawRel space dispatch live (typing := typing)
        argument expectedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      headResult.1 ≠ argument →
      InterpretArgsRel space dispatch live (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings headResult
  | tailError (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : Bindings) (headResult tailResult : ResultPair) :
      EvalAtomRawRel space dispatch live (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      InterpretArgsRel space dispatch live (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      InterpretArgsRel space dispatch live (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes)
        bindings tailResult
  | success (argument : Atom) (arguments : List Atom)
      (expectedType : Atom) (expectedTypes : List Atom)
      (bindings : Bindings) (headResult tailResult : ResultPair) :
      EvalAtomRawRel space dispatch live (typing := typing)
        argument expectedType bindings
        headResult →
      (¬IsEmptyOrErrorRel headResult.1 ∨ headResult.1 = argument) →
      InterpretArgsRel space dispatch live (typing := typing)
        arguments expectedTypes
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      InterpretArgsRel space dispatch live (typing := typing)
        (argument :: arguments) (expectedType :: expectedTypes) bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Evaluate tuple elements left to right. -/
inductive InterpretTupleRel :
    Space → GroundedDispatch → List Atom →
    Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | singleton (atom : Atom) (bindings : Bindings) (result : ResultPair) :
      EvalAtomRawRel space dispatch live (typing := typing)
        atom Atom.undefinedType bindings
        result →
      InterpretTupleRel space dispatch live (typing := typing)
        (.expression [atom])
        bindings result
  | headError (head : Atom) (tail : List Atom) (bindings : Bindings)
      (headResult : ResultPair) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch live (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch live (typing := typing)
        (.expression (head :: tail))
        bindings headResult
  | tailError (head : Atom) (tail : List Atom) (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch live (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch live (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      IsEmptyOrErrorRel tailResult.1 →
      InterpretTupleRel space dispatch live (typing := typing)
        (.expression (head :: tail))
        bindings tailResult
  | success (head : Atom) (tail : List Atom) (bindings : Bindings)
      (headResult tailResult : ResultPair) :
      tail ≠ [] →
      EvalAtomRawRel space dispatch live (typing := typing)
        head Atom.undefinedType bindings
        headResult →
      ¬IsEmptyOrErrorRel headResult.1 →
      InterpretTupleRel space dispatch live (typing := typing)
        (.expression tail)
        headResult.2 tailResult →
      ¬IsEmptyOrErrorRel tailResult.1 →
      InterpretTupleRel space dispatch live (typing := typing)
        (.expression (head :: tail))
        bindings
        (.expression (headResult.1 :: match tailResult.1 with
          | .expression atoms => atoms | atom => [atom]), tailResult.2)

/-- Perform one MeTTa call step, recursively evaluating host or equation
results when the published evaluator requires it. -/
inductive CallRel :
    Space → GroundedDispatch → List Atom →
    Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | errorPassthrough (atom expectedType : Atom) (bindings : Bindings) :
      IsErrorRel atom →
      CallRel space dispatch live (typing := typing) atom expectedType bindings
        (atom, bindings)
  | unify (atom expectedType target pattern thenBranch elseBranch result : Atom)
      (bindings output : Bindings) :
      atom = .expression
        [.symbol "unify", target, pattern, thenBranch, elseBranch] →
      ¬IsErrorRel atom →
      UnifyStep target pattern thenBranch elseBranch bindings
        result output →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings (result, output)
  | unifyBadArity (atom expectedType : Atom) (tail : List Atom)
      (bindings : Bindings) :
      atom = .expression (.symbol "unify" :: tail) →
      tail.length ≠ 4 →
      ¬IsErrorRel atom →
      CallRel space dispatch live (typing := typing) atom expectedType bindings
        (mkUnifyBadArityError atom, bindings)
  | switchMinimal (atom expectedType scrutinee : Atom)
      (branches : List Atom) (bindings : Bindings) (result : ResultPair) :
      atom = .expression
        [.symbol "switch-minimal", scrutinee, .expression branches] →
      ¬IsErrorRel atom →
      SwitchStep scrutinee branches bindings result.1 result.2 →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings result
  | switchMinimalBadShape (atom expectedType : Atom) (tail : List Atom)
      (bindings : Bindings) :
      atom = .expression (.symbol "switch-minimal" :: tail) →
      (¬∃ scrutinee branches,
        tail = [scrutinee, .expression branches]) →
      ¬IsErrorRel atom →
      CallRel space dispatch live (typing := typing) atom expectedType bindings
        (mkError atom .incorrectNumberOfArguments, bindings)
  | groundedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings)
      (nativeResults : ResultSet) (nativeResult finalResult : ResultPair)
      (merged : Bindings) (completed : ResultPair) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .emitted →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      Minimal.CoreInvocationResultRel space dispatch live (typing := typing)
        nativeResult.1 merged completed →
      EvalAtomRawRel space dispatch live (typing := typing)
        completed.1 expectedType completed.2 finalResult →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings finalResult
  | groundedCompletedSuccess (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings)
      (nativeResults : ResultSet) (nativeResult finalResult : ResultPair)
      (merged : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .completed →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok nativeResults) →
      nativeResult ∈ nativeResults →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      CompletedNativeReturnRel space typing nativeResult.1 expectedType merged finalResult →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings finalResult
  | groundedRuntimeError (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) (message : String) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.runtimeError message) →
      CallRel space dispatch live (typing := typing) atom expectedType bindings
        (Atom.error atom (.symbol message), bindings)
  | groundedNoReduce (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .noReduce →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedIncorrectArgument (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments .incorrectArgument →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings (atom, bindings)
  | groundedEmpty (atom expectedType operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      atom = .expression (operator :: arguments) →
      dispatch.executable operator →
      operator ≠ .symbol "unify" →
      operator ≠ .symbol "switch-minimal" →
      ¬IsErrorRel atom →
      dispatch.outcome operator arguments (.ok []) →
      CallRel space dispatch live (typing := typing) atom expectedType bindings
        (Atom.empty, bindings)
  | equation (atom expectedType emitted : Atom) (bindings merged : Bindings)
      (finalResult completed : ResultPair) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryCandidateRel space live atom bindings emitted merged →
      Minimal.CoreInvocationResultRel space dispatch live (typing := typing)
        emitted merged completed →
      EvalAtomRawRel space dispatch live (typing := typing)
        completed.1 expectedType completed.2 finalResult →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings finalResult
  | noEquation (atom expectedType : Atom) (bindings : Bindings) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryNoMatchRel space live atom bindings →
      CallRel space dispatch live (typing := typing)
        atom expectedType bindings (atom, bindings)
  | allEquationsFiltered (atom expectedType : Atom) (bindings : Bindings) :
      ¬IsErrorRel atom →
      NonGroundedCallRel dispatch atom →
      EquationQueryAllFilteredRel space live atom bindings →
      CallRel space dispatch live (typing := typing) atom expectedType bindings
        (Atom.empty, bindings)


/-- One state-free minimal-instruction step.  The context space is read-only;
the state-writing extension is specified separately by `StateAlgebra`.

`live` is the published equation-query environment threaded by `EvalRel`.
Its `eval` operand invokes one raw native/equation operation. Full typed
interpretation is explicit in the separate `metta` instruction. -/
inductive Minimal.CoreStepRel :
    Space → GroundedDispatch → List Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | eval (space : Space) (atom : Atom) (bindings : Bindings)
      (result : ResultPair) :
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        atom bindings result →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "eval", atom]) bindings result
  | evalc (space context : Space) (atom : Atom) (bindings : Bindings)
      (result : ResultPair) (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreInvocationRel context dispatch live (typing := typing)
        atom bindings result →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "evalc", atom,
          .grounded (services.contextPayload context)]) bindings result
  | chain (space : Space) (atom : Atom) (name : String) (template : Atom)
      (bindings : Bindings) (result : ResultPair) :
      Minimal.CoreRunRel space dispatch live (typing := typing)
        atom bindings result →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "chain", atom, .var name, template]) bindings
        (substituteName name result.1 template, result.2)
  | unify (space : Space) (target pattern thenBranch elseBranch result : Atom)
      (bindings output : Bindings) :
      UnifyStep target pattern thenBranch elseBranch bindings result output →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
        bindings (result, output)
  | consAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : Bindings) :
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "cons-atom", head, .expression tail]) bindings
        (.expression (head :: tail), bindings)
  | deconsAtom (space : Space) (head : Atom) (tail : List Atom)
      (bindings : Bindings) :
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "decons-atom", .expression (head :: tail)])
        bindings (.expression [head, .expression tail], bindings)
  | collapseBind (space : Space) (atom : Atom) (bindings : Bindings)
      (results : ResultSet) (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      enumeration.minimalResults space atom bindings results →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "collapse-bind", atom]) bindings
        (encodeResults services results, bindings)
  | superposeBind (space : Space) (results : ResultSet)
      (stored : ResultPair) (bindings merged : Bindings)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      stored ∈ results →
      MergeRel equalityGroundedSemantic stored.2 bindings merged →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "superpose-bind", encodeResults services results])
        bindings (stored.1, merged)
  | functionReturn (space : Space) (body returned : Atom)
      (bindings output : Bindings) :
      (∃ atoms, body = .expression atoms) →
      Minimal.CoreFunctionBodyRel space dispatch live (typing := typing)
        body bindings (.expression [.symbol "return", returned], output) →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "function", body]) bindings (returned, output)
  | functionNoReturn (space : Space) (body result : Atom)
      (bindings output : Bindings) :
      (∃ atoms, body = .expression atoms) →
      Minimal.CoreFunctionBodyRel space dispatch live (typing := typing)
        body bindings (result, output) →
      (∀ returned, result ≠ .expression [.symbol "return", returned]) →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "function", body]) bindings
        (Atom.error (.expression [.symbol "function", body])
          (.symbol "NoReturn"), output)
  | metta (space context : Space) (atom expectedType : Atom)
      (bindings : Bindings) (result : ResultPair)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      EvalAtomRawRel context dispatch live atom expectedType bindings result
        (typing := typing) →
      ¬IsErrorRel result.1 →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings result
  | mettaAtom (space context : Space) (atom : Atom) (bindings : Bindings)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "metta", atom, Atom.atomType,
          .grounded (services.contextPayload context)]) bindings (atom, bindings)
  | mettaError (space context : Space) (atom expectedType : Atom) (bindings : Bindings)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      IsErrorRel atom →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "metta", atom, expectedType,
          .grounded (services.contextPayload context)]) bindings (atom, bindings)
  | contextSpace (space : Space) (bindings : Bindings)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "context-space"]) bindings
        (.grounded (services.contextPayload space), bindings)
  | callNative (space : Space) (name function arguments : Atom)
      (bindings : Bindings) (result : ResultPair) (merged : Bindings)
      (services : Services) (enumeration : Enumeration) :
      dispatch.minimal = some ⟨services, enumeration⟩ →
      services.nativeCall name function arguments bindings result →
      MergeRel equalityGroundedSemantic result.2 bindings merged →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "call-native", name, function, arguments])
        bindings (result.1, merged)

/-- Raw native/equation invocation: bindings are merged, but the emitted
ordinary atom is not recursively interpreted. An embedded operand is executed
by the minimal machine; an emitted `function` block has its own return frame. -/
inductive Minimal.CoreInvocationRel :
    Space → GroundedDispatch → List Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | embedded (space : Space) (atom : Atom) (bindings : Bindings)
      (result : ResultPair) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = true →
      Minimal.CoreRunRel space dispatch live (typing := typing)
        atom bindings result →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        atom bindings result
  | grounded (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings merged : Bindings) (results : ResultSet)
      (nativeResult result : ResultPair) (emitted : Atom) :
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .emitted →
      dispatch.outcome operator arguments (.ok results) →
      nativeResult ∈ results →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      (∃ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation merged) →
      (∀ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation merged →
          LeaTTaBridge.HEAtomEquationSatisfied valuation emitted nativeResult.1) →
      Minimal.CoreInvocationResultRel space dispatch live (typing := typing)
        emitted merged result →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        (.expression (operator :: arguments)) bindings result
  | completedGrounded (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings merged : Bindings) (results : ResultSet)
      (nativeResult : ResultPair) (emitted : Atom) :
      dispatch.executable operator →
      dispatch.valueProvenance operator arguments = .completed →
      dispatch.outcome operator arguments (.ok results) →
      nativeResult ∈ results →
      MergeRel equalityGroundedSemantic nativeResult.2 bindings merged →
      (∃ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation merged) →
      (∀ valuation : String → Metta.Atom,
        LeaTTaBridge.HEBindingSatisfied valuation merged →
          LeaTTaBridge.HEAtomEquationSatisfied valuation emitted nativeResult.1) →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        (.expression (operator :: arguments)) bindings (emitted, merged)
  | groundedEmpty (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : Bindings) :
      dispatch.executable operator →
      dispatch.outcome operator arguments (.ok []) →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        (.expression (operator :: arguments)) bindings (Atom.empty, bindings)
  | groundedError (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : Bindings) (message : String) :
      dispatch.executable operator →
      dispatch.outcome operator arguments (.runtimeError message) →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        (.expression (operator :: arguments)) bindings
        (Atom.error (.expression (operator :: arguments)) (.symbol message), bindings)
  | groundedNoReduce (space : Space) (operator : Atom) (arguments : List Atom)
      (bindings : Bindings) :
      dispatch.executable operator →
      dispatch.outcome operator arguments .noReduce →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        (.expression (operator :: arguments)) bindings
        (Atom.notReducible, bindings)
  | groundedIncorrectArgument (space : Space) (operator : Atom)
      (arguments : List Atom) (bindings : Bindings) :
      dispatch.executable operator →
      dispatch.outcome operator arguments .incorrectArgument →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        (.expression (operator :: arguments)) bindings
        (Atom.notReducible, bindings)
  | equation (space : Space) (atom emitted : Atom)
      (bindings merged : Bindings) (result : ResultPair) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryCandidateRel space live atom bindings emitted merged →
      Minimal.CoreInvocationResultRel space dispatch live (typing := typing)
        emitted merged result →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        atom bindings result
  | noEquation (space : Space) (atom : Atom) (bindings : Bindings) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryNoMatchRel space live atom bindings →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        atom bindings (Atom.notReducible, bindings)
  | allEquationsFiltered (space : Space) (atom : Atom) (bindings : Bindings) :
      ¬HostCall dispatch atom →
      embeddedInstruction atom = false →
      EquationQueryAllFilteredRel space live atom bindings →
      Minimal.CoreInvocationRel space dispatch live (typing := typing)
        atom bindings (Atom.notReducible, bindings)

/-- Completing a raw invocation interprets only an authored `function`
block. Other emitted expressions, including callable-looking data, remain
raw. This is independent of the ordinary typed result continuation. -/
inductive Minimal.CoreInvocationResultRel :
    Space → GroundedDispatch → List Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | raw (space : Space) (atom : Atom) (bindings : Bindings) :
      ¬IsFunction atom →
      Minimal.CoreInvocationResultRel space dispatch live (typing := typing)
        atom bindings (atom, bindings)
  | function (space : Space) (body : Atom) (bindings : Bindings)
      (result : ResultPair) :
      Minimal.CoreStepRel space dispatch live (typing := typing)
        (.expression [.symbol "function", body]) bindings result →
      Minimal.CoreInvocationResultRel space dispatch live (typing := typing)
        (.expression [.symbol "function", body]) bindings result

/-- Completed raw minimal execution. `chain` schedules the substituted
template; other instruction outputs are returned raw. The reference minimal
machine carries Empty and NotReducible through chain as ordinary sentinel
atoms; final observation, not this continuation, removes Empty. -/
inductive Minimal.CoreRunRel :
    Space → GroundedDispatch → List Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | data (space : Space) (atom : Atom) (bindings : Bindings) :
      embeddedInstruction atom = false →
      Minimal.CoreRunRel space dispatch live (typing := typing)
        atom bindings (atom, bindings)
  | instruction (space : Space) (atom : Atom) (bindings : Bindings)
      (result : ResultPair) :
      embeddedInstruction atom = true →
      ¬IsChain atom →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        atom bindings result →
      Minimal.CoreRunRel space dispatch live (typing := typing)
        atom bindings result
  | chain (space : Space) (atom : Atom) (bindings : Bindings)
      (selected result : ResultPair) :
      IsChain atom →
      Minimal.CoreStepRel space dispatch live (typing := typing)
        atom bindings selected →
      Minimal.CoreRunRel space dispatch live (typing := typing)
        selected.1 selected.2 result →
      Minimal.CoreRunRel space dispatch live (typing := typing)
        atom bindings result

/-- A function body resumes embedded instructions until a noninstruction
terminal is reached. A terminal without `return` produces NoReturn, including
an internal Empty sentinel reached by a valid expression-shaped body. -/
inductive Minimal.CoreFunctionBodyRel :
    Space → GroundedDispatch → List Atom → Atom → Bindings → ResultPair →
      (typing : EvalTypeService := publishedTypeService) → Prop where
  | terminal (space : Space) (atom : Atom) (bindings : Bindings) :
      embeddedInstruction atom = false →
      Minimal.CoreFunctionBodyRel space dispatch live (typing := typing)
        atom bindings (atom, bindings)
  | resume (space : Space) (atom : Atom) (bindings : Bindings)
      (intermediate result : ResultPair) :
      embeddedInstruction atom = true →
      Minimal.CoreRunRel space dispatch live (typing := typing)
        atom bindings intermediate →
      Minimal.CoreFunctionBodyRel space dispatch live (typing := typing)
        intermediate.1 intermediate.2 result →
      Minimal.CoreFunctionBodyRel space dispatch live (typing := typing)
        atom bindings result

end

/-! ## Public success-priority boundary -/

/-- A published evaluator result: raw successes are admitted directly; a raw
error is admitted only if no raw non-error result exists for the same input. -/
def EvalRel
    (space : Space) (dispatch : GroundedDispatch) (live : List Atom)
    (atom expectedType : Atom) (bindings : Bindings) (result : ResultPair)
    (typing : EvalTypeService := publishedTypeService) : Prop :=
  EvalAtomRawRel space dispatch live (typing := typing)
      atom expectedType bindings result ∧
    (IsErrorRel result.1 →
      ∀ candidate,
        EvalAtomRawRel space dispatch live (typing := typing)
          atom expectedType bindings candidate →
          IsErrorRel candidate.1)

/-! ## Boundary examples -/

private def noHostDispatch : GroundedDispatch where
  executable := fun _ => False
  outcome := fun _ _ _ => False

/-- Positive error-shape canary: the published ellipsis permits an empty
tail after the `Error` head. -/
example : IsErrorRel (.expression [.symbol "Error"]) :=
  ⟨[], rfl⟩

/-- Negative error-shape canary: the bare `Error` symbol is data, not an
error expression. -/
example : ¬IsErrorRel (.symbol "Error") := by
  rintro ⟨tail, h⟩
  cases h

/-- Positive: `Empty` passes through unchanged. -/
example : EvalRel Space.empty noHostDispatch []
    Atom.empty Atom.undefinedType Bindings.empty
    (Atom.empty, Bindings.empty) := by
  constructor
  · exact EvalAtomRawRel.emptyOrError _ _ _ (Or.inl rfl)
  · intro herror
    exact (by rcases herror with ⟨tail, h⟩; cases h)

private theorem variablePassRaw (name : String) (expectedType : Atom)
    (protectedScope : List String := []) :
    EvalAtomRawRel Space.empty noHostDispatch []
    (.var name) expectedType Bindings.empty
    (.var name, Bindings.empty) protectedScope := by
  apply EvalAtomRawRel.typePass (.var name) expectedType
      Atom.variableType Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.variable name
  · exact Or.inr (Or.inr rfl)

/-- Positive tuple recursion: a singleton tuple delegates to atom evaluation. -/
example : InterpretTupleRel Space.empty noHostDispatch []
    (.expression [.var "x"]) Bindings.empty
    (.var "x", Bindings.empty) :=
  InterpretTupleRel.singleton (.var "x") Bindings.empty
    (.var "x", Bindings.empty) (variablePassRaw "x" Atom.undefinedType)

private def unaryWantedType : Atom :=
  .expression [.symbol "->", .symbol "Wanted", .symbol "Wanted"]

private theorem variableArgumentRaw :
    InterpretArgsRel Space.empty noHostDispatch []
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (.expression [.var "x"], Bindings.empty) := by
  apply InterpretArgsRel.success
      (.var "x") [] (.symbol "Wanted") [] Bindings.empty
      (.var "x", Bindings.empty) (Atom.unit, Bindings.empty)
  · exact variablePassRaw "x" (.symbol "Wanted")
  · exact Or.inr rfl
  · exact InterpretArgsRel.nil Bindings.empty
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty, Atom.unit]

/-- Positive function recursion: variables pass the declared unary function
and argument types, producing the interpreted call expression. -/
example : InterpretFunctionRel Space.empty noHostDispatch []
    (.expression [.var "f", .var "x"])
    unaryWantedType (.symbol "Wanted") Bindings.empty
    (.expression [.var "f", .var "x"], Bindings.empty) := by
  apply InterpretFunctionRel.success
      (.expression [.var "f", .var "x"])
      unaryWantedType (.symbol "Wanted") (.var "f")
      (.symbol "Wanted")
      [.var "x"] [.symbol "Wanted"] Bindings.empty
      (.var "f", Bindings.empty)
      (.expression [.var "x"], Bindings.empty)
  · rfl
  · rfl
  · exact variablePassRaw "f" unaryWantedType
      (expectedApplicationScope
        (.expression [.var "f", .var "x"]) (.symbol "Wanted"))
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact variableArgumentRaw
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]

/-- Positive type-cast path: an unannotated symbol has `%Undefined%`, which
matches any expected type. -/
example : EvalAtomRawRel Space.empty noHostDispatch []
    (.symbol "x") (.symbol "Wanted") Bindings.empty
    (.symbol "x", Bindings.empty) := by
  apply EvalAtomRawRel.cast
      (.symbol "x") (.symbol "Wanted") Atom.symbolType Bindings.empty
      (.symbol "x", Bindings.empty)
  · simp [IsEmptyOrErrorRel, IsErrorRel, Atom.empty]
  · exact MetaTypeRel.symbol "x"
  · simp [Atom.atomType, Atom.symbolType, Atom.variableType]
  · exact Or.inl ⟨"x", rfl⟩
  · apply TypeCastRel.success
        (types := [Atom.undefinedType]) (earlierTypes := [])
        (laterTypes := []) (actualType := Atom.undefinedType)
    · exact TypesOfRel.symbolUndefined AnnotationTypesRel.nil
    · rfl
    · simp
    · exact TypeMatchRel.undefinedRight (.symbol "Wanted") Bindings.empty

/-- Negative unify branch: a symbol mismatch returns the else atom. -/
example : CallRel Space.empty noHostDispatch []
    (.expression [.symbol "unify", .symbol "a", .symbol "b",
      .symbol "then", .symbol "else"])
    Atom.undefinedType Bindings.empty (.symbol "else", Bindings.empty) := by
  apply CallRel.unify
      (.expression [.symbol "unify", .symbol "a", .symbol "b",
        .symbol "then", .symbol "else"])
      Atom.undefinedType (.symbol "a") (.symbol "b")
      (.symbol "then") (.symbol "else") (.symbol "else")
      Bindings.empty Bindings.empty rfl
  · simp [IsErrorRel]
  · apply UnifyStep.noMatch
    intro output hcandidate
    obtain ⟨matched, hmatch, _⟩ := hcandidate
    exact symbol_mismatch_not_match (by decide) matched hmatch

/-- Negative switch branch: an empty branch list has no selected result and
therefore reduces to `Empty`. -/
example : CallRel Space.empty noHostDispatch []
    (.expression [.symbol "switch-minimal", .symbol "a", .expression []])
    Atom.undefinedType Bindings.empty (Atom.empty, Bindings.empty) := by
  apply CallRel.switchMinimal
      (.expression [.symbol "switch-minimal", .symbol "a", .expression []])
      Atom.undefinedType (.symbol "a") [] Bindings.empty
      (Atom.empty, Bindings.empty) rfl
  · simp [IsErrorRel]
  · exact SwitchStep.noMatch SwitchRawRel.nil

/-- Negative equation-query branch: an empty space returns the atom unchanged. -/
example : CallRel Space.empty noHostDispatch []
    (.symbol "unreduced") Atom.undefinedType Bindings.empty
    (.symbol "unreduced", Bindings.empty) := by
  apply CallRel.noEquation
  · rintro ⟨tail, hError⟩
    cases hError
  · trivial
  · intro freshPattern freshRhs matched hmatch
    obtain ⟨rawLhs, rawRhs, hmem, _⟩ := hmatch
    simp [Space.empty] at hmem

private def noReduceDispatch : GroundedDispatch where
  executable := fun operator => operator = .symbol "native"
  outcome := fun operator _ result =>
    operator = .symbol "native" ∧ result = .noReduce

/-- Positive grounded boundary: a host `NoReduce` outcome preserves the call
unchanged without importing an executable dispatcher. -/
example : CallRel Space.empty noReduceDispatch []
    (.expression [.symbol "native", .symbol "argument"])
    Atom.undefinedType Bindings.empty
    (.expression [.symbol "native", .symbol "argument"], Bindings.empty) := by
  apply CallRel.groundedNoReduce
      (.expression [.symbol "native", .symbol "argument"])
      Atom.undefinedType (.symbol "native") [.symbol "argument"]
      Bindings.empty rfl
  · rfl
  · decide
  · decide
  · simp [IsErrorRel]
  · exact ⟨rfl, rfl⟩

end Mettapedia.Languages.MeTTa.HE.Spec.Eval
