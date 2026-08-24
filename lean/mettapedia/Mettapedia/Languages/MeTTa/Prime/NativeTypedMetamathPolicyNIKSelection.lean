import Mettapedia.Languages.MeTTa.Prime.DataFibration
import Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
import Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathAssertionOptimization

/-!
# Maximal-native and policy selection for prepared Metamath assertions

An authored assertion table has two admitted realizations of the same ordered
observation contract: the ordinary source scan and the immutable prepared
index.  A valid projection licenses both, and the prepared realization is
strictly stronger because it additionally supports direct keyed lookup.

This module places that concrete family under the common maximal-native NIK
selection theorem.  Exact observations and occurrence counts are independent
policies over the retained receipt.  A result-only readout cannot reconstruct
the execution face, and profitability cannot select a cheaper non-maximal
scan or manufacture admission for an ambiguous table.

Fused assertion application remains a subsequent admitted transformation.
It is composed after exact record selection rather than inserted into an
artificial global ranking with the two lookup realizations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathPolicyNIKSelection

open Mettapedia.GSLT.Core
open Mettapedia.GSLT.LanguageDef.MaximalNativeCalculus
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKPolicyFamilyAdmission
open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.MonotoneUniqueIndexCompilation
open Mettapedia.Languages.MeTTa.Prime.DataFibration
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCapabilitySelection
open Mettapedia.Languages.MeTTa.Prime.NIKPolicyFamilyCurrentSelection
open Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection
open Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathAssertionOptimization
open Mettapedia.Languages.Metamath.MMLean4Bridge
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceProjection.AssertionApplication
open Mettapedia.Languages.Metamath.InferenceAssertionFusedCompilation
open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation

/-! ## Two concrete realizations of one observation contract -/

/-- The runtime face retained by an exact lookup receipt. -/
inductive LookupFace where
  | orderedScan
  | preparedIndex
  deriving DecidableEq, Repr

/-- A lookup receipt retains its authored query occurrences, ordered optional
results, and the realization face that produced them. -/
structure LookupReceipt where
  queries : List String
  observations : List (Option AssertionView)
  face : LookupFace

/-- The source fibre is the authored ordered list of query occurrences. -/
def lookupSource : AdmissionObject where
  Carrier := List String
  Meaning := fun _ => True

/-- Both implementations target the exact authored source-scan semantics.
The face remains proof-relevant but is not part of semantic equality. -/
def lookupTarget (projection : PrefixProjection) : AdmissionObject where
  Carrier := LookupReceipt
  Meaning := fun receipt =>
    receipt.observations =
      runSource (assertionRecordSource projection receipt.queries)

/-- Ordinary relational execution scans the authored assertion records in
source order. -/
def orderedScanOperation (projection : PrefixProjection) :
    lookupSource ⟶ lookupTarget projection where
  run := fun queries =>
    { queries
      observations := runSource (assertionRecordSource projection queries)
      face := .orderedScan }
  preserves := by
    intro queries _meaningful
    rfl

/-- A validated projection constructs the immutable index once and performs
the same ordered query occurrences by direct lookup. -/
def preparedIndexOperation (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    lookupSource ⟶ lookupTarget projection where
  run := fun queries =>
    { queries
      observations :=
        runArtifact
          (compile (admittedAssertionRecords projection queries valid).plan
            (admittedAssertionRecords projection queries valid).source)
      face := .preparedIndex }
  preserves := by
    intro queries _meaningful
    exact compiledAssertionRecords_observe_source projection queries valid

/-- Candidate indices use the existing Boolean order: `false` is the ordered
scan and `true` is the prepared index. -/
abbrev LookupRealization := Bool

def orderedScan : LookupRealization := false
def preparedIndex : LookupRealization := true

inductive LookupCapability where
  | exactOrderedObservations
  | compiledKeyedLookup
  deriving DecidableEq, Repr

/-- Both faces preserve exact ordered observations.  Only the prepared index
supports compiled keyed lookup. -/
def supports : LookupRealization -> LookupCapability -> Prop
  | _, .exactOrderedObservations => True
  | realization, .compiledKeyedLookup => realization = preparedIndex

/-- The capability ordering is grounded by the executable equality between
the compiled table lookup and the authored source lookup. -/
theorem compiled_keyed_lookup_exact
    (projection : PrefixProjection) (label : String) :
    compiledAssertionRecord? projection label =
      sourceLookup label (assertionRecordEntries projection) := by
  exact lookup_compileIndex (assertionRecordEntries projection) label

theorem prepared_supports_compiled_keyed_lookup :
    supports preparedIndex .compiledKeyedLookup :=
  rfl

theorem ordered_scan_refuses_compiled_keyed_lookup :
    Not (supports orderedScan .compiledKeyedLookup) := by
  intro impossible
  change false = true at impossible
  cases impossible

/-- The recognized family contains actual source-scan and compiled-index
functions, both already carrying their semantic-preservation proof. -/
def lookupFamily (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    RecognizedFamily LookupRealization lookupSource (lookupTarget projection)
    where
  package
    | false => orderedScanOperation projection
    | true => preparedIndexOperation projection valid
  Capability := LookupCapability
  supports := supports
  supports_mono := by
    intro weaker stronger related capability supported
    cases capability with
    | exactOrderedObservations => trivial
    | compiledKeyedLookup =>
      change weaker = true at supported
      subst weaker
      change stronger = true
      cases stronger with
      | false =>
          exact False.elim ((by decide : ¬ (true ≤ false)) related)
      | true => rfl
  strict_support_gain := by
    intro weaker stronger strict
    cases weaker with
    | false =>
        cases stronger with
        | false =>
            exact False.elim ((by decide : ¬ (false < false)) strict)
        | true =>
            exact ⟨.compiledKeyedLookup,
              prepared_supports_compiled_keyed_lookup,
              ordered_scan_refuses_compiled_keyed_lookup⟩
    | true =>
        cases stronger with
        | false =>
            exact False.elim ((by decide : ¬ (true < false)) strict)
        | true =>
            exact False.elim ((by decide : ¬ (true < true)) strict)
  recognized := Finset.univ
  licensed := Finset.univ
  licensed_subset_recognized := by
    intro candidate _member
    simp
  licensed_nonempty := ⟨false, by simp⟩

/-- The semantic request asks only for exact ordered observations.  Both
implementations qualify; native maximality, not a hand-written dispatcher,
selects the strictly stronger prepared index. -/
def lookupRequest (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (lookupFamily projection valid).CapabilityRequest where
  required := fun capability => capability = .exactOrderedObservations
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      constructor
      · simp [lookupFamily]
      · intro capability required
        subst capability
        cases candidate <;> trivial
    · intro _data
      simp
  candidates_nonempty := ⟨false, by simp⟩

/-- The prepared index is genuinely greatest in this exact request fibre. -/
def strongestLookup (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (lookupRequest projection valid).StrongestNativeCalculusPrinciple where
  val := preparedIndex
  property := by
    constructor
    · change true ∈ (lookupRequest projection valid).candidates
      simp [lookupRequest]
    · intro candidate _member
      cases candidate <;> decide

theorem strongest_lookup_is_prepared
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (strongestLookup projection valid).1 = preparedIndex :=
  rfl

/-! ## Independent policies over the retained receipt -/

inductive ReceiptPolicy where
  | exactObservations
  | occurrenceCount
  | executionFace
  deriving DecidableEq, Repr

def receiptPolicies : PolicyFamily LookupReceipt where
  Policy := ReceiptPolicy
  Result
    | .exactObservations => List (Option AssertionView)
    | .occurrenceCount => Nat
    | .executionFace => LookupFace
  decide
    | .exactObservations => LookupReceipt.observations
    | .occurrenceCount => fun receipt => receipt.observations.length
    | .executionFace => LookupReceipt.face

def resultOnlySupports (_ : LookupRealization) : ReceiptPolicy -> Prop
  | .exactObservations => True
  | .occurrenceCount => True
  | .executionFace => False

/-- The policy readout deliberately forgets operational face provenance. -/
def resultOnlyCatalog :
    PolicyReadoutCatalog LookupRealization LookupReceipt receiptPolicies where
  Key := fun _ => List (Option AssertionView)
  readout := fun _ receipt => receipt.observations
  Supports := resultOnlySupports
  runner := by
    intro index policy supported
    cases policy with
    | exactObservations => exact id
    | occurrenceCount => exact List.length
    | executionFace => exact False.elim supported
  agrees := by
    intro index policy supported state
    cases policy with
    | exactObservations => rfl
    | occurrenceCount => rfl
    | executionFace => exact False.elim supported
  supports_mono := by
    intro weaker stronger _related policy supported
    cases policy <;> exact supported

def requiredReceiptPolicies : Set ReceiptPolicy :=
  fun policy =>
    policy = .exactObservations ∨ policy = .occurrenceCount

/-- Add exact-result and occurrence-count policies without changing the
underlying semantic request. -/
def policyRequest (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    PolicyCapabilityRequest resultOnlyCatalog
      (lookupRequest projection valid) where
  requiredPolicies := requiredReceiptPolicies
  candidates := Finset.univ
  candidates_exact := by
    intro candidate
    constructor
    · intro _member
      constructor
      · simp [lookupRequest]
      · intro policy required
        rcases required with left | right
        · subst policy
          trivial
        · subst policy
          trivial
    · intro _data
      simp
  candidates_nonempty := ⟨false, by simp⟩

/-- Policy requirements preserve the same unique strongest realization. -/
def strongestPolicyLookup (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (policyRequest projection valid).toCapabilityRequest
      |>.StrongestNativeCalculusPrinciple where
  val := preparedIndex
  property := by
    constructor
    · change true ∈ (policyRequest projection valid).candidates
      simp [policyRequest]
    · intro candidate _member
      cases candidate <;> decide

def dependencies : DependencySystem where
  Revision := Nat
  Dependency := Unit
  Value := Nat
  read := fun revision _ => revision

/-- Retain the concrete strongest operation and its two requested policies at
one exact logical revision. -/
def selectedAt (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) (revision : Nat) :
    SelectedPolicyAdmissionAt (policyRequest projection valid)
      dependencies revision :=
  SelectedPolicyAdmissionAt.ofStrongest (policyRequest projection valid)
    (strongestPolicyLookup projection valid) dependencies revision

def exactPolicy (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (policyRequest projection valid).requestedFamily.Policy :=
  ⟨.exactObservations, Or.inl rfl⟩

def countPolicy (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (policyRequest projection valid).requestedFamily.Policy :=
  ⟨.occurrenceCount, Or.inr rfl⟩

def activeAt (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) (revision : Nat) :
    (selectedAt projection valid revision).Active revision :=
  (selectedAt projection valid revision).activate
    (dependencies.sameDependencies_refl revision)

/-- Execute the selected lookup once and run a requested policy from its
retained result-only key. -/
def runObserved
    {projection : PrefixProjection}
    {valid : prefixProjectionValid projection = true}
    {revision currentRevision : Nat}
    {selected : SelectedPolicyAdmissionAt (policyRequest projection valid)
      dependencies revision}
    (active : selected.Active currentRevision)
    (queries : List String)
    (policy : (policyRequest projection valid).requestedFamily.Policy) :
    LookupReceipt ×
      (policyRequest projection valid).requestedFamily.Result policy :=
  let receipt : LookupReceipt := active.run queries
  (receipt,
    active.policyActive.runKey policy
      (resultOnlyCatalog.readout selected.candidate receipt))

@[simp] theorem runObserved_eq
    {projection : PrefixProjection}
    {valid : prefixProjectionValid projection = true}
    {revision currentRevision : Nat}
    {selected : SelectedPolicyAdmissionAt (policyRequest projection valid)
      dependencies revision}
    (active : selected.Active currentRevision)
    (queries : List String)
    (policy : (policyRequest projection valid).requestedFamily.Policy) :
    runObserved active queries policy =
      let receipt : LookupReceipt := selected.operation.run queries
      (receipt,
        (policyRequest projection valid).requestedFamily.decide policy
          receipt) := by
  simp [runObserved]

/-- The selected current operation is the prepared-index implementation and
its retained preservation proof establishes exact ordered observations. -/
theorem current_lookup_is_prepared_and_exact
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true)
    (revision : Nat) (queries : List String) :
    ((activeAt projection valid revision).run queries).face =
        .preparedIndex ∧
      ((activeAt projection valid revision).run queries).observations =
        runSource (assertionRecordSource projection queries) := by
  constructor
  · rfl
  · exact (activeAt projection valid revision).run_preserves queries trivial

/-- The current hot path is an admitted flow: its operation already carries
the semantic proof and therefore needs no interior certificate replay. -/
def admittedFlowMode (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) (revision : Nat) :
    EntryMode LookupReceipt :=
  .admittedFlow lookupSource (lookupTarget projection).Meaning
    (selectedAt projection valid revision).operation

@[simp] theorem admittedFlowMode_certificateFree
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) (revision : Nat) :
    EntryMode.requiresCertificate
      (admittedFlowMode projection valid revision) = false :=
  rfl

theorem current_lookup_accepted_by_admittedFlow
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true)
    (revision : Nat) (queries : List String) :
    EntryMode.Accepted (admittedFlowMode projection valid revision)
      ((activeAt projection valid revision).run queries) :=
  (activeAt projection valid revision).run_preserves queries trivial

/-! ## Staleness and information-loss boundaries -/

theorem nextRevision_is_stale
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) (revision : Nat) :
    (selectedAt projection valid revision).StaleAt (revision + 1) := by
  intro current
  have impossible := current ()
  simp [dependencies] at impossible

def preparedFallback (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true)
    (revision : Nat) (queries : List String) :
    (selectedAt projection valid revision).Prepared :=
  (selectedAt projection valid revision).prepare queries
    ((activeAt projection valid revision).run queries)

/-- A revision change disables the operation and all requested policies
together, while retaining both the raw query list and complete lookup receipt
for ordinary execution or re-admission. -/
theorem changed_revision_refuses_selection_and_preserves_fallback
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true)
    (revision : Nat) (queries : List String) :
    (Not ((selectedAt projection valid revision).Active (revision + 1))) ∧
      (preparedFallback projection valid revision queries).fallback =
        (queries, (activeAt projection valid revision).run queries) :=
  (selectedAt projection valid revision)
    |>.stale_prevents_activation_and_preserves_fallback
      (nextRevision_is_stale projection valid revision)
      (preparedFallback projection valid revision queries)

/-- Two receipts may have identical result-only keys while retaining
different execution faces.  Hence the result key cannot silently answer the
larger face-sensitive policy family. -/
theorem resultOnlyReadout_refuses_fullFamily
    (queries : List String) (observations : List (Option AssertionView)) :
    Not (receiptPolicies.SupportsReadout LookupReceipt.observations) := by
  apply receiptPolicies.not_supportsReadout_of_policy_collision
    LookupReceipt.observations
    (first := ⟨queries, observations, .orderedScan⟩)
    (second := ⟨queries, observations, .preparedIndex⟩)
    rfl .executionFace
  intro equal
  cases equal

/-! ## Profitability is downstream of semantic maximality -/

/-- Deliberately price the weaker scan lower.  This adversarial policy checks
that cost cannot promote a semantically non-maximal realization. -/
def preferRawCost : LookupRealization -> Nat
  | false => 0
  | true => 1

noncomputable def profitabilitySelection
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    RecognizedFamily.CapabilityRequest.ProfitabilitySelection
      (policyRequest projection valid).toCapabilityRequest Nat preferRawCost :=
  Classical.choice
    (Mettapedia.Languages.MeTTa.Prime.NIKProfitabilityFrontierSelection.RecognizedFamily.CapabilityRequest.profitabilitySelection_inhabited
      (policyRequest projection valid).toCapabilityRequest Nat preferRawCost)

/-- Even an adversarial cost that prefers raw scanning must select the
prepared index, because cost is allowed to compare only the semantic maximal
frontier. -/
theorem cheaper_nonmaximal_scan_cannot_be_selected
    (projection : PrefixProjection)
    (valid : prefixProjectionValid projection = true) :
    (profitabilitySelection projection valid).chosen = preparedIndex := by
  let strongest := strongestPolicyLookup projection valid
  let profitable := profitabilitySelection projection valid
  have chosenLePrepared : profitable.chosen ≤ strongest.1 :=
    strongest.2.2 profitable.chosen profitable.semanticMaximal.1
  have preparedLeChosen : strongest.1 ≤ profitable.chosen :=
    profitable.semanticMaximal.2 strongest.2.1 chosenLePrepared
  exact le_antisymm chosenLePrepared preparedLeChosen

/-! ## Exact composition with fused assertion application -/

/-- Maximal record selection and fused substitution compose without being
conflated into one arbitrary global ranking.  The selected operation returns
the exact stored record, and the independently admitted fused semantics is
equivalent to the authored assertion semantics. -/
theorem selected_record_then_fused_application
    (db : RuntimeDB) (projection : PrefixProjection)
    (assertion : AssertionView)
    (projected : projectPrefix? db = some projection)
    (member : assertion ∈ projection.assertions)
    (revision : Nat) (actuals : List ConstantHeadedFormula)
    (result : ConstantHeadedFormula) :
    let valid :=
      prefixProjectionValid_of_projectPrefix?_eq_some db projection projected
    ((activeAt projection valid revision).run [assertion.label]).observations =
        [some assertion] ∧
      (AssertionApplicationSemantics projection.callerFrame assertion actuals
          result ↔
        FusedAssertionApplicationSemantics projection.callerFrame assertion
          actuals result) := by
  intro valid
  constructor
  · rw [(current_lookup_is_prepared_and_exact projection valid revision
        [assertion.label]).2]
    change
      [sourceLookup assertion.label (assertionRecordEntries projection)] =
        [some assertion]
    apply congrArg (fun observation => [observation])
    simpa [assertionRecordEntries] using
      sourceLookup_assertionRecord_of_mem projection.assertions assertion
        (assertionLabels_nodup_of_prefixProjectionValid projection valid) member
  · exact projected_assertionApplicationSemantics_iff_fused db projection
      assertion projected member actuals result

/-! ## Refusing an ambiguous assertion table -/

namespace Examples

open Mettapedia.Languages.Metamath.InferencePreparedAssertionCompilation.Examples

/-- The duplicate-label projection cannot construct the validity evidence
needed by the family, so neither policy nor profitability can mint its native
selection. -/
theorem duplicate_projection_never_reaches_native_selection :
    Not (Exists fun valid :
        prefixProjectionValid duplicateProjection = true =>
      Nonempty ((policyRequest duplicateProjection valid).toCapabilityRequest
        |>.StrongestNativeCalculusPrinciple)) := by
  rintro ⟨valid, _selection⟩
  rw [duplicate_projection_refused] at valid
  contradiction

end Examples

#print axioms current_lookup_is_prepared_and_exact
#print axioms compiled_keyed_lookup_exact
#print axioms ordered_scan_refuses_compiled_keyed_lookup
#print axioms admittedFlowMode_certificateFree
#print axioms current_lookup_accepted_by_admittedFlow
#print axioms changed_revision_refuses_selection_and_preserves_fallback
#print axioms resultOnlyReadout_refuses_fullFamily
#print axioms cheaper_nonmaximal_scan_cannot_be_selected
#print axioms selected_record_then_fused_application
#print axioms Examples.duplicate_projection_never_reaches_native_selection

end Mettapedia.Languages.MeTTa.Prime.NativeTypedMetamathPolicyNIKSelection
