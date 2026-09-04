import Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
import Mettapedia.Languages.Metamath.MM2SourceScopeExecution

/-!
# Source-relative assertion-frame certificates

An assertion candidate is passive data.  Before ordinary MM2 execution may
publish it, the active source ledgers must establish that its variable
certificate names exactly the variables occurring in the conclusion and
active essential hypotheses.  The same certificate then determines the
mandatory hypothesis and distinct-variable projections.

The certificate is intentionally set-like: order is retained by the active
hypothesis and distinct-variable ledgers, while duplicate certificate entries
are rejected.  This is the contract implemented by the subsequent MM2 walker;
it does not use the candidate as its own authorization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Metamath.MM2SourceAssertionFrame

open Mettapedia.Languages.Metamath.InferenceProjection
open Mettapedia.Languages.Metamath.InferenceEncoding
open Mettapedia.Languages.Metamath.MM2SourceAssertionPlan
open Mettapedia.Languages.Metamath.SourceGSLTState
open Mettapedia.Languages.Metamath.SourceInferenceProjection

/-! ## Reverse-ledger snapshot -/

/-- Active source ledgers expose their newest entry first.  Prepending every
visited entry reconstructs the original chronological sequence without
sorting, deduplication, or an auxiliary oracle. -/
def prependReverseSnapshot {Entry : Type}
    (reverseChronological : List Entry) : List Entry :=
  reverseChronological.foldl (fun snapshot entry => entry :: snapshot) []

theorem prependReverseSnapshot_reverse {Entry : Type}
    (chronological : List Entry) :
    prependReverseSnapshot chronological.reverse = chronological := by
  simp [prependReverseSnapshot, List.foldl_reverse]

theorem prependReverseSnapshot_preserves_repeated_occurrences :
    prependReverseSnapshot (["d1", "d2", "d1"] : List String).reverse =
      ["d1", "d2", "d1"] := by
  decide

/-! ## Exact certificate contract -/

/-- An executable assertion-frame walk may use the candidate variable list as
a finite membership index only after proving that it is duplicate-free and
has exactly the source-derived members. -/
def MandatoryVariableCertificate (state : SourceState)
    (formula : ConstantHeadedFormula) (certificate : List String) : Prop :=
  certificate.Nodup /\
    forall variableName,
      variableName ∈ certificate <->
        variableName ∈ mandatoryVariableNames state formula

/-- `eraseDups` really produces a duplicate-free list.  Lean's core list
library exposes membership preservation but not this proposition under a
public theorem name, so the proof is kept local and structural. -/
theorem eraseDups_nodup :
    forall names : List String, names.eraseDups.Nodup
  | [] => by simp
  | name :: names => by
      rw [List.eraseDups_cons]
      apply List.nodup_cons.mpr
      constructor
      · rw [List.mem_eraseDups]
        simp
      · exact eraseDups_nodup
          (names.filter fun candidate => !candidate == name)
termination_by names => names.length
decreasing_by
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- The source-computed variable list is itself an admitted certificate. -/
theorem mandatoryVariableCertificate_source
    (state : SourceState) (formula : ConstantHeadedFormula) :
    MandatoryVariableCertificate state formula
      (mandatoryVariableNames state formula) := by
  constructor
  · unfold mandatoryVariableNames
    exact eraseDups_nodup _
  · intro variableName
    rfl

theorem MandatoryVariableCertificate.membership
    {state : SourceState} {formula : ConstantHeadedFormula}
    {certificate : List String}
    (valid : MandatoryVariableCertificate state formula certificate)
    (variableName : String) :
    certificate.contains variableName =
      (mandatoryVariableNames state formula).contains variableName := by
  apply Bool.eq_iff_iff.mpr
  simpa only [List.contains_iff_mem] using valid.2 variableName

/-! ## Executable occurrence view of the certificate obligation -/

/-- Variable occurrences contributed by active essential hypotheses.  The
list deliberately retains repetition: the MM2 walker checks every occurrence,
while certificate uniqueness is checked in the opposite direction. -/
def essentialVariableOccurrences : List HypothesisView → List String
  | [] => []
  | .floating _ _ _ :: hypotheses =>
      essentialVariableOccurrences hypotheses
  | .essential _ formula :: hypotheses =>
      taggedVariableNames formula.body ++
        essentialVariableOccurrences hypotheses

theorem mem_essentialVariableOccurrences_iff :
    forall {hypotheses : List HypothesisView} {variableName : String},
      variableName ∈ essentialVariableOccurrences hypotheses ↔
        ∃ label formula,
          HypothesisView.essential label formula ∈ hypotheses ∧
            variableName ∈ taggedVariableNames formula.body
  | [], variableName => by
      simp [essentialVariableOccurrences]
  | .floating label typecode floatingVariable :: hypotheses, variableName => by
      simp only [essentialVariableOccurrences]
      rw [mem_essentialVariableOccurrences_iff]
      constructor
      · rintro ⟨essentialLabel, formula, member, variableMember⟩
        exact
          ⟨essentialLabel, formula, List.mem_cons_of_mem _ member,
            variableMember⟩
      · rintro ⟨essentialLabel, formula, member, variableMember⟩
        rcases List.mem_cons.mp member with equal | member
        · cases equal
        · exact ⟨essentialLabel, formula, member, variableMember⟩
  | .essential label formula :: hypotheses, variableName => by
      simp only [essentialVariableOccurrences, List.mem_append]
      rw [mem_essentialVariableOccurrences_iff]
      constructor
      · rintro (variableMember |
          ⟨essentialLabel, essentialFormula, member,
            essentialVariableMember⟩)
        · exact ⟨label, formula, by simp, variableMember⟩
        · exact
            ⟨essentialLabel, essentialFormula,
              List.mem_cons_of_mem _ member, essentialVariableMember⟩
      · rintro ⟨essentialLabel, essentialFormula, member,
          essentialVariableMember⟩
        rcases List.mem_cons.mp member with equal | member
        · obtain ⟨rfl, rfl⟩ :
              essentialLabel = label ∧ essentialFormula = formula := by
            simpa [HypothesisView.essential.injEq] using equal
          exact Or.inl essentialVariableMember
        · exact
            Or.inr
              ⟨essentialLabel, essentialFormula, member,
                essentialVariableMember⟩

/-- Exact occurrence stream walked by the executable certificate checker. -/
def requiredVariableOccurrences (formula : ConstantHeadedFormula)
    (activeHypotheses : List HypothesisView) : List String :=
  taggedVariableNames formula.body ++
    essentialVariableOccurrences activeHypotheses

theorem mem_requiredVariableOccurrences_iff
    {state : SourceState} {formula : ConstantHeadedFormula}
    {variableName : String} :
    variableName ∈
        requiredVariableOccurrences formula state.activeHypotheses ↔
      variableName ∈ mandatoryVariableNames state formula := by
  rw [mem_mandatoryVariableNames_iff]
  simp only [requiredVariableOccurrences, List.mem_append,
    mem_essentialVariableOccurrences_iff]

/-- Executable two-sided finite check.  The first `all` rejects a missing
certificate member; the second rejects an extra member; `decide Nodup`
rejects repeated certificate entries. -/
def certificateChecksOccurrences (certificate occurrences : List String) :
    Bool :=
  decide certificate.Nodup &&
    occurrences.all certificate.contains &&
      certificate.all occurrences.contains

theorem certificateChecksOccurrences_eq_true_iff
    (certificate occurrences : List String) :
    certificateChecksOccurrences certificate occurrences = true ↔
      certificate.Nodup ∧
        (∀ variableName,
          variableName ∈ certificate ↔ variableName ∈ occurrences) := by
  simp only [certificateChecksOccurrences, Bool.and_eq_true,
    decide_eq_true_eq, List.all_eq_true, List.contains_iff_mem]
  constructor
  · rintro ⟨⟨nodup, occurrenceCovered⟩, certificateCovered⟩
    refine ⟨nodup, ?_⟩
    intro variableName
    constructor
    · intro member
      exact certificateCovered variableName member
    · intro member
      exact occurrenceCovered variableName member
  · rintro ⟨nodup, exactMembership⟩
    refine ⟨⟨nodup, ?_⟩, ?_⟩
    · intro variableName member
      exact (exactMembership variableName).mpr member
    · intro variableName member
      exact (exactMembership variableName).mp member

/-- The finite occurrence check is exactly the source-state certificate
contract, not an approximation to it. -/
theorem certificateChecksRequiredOccurrences_iff
    (state : SourceState) (formula : ConstantHeadedFormula)
    (certificate : List String) :
    certificateChecksOccurrences certificate
        (requiredVariableOccurrences formula state.activeHypotheses) = true ↔
      MandatoryVariableCertificate state formula certificate := by
  rw [certificateChecksOccurrences_eq_true_iff]
  constructor
  · rintro ⟨nodup, exactMembership⟩
    refine ⟨nodup, ?_⟩
    intro variableName
    rw [← mem_requiredVariableOccurrences_iff]
    exact exactMembership variableName
  · rintro ⟨nodup, exactMembership⟩
    refine ⟨nodup, ?_⟩
    intro variableName
    rw [mem_requiredVariableOccurrences_iff]
    exact exactMembership variableName

/-! ## Frame reconstructed from a checked certificate -/

/-- Select mandatory hypotheses from the active ledger using only a checked
variable-membership certificate.  Active-ledger order and multiplicity are
therefore preserved by construction. -/
def mandatoryHypothesesFromCertificate (state : SourceState)
    (certificate : List String) : List HypothesisView :=
  state.activeHypotheses.filter fun hypothesis =>
    match hypothesis with
    | .floating _ _ variableName => certificate.contains variableName
    | .essential _ _ => true

/-- Select mandatory disjoint-variable occurrences in active-ledger order.
Repeated source occurrences remain repeated; the certificate changes only the
membership decision. -/
def mandatoryDistinctVariablesFromCertificate (state : SourceState)
    (certificate : List String) : List (String × String) :=
  state.activeDistinctVariables.filter fun pair =>
    certificate.contains pair.1 && certificate.contains pair.2

def mandatoryFrameFromCertificate (state : SourceState)
    (certificate : List String) : SourceFrame :=
  let hypotheses := mandatoryHypothesesFromCertificate state certificate
  { distinctVariables :=
      mandatoryDistinctVariablesFromCertificate state certificate
    hypothesisLabels := hypotheses.map HypothesisView.label }

def sourceAssertionFromCertificate (state : SourceState) (label : String)
    (formula : ConstantHeadedFormula) (certificate : List String) :
    SourceAssertion :=
  { label
    formula
    frame := mandatoryFrameFromCertificate state certificate
    hypotheses := mandatoryHypothesesFromCertificate state certificate }

theorem mandatoryHypothesesFromCertificate_eq
    {state : SourceState} {formula : ConstantHeadedFormula}
    {certificate : List String}
    (valid : MandatoryVariableCertificate state formula certificate) :
    mandatoryHypothesesFromCertificate state certificate =
      mandatoryHypotheses state formula := by
  rw [mandatoryHypotheses_eq_filter]
  apply List.filter_congr
  intro hypothesis member
  cases hypothesis with
  | floating label typecode variableName =>
      exact valid.membership variableName
  | essential label hypothesisFormula => rfl

theorem mandatoryDistinctVariablesFromCertificate_eq
    {state : SourceState} {formula : ConstantHeadedFormula}
    {certificate : List String}
    (valid : MandatoryVariableCertificate state formula certificate) :
    mandatoryDistinctVariablesFromCertificate state certificate =
      (mandatoryFrame state formula).distinctVariables := by
  unfold mandatoryDistinctVariablesFromCertificate mandatoryFrame
  apply List.filter_congr
  intro pair member
  rw [valid.membership pair.1, valid.membership pair.2]

theorem mandatoryFrameFromCertificate_eq
    {state : SourceState} {formula : ConstantHeadedFormula}
    {certificate : List String}
    (valid : MandatoryVariableCertificate state formula certificate) :
    mandatoryFrameFromCertificate state certificate =
      mandatoryFrame state formula := by
  have hypotheses_eq := mandatoryHypothesesFromCertificate_eq valid
  have distinct_eq :
      mandatoryDistinctVariablesFromCertificate state certificate =
        state.activeDistinctVariables.filter fun pair =>
          (mandatoryVariableNames state formula).contains pair.1 &&
            (mandatoryVariableNames state formula).contains pair.2 := by
    unfold mandatoryDistinctVariablesFromCertificate
    apply List.filter_congr
    intro pair member
    rw [valid.membership pair.1, valid.membership pair.2]
  unfold mandatoryFrameFromCertificate mandatoryFrame
  rw [hypotheses_eq, distinct_eq]

/-- The central frame-reconstruction theorem.  A duplicate-free certificate
with exactly the mandatory variable members reconstructs the complete source
assertion, including ordered hypotheses and repeated `$d` occurrences. -/
theorem sourceAssertionFromCertificate_eq
    {state : SourceState} {label : String}
    {formula : ConstantHeadedFormula} {certificate : List String}
    (valid : MandatoryVariableCertificate state formula certificate) :
    sourceAssertionFromCertificate state label formula certificate =
      sourceAssertion state label formula := by
  unfold sourceAssertionFromCertificate sourceAssertion
  rw [mandatoryFrameFromCertificate_eq valid]
  rw [mandatoryHypothesesFromCertificate_eq valid]

/-! ## Snapshot-local executable frame comparison -/

/-- Reconstruct the only part of source state needed by assertion-frame
selection.  Formula/label provenance is checked by the preceding source
transaction; this state contains exactly the two active ledgers consumed by
the selection walk. -/
def sourceStateFromAssertionSnapshot
    (activeHypotheses : List HypothesisView)
    (activeDistinctVariables : List (String × String)) : SourceState :=
  { initialState with activeHypotheses, activeDistinctVariables }

/-- Candidate frame equality as a finite executable check.  The candidate's
formula and label are not used as authorities: the preceding raw-statement
transaction has already forced those fields to the checked source formula
and label. -/
def assertionFrameChecksSnapshot (certificate : List String)
    (activeHypotheses : List HypothesisView)
    (activeDistinctVariables : List (String × String))
    (candidate : SourceAssertion) : Bool :=
  let snapshotState :=
    sourceStateFromAssertionSnapshot activeHypotheses
      activeDistinctVariables
  candidate.hypotheses ==
      mandatoryHypothesesFromCertificate snapshotState certificate &&
    candidate.frame ==
      mandatoryFrameFromCertificate snapshotState certificate

theorem assertionFrameChecksSnapshot_eq_true_iff
    (certificate : List String)
    (activeHypotheses : List HypothesisView)
    (activeDistinctVariables : List (String × String))
    (candidate : SourceAssertion) :
    assertionFrameChecksSnapshot certificate activeHypotheses
        activeDistinctVariables candidate = true ↔
      candidate =
        sourceAssertionFromCertificate
          (sourceStateFromAssertionSnapshot activeHypotheses
            activeDistinctVariables)
          candidate.label candidate.formula certificate := by
  simp only [assertionFrameChecksSnapshot, Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨hypotheses_eq, frame_eq⟩
    cases candidate with
    | mk label formula frame hypotheses =>
        cases hypotheses_eq
        cases frame_eq
        rfl
  · intro candidate_eq
    rw [candidate_eq]
    constructor <;> rfl

/-- Once the occurrence certificate and the two snapshot lists are exact,
the finite comparison admits precisely the source assertion. -/
theorem assertionFrameChecksSnapshot_source_iff
    (state : SourceState) (formula : ConstantHeadedFormula)
    (label : String) (certificate : List String)
    (certificateValid :
      MandatoryVariableCertificate state formula certificate)
    (candidate : SourceAssertion)
    (labelExact : candidate.label = label)
    (formulaExact : candidate.formula = formula) :
    assertionFrameChecksSnapshot certificate state.activeHypotheses
        state.activeDistinctVariables candidate = true ↔
      candidate = sourceAssertion state label formula := by
  rw [assertionFrameChecksSnapshot_eq_true_iff]
  subst label
  subst formula
  have snapshotCertificate :
      MandatoryVariableCertificate
        (sourceStateFromAssertionSnapshot state.activeHypotheses
          state.activeDistinctVariables)
        candidate.formula certificate := by
    constructor
    · exact certificateValid.1
    · intro variableName
      have membership := certificateValid.2 variableName
      simpa [mandatoryVariableNames, sourceStateFromAssertionSnapshot] using
        membership
  rw [sourceAssertionFromCertificate_eq snapshotCertificate]
  have source_eq :
      sourceAssertion
          (sourceStateFromAssertionSnapshot state.activeHypotheses
            state.activeDistinctVariables)
          candidate.label candidate.formula =
        sourceAssertion state candidate.label candidate.formula := by
    simp [sourceAssertion, mandatoryFrame, mandatoryHypotheses,
      mandatoryVariableNames, sourceStateFromAssertionSnapshot]
  rw [source_eq]

/-! ## Positive and adversarial controls -/

private def fixtureFormula : ConstantHeadedFormula :=
  { typecode := "wff"
    body := [.var "x", .const "imp", .var "x", .var "y"] }

private def fixtureState : SourceState :=
  { initialState with
    activeHypotheses :=
      [.floating "vx" "setvar" "x",
       .floating "vz" "setvar" "z",
       .essential "e1"
         { typecode := "wff", body := [.var "y", .var "x"] }]
    activeDistinctVariables := [("x", "y"), ("x", "z"), ("x", "y")] }

theorem fixture_mandatory_variables_exact :
    mandatoryVariableNames fixtureState fixtureFormula = ["x", "y"] := by
  decide

theorem fixture_certificate_reconstructs_assertion :
    sourceAssertionFromCertificate fixtureState "ax" fixtureFormula
        ["y", "x"] =
      sourceAssertion fixtureState "ax" fixtureFormula := by
  apply sourceAssertionFromCertificate_eq
  constructor
  · decide
  · intro variableName
    rw [fixture_mandatory_variables_exact]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    aesop

theorem fixture_snapshot_check_accepts_exact_assertion :
    assertionFrameChecksSnapshot ["y", "x"]
        fixtureState.activeHypotheses fixtureState.activeDistinctVariables
        (sourceAssertion fixtureState "ax" fixtureFormula) = true := by
  decide

theorem fixture_snapshot_check_rejects_missing_hypothesis :
    assertionFrameChecksSnapshot ["y", "x"]
        fixtureState.activeHypotheses fixtureState.activeDistinctVariables
        { sourceAssertion fixtureState "ax" fixtureFormula with
          hypotheses := [] } = false := by
  decide

theorem fixture_snapshot_check_rejects_dropped_dv_occurrence :
    assertionFrameChecksSnapshot ["y", "x"]
        fixtureState.activeHypotheses fixtureState.activeDistinctVariables
        { sourceAssertion fixtureState "ax" fixtureFormula with
          frame :=
            { (sourceAssertion fixtureState "ax" fixtureFormula).frame with
              distinctVariables := [("x", "y")] } } = false := by
  decide

/-- Missing one variable prevents certificate admission. -/
theorem fixture_missing_variable_rejected :
    Not (MandatoryVariableCertificate fixtureState fixtureFormula ["x"]) := by
  intro valid
  have exactMembership := valid.2 "y"
  rw [fixture_mandatory_variables_exact] at exactMembership
  simp at exactMembership

/-- An extra variable prevents certificate admission. -/
theorem fixture_extra_variable_rejected :
    Not (MandatoryVariableCertificate fixtureState fixtureFormula
      ["x", "y", "ghost"]) := by
  intro valid
  have exactMembership := valid.2 "ghost"
  rw [fixture_mandatory_variables_exact] at exactMembership
  simp at exactMembership

/-- Duplicate names are rejected even though they denote the same finite set.
This prevents an executable lookup index from acquiring ambiguous entries. -/
theorem fixture_duplicate_variable_rejected :
    Not (MandatoryVariableCertificate fixtureState fixtureFormula
      ["x", "y", "x"]) := by
  intro valid
  simp [MandatoryVariableCertificate] at valid

#print axioms eraseDups_nodup
#print axioms prependReverseSnapshot_reverse
#print axioms prependReverseSnapshot_preserves_repeated_occurrences
#print axioms mandatoryVariableCertificate_source
#print axioms MandatoryVariableCertificate.membership
#print axioms mem_essentialVariableOccurrences_iff
#print axioms mem_requiredVariableOccurrences_iff
#print axioms certificateChecksOccurrences_eq_true_iff
#print axioms certificateChecksRequiredOccurrences_iff
#print axioms mandatoryHypothesesFromCertificate_eq
#print axioms mandatoryDistinctVariablesFromCertificate_eq
#print axioms mandatoryFrameFromCertificate_eq
#print axioms sourceAssertionFromCertificate_eq
#print axioms assertionFrameChecksSnapshot_eq_true_iff
#print axioms assertionFrameChecksSnapshot_source_iff
#print axioms fixture_mandatory_variables_exact
#print axioms fixture_certificate_reconstructs_assertion
#print axioms fixture_snapshot_check_accepts_exact_assertion
#print axioms fixture_snapshot_check_rejects_missing_hypothesis
#print axioms fixture_snapshot_check_rejects_dropped_dv_occurrence
#print axioms fixture_missing_variable_rejected
#print axioms fixture_extra_variable_rejected
#print axioms fixture_duplicate_variable_rejected

end Mettapedia.Languages.Metamath.MM2SourceAssertionFrame
