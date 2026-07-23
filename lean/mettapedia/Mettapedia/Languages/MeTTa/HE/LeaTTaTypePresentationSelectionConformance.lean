import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Selection
import Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationCompleteness

/-!
# Exact conformance of one ordered runtime type-candidate scan

The presentation selection relation deliberately starts after type lookup and
freshening.  This module seals the corresponding repaired-LeaTTa list scan on
those already-prepared candidates.  Environment- and state-dependent
preparation remains outside this boundary.

The load-bearing negative interface is an exact characterization of
`matchType = none`: on disjoint fresh scopes, runtime failure is equivalent to
the absence of every core-plus-R2 finite-presentation derivation.  Ordered
selection can therefore retain exact negative evidence without unfolding the
matcher at each scan site.
-/

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationSelectionConformance

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Theory
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.Selection
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Freshness
open Spec.Type.RuntimeRefinement
open LeaTTaBridge
open LeaTTaSpecConformance
open LeaTTaTypeConformance
open LeaTTaTypePresentationFoldConformance
open LeaTTaTypePresentationCompleteness

/-- A complete finite-presentation derivation supplies the translated runtime
valuation state needed by matcher completeness.  The valuation is the
derivation output's own presented model, so no external model choice enters
the negative scan boundary. -/
private theorem runtimeValuationState_of_presentation
    {incoming output : TypeSubst} {spec : Bindings}
    {lea : Metta.Bindings} {expected actual : Atom}
    (state : TypePresentationSimulationState incoming spec lea)
    (derivation : CorePlusR2TypePresentationMatchRel
      incoming expected actual output) :
    RuntimeValuationState (presentedValuation output) lea := by
  have outputNormal : output.Normal :=
    derivation.output_normal state.normal
  have outputSatisfied :
      TypeSubstSatisfied (presentedValuation output) output :=
    normal_presentedValuation_satisfied outputNormal
  have incomingSatisfied :
      TypeSubstSatisfied (presentedValuation output) incoming :=
    (Spec.Type.Presentation.MatchSolutionTheory.CorePlusR2TypePresentationMatchRel.solutions
      derivation state.normal (presentedValuation output)).mp
        outputSatisfied |>.1
  have specSatisfied :
      TypeBindingSatisfied (presentedValuation output) spec :=
    (state.specSolutions (presentedValuation output)).mp incomingSatisfied
  have heSatisfied :
      HEBindingSatisfied
        (fun name => toLeaTTaAtom (presentedValuation output name)) spec :=
    heBindingSatisfied_of_specTypeBindingSatisfied specSatisfied
  exact
    { satisfied := (state.semantic.theory _).mp heSatisfied
      runtime := state.semantic.runtime }

/-- On fresh disjoint type scopes, repaired-LeaTTa failure is exactly the
absence of every finite-presentation match.  This is the negative boundary
consumed by ordered candidate selection. -/
theorem matchType_eq_none_iff_no_presentation
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (expected actual : Atom) (disjoint : VarsDisjoint expected actual) :
    Metta.Minimal.matchType lea
        (toLeaTTaAtom expected) (toLeaTTaAtom actual) = none ↔
      ∀ output,
        ¬CorePlusR2TypePresentationMatchRel
          incoming expected actual output := by
  constructor
  · intro runtimeFailure output derivation
    have outputNormal : output.Normal :=
      derivation.output_normal state.normal
    have outputSatisfied :
        TypeSubstSatisfied (presentedValuation output) output :=
      normal_presentedValuation_satisfied outputNormal
    obtain ⟨runtimeOutput, runtimeSuccess, _⟩ :=
      matchType_complete (presentedValuation output) state.normal
        outputSatisfied derivation
        (runtimeValuationState_of_presentation state derivation) disjoint
    rw [runtimeFailure] at runtimeSuccess
    contradiction
  · intro noPresentation
    cases runtimeEquation : Metta.Minimal.matchType lea
        (toLeaTTaAtom expected) (toLeaTTaAtom actual) with
    | none => rfl
    | some runtimeOutput =>
        obtain ⟨presentationOutput, _specOutput, derivation, _outputState⟩ :=
          state.matchType expected actual runtimeEquation
        exact False.elim (noPresentation presentationOutput derivation)

/-- One repaired runtime candidate is classified exactly by the independent
presentation relation.  Successful classifications retain the complete
simulation state; failed classifications retain the exact universal
negative. -/
inductive ActualTypeCandidateRuntimeRel
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (expected candidate : Atom) :
    ActualTypeCandidateClassification → Prop where
  | matched {presentationOutput : TypeSubst} {specOutput : Bindings}
      {leaOutput : Metta.Bindings} :
      Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) = some leaOutput →
      CorePlusR2TypePresentationMatchRel
          incoming expected candidate presentationOutput →
      TypePresentationSimulationState
          presentationOutput specOutput leaOutput →
      ActualTypeCandidateRuntimeRel state expected candidate
        (.matched presentationOutput)
  | failed :
      Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) = none →
      (∀ output,
        ¬CorePlusR2TypePresentationMatchRel
          incoming expected candidate output) →
      ActualTypeCandidateRuntimeRel state expected candidate .failed

/-- Every already-freshened candidate list has a pointwise exact
classification.  Runtime failure order is exactly the order selected by
`failedActualTypes`. -/
theorem classify_actual_type_candidates
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (expected : Atom) :
    ∀ candidates : List Atom,
      (∀ candidate ∈ candidates, VarsDisjoint expected candidate) →
      ∃ classifications,
        List.Forall₂
          (ActualTypeCandidateRuntimeRel state expected)
          candidates classifications ∧
        (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
            (toLeaTTaAtoms candidates)).failures =
          toLeaTTaAtoms (failedActualTypes candidates classifications) := by
  intro candidates
  induction candidates with
  | nil =>
      intro _
      exact ⟨[], .nil, rfl⟩
  | cons candidate candidates inductionHypothesis =>
      intro disjoint
      obtain ⟨classifications, tailClassifications, tailFailures⟩ :=
        inductionHypothesis (fun item member =>
          disjoint item (by simp [member]))
      cases runtimeEquation : Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
      | none =>
          have noPresentation :=
            (matchType_eq_none_iff_no_presentation state expected candidate
              (disjoint candidate (by simp))).mp runtimeEquation
          refine ⟨.failed :: classifications,
            .cons (.failed runtimeEquation noPresentation)
              tailClassifications, ?_⟩
          simp only [toLeaTTaAtoms, Metta.Minimal.scanActualTypes,
            runtimeEquation, failedActualTypes]
          rw [tailFailures]
      | some leaOutput =>
          obtain ⟨presentationOutput, specOutput, presentationMatch,
              outputState⟩ :=
            state.matchType expected candidate runtimeEquation
          refine ⟨.matched presentationOutput :: classifications,
            .cons (.matched runtimeEquation presentationMatch outputState)
              tailClassifications, ?_⟩
          simp only [toLeaTTaAtoms, Metta.Minimal.scanActualTypes,
            runtimeEquation, failedActualTypes]
          exact tailFailures

/-- Pointwise exact simulation states for an ordered list of successful
private type presentations. -/
def TypePresentationSimulationStates
    (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (fun presentation lea =>
      ∃ spec, TypePresentationSimulationState presentation spec lea)
    presentations runtimeBindings

/-- One spec expected-return mismatch and one repaired runtime mismatch have
the same expected type and alpha-equivalent private return presentation. -/
inductive ExpectedReturnDiagnosticRuntimeRel :
    ExpectedReturnDiagnostic → Metta.Minimal.ExpectedFunctionTypeError → Prop where
  | badReturn {expected actual : Atom} {runtimeActual : Metta.Atom} :
      ObservedTypeAlphaRel actual (fromLeaTTaAtom runtimeActual) →
      ExpectedReturnDiagnosticRuntimeRel
        ⟨expected, actual⟩
        (.badReturn (toLeaTTaAtom expected) runtimeActual)

/-- Exact correspondence for the selected private presentation and complete
ordered expected-return mismatch ledger. -/
structure ExpectedReturnBranchOutcomeRuntimeRel
    (specOutcome : ExpectedReturnBranchOutcome)
    (runtimeOutcome : Metta.Minimal.ExpectedReturnBranchScanResult) : Prop where
  selected : Option.Rel
    (fun presentation lea =>
      ∃ spec, TypePresentationSimulationState presentation spec lea)
    specOutcome.selected runtimeOutcome.selected
  errors : List.Forall₂ ExpectedReturnDiagnosticRuntimeRel
    specOutcome.errors runtimeOutcome.errors

/-- Successful runtime branches retain both their exact simulation state and
the candidate match that produced the presentation. -/
def TypePresentationCandidateBranchStates
    (incoming : TypeSubst) (expected : Atom) (candidates : List Atom)
    (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (fun presentation lea =>
      ∃ candidate ∈ candidates,
        CorePlusR2TypePresentationMatchRel incoming expected candidate
            presentation ∧
          ∃ spec,
            TypePresentationSimulationState presentation spec lea)
    presentations runtimeBindings

/-- The branch-valued runtime scan classifies every candidate exactly.  Both
successful private presentations and failed candidates retain declaration
order. -/
theorem scanActualTypeBranches_presentation_exact
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (expected : Atom) :
    ∀ candidates : List Atom,
      (∀ candidate ∈ candidates, VarsDisjoint expected candidate) →
      ∃ presentations failedActuals,
        ActualTypeCandidateBranchesRel incoming expected candidates
          presentations failedActuals ∧
        TypePresentationCandidateBranchStates incoming expected candidates
          presentations
          (Metta.Minimal.scanActualTypeBranches lea
            (toLeaTTaAtom expected)
            (toLeaTTaAtoms candidates)).successes ∧
        (Metta.Minimal.scanActualTypeBranches lea
            (toLeaTTaAtom expected)
            (toLeaTTaAtoms candidates)).failures =
          toLeaTTaAtoms failedActuals := by
  intro candidates
  induction candidates with
  | nil =>
      intro _
      exact ⟨[], [], .nil, .nil, rfl⟩
  | cons candidate candidates inductionHypothesis =>
      intro disjoint
      obtain ⟨presentations, failedActuals, tailRel, tailStates,
          tailFailures⟩ :=
        inductionHypothesis (fun item member =>
          disjoint item (by simp [member]))
      cases runtimeEquation : Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
      | none =>
          have noPresentation :=
            (matchType_eq_none_iff_no_presentation state expected candidate
              (disjoint candidate (by simp))).mp runtimeEquation
          refine ⟨presentations, candidate :: failedActuals,
            .failed noPresentation tailRel, ?_, ?_⟩
          · have tailStates' : TypePresentationCandidateBranchStates
                incoming expected (candidate :: candidates)
                presentations
                (Metta.Minimal.scanActualTypeBranches lea
                  (toLeaTTaAtom expected)
                  (toLeaTTaAtoms candidates)).successes :=
              tailStates.imp fun presentation runtimeBinding evidence => by
                obtain ⟨source, member, matched, specOutput, outputState⟩ :=
                  evidence
                exact ⟨source, List.mem_cons_of_mem candidate member, matched,
                  specOutput, outputState⟩
            simpa [Metta.Minimal.scanActualTypeBranches,
              runtimeEquation] using tailStates'
          · simp only [toLeaTTaAtoms,
              Metta.Minimal.scanActualTypeBranches, runtimeEquation]
            rw [tailFailures]
      | some leaOutput =>
          obtain ⟨presentationOutput, specOutput, presentationMatch,
              outputState⟩ :=
            state.matchType expected candidate runtimeEquation
          refine ⟨presentationOutput :: presentations, failedActuals,
            .matched presentationMatch tailRel, ?_, ?_⟩
          · have tailStates' : TypePresentationCandidateBranchStates
                incoming expected (candidate :: candidates)
                presentations
                (Metta.Minimal.scanActualTypeBranches lea
                  (toLeaTTaAtom expected)
                  (toLeaTTaAtoms candidates)).successes :=
              tailStates.imp fun presentation runtimeBinding evidence => by
                obtain ⟨source, member, matched, specTail, tailState⟩ :=
                  evidence
                exact ⟨source, List.mem_cons_of_mem candidate member, matched,
                  specTail, tailState⟩
            simpa [TypePresentationCandidateBranchStates,
              Metta.Minimal.scanActualTypeBranches, runtimeEquation] using
              (List.Forall₂.cons
                ⟨candidate, by simp, presentationMatch,
                  specOutput, outputState⟩ tailStates')
          · simpa [Metta.Minimal.scanActualTypeBranches, runtimeEquation]
              using tailFailures

/-- The repaired expected-return worker is exact over a list of already
reconstructed private argument presentations.  It selects the first branch
whose raw declared return satisfies the expected type and retains every
earlier mismatch in branch order. -/
theorem scanExpectedReturnBranches_presentation_exact
    (expected returnType : Atom)
    (disjoint : VarsDisjoint expected returnType) :
    ∀ {presentations : List TypeSubst}
      {runtimeBindings : List Metta.Bindings},
      TypePresentationSimulationStates presentations runtimeBindings →
      ∃ specOutcome,
        ExpectedReturnBranchScanRel expected returnType presentations
            specOutcome ∧
          ExpectedReturnBranchOutcomeRuntimeRel specOutcome
            (Metta.Minimal.scanExpectedReturnBranches
              (toLeaTTaAtom expected) (toLeaTTaAtom returnType)
              runtimeBindings) := by
  intro presentations runtimeBindings states
  induction states with
  | nil =>
      exact ⟨⟨none, []⟩, .nil,
        { selected := .none
          errors := .nil }⟩
  | @cons presentation lea presentations runtimeBindings head tail ih =>
      obtain ⟨spec, state⟩ := head
      cases runtimeEquation : Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom returnType) with
      | some leaOutput =>
          obtain ⟨presentationOutput, specOutput, matched, outputState⟩ :=
            state.matchType expected returnType runtimeEquation
          refine ⟨⟨some presentationOutput, []⟩,
            .matched matched, ?_⟩
          simp only [Metta.Minimal.scanExpectedReturnBranches,
            runtimeEquation]
          exact
            { selected := .some ⟨specOutput, outputState⟩
              errors := .nil }
      | none =>
          have noPresentation :=
            (matchType_eq_none_iff_no_presentation state expected returnType
              disjoint).mp runtimeEquation
          obtain ⟨tailOutcome, tailScan, tailCorrespondence⟩ := ih
          let specOutcome : ExpectedReturnBranchOutcome :=
            ⟨tailOutcome.selected,
              { expected := expected
                actual := presentation.apply returnType } ::
                tailOutcome.errors⟩
          refine ⟨specOutcome,
            ExpectedReturnBranchScanRel.failed noPresentation tailScan, ?_⟩
          simp only [Metta.Minimal.scanExpectedReturnBranches,
            runtimeEquation]
          exact
            { selected := tailCorrespondence.selected
              errors := .cons (.badReturn (state.returnAlpha returnType))
                tailCorrespondence.errors }

/-- Forget the runtime witnesses from a pointwise exact classification. -/
private theorem runtime_classifications_to_presentation
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    {state : TypePresentationSimulationState incoming spec lea}
    {expected : Atom} :
    ∀ {candidates classifications},
      List.Forall₂
        (ActualTypeCandidateRuntimeRel state expected)
        candidates classifications →
      List.Forall₂
        (ActualTypeCandidateClassificationRel incoming expected)
        candidates classifications
  | _, _, .nil => .nil
  | _, _, .cons head tail => by
      apply List.Forall₂.cons
      · cases head with
        | matched _ presentationMatch _ =>
            exact .matched presentationMatch
        | failed _ noPresentation =>
            exact .failed noPresentation
      · exact runtime_classifications_to_presentation tail

/-- If the repaired runtime selects one candidate, the independent relation
selects the same first successful position, retains every other failed actual
in order, and relates the selected private binding state exactly. -/
theorem scanActualTypes_selected_presentation_exact
    {incoming : TypeSubst} {spec : Bindings} {lea leaOutput : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (expected : Atom) :
    ∀ candidates : List Atom,
      (∀ candidate ∈ candidates, VarsDisjoint expected candidate) →
      (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
        (toLeaTTaAtoms candidates)).selected = some leaOutput →
      ∃ presentationOutput specOutput failedActuals,
        ActualTypeCandidateScanRel incoming expected candidates
          (.success presentationOutput failedActuals) ∧
        (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
          (toLeaTTaAtoms candidates)).failures =
            toLeaTTaAtoms failedActuals ∧
        TypePresentationSimulationState
          presentationOutput specOutput leaOutput := by
  intro candidates
  induction candidates with
  | nil =>
      intro _ selected
      simp [Metta.Minimal.scanActualTypes, toLeaTTaAtoms] at selected
  | cons candidate candidates inductionHypothesis =>
      intro disjoint selected
      cases runtimeEquation : Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
      | none =>
          have tailSelected :
              (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
                (toLeaTTaAtoms candidates)).selected = some leaOutput := by
            simpa [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
              runtimeEquation] using selected
          obtain ⟨presentationOutput, specOutput, failedActuals,
              tailScan, tailFailures, outputState⟩ :=
            inductionHypothesis
              (fun item member => disjoint item (by simp [member]))
              tailSelected
          have candidateFailure :=
            (matchType_eq_none_iff_no_presentation state expected candidate
              (disjoint candidate (by simp))).mp runtimeEquation
          cases tailScan with
          | firstSuccess beforeFailures selectedMatch suffixRel =>
              rename_i before selectedCandidate suffix suffixClassifications
              refine ⟨presentationOutput, specOutput,
                candidate ::
                  (before ++ failedActualTypes suffix suffixClassifications),
                ?_, ?_, outputState⟩
              · simpa [List.cons_append] using
                  (ActualTypeCandidateScanRel.firstSuccess
                    (incoming := incoming) (expected := expected)
                    (before := candidate :: before)
                    (candidate := selectedCandidate) (suffix := suffix)
                    (suffixClassifications := suffixClassifications)
                    (output := presentationOutput)
                    (by
                      intro earlier member candidateOutput
                      rcases List.mem_cons.mp member with rfl | member
                      · exact candidateFailure candidateOutput
                      · exact beforeFailures earlier member candidateOutput)
                    selectedMatch suffixRel)
              · simpa [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
                  runtimeEquation] using congrArg (List.cons (toLeaTTaAtom candidate))
                    tailFailures
      | some selectedOutput =>
          have selectedOutputEq : selectedOutput = leaOutput := by
            simpa [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
              runtimeEquation] using selected
          subst selectedOutput
          obtain ⟨presentationOutput, specOutput, presentationMatch,
              outputState⟩ :=
            state.matchType expected candidate runtimeEquation
          obtain ⟨classifications, runtimeClassifications, tailFailures⟩ :=
            classify_actual_type_candidates state expected candidates
              (fun item member => disjoint item (by simp [member]))
          have presentationClassifications :=
            runtime_classifications_to_presentation runtimeClassifications
          refine ⟨presentationOutput, specOutput,
            failedActualTypes candidates classifications, ?_, ?_, outputState⟩
          · exact ActualTypeCandidateScanRel.firstSuccess
              (before := []) (candidate := candidate) (suffix := candidates)
              (suffixClassifications := classifications)
              (output := presentationOutput)
              (by simp) presentationMatch presentationClassifications
          · simpa [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
              runtimeEquation] using tailFailures

/-- A runtime scan with no selected candidate failed on every candidate, and
its failure projection is exactly the input list in declaration order. -/
private theorem scanActualTypes_selected_none_all_failed
    (lea : Metta.Bindings) (expected : Atom) :
    ∀ candidates : List Atom,
      (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
        (toLeaTTaAtoms candidates)).selected = none →
      (∀ candidate ∈ candidates,
        Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) = none) ∧
      (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
        (toLeaTTaAtoms candidates)).failures = toLeaTTaAtoms candidates := by
  intro candidates
  induction candidates with
  | nil =>
      intro _
      exact ⟨by simp, rfl⟩
  | cons candidate candidates inductionHypothesis =>
      intro selected
      cases runtimeEquation : Metta.Minimal.matchType lea
          (toLeaTTaAtom expected) (toLeaTTaAtom candidate) with
      | some output =>
          simp [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
            runtimeEquation] at selected
      | none =>
          have tailSelected :
              (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
                (toLeaTTaAtoms candidates)).selected = none := by
            simpa [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
              runtimeEquation] using selected
          obtain ⟨tailFailed, tailFailures⟩ :=
            inductionHypothesis tailSelected
          constructor
          · intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact runtimeEquation
            · exact tailFailed item member
          · simpa [Metta.Minimal.scanActualTypes, toLeaTTaAtoms,
              runtimeEquation] using
                congrArg (List.cons (toLeaTTaAtom candidate)) tailFailures

/-- If the repaired runtime selects no candidate, the independent relation
has the exact all-failed derivation.  The empty runtime scan has no concrete
failure member, while the spec relation deliberately supplies its published
`%Undefined%` diagnostic sentinel. -/
theorem scanActualTypes_failure_presentation_exact
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (expected : Atom) (candidates : List Atom)
    (disjoint : ∀ candidate ∈ candidates, VarsDisjoint expected candidate)
    (selected :
      (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
        (toLeaTTaAtoms candidates)).selected = none) :
    (candidates = [] ∧
        ActualTypeCandidateScanRel incoming expected []
          (.failure [Atom.undefinedType]) ∧
        (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
          (toLeaTTaAtoms candidates)).failures = []) ∨
      (candidates ≠ [] ∧
        ActualTypeCandidateScanRel incoming expected candidates
          (.failure candidates) ∧
        (Metta.Minimal.scanActualTypes lea (toLeaTTaAtom expected)
          (toLeaTTaAtoms candidates)).failures = toLeaTTaAtoms candidates) := by
  obtain ⟨allRuntimeFailed, runtimeFailures⟩ :=
    scanActualTypes_selected_none_all_failed lea expected candidates selected
  cases candidates with
  | nil =>
      exact Or.inl ⟨rfl, .empty, runtimeFailures⟩
  | cons first rest =>
      apply Or.inr
      refine ⟨by simp, ?_, runtimeFailures⟩
      apply ActualTypeCandidateScanRel.allFailed
      intro candidate member candidateOutput
      have runtimeFailure := allRuntimeFailed candidate member
      exact (matchType_eq_none_iff_no_presentation state expected candidate
        (disjoint candidate member)).mp runtimeFailure candidateOutput

/-! ## Prepared argument-candidate boundary -/

/-- A complete ordered family of runtime argument candidates and its native
presentation.  This is the static preparation seam used by the recursive
argument scan: every candidate avoids the complete formal scope and the
initial presentation, while different argument positions have disjoint
private variable families.

Candidates within one position are alternatives and may share private
variables.  Candidate families at distinct positions are conjoined along a
selected branch, so those families must be disjoint. -/
structure PreparedArgumentCandidateLists
    (formals : List Atom) (initial : TypeSubst)
    (native : List (List Atom))
    (runtime : List (List Metta.Atom)) : Prop where
  link : native.map toLeaTTaAtoms = runtime
  avoidFormals : AtomsAvoid native.flatten
    (TypeSubst.typeVarsList formals)
  avoidInitial : initial.Avoids
    (TypeSubst.typeVarsList native.flatten)
  families : native.Pairwise FreshFamiliesSeparated

/-- Every candidate in a prepared family is structurally disjoint from every
formal type in the same scan. -/
theorem PreparedArgumentCandidateLists.formal_candidate_disjoint
    {formals : List Atom} {initial : TypeSubst}
    {native : List (List Atom)} {runtime : List (List Metta.Atom)}
    (prepared : PreparedArgumentCandidateLists
      formals initial native runtime)
    {formal candidate : Atom} {family : List Atom}
    (formalMember : formal ∈ formals)
    (familyMember : family ∈ native)
    (candidateMember : candidate ∈ family) :
    VarsDisjoint formal candidate := by
  intro name formalOccurrence candidateOccurrence
  rw [LeaTTaTypePresentationExactConformance.toLeaTTaAtom_vars_eq_typeVars]
    at formalOccurrence candidateOccurrence
  have candidateInFlatten : candidate ∈ native.flatten :=
    List.mem_flatten.mpr ⟨family, familyMember, candidateMember⟩
  have candidateAvoids :=
    Spec.Type.Presentation.Freshness.AtomsAvoid.atom
      prepared.avoidFormals candidateInFlatten
  exact candidateAvoids name candidateOccurrence
    (typeVars_mem_typeVarsList_of_mem formalMember name formalOccurrence)

/-- A selected head candidate may extend the presentation without capturing
any private variable reserved for later argument positions. -/
theorem PreparedArgumentCandidateLists.selected_output_avoids_tail
    {formal : Atom} {formals candidates : List Atom}
    {remaining : List (List Atom)} {incoming output : TypeSubst}
    {runtimeHead : List Metta.Atom}
    {runtimeTail : List (List Metta.Atom)}
    (prepared : PreparedArgumentCandidateLists
      (formal :: formals) incoming (candidates :: remaining)
      (runtimeHead :: runtimeTail))
    {candidate : Atom} (candidateMember : candidate ∈ candidates)
    (matched : CorePlusR2TypePresentationMatchRel
      incoming formal candidate output) :
    output.Avoids (TypeSubst.typeVarsList remaining.flatten) := by
  let tailVars := TypeSubst.typeVarsList remaining.flatten
  have liftTailVariable {name : String}
      (occurrence : name ∈ tailVars) :
      name ∈ TypeSubst.typeVarsList (candidates :: remaining).flatten := by
    obtain ⟨atom, atomMember, atomOccurrence⟩ :=
      exists_mem_of_mem_typeVarsList occurrence
    apply typeVars_mem_typeVarsList_of_mem
      (atom := atom) (atoms := (candidates :: remaining).flatten)
    · simp only [List.flatten_cons, List.mem_append]
      exact Or.inr atomMember
    · exact atomOccurrence
  have incomingAvoids : incoming.Avoids tailVars := by
    constructor
    · intro name keyMember occurrence
      exact prepared.avoidInitial.keys name keyMember
        (liftTailVariable occurrence)
    · intro key value entryMember name valueOccurrence occurrence
      exact prepared.avoidInitial.values key value entryMember name
        valueOccurrence (liftTailVariable occurrence)
  have formalAvoids : AtomAvoids formal tailVars := by
    intro name formalOccurrence tailOccurrence
    exact prepared.avoidFormals name (liftTailVariable tailOccurrence)
      (typeVars_mem_typeVarsList_of_mem (by simp) name formalOccurrence)
  have candidateAvoids : AtomAvoids candidate tailVars := by
    intro name candidateOccurrence tailOccurrence
    obtain ⟨tailAtom, tailAtomMember, tailAtomOccurrence⟩ :=
      exists_mem_of_mem_typeVarsList tailOccurrence
    obtain ⟨tailFamily, tailFamilyMember, tailAtomMember⟩ :=
      List.mem_flatten.mp tailAtomMember
    cases prepared.families with
    | cons headDisjoint _ =>
        have disjoint := headDisjoint tailFamily tailFamilyMember
        exact disjoint name
          (typeVars_mem_typeVarsList_of_mem candidateMember name
            candidateOccurrence)
          (typeVars_mem_typeVarsList_of_mem tailAtomMember name
            tailAtomOccurrence)
  exact corePlusR2TypePresentationMatch_output_avoids matched
    incomingAvoids formalAvoids candidateAvoids

/-- Dropping the completed head position preserves the static preparation
contract, provided the selected presentation has been shown fresh for the
tail. -/
theorem PreparedArgumentCandidateLists.tail
    {formal : Atom} {formals candidates : List Atom}
    {remaining : List (List Atom)} {initial next : TypeSubst}
    {runtimeHead : List Metta.Atom}
    {runtimeTail : List (List Metta.Atom)}
    (prepared : PreparedArgumentCandidateLists
      (formal :: formals) initial (candidates :: remaining)
      (runtimeHead :: runtimeTail))
    (nextAvoids : next.Avoids
      (TypeSubst.typeVarsList remaining.flatten)) :
    PreparedArgumentCandidateLists formals next remaining runtimeTail := by
  constructor
  · simpa using congrArg List.tail prepared.link
  · intro name candidateOccurrence formalOccurrence
    apply prepared.avoidFormals name
    · obtain ⟨atom, atomMember, atomOccurrence⟩ :=
        exists_mem_of_mem_typeVarsList candidateOccurrence
      apply typeVars_mem_typeVarsList_of_mem
        (atom := atom) (atoms := (candidates :: remaining).flatten)
      · simp only [List.flatten_cons, List.mem_append]
        exact Or.inr atomMember
      · exact atomOccurrence
    · simp only [TypeSubst.typeVarsList, List.mem_append]
      exact Or.inr formalOccurrence
  · exact nextAvoids
  · cases prepared.families with
    | cons _ tailFamilies => exact tailFamilies

/-- A closed pair of distinct private scopes satisfies the complete static
preparation contract. -/
theorem prepared_argument_candidates_positive_canary :
    PreparedArgumentCandidateLists [.var "t"] [] [[.var "u"]]
      [[.var "u"]] := by
  constructor
  · simp [toLeaTTaAtoms, toLeaTTaAtom]
  · simp [AtomsAvoid, TypeSubst.typeVarsList, TypeSubst.typeVars]
  · exact TypeSubst.avoids_empty _
  · simp [FreshFamiliesSeparated, AtomsAvoid,
      TypeSubst.typeVarsList, TypeSubst.typeVars]

/-- A candidate spelling that captures a formal variable cannot satisfy the
preparation boundary, independently of its runtime representation. -/
theorem prepared_argument_candidates_reject_formal_capture :
    ¬∃ runtime,
      PreparedArgumentCandidateLists [.var "t"] [] [[.var "t"]]
        runtime := by
  rintro ⟨runtime, prepared⟩
  have disjoint := prepared.formal_candidate_disjoint
    (formal := .var "t") (candidate := .var "t")
    (family := [.var "t"]) (by simp) (by simp) (by simp)
  exact disjoint "t" (by simp [toLeaTTaAtom, Metta.Atom.vars])
    (by simp [toLeaTTaAtom, Metta.Atom.vars])

/-! ## Runtime scan over prepared candidates -/

/-- Runtime diagnostics for one already-prepared argument candidate list. -/
def runtimeArgumentTypeDiagnosticBlock (position : Nat)
    (bindings : Metta.Bindings) (formal : Atom) :
    List Metta.Atom → List Metta.Minimal.TypeCheckArgsError :=
  List.map fun actual =>
    { position
      expected := Metta.instantiate bindings (toLeaTTaAtom formal)
      actual }

/-- Add one earlier runtime diagnostic block after every later block. -/
def appendRuntimeArgumentErrors
    (outcome : Metta.Minimal.TypeCheckArgsDetailedOutcome)
    (earlier : List Metta.Minimal.TypeCheckArgsError) :
    Metta.Minimal.TypeCheckArgsDetailedOutcome :=
  match outcome with
  | .success output later => .success output (later ++ earlier)
  | .failure first later => .failure first (later ++ earlier)

/-- Construct the runtime's exact failure outcome for one rejected argument.
An empty type lookup uses the published `%Undefined%` sentinel. -/
def runtimeArgumentFailure (position : Nat)
    (bindings : Metta.Bindings) (formal : Atom)
    (failedActuals : List Metta.Atom) :
    Metta.Minimal.TypeCheckArgsDetailedOutcome :=
  match runtimeArgumentTypeDiagnosticBlock position bindings formal
      failedActuals with
  | first :: rest => .failure first rest
  | [] => .failure
      { position
        expected := Metta.instantiate bindings (toLeaTTaAtom formal)
        actual := .sym "%Undefined%" } []

/-- The repaired runtime's recursive argument scan after state-dependent type
preparation has supplied the ordered candidate lists.  This bridge-local
relation contains no environment, world, lookup, or freshening operation;
those are isolated behind the preparation realization theorem. -/
inductive RuntimePreparedArgumentScanRel :
    List Atom → List (List Atom) → Nat → Metta.Bindings →
      Metta.Minimal.TypeCheckArgsDetailedOutcome → Prop where
  | noArguments (formals : List Atom) (position : Nat)
      (bindings : Metta.Bindings) :
      RuntimePreparedArgumentScanRel formals [] position bindings
        (.success bindings [])
  | noFormal (candidates : List Atom) (remaining : List (List Atom))
      (position : Nat) (bindings : Metta.Bindings) :
      RuntimePreparedArgumentScanRel [] (candidates :: remaining)
        position bindings (.success bindings [])
  | stepSuccess {formal : Atom} {formals : List Atom}
      {candidates : List Atom} {remaining : List (List Atom)}
      {position : Nat} {bindings next : Metta.Bindings}
      {runtimeFailures : List Metta.Atom}
      {tailOutcome : Metta.Minimal.TypeCheckArgsDetailedOutcome} :
      Metta.Minimal.scanActualTypes bindings (toLeaTTaAtom formal)
          (toLeaTTaAtoms candidates) =
        { selected := some next, failures := runtimeFailures } →
      RuntimePreparedArgumentScanRel formals remaining (position + 1)
        next tailOutcome →
      RuntimePreparedArgumentScanRel (formal :: formals)
        (candidates :: remaining) position bindings
        (appendRuntimeArgumentErrors tailOutcome
          (runtimeArgumentTypeDiagnosticBlock (position + 1)
            bindings formal runtimeFailures))
  | stepFailure {formal : Atom} {formals : List Atom}
      {candidates : List Atom} {remaining : List (List Atom)}
      {position : Nat} {bindings : Metta.Bindings}
      {runtimeFailures : List Metta.Atom} :
      Metta.Minimal.scanActualTypes bindings (toLeaTTaAtom formal)
          (toLeaTTaAtoms candidates) =
        { selected := none, failures := runtimeFailures } →
      RuntimePreparedArgumentScanRel (formal :: formals)
        (candidates :: remaining) position bindings
        (runtimeArgumentFailure (position + 1) bindings formal
          runtimeFailures)

mutual
  /-- The branch-valued runtime scan after state-dependent preparation has
  supplied the ordered candidate families. -/
  inductive RuntimePreparedArgumentBranchScanRel :
      List Atom → List (List Atom) → Nat → Metta.Bindings →
        Metta.Minimal.TypeCheckArgsBranchResult → Prop where
    | noArguments (formals : List Atom) (position : Nat)
        (bindings : Metta.Bindings) :
        RuntimePreparedArgumentBranchScanRel formals [] position bindings
          ⟨[bindings], []⟩
    | noFormal (candidates : List Atom) (remaining : List (List Atom))
        (position : Nat) (bindings : Metta.Bindings) :
        RuntimePreparedArgumentBranchScanRel [] (candidates :: remaining)
          position bindings ⟨[bindings], []⟩
    | step {formal : Atom} {formals : List Atom}
        {candidates : List Atom} {remaining : List (List Atom)}
        {position : Nat} {bindings : Metta.Bindings}
        {head : Metta.Minimal.ActualTypeBranchScanResult}
        {tailOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult} :
        Metta.Minimal.scanActualTypeBranches bindings
            (toLeaTTaAtom formal) (toLeaTTaAtoms candidates) = head →
        RuntimePreparedArgumentBranchTailsRel formals remaining
          (position + 1) head.successes tailOutcomes →
        RuntimePreparedArgumentBranchScanRel (formal :: formals)
          (candidates :: remaining) position bindings
          ⟨tailOutcomes.flatMap (·.successes),
            tailOutcomes.flatMap (·.errors) ++
              runtimeArgumentTypeDiagnosticBlock (position + 1)
                bindings formal head.failures⟩

  /-- Recursive runtime scans aligned with every successful private binding
  presentation at the current argument position. -/
  inductive RuntimePreparedArgumentBranchTailsRel :
      List Atom → List (List Atom) → Nat → List Metta.Bindings →
        List Metta.Minimal.TypeCheckArgsBranchResult → Prop where
    | nil {formals : List Atom} {remaining : List (List Atom)}
        {position : Nat} :
        RuntimePreparedArgumentBranchTailsRel formals remaining position [] []
    | cons {formals : List Atom} {remaining : List (List Atom)}
        {position : Nat} {next : Metta.Bindings}
        {nexts : List Metta.Bindings}
        {outcome : Metta.Minimal.TypeCheckArgsBranchResult}
        {outcomes : List Metta.Minimal.TypeCheckArgsBranchResult} :
        RuntimePreparedArgumentBranchScanRel formals remaining
          position next outcome →
        RuntimePreparedArgumentBranchTailsRel formals remaining
          position nexts outcomes →
        RuntimePreparedArgumentBranchTailsRel formals remaining
          position (next :: nexts) (outcome :: outcomes)
end

/-! ## Diagnostic-ledger boundary -/

/-- One spec diagnostic and one runtime diagnostic carry the same position
and displayed formal type, while the freshened actual type is compared up to
private alpha-renaming.  Runtime fresh-name prefixes depend on the
branch-local binding avoid set, so literal equality of polymorphic failure
diagnostics is false even though their public structure is identical. -/
structure ArgumentTypeDiagnosticRuntimeRel
    (specDiagnostic : ArgumentTypeDiagnostic)
    (runtimeDiagnostic : Metta.Minimal.TypeCheckArgsError) : Prop where
  position : specDiagnostic.position = runtimeDiagnostic.position
  expected : ObservedTypeAlphaRel specDiagnostic.expected
    (fromLeaTTaAtom runtimeDiagnostic.expected)
  actual : ObservedTypeAlphaRel specDiagnostic.actual
    (fromLeaTTaAtom runtimeDiagnostic.actual)

/-- Exact correspondence for one branch-valued argument-scan outcome. -/
structure ArgumentCandidateListsBranchOutcomeRuntimeRel
    (specOutcome : ArgumentCandidateListsBranchOutcome)
    (runtimeOutcome : Metta.Minimal.TypeCheckArgsBranchResult) : Prop where
  successes : TypePresentationSimulationStates specOutcome.successes
    runtimeOutcome.successes
  errors : List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
    specOutcome.errors runtimeOutcome.errors

/-- Simulation states for every branch entering one recursive tail, together
with the static preparation contract specialized to that branch. -/
def PreparedArgumentBranchTailStates
    (formals : List Atom) (remaining : List (List Atom))
    (presentations : List TypeSubst)
    (runtimeBindings : List Metta.Bindings) : Prop :=
  List.Forall₂
    (fun presentation lea =>
      ∃ spec,
        TypePresentationSimulationState presentation spec lea ∧
          PreparedArgumentCandidateLists formals presentation remaining
            (remaining.map toLeaTTaAtoms))
    presentations runtimeBindings

/-- Flattening aligned branch outcomes preserves exact success-state
correspondence. -/
theorem branchOutcomeRuntimeRel_flatMap_successes
    {specOutcomes : List ArgumentCandidateListsBranchOutcome}
    {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
    (outcomes : List.Forall₂ ArgumentCandidateListsBranchOutcomeRuntimeRel
      specOutcomes runtimeOutcomes) :
    TypePresentationSimulationStates
      (specOutcomes.flatMap (·.successes))
      (runtimeOutcomes.flatMap (·.successes)) := by
  induction outcomes with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head.successes inductionHypothesis

/-- Flattening aligned branch outcomes preserves exact diagnostic order. -/
theorem branchOutcomeRuntimeRel_flatMap_errors
    {specOutcomes : List ArgumentCandidateListsBranchOutcome}
    {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
    (outcomes : List.Forall₂ ArgumentCandidateListsBranchOutcomeRuntimeRel
      specOutcomes runtimeOutcomes) :
    List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
      (specOutcomes.flatMap (·.errors))
      (runtimeOutcomes.flatMap (·.errors)) := by
  induction outcomes with
  | nil => exact .nil
  | cons head _ inductionHypothesis =>
      exact List.rel_append head.errors inductionHypothesis

/-- The current argument's diagnostic block agrees exactly with the runtime
block: declaration order and one-based position are literal, while the
private formal presentation is alpha-observational. -/
theorem argumentTypeDiagnosticBlock_runtime_exact
    {incoming : TypeSubst} {spec : Bindings} {lea : Metta.Bindings}
    (state : TypePresentationSimulationState incoming spec lea)
    (formal : Atom) (position : Nat) (failedActuals : List Atom) :
    List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
      (argumentTypeDiagnosticBlock position (incoming.apply formal)
        failedActuals)
      ((toLeaTTaAtoms failedActuals).map fun actual =>
        { position := position
          expected := Metta.instantiate lea (toLeaTTaAtom formal)
          actual := actual }) := by
  simp only [argumentTypeDiagnosticBlock, toLeaTTaAtoms_eq_map,
    List.map_map]
  induction failedActuals with
  | nil => exact .nil
  | cons actual failedActuals inductionHypothesis =>
      apply List.Forall₂.cons
      · exact
          { position := rfl
            expected := state.returnAlpha formal
            actual := by
              simpa using ObservedTypeAlphaRel.refl actual }
      · exact inductionHypothesis

/-- Exact correspondence between the spec argument-fold outcome and the
runtime's detailed outcome.  Successful outcomes retain the complete private
binding simulation; failed outcomes retain the whole ordered error ledger. -/
inductive ArgumentCandidateListsOutcomeRuntimeRel :
    ArgumentCandidateListsScanOutcome →
      Metta.Minimal.TypeCheckArgsDetailedOutcome → Prop where
  | success {presentationOutput : TypeSubst} {specOutput : Bindings}
      {leaOutput : Metta.Bindings}
      {specErrors : List ArgumentTypeDiagnostic}
      {runtimeErrors : List Metta.Minimal.TypeCheckArgsError} :
      TypePresentationSimulationState
        presentationOutput specOutput leaOutput →
      List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
        specErrors runtimeErrors →
      ArgumentCandidateListsOutcomeRuntimeRel
        (.success presentationOutput specErrors)
        (.success leaOutput runtimeErrors)
  | failure {specErrors : List ArgumentTypeDiagnostic}
      {firstRuntimeError : Metta.Minimal.TypeCheckArgsError}
      {moreRuntimeErrors : List Metta.Minimal.TypeCheckArgsError} :
      List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
        specErrors (firstRuntimeError :: moreRuntimeErrors) →
      ArgumentCandidateListsOutcomeRuntimeRel (.failure specErrors)
        (.failure firstRuntimeError moreRuntimeErrors)

/-- Appending one earlier diagnostic block preserves outcome
correspondence.  This is the reusable algebraic statement of #13's
block-prepend rule: later errors stay in front and the earlier block is
appended once. -/
theorem ArgumentCandidateListsOutcomeRuntimeRel.appendEarlierErrors
    {specOutcome : ArgumentCandidateListsScanOutcome}
    {runtimeOutcome : Metta.Minimal.TypeCheckArgsDetailedOutcome}
    (outcome : ArgumentCandidateListsOutcomeRuntimeRel
      specOutcome runtimeOutcome)
    {specEarlier : List ArgumentTypeDiagnostic}
    {runtimeEarlier : List Metta.Minimal.TypeCheckArgsError}
    (earlier : List.Forall₂ ArgumentTypeDiagnosticRuntimeRel
      specEarlier runtimeEarlier) :
    ArgumentCandidateListsOutcomeRuntimeRel
      (specOutcome.appendEarlierErrors specEarlier)
      (match runtimeOutcome with
        | .success output later => .success output (later ++ runtimeEarlier)
        | .failure first later => .failure first (later ++ runtimeEarlier)) := by
  cases outcome with
  | success state later =>
      exact .success state
        (List.rel_append (R := ArgumentTypeDiagnosticRuntimeRel)
          later earlier)
  | failure later =>
      cases later with
      | cons first rest =>
          exact .failure
            (List.rel_append (R := ArgumentTypeDiagnosticRuntimeRel)
              (.cons first rest) earlier)

/-! ## Exact prepared-fold conformance -/

/-- The complete repaired runtime argument scan over already-prepared
candidates is exact with respect to the independent presentation-selection
relation.  Dynamic tail freshness is derived from the one static preparation
contract; it is not assumed at recursive states. -/
theorem runtimePreparedArgumentScan_presentation_exact
    {formals : List Atom} {candidateLists : List (List Atom)}
    {position : Nat} {incoming : TypeSubst} {spec : Bindings}
    {lea : Metta.Bindings}
    {runtimeOutcome : Metta.Minimal.TypeCheckArgsDetailedOutcome}
    (state : TypePresentationSimulationState incoming spec lea)
    (prepared : PreparedArgumentCandidateLists formals incoming
      candidateLists (candidateLists.map toLeaTTaAtoms))
    (runtimeScan : RuntimePreparedArgumentScanRel formals candidateLists
      position lea runtimeOutcome) :
    ∃ specOutcome,
      ArgumentCandidateListsScanRel formals candidateLists position
          incoming specOutcome ∧
        ArgumentCandidateListsOutcomeRuntimeRel specOutcome
          runtimeOutcome := by
  induction runtimeScan generalizing incoming spec with
  | noArguments formals position bindings =>
      exact ⟨.success incoming [],
        ArgumentCandidateListsScanRel.noArguments formals position incoming,
        .success state .nil⟩
  | noFormal candidates remaining position bindings =>
      exact ⟨.success incoming [],
        ArgumentCandidateListsScanRel.noFormal candidates remaining position
          incoming,
        .success state .nil⟩
  | @stepSuccess formal formals candidates remaining position bindings next
      runtimeFailures tailOutcome scanEquation tailScan inductionHypothesis =>
      have selected :
          (Metta.Minimal.scanActualTypes bindings (toLeaTTaAtom formal)
            (toLeaTTaAtoms candidates)).selected = some next := by
        rw [scanEquation]
      have disjoint : ∀ candidate ∈ candidates,
          VarsDisjoint formal candidate := by
        intro candidate member
        exact prepared.formal_candidate_disjoint
          (formal := formal) (candidate := candidate)
          (family := candidates) (by simp) (by simp) member
      obtain ⟨presentationNext, specNext, failedActuals, headScan,
          failuresEquation, nextState⟩ :=
        scanActualTypes_selected_presentation_exact state formal candidates
          disjoint selected
      have runtimeFailuresEquation :
          runtimeFailures = toLeaTTaAtoms failedActuals := by
        rw [← failuresEquation, scanEquation]
      subst runtimeFailures
      have nextAvoids : presentationNext.Avoids
          (TypeSubst.typeVarsList remaining.flatten) := by
        obtain ⟨candidate, candidateMember, headMatch⟩ :=
          headScan.success_candidate
        exact prepared.selected_output_avoids_tail
          candidateMember headMatch
      have tailPrepared : PreparedArgumentCandidateLists formals
          presentationNext remaining (remaining.map toLeaTTaAtoms) := by
        simpa using prepared.tail nextAvoids
      obtain ⟨specTailOutcome, specTailScan, tailCorrespondence⟩ :=
        inductionHypothesis nextState tailPrepared
      let specOutcome :=
        specTailOutcome.appendEarlierErrors
          (argumentTypeDiagnosticBlock (position + 1)
            (incoming.apply formal) failedActuals)
      refine ⟨specOutcome,
        ArgumentCandidateListsScanRel.stepSuccess headScan specTailScan,
        ?_⟩
      have diagnostics := argumentTypeDiagnosticBlock_runtime_exact
        state formal (position + 1) failedActuals
      cases tailCorrespondence with
      | success tailState tailDiagnostics =>
          exact .success tailState
            (List.rel_append
              (R := ArgumentTypeDiagnosticRuntimeRel)
              tailDiagnostics diagnostics)
      | failure tailDiagnostics =>
          cases tailDiagnostics with
          | cons first rest =>
              exact .failure
                (List.rel_append
                  (R := ArgumentTypeDiagnosticRuntimeRel)
                  (.cons first rest) diagnostics)
  | @stepFailure formal formals candidates remaining position bindings
      runtimeFailures scanEquation =>
      have selected :
          (Metta.Minimal.scanActualTypes bindings (toLeaTTaAtom formal)
            (toLeaTTaAtoms candidates)).selected = none := by
        rw [scanEquation]
      have disjoint : ∀ candidate ∈ candidates,
          VarsDisjoint formal candidate := by
        intro candidate member
        exact prepared.formal_candidate_disjoint
          (formal := formal) (candidate := candidate)
          (family := candidates) (by simp) (by simp) member
      obtain emptyCase | nonemptyCase :=
        scanActualTypes_failure_presentation_exact state formal candidates
          disjoint selected
      · rcases emptyCase with ⟨rfl, headScan, failuresEquation⟩
        have runtimeFailuresEquation : runtimeFailures = [] := by
          rw [← failuresEquation, scanEquation]
        subst runtimeFailures
        let specDiagnostic : ArgumentTypeDiagnostic :=
          { position := position + 1
            expected := incoming.apply formal
            actual := Atom.undefinedType }
        let runtimeDiagnostic : Metta.Minimal.TypeCheckArgsError :=
          { position := position + 1
            expected := Metta.instantiate bindings (toLeaTTaAtom formal)
            actual := .sym "%Undefined%" }
        have diagnostic : ArgumentTypeDiagnosticRuntimeRel
            specDiagnostic runtimeDiagnostic :=
          { position := rfl
            expected := state.returnAlpha formal
            actual := ObservedTypeAlphaRel.refl Atom.undefinedType }
        refine ⟨.failure [specDiagnostic],
          ArgumentCandidateListsScanRel.stepFailure headScan, ?_⟩
        simpa [runtimeArgumentFailure, runtimeArgumentTypeDiagnosticBlock,
          specDiagnostic, runtimeDiagnostic] using
          (ArgumentCandidateListsOutcomeRuntimeRel.failure
            (List.Forall₂.cons diagnostic .nil))
      · rcases nonemptyCase with
          ⟨candidatesNonempty, headScan, failuresEquation⟩
        have runtimeFailuresEquation :
            runtimeFailures = toLeaTTaAtoms candidates := by
          rw [← failuresEquation, scanEquation]
        subst runtimeFailures
        have diagnostics := argumentTypeDiagnosticBlock_runtime_exact
          state formal (position + 1) candidates
        refine ⟨.failure
            (argumentTypeDiagnosticBlock (position + 1)
              (incoming.apply formal) candidates),
          ArgumentCandidateListsScanRel.stepFailure headScan, ?_⟩
        cases candidates with
        | nil => exact False.elim (candidatesNonempty rfl)
        | cons candidate candidates =>
            simpa [runtimeArgumentFailure,
              runtimeArgumentTypeDiagnosticBlock] using
              (ArgumentCandidateListsOutcomeRuntimeRel.failure diagnostics)

/-! ## Exact branch-valued prepared-fold conformance -/

mutual
  /-- The complete branch-valued runtime argument scan over prepared
  candidates is exact with respect to the independent DFS presentation
  relation. -/
  theorem runtimePreparedArgumentBranchScan_presentation_exact
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming : TypeSubst} {spec : Bindings}
      {lea : Metta.Bindings}
      {runtimeOutcome : Metta.Minimal.TypeCheckArgsBranchResult}
      (state : TypePresentationSimulationState incoming spec lea)
      (prepared : PreparedArgumentCandidateLists formals incoming
        candidateLists (candidateLists.map toLeaTTaAtoms))
      (runtimeScan : RuntimePreparedArgumentBranchScanRel formals
        candidateLists position lea runtimeOutcome) :
      ∃ specOutcome,
        ArgumentCandidateListsBranchScanRel formals candidateLists position
            incoming specOutcome ∧
          ArgumentCandidateListsBranchOutcomeRuntimeRel specOutcome
            runtimeOutcome := by
    cases runtimeScan with
    | noArguments formals position bindings =>
        exact ⟨⟨[incoming], []⟩,
          ArgumentCandidateListsBranchScanRel.noArguments formals position
            incoming,
          ⟨.cons ⟨spec, state⟩ .nil, .nil⟩⟩
    | noFormal candidates remaining position bindings =>
        exact ⟨⟨[incoming], []⟩,
          ArgumentCandidateListsBranchScanRel.noFormal candidates remaining
            position incoming,
          ⟨.cons ⟨spec, state⟩ .nil, .nil⟩⟩
    | @step formal formals candidates remaining position bindings head
        runtimeTailOutcomes scanEquation runtimeTails =>
        have disjoint : ∀ candidate ∈ candidates,
            VarsDisjoint formal candidate := by
          intro candidate member
          exact prepared.formal_candidate_disjoint
            (formal := formal) (candidate := candidate)
            (family := candidates) (by simp) (by simp) member
        obtain ⟨presentations, failedActuals, headRel, branchStates,
            failuresEquation⟩ :=
          scanActualTypeBranches_presentation_exact state formal candidates
            disjoint
        have branchStates' : TypePresentationCandidateBranchStates incoming
            formal candidates presentations head.successes := by
          rw [scanEquation] at branchStates
          exact branchStates
        have preparedTailStates : PreparedArgumentBranchTailStates formals
            remaining presentations head.successes := by
          apply branchStates'.imp
          intro presentation runtimeBindings evidence
          obtain ⟨candidate, candidateMember, matched, specNext, nextState⟩ :=
            evidence
          have nextAvoids := prepared.selected_output_avoids_tail
            candidateMember matched
          exact ⟨specNext, nextState, by
            simpa using prepared.tail nextAvoids⟩
        obtain ⟨specTailOutcomes, specTails, tailCorrespondence⟩ :=
          runtimePreparedArgumentBranchTails_presentation_exact
            preparedTailStates runtimeTails
        let specOutcome : ArgumentCandidateListsBranchOutcome :=
          ⟨specTailOutcomes.flatMap (·.successes),
            specTailOutcomes.flatMap (·.errors) ++
              argumentTypeDiagnosticBlock (position + 1)
                (incoming.apply formal) failedActuals⟩
        refine ⟨specOutcome,
          ArgumentCandidateListsBranchScanRel.step headRel specTails,
          ?_⟩
        have headFailuresEquation :
            head.failures = toLeaTTaAtoms failedActuals := by
          rw [← scanEquation]
          exact failuresEquation
        have currentDiagnostics : List.Forall₂
            ArgumentTypeDiagnosticRuntimeRel
            (argumentTypeDiagnosticBlock (position + 1)
              (incoming.apply formal) failedActuals)
            (runtimeArgumentTypeDiagnosticBlock (position + 1)
              lea formal head.failures) := by
          rw [headFailuresEquation]
          simpa [runtimeArgumentTypeDiagnosticBlock] using
            argumentTypeDiagnosticBlock_runtime_exact state formal
              (position + 1) failedActuals
        exact
          { successes :=
              branchOutcomeRuntimeRel_flatMap_successes tailCorrespondence
            errors := List.rel_append
              (branchOutcomeRuntimeRel_flatMap_errors tailCorrespondence)
              currentDiagnostics }

  /-- Pointwise exactness for the recursive tails of every successful branch
  at one argument position. -/
  theorem runtimePreparedArgumentBranchTails_presentation_exact
      {formals : List Atom} {remaining : List (List Atom)}
      {position : Nat} {presentations : List TypeSubst}
      {runtimeBindings : List Metta.Bindings}
      {runtimeOutcomes : List Metta.Minimal.TypeCheckArgsBranchResult}
      (states : PreparedArgumentBranchTailStates formals remaining
        presentations runtimeBindings)
      (runtimeTails : RuntimePreparedArgumentBranchTailsRel formals remaining
        position runtimeBindings runtimeOutcomes) :
      ∃ specOutcomes,
        ArgumentCandidateListsBranchTailsRel formals remaining position
            presentations specOutcomes ∧
          List.Forall₂ ArgumentCandidateListsBranchOutcomeRuntimeRel
            specOutcomes runtimeOutcomes := by
    cases runtimeTails with
    | nil =>
        cases states
        exact ⟨[], .nil, .nil⟩
    | cons headScan tailScans =>
        cases states with
        | cons headState tailStates =>
            obtain ⟨spec, state, prepared⟩ := headState
            obtain ⟨specOutcome, specScan, outcomeCorrespondence⟩ :=
              runtimePreparedArgumentBranchScan_presentation_exact
                state prepared headScan
            obtain ⟨specOutcomes, specScans, outcomeCorrespondences⟩ :=
              runtimePreparedArgumentBranchTails_presentation_exact
                tailStates tailScans
            exact ⟨specOutcome :: specOutcomes,
              .cons specScan specScans,
              .cons outcomeCorrespondence outcomeCorrespondences⟩
end

/-! ## Boundary canaries -/

/-- Positive: the gradual `Atom` formal selects a concrete actual type through
the exact runtime/presentation boundary. -/
theorem scanActualTypes_atom_positive_canary :
    ∃ presentationOutput specOutput failedActuals,
      ActualTypeCandidateScanRel [] Atom.atomType [.symbol "B"]
        (.success presentationOutput failedActuals) ∧
      TypePresentationSimulationState presentationOutput specOutput
        Metta.Bindings.empty := by
  have selected :
      (Metta.Minimal.scanActualTypes Metta.Bindings.empty
        (toLeaTTaAtom Atom.atomType)
        (toLeaTTaAtoms [.symbol "B"])).selected =
          some Metta.Bindings.empty := by
    rfl
  obtain ⟨presentationOutput, specOutput, failedActuals,
      scan, _failures, outputState⟩ :=
    scanActualTypes_selected_presentation_exact
      typePresentationSimulationState_empty Atom.atomType [.symbol "B"]
      (by simp [VarsDisjoint, toLeaTTaAtom, Metta.Atom.vars]) selected
  exact ⟨presentationOutput, specOutput, failedActuals, scan, outputState⟩

/-- Negative: two distinct concrete type symbols have an exact all-failed
scan derivation; no wildcard or default silently turns it into success. -/
theorem scanActualTypes_distinct_symbols_negative_canary :
    ActualTypeCandidateScanRel [] (.symbol "B") [.symbol "C"]
      (.failure [.symbol "C"]) := by
  have selected :
      (Metta.Minimal.scanActualTypes Metta.Bindings.empty
        (toLeaTTaAtom (.symbol "B"))
        (toLeaTTaAtoms [.symbol "C"])).selected = none := by
    rfl
  have exactFailure :=
    scanActualTypes_failure_presentation_exact
      typePresentationSimulationState_empty (.symbol "B") [.symbol "C"]
      (by simp [VarsDisjoint, toLeaTTaAtom, Metta.Atom.vars]) selected
  rcases exactFailure with empty | nonempty
  · simp at empty
  · exact nonempty.2.1

end Mettapedia.Languages.MeTTa.HE.LeaTTaTypePresentationSelectionConformance
