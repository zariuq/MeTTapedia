import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Freshness
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance

/-!
# Exact ordered selection for type presentations

The runtime type checker receives already-prepared, already-freshened lists
of actual type candidates.  This module gives that list processing an
executable-independent relation.  Preparation and lookup are deliberately
absent: a later conformance layer supplies the ordered lists together with
their existing finite-scope avoidance facts.

Each argument uses the first matching actual type as its private binding
presentation, but classifies the whole ordered actual-type list so every
failed actual remains available as a latent diagnostic.  When a later
argument or return check rejects the function candidate, later argument
blocks precede earlier blocks while each block retains declaration order.
No relation here mentions an evaluator state, a runtime environment, or fuel.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Selection

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Type.Presentation
open Spec.Type.Presentation.Alpha
open Spec.Type.Presentation.Exact
open Spec.Type.Presentation.ApplicationEquivariance
open Spec.Type.Presentation.Completeness
open Spec.Type.Presentation.Freshness
open Spec.Type.Presentation.MatchSolutionTheory
open Spec.Type.Presentation.Theory
open Spec.Type.RuntimeRefinement

/-! ## Generic ordered-option characterization -/

/-- `findSome?` succeeds exactly at one element preceded only by failures.
The suffix is intentionally unconstrained because the scan stops at the first
success. -/
theorem List.findSome_eq_some_iff_split
    {α β : Type*} (items : List α) (f : α → Option β) (result : β) :
    items.findSome? f = some result ↔
      ∃ before item suffix,
        items = before ++ item :: suffix ∧
          f item = some result ∧
          ∀ earlier ∈ before, f earlier = none := by
  constructor
  · intro success
    induction items with
    | nil => simp at success
    | cons head tail ih =>
        rw [List.findSome?_cons] at success
        cases headResult : f head with
        | none =>
            rw [headResult] at success
            obtain ⟨before, item, suffix, equation, selected, failures⟩ :=
              ih success
            refine ⟨head :: before, item, suffix, ?_, selected, ?_⟩
            · simp [equation]
            · intro earlier member
              rcases List.mem_cons.mp member with rfl | member
              · exact headResult
              · exact failures earlier member
        | some value =>
            rw [headResult] at success
            cases success
            exact ⟨[], head, tail, rfl, headResult, by simp⟩
  · rintro ⟨before, item, suffix, rfl, selected, failures⟩
    induction before with
    | nil => simp [selected]
    | cons head tail ih =>
        rw [List.cons_append, List.findSome?_cons,
          failures head (by simp)]
        exact ih fun earlier member => failures earlier (by simp [member])

/-- `findSome?` fails exactly when every element fails. -/
theorem List.findSome_eq_none_iff_all
    {α β : Type*} (items : List α) (f : α → Option β) :
    items.findSome? f = none ↔ ∀ item ∈ items, f item = none := by
  constructor
  · intro failure
    induction items with
    | nil => simp
    | cons head tail ih =>
        rw [List.findSome?_cons] at failure
        cases headResult : f head with
        | none =>
            rw [headResult] at failure
            intro item member
            rcases List.mem_cons.mp member with rfl | member
            · exact headResult
            · exact ih failure item member
        | some value => simp [headResult] at failure
  · intro failures
    induction items with
    | nil => rfl
    | cons head tail ih =>
        rw [List.findSome?_cons, failures head (by simp)]
        exact ih fun item member => failures item (by simp [member])

/-! ## One argument's ordered candidate scan -/

/-- Exact classification of one actual type against one raw formal type. -/
inductive ActualTypeCandidateClassification where
  | matched (output : TypeSubst)
  | failed

/-- A candidate classification is justified by the exact presentation match
relation.  Failure is genuinely negative: no presentation can make that
candidate match. -/
inductive ActualTypeCandidateClassificationRel
    (incoming : TypeSubst) (expected : Atom) :
    Atom -> ActualTypeCandidateClassification -> Prop where
  | matched {candidate : Atom} {output : TypeSubst} :
      CorePlusR2TypePresentationMatchRel incoming expected candidate output ->
      ActualTypeCandidateClassificationRel incoming expected candidate
        (.matched output)
  | failed {candidate : Atom} :
      (forall output,
        ¬CorePlusR2TypePresentationMatchRel
          incoming expected candidate output) ->
      ActualTypeCandidateClassificationRel incoming expected candidate .failed

/-- Failed actual types selected from a pointwise classification, retaining
their input order. -/
def failedActualTypes :
    List Atom -> List ActualTypeCandidateClassification -> List Atom
  | [], _ => []
  | _, [] => []
  | _ :: actuals, .matched _ :: classifications =>
      failedActualTypes actuals classifications
  | actual :: actuals, .failed :: classifications =>
      actual :: failedActualTypes actuals classifications

/-- Result of scanning one argument's ordered actual-type list.  Successful
scans carry the first matching presentation and every other failed actual;
failed scans carry every actual type, all of which failed. -/
inductive ActualTypeCandidateScanOutcome where
  | success (output : TypeSubst) (failedActuals : List Atom)
  | failure (failedActuals : List Atom)

/-- Exact scan of one already-freshened actual-type list.  The first match
chooses the private binding presentation, while the suffix is still
classified so its failures remain observable if the enclosing function
candidate later fails.  Failures cannot change the incoming presentation,
so every candidate is tested against the same input. -/
inductive ActualTypeCandidateScanRel
    (incoming : TypeSubst) (expected : Atom) :
    List Atom → ActualTypeCandidateScanOutcome → Prop where
  | firstSuccess {before : List Atom} {candidate : Atom}
      {suffix : List Atom} {suffixClassifications :
        List ActualTypeCandidateClassification}
      {output : TypeSubst} :
      (∀ earlier ∈ before, ∀ candidateOutput,
        ¬CorePlusR2TypePresentationMatchRel
          incoming expected earlier candidateOutput) →
      CorePlusR2TypePresentationMatchRel
        incoming expected candidate output →
      List.Forall₂
        (ActualTypeCandidateClassificationRel incoming expected)
        suffix suffixClassifications ->
      ActualTypeCandidateScanRel incoming expected
        (before ++ candidate :: suffix)
        (.success output
          (before ++ failedActualTypes suffix suffixClassifications))
  | allFailed {first : Atom} {rest : List Atom} :
      (∀ candidate ∈ first :: rest, ∀ candidateOutput,
        ¬CorePlusR2TypePresentationMatchRel
          incoming expected candidate candidateOutput) →
      ActualTypeCandidateScanRel incoming expected
        (first :: rest) (.failure (first :: rest))
  | empty :
      ActualTypeCandidateScanRel incoming expected []
        (.failure [Atom.undefinedType])

/-- A successful ordered scan exposes the candidate and presentation step
that witness its first success. -/
theorem ActualTypeCandidateScanRel.success_candidate
    {incoming output : TypeSubst} {expected : Atom}
    {candidates failedActuals : List Atom}
    (scan : ActualTypeCandidateScanRel incoming expected candidates
      (.success output failedActuals)) :
  ∃ candidate ∈ candidates,
      CorePlusR2TypePresentationMatchRel
        incoming expected candidate output := by
  cases scan with
  | firstSuccess beforeFailed headMatch suffixes =>
      exact ⟨_, by simp, headMatch⟩

/-! ## Left-to-right argument scan -/

/-- One argument-type diagnostic, before it is embedded into an evaluator
error atom. -/
structure ArgumentTypeDiagnostic where
  position : Nat
  expected : Atom
  actual : Atom
  deriving DecidableEq

/-- Build one argument's diagnostic block in actual-type declaration order. -/
def argumentTypeDiagnosticBlock (position : Nat) (expected : Atom) :
    List Atom -> List ArgumentTypeDiagnostic :=
  List.map fun actual => { position, expected, actual }

/-- Observable result of checking all arguments against raw formal types.
Successful scans retain latent diagnostics: the enclosing function-candidate
scan discards them on final success and exposes them if a later check fails. -/
inductive ArgumentCandidateListsScanOutcome where
  | success (output : TypeSubst) (latentErrors : List ArgumentTypeDiagnostic)
  | failure (errors : List ArgumentTypeDiagnostic)

/-- Add one earlier argument's diagnostic block behind all later blocks.
This is the published block-prepend order: later argument positions appear
first, while each position retains actual-type declaration order. -/
def ArgumentCandidateListsScanOutcome.appendEarlierErrors
    (outcome : ArgumentCandidateListsScanOutcome)
    (earlier : List ArgumentTypeDiagnostic) :
    ArgumentCandidateListsScanOutcome :=
  match outcome with
  | .success output later => .success output (later ++ earlier)
  | .failure later => .failure (later ++ earlier)

/-- Exact scan over precomputed ordered actual-type lists.  The initial
position is explicit because the runtime uses the same worker for its
one-based diagnostic counter.  An exhausted formal list accepts remaining
arguments only in the separately-controlled optional-argument profile. -/
inductive ArgumentCandidateListsScanRel :
    List Atom → List (List Atom) → Nat → TypeSubst →
      ArgumentCandidateListsScanOutcome → Prop where
  | noArguments (formals : List Atom) (position : Nat)
      (incoming : TypeSubst) :
      ArgumentCandidateListsScanRel formals [] position incoming
        (.success incoming [])
  | noFormal (candidates : List Atom) (remaining : List (List Atom))
      (position : Nat) (incoming : TypeSubst) :
      ArgumentCandidateListsScanRel [] (candidates :: remaining)
        position incoming (.success incoming [])
  | stepSuccess {formal : Atom} {formals : List Atom}
      {candidates : List Atom} {remaining : List (List Atom)}
      {position : Nat} {incoming next : TypeSubst}
      {failedActuals : List Atom}
      {outcome : ArgumentCandidateListsScanOutcome} :
      ActualTypeCandidateScanRel incoming formal candidates
        (.success next failedActuals) →
      ArgumentCandidateListsScanRel formals remaining (position + 1)
        next outcome →
      ArgumentCandidateListsScanRel (formal :: formals)
        (candidates :: remaining) position incoming
        (ArgumentCandidateListsScanOutcome.appendEarlierErrors outcome
          (argumentTypeDiagnosticBlock (position + 1)
            (incoming.apply formal) failedActuals))
  | stepFailure {formal : Atom} {formals : List Atom}
      {candidates : List Atom} {remaining : List (List Atom)}
      {position : Nat} {incoming : TypeSubst}
      {failedActuals : List Atom} :
      ActualTypeCandidateScanRel incoming formal candidates
        (.failure failedActuals) →
      ArgumentCandidateListsScanRel (formal :: formals)
        (candidates :: remaining) position incoming
        (.failure (argumentTypeDiagnosticBlock (position + 1)
          (incoming.apply formal) failedActuals))

/-! ## Branch-valued applicability scan -/

/-- Classify every actual type for one argument.  Successful presentations
and failures both retain declaration order; unlike
`ActualTypeCandidateScanRel`, no successful alternative is discarded. -/
inductive ActualTypeCandidateBranchesRel
    (incoming : TypeSubst) (expected : Atom) :
    List Atom → List TypeSubst → List Atom → Prop where
  | nil : ActualTypeCandidateBranchesRel incoming expected [] [] []
  | matched {candidate : Atom} {candidates : List Atom}
      {output : TypeSubst} {outputs : List TypeSubst}
      {failedActuals : List Atom} :
      CorePlusR2TypePresentationMatchRel
        incoming expected candidate output →
      ActualTypeCandidateBranchesRel incoming expected candidates
        outputs failedActuals →
      ActualTypeCandidateBranchesRel incoming expected
        (candidate :: candidates) (output :: outputs) failedActuals
  | failed {candidate : Atom} {candidates : List Atom}
      {outputs : List TypeSubst} {failedActuals : List Atom} :
      (∀ output,
        ¬CorePlusR2TypePresentationMatchRel
          incoming expected candidate output) →
      ActualTypeCandidateBranchesRel incoming expected candidates
        outputs failedActuals →
      ActualTypeCandidateBranchesRel incoming expected
        (candidate :: candidates) outputs (candidate :: failedActuals)

/-- Branch-valued result of scanning all argument positions.  Successful
presentations are in lexicographic DFS order.  Errors from later positions
precede the current position's declaration-ordered block. -/
structure ArgumentCandidateListsBranchOutcome where
  successes : List TypeSubst
  errors : List ArgumentTypeDiagnostic

mutual
  /-- Complete branch-valued argument applicability.  Each successful
  presentation at the current position recursively scans the remaining
  positions; flattening the aligned tail outcomes gives row-major DFS
  order. -/
  inductive ArgumentCandidateListsBranchScanRel :
      List Atom → List (List Atom) → Nat → TypeSubst →
        ArgumentCandidateListsBranchOutcome → Prop where
    | noArguments (formals : List Atom) (position : Nat)
        (incoming : TypeSubst) :
        ArgumentCandidateListsBranchScanRel formals [] position incoming
          ⟨[incoming], []⟩
    | noFormal (candidates : List Atom) (remaining : List (List Atom))
        (position : Nat) (incoming : TypeSubst) :
        ArgumentCandidateListsBranchScanRel [] (candidates :: remaining)
          position incoming ⟨[incoming], []⟩
    | step {formal : Atom} {formals : List Atom}
        {candidates : List Atom} {remaining : List (List Atom)}
        {position : Nat} {incoming : TypeSubst}
        {headSuccesses : List TypeSubst} {failedActuals : List Atom}
        {tailOutcomes : List ArgumentCandidateListsBranchOutcome} :
        ActualTypeCandidateBranchesRel incoming formal candidates
          headSuccesses failedActuals →
        ArgumentCandidateListsBranchTailsRel formals remaining
          (position + 1) headSuccesses tailOutcomes →
        ArgumentCandidateListsBranchScanRel (formal :: formals)
          (candidates :: remaining) position incoming
          ⟨tailOutcomes.flatMap (·.successes),
            tailOutcomes.flatMap (·.errors) ++
              argumentTypeDiagnosticBlock (position + 1)
                (incoming.apply formal) failedActuals⟩

  /-- Pointwise recursive scans for every successful presentation at one
  argument position.  This mutual relation is the inductive analogue of
  `List.Forall₂` and keeps the recursive occurrence strictly positive. -/
  inductive ArgumentCandidateListsBranchTailsRel :
      List Atom → List (List Atom) → Nat → List TypeSubst →
        List ArgumentCandidateListsBranchOutcome → Prop where
    | nil {formals : List Atom} {remaining : List (List Atom)}
        {position : Nat} :
        ArgumentCandidateListsBranchTailsRel formals remaining position [] []
    | cons {formals : List Atom} {remaining : List (List Atom)}
        {position : Nat} {next : TypeSubst} {nexts : List TypeSubst}
        {outcome : ArgumentCandidateListsBranchOutcome}
        {outcomes : List ArgumentCandidateListsBranchOutcome} :
        ArgumentCandidateListsBranchScanRel formals remaining
          position next outcome →
        ArgumentCandidateListsBranchTailsRel formals remaining
          position nexts outcomes →
        ArgumentCandidateListsBranchTailsRel formals remaining
          position (next :: nexts) (outcome :: outcomes)
end

/-! ### Successful branch witnesses -/

/-- Membership in the successful output list identifies the actual candidate
that produced that presentation.  Failed alternatives remain in the source
derivation but cannot manufacture a successful member. -/
theorem ActualTypeCandidateBranchesRel.exists_match_of_mem_success
    {incoming : TypeSubst} {expected : Atom}
    {candidates : List Atom} {outputs : List TypeSubst}
    {failedActuals : List Atom}
    (scan : ActualTypeCandidateBranchesRel incoming expected candidates
      outputs failedActuals) {output : TypeSubst}
    (member : output ∈ outputs) :
    ∃ candidate, candidate ∈ candidates ∧
      CorePlusR2TypePresentationMatchRel incoming expected candidate output := by
  induction scan with
  | nil => simp at member
  | @matched candidate candidates headOutput tailOutputs failed head tail ih =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨candidate, by simp, head⟩
      · obtain ⟨selected, selectedMember, selectedMatch⟩ := ih tailMember
        exact ⟨selected, by simp [selectedMember], selectedMatch⟩
  | @failed candidate candidates outputs failedActuals noMatch tail ih =>
      obtain ⟨selected, selectedMember, selectedMatch⟩ := ih member
      exact ⟨selected, by simp [selectedMember], selectedMatch⟩

/-- If one declared actual candidate is consistent with a satisfied normal
incoming presentation, the complete all-candidate classification contains a
satisfied successful output for that declaration position.  The theorem does
not assume functionality of finite presentations: it consumes the output
already retained by the classification. -/
theorem ActualTypeCandidateBranchesRel.exists_satisfied_output_of_mem
    {incoming : TypeSubst} {expected : Atom}
    {candidates : List Atom} {outputs : List TypeSubst}
    {failedActuals : List Atom}
    (scan : ActualTypeCandidateBranchesRel incoming expected candidates
      outputs failedActuals)
    {candidate : Atom} (candidateMember : candidate ∈ candidates)
    {valuation : String → Atom}
    (incomingNormal : incoming.Normal)
    (incomingSatisfied : TypeSubstSatisfied valuation incoming)
    (consistent : CorePlusR2TypeConsistent valuation expected candidate) :
    ∃ output, output ∈ outputs ∧ output.Normal ∧
      TypeSubstSatisfied valuation output := by
  induction scan with
  | nil => simp at candidateMember
  | @matched headCandidate candidates headOutput outputs failedActuals
      headMatch tail inductionHypothesis =>
      rcases List.mem_cons.mp candidateMember with rfl | tailMember
      · refine ⟨headOutput, by simp,
          headMatch.output_normal incomingNormal, ?_⟩
        exact (CorePlusR2TypePresentationMatchRel.solutions
          headMatch incomingNormal valuation).2
            ⟨incomingSatisfied, consistent⟩
      · obtain ⟨output, outputMember, outputNormal, outputSatisfied⟩ :=
          inductionHypothesis tailMember
        exact ⟨output, by simp [outputMember], outputNormal, outputSatisfied⟩
  | @failed headCandidate candidates outputs failedActuals noMatch tail
      inductionHypothesis =>
      rcases List.mem_cons.mp candidateMember with rfl | tailMember
      · obtain ⟨output, outputMatch, _outputNormal, _outputSatisfied⟩ :=
          CorePlusR2TypePresentationMatchRel.exists_of_satisfied
            incomingNormal incomingSatisfied _ _ consistent
        exact (noMatch output outputMatch).elim
      · exact inductionHypothesis tailMember

/-- Membership in an aligned chosen-candidate list identifies the family at
the same declaration position. -/
theorem alignedChoice_exists_family
    {choices : List Atom} {families : List (List Atom)}
    (aligned : List.Forall₂ (fun choice family => choice ∈ family)
      choices families) {choice : Atom} (member : choice ∈ choices) :
    ∃ family, family ∈ families ∧ choice ∈ family := by
  induction aligned with
  | nil => simp at member
  | @cons headChoice headFamily choices families headMember tailAligned
      inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact ⟨headFamily, by simp, headMember⟩
      · obtain ⟨family, familyMember, choiceMember⟩ :=
          inductionHypothesis tailMember
        exact ⟨family, by simp [familyMember], choiceMember⟩

/-- Selecting one declared atom from every pairwise-separated family retains
pairwise separation of the chosen atoms. -/
theorem chosenCandidates_pairwiseSeparated
    {choices : List Atom} {families : List (List Atom)}
    (aligned : List.Forall₂ (fun choice family => choice ∈ family)
      choices families)
    (separated : families.Pairwise FreshFamiliesSeparated) :
    choices.Pairwise
      (fun left right => FreshFamiliesSeparated [left] [right]) := by
  induction aligned with
  | nil => exact List.Pairwise.nil
  | @cons headChoice headFamily choices families headMember tailAligned
      inductionHypothesis =>
      rw [List.pairwise_cons] at separated ⊢
      constructor
      · intro choice choiceMember
        obtain ⟨family, familyMember, member⟩ :=
          alignedChoice_exists_family tailAligned choiceMember
        exact (separated.1 family familyMember).mono
          (fun atom atomMember => by
            have equation : atom = headChoice :=
              List.mem_singleton.mp atomMember
            simpa [equation] using headMember)
          (fun atom atomMember => by
            have equation : atom = choice := List.mem_singleton.mp atomMember
            simpa [equation] using member)
      · exact inductionHypothesis separated.2

/-- Pairwise-separated atoms give the head-versus-tail freshness clause used
by the finite global-permutation constructor. -/
theorem atomVarsFreshFromAtoms_of_pairwiseSeparated
    {head : Atom} {tail : List Atom}
    (separated : (head :: tail).Pairwise
      (fun left right => FreshFamiliesSeparated [left] [right])) :
    AtomVarsFreshFromAtoms head tail := by
  rw [List.pairwise_cons] at separated
  intro name headOccurrence tailOccurrence
  obtain ⟨tailAtom, tailMember, tailVariable⟩ :=
    exists_mem_of_mem_typeVarsList tailOccurrence
  exact separated.1 tailAtom tailMember name
    (by simp [TypeSubst.typeVarsList, headOccurrence])
    (by simp [TypeSubst.typeVarsList, tailVariable])

/-- Pointwise alpha evidence over pairwise-separated private atoms combines
into the scoped list relation expected by the one-global-permutation theorem.
No generator or counter enters this interface. -/
theorem ScopedObservedTypeListAlphaRel.of_forall₂_pairwiseSeparated
    {left right : List Atom}
    (alpha : List.Forall₂ ObservedTypeAlphaRel left right)
    (leftSeparated : left.Pairwise
      (fun head tail => FreshFamiliesSeparated [head] [tail]))
    (rightSeparated : right.Pairwise
      (fun head tail => FreshFamiliesSeparated [head] [tail])) :
    ScopedObservedTypeListAlphaRel left right := by
  induction alpha with
  | nil => exact .nil
  | @cons leftHead rightHead leftTail rightTail headAlpha tailAlpha
      inductionHypothesis =>
      rw [List.pairwise_cons] at leftSeparated rightSeparated
      exact .cons headAlpha
        (atomVarsFreshFromAtoms_of_pairwiseSeparated
          (List.pairwise_cons.mpr leftSeparated))
        (atomVarsFreshFromAtoms_of_pairwiseSeparated
          (List.pairwise_cons.mpr rightSeparated))
        (inductionHypothesis leftSeparated.2 rightSeparated.2)

mutual

  /-- Every successful complete branch has an explicit ordered choice of one
  declared actual type per argument and an ordinary presentation fold for
  that choice.  The length hypothesis rules out the permissive exhausted-input
  constructors, which are used only by compatibility paths. -/
  theorem ArgumentCandidateListsBranchScanRel.exists_choice_of_mem_success
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming output : TypeSubst}
      {outcome : ArgumentCandidateListsBranchOutcome}
      (scan : ArgumentCandidateListsBranchScanRel formals candidateLists
        position incoming outcome)
      (lengthEquation : formals.length = candidateLists.length)
      (member : output ∈ outcome.successes) :
      ∃ actuals,
        List.Forall₂ (fun actual candidates => actual ∈ candidates)
          actuals candidateLists ∧
        PresentationArgumentListMatchRel formals actuals incoming output := by
    cases scan with
    | noArguments =>
        have emptyFormals : formals = [] :=
          List.eq_nil_of_length_eq_zero (by simpa using lengthEquation)
        subst formals
        have outputEquation : output = incoming := by simpa using member
        subst output
        exact ⟨[], .nil, .nil incoming⟩
    | noFormal candidates remaining position incoming =>
        simp at lengthEquation
    | @step formal tailFormals candidates remaining position incoming
        headSuccesses failedActuals tailOutcomes headScan tailScans =>
        have tailLength : tailFormals.length = remaining.length := by
          simpa using Nat.succ.inj lengthEquation
        obtain ⟨next, nextMember, tailActuals, tailChoices, tailMatch⟩ :=
          ArgumentCandidateListsBranchTailsRel.exists_choice_of_mem_success
            tailScans tailLength member
        obtain ⟨actual, actualMember, headMatch⟩ :=
          headScan.exists_match_of_mem_success nextMember
        exact ⟨actual :: tailActuals, .cons actualMember tailChoices,
          .cons headMatch tailMatch⟩

  /-- Tail companion of
  `ArgumentCandidateListsBranchScanRel.exists_choice_of_mem_success`.
  It records which incoming head branch owns the selected flattened output. -/
  theorem ArgumentCandidateListsBranchTailsRel.exists_choice_of_mem_success
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming : List TypeSubst}
      {outcomes : List ArgumentCandidateListsBranchOutcome}
      (scans : ArgumentCandidateListsBranchTailsRel formals candidateLists
        position incoming outcomes)
      (lengthEquation : formals.length = candidateLists.length)
      {output : TypeSubst}
      (member : output ∈ outcomes.flatMap (fun outcome => outcome.successes)) :
      ∃ next, next ∈ incoming ∧ ∃ actuals,
        List.Forall₂ (fun actual candidates => actual ∈ candidates)
          actuals candidateLists ∧
        PresentationArgumentListMatchRel formals actuals next output := by
    cases scans with
    | nil => simp at member
    | @cons formals candidateLists position next nexts outcome outcomes
        head tail =>
        simp only [List.flatMap_cons, List.mem_append] at member
        rcases member with headMember | tailMember
        · obtain ⟨actuals, choices, matched⟩ :=
            head.exists_choice_of_mem_success lengthEquation headMember
          exact ⟨next, by simp, actuals, choices, matched⟩
        · obtain ⟨selected, selectedMember, actuals, choices, matched⟩ :=
            tail.exists_choice_of_mem_success lengthEquation tailMember
          exact ⟨selected, by simp [selectedMember], actuals, choices, matched⟩

end

/-! ### Nonempty failure ledgers -/

/-- A complete scan of a nonempty actual-type family produces either a
successful presentation or at least one failed actual. -/
theorem ActualTypeCandidateBranchesRel.successes_or_failures_nonempty
    {incoming : TypeSubst} {expected : Atom} {candidates : List Atom}
    {outputs : List TypeSubst} {failedActuals : List Atom}
    (scan : ActualTypeCandidateBranchesRel incoming expected candidates
      outputs failedActuals)
    (candidatesNonempty : candidates ≠ []) :
    outputs ≠ [] ∨ failedActuals ≠ [] := by
  cases scan with
  | nil => exact (candidatesNonempty rfl).elim
  | matched matched tail => exact Or.inl (by simp)
  | failed noMatch tail => exact Or.inr (by simp)

mutual

  /-- With one nonempty actual-type family for every formal, a complete
  argument branch scan cannot return both no successes and no diagnostics. -/
  theorem ArgumentCandidateListsBranchScanRel.successes_or_errors_nonempty
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming : TypeSubst}
      {outcome : ArgumentCandidateListsBranchOutcome}
      (scan : ArgumentCandidateListsBranchScanRel formals candidateLists
        position incoming outcome)
      (lengthEquation : formals.length = candidateLists.length)
      (familiesNonempty : ∀ family ∈ candidateLists, family ≠ []) :
      outcome.successes ≠ [] ∨ outcome.errors ≠ [] := by
    cases scan with
    | noArguments formals position incoming => exact Or.inl (by simp)
    | noFormal candidates remaining position incoming =>
        simp at lengthEquation
    | @step formal formals candidates remaining position incoming
        headSuccesses failedActuals tailOutcomes headScan tailScans =>
        have headNonempty : candidates ≠ [] :=
          familiesNonempty candidates (by simp)
        rcases headScan.successes_or_failures_nonempty headNonempty with
          headSucceeded | headFailed
        · cases headSuccesses with
          | nil => exact (headSucceeded rfl).elim
          | cons next nexts =>
              cases tailScans with
              | @cons _ _ _ _ _ tailOutcome tailOutcomes tailScan tailScans =>
                  have tailLength : formals.length = remaining.length := by
                    exact Nat.succ.inj lengthEquation
                  have tailFamilies : ∀ family ∈ remaining, family ≠ [] := by
                    intro family member
                    exact familiesNonempty family (by simp [member])
                  rcases tailScan.successes_or_errors_nonempty tailLength
                      tailFamilies with tailSucceeded | tailFailed
                  · exact Or.inl (by
                      intro empty
                      obtain ⟨selected, selectedMember⟩ :=
                        List.exists_mem_of_ne_nil tailOutcome.successes
                          tailSucceeded
                      have flattenedMember : selected ∈
                          (tailOutcome :: tailOutcomes).flatMap
                            (fun branch => branch.successes) :=
                        List.mem_flatMap.mpr
                          ⟨tailOutcome, by simp, selectedMember⟩
                      change (tailOutcome :: tailOutcomes).flatMap
                        (fun branch => branch.successes) = [] at empty
                      rw [empty] at flattenedMember
                      simp at flattenedMember)
                  · exact Or.inr (by
                      intro empty
                      obtain ⟨diagnostic, diagnosticMember⟩ :=
                        List.exists_mem_of_ne_nil tailOutcome.errors tailFailed
                      have flattenedMember : diagnostic ∈
                          (tailOutcome :: tailOutcomes).flatMap
                            (fun branch => branch.errors) :=
                        List.mem_flatMap.mpr
                          ⟨tailOutcome, by simp, diagnosticMember⟩
                      have flattenedEmpty := List.append_eq_nil_iff.mp empty |>.1
                      rw [flattenedEmpty] at flattenedMember
                      simp at flattenedMember)
        · exact Or.inr (by
            intro empty
            have currentEmpty : argumentTypeDiagnosticBlock (position + 1)
                (incoming.apply formal) failedActuals = [] :=
              List.append_eq_nil_iff.mp empty |>.2
            apply headFailed
            simpa [argumentTypeDiagnosticBlock] using
              congrArg List.length currentEmpty)
end

/-! ### Consistency-complete successful branches -/

mutual

  /-- A declared choice whose complete pointwise constraints have a model
  occurs in the successful output of the all-branches scan.  This is the
  converse companion of `exists_choice_of_mem_success`: it reflects semantic
  applicability into an already-complete branch derivation without rebuilding
  the classifier or choosing a preferred presentation syntax. -/
  theorem ArgumentCandidateListsBranchScanRel.exists_satisfied_success
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming : TypeSubst}
      {outcome : ArgumentCandidateListsBranchOutcome}
      (scan : ArgumentCandidateListsBranchScanRel formals candidateLists
        position incoming outcome)
      {actuals : List Atom}
      (choices : List.Forall₂ (fun actual candidates => actual ∈ candidates)
        actuals candidateLists)
      {valuation : String → Atom}
      (incomingNormal : incoming.Normal)
      (incomingSatisfied : TypeSubstSatisfied valuation incoming)
      (consistent : List.Forall₂
        (CorePlusR2TypeConsistent valuation) formals actuals) :
      ∃ output, output ∈ outcome.successes ∧ output.Normal ∧
        TypeSubstSatisfied valuation output := by
    cases scan with
    | noArguments formals position incoming =>
        cases choices
        cases consistent
        exact ⟨incoming, by simp, incomingNormal, incomingSatisfied⟩
    | noFormal candidates remaining position incoming =>
        cases choices with
        | cons => cases consistent
    | @step formal formals candidates remaining position incoming
        headSuccesses failedActuals tailOutcomes headScan tailScans =>
        cases choices with
        | @cons actual candidates actuals remaining actualMember tailChoices =>
            cases consistent with
            | @cons _ _ _ _ headConsistent tailConsistent =>
                obtain ⟨next, nextMember, nextNormal, nextSatisfied⟩ :=
                  headScan.exists_satisfied_output_of_mem actualMember
                    incomingNormal incomingSatisfied headConsistent
                obtain ⟨output, outputMember, outputNormal,
                    outputSatisfied⟩ :=
                  ArgumentCandidateListsBranchTailsRel.exists_satisfied_success
                    tailScans nextMember tailChoices nextNormal nextSatisfied
                      tailConsistent
                exact ⟨output, outputMember, outputNormal, outputSatisfied⟩

  /-- Tail companion selecting the recursive scan aligned with one satisfied
  successful presentation from the preceding argument position. -/
  theorem ArgumentCandidateListsBranchTailsRel.exists_satisfied_success
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming : List TypeSubst}
      {outcomes : List ArgumentCandidateListsBranchOutcome}
      (scans : ArgumentCandidateListsBranchTailsRel formals candidateLists
        position incoming outcomes)
      {next : TypeSubst} (nextMember : next ∈ incoming)
      {actuals : List Atom}
      (choices : List.Forall₂ (fun actual candidates => actual ∈ candidates)
        actuals candidateLists)
      {valuation : String → Atom}
      (nextNormal : next.Normal)
      (nextSatisfied : TypeSubstSatisfied valuation next)
      (consistent : List.Forall₂
        (CorePlusR2TypeConsistent valuation) formals actuals) :
      ∃ output,
        output ∈ outcomes.flatMap (fun outcome => outcome.successes) ∧
          output.Normal ∧ TypeSubstSatisfied valuation output := by
    cases scans with
    | nil => simp at nextMember
    | @cons formals candidateLists position headNext nexts outcome outcomes
        headScan tailScans =>
        rcases List.mem_cons.mp nextMember with rfl | tailMember
        · obtain ⟨output, outputMember, outputNormal, outputSatisfied⟩ :=
            headScan.exists_satisfied_success choices nextNormal
              nextSatisfied consistent
          exact ⟨output, by simp [outputMember], outputNormal,
            outputSatisfied⟩
        · obtain ⟨output, outputMember, outputNormal, outputSatisfied⟩ :=
            tailScans.exists_satisfied_success tailMember choices nextNormal
              nextSatisfied consistent
          exact ⟨output, by simp [outputMember], outputNormal,
            outputSatisfied⟩

end

/-! ### Branch-scan freshness algebra -/

/-- Every presentation emitted by one all-candidate argument scan avoids a
scope avoided by the incoming presentation, the formal, and every candidate.
This theorem is independent of which alternatives succeed. -/
theorem ActualTypeCandidateBranchesRel.outputs_avoid
    {incoming : TypeSubst} {expected : Atom}
    {candidates : List Atom} {outputs : List TypeSubst}
    {failedActuals : List Atom} {forbidden : List String}
    (scan : ActualTypeCandidateBranchesRel incoming expected candidates
      outputs failedActuals)
    (incomingAvoids : incoming.Avoids forbidden)
    (expectedAvoids : AtomAvoids expected forbidden)
    (candidatesAvoid : AtomsAvoid candidates forbidden) :
    ∀ output ∈ outputs, output.Avoids forbidden := by
  induction scan with
  | nil => simp
  | @matched candidate candidates output outputs failedActuals
      matched tail inductionHypothesis =>
      intro selected member
      rcases List.mem_cons.mp member with rfl | tailMember
      · exact corePlusR2TypePresentationMatch_output_avoids matched
          incomingAvoids expectedAvoids
          (candidatesAvoid.atom (by simp))
      · have tailCandidatesAvoid : AtomsAvoid candidates forbidden := by
          intro name occurrence
          exact candidatesAvoid name (by
            simp [TypeSubst.typeVarsList, occurrence])
        exact inductionHypothesis tailCandidatesAvoid selected tailMember
  | @failed candidate candidates outputs failedActuals _ tail
      inductionHypothesis =>
      intro selected member
      have tailCandidatesAvoid : AtomsAvoid candidates forbidden := by
        intro name occurrence
        exact candidatesAvoid name (by
          simp [TypeSubst.typeVarsList, occurrence])
      exact inductionHypothesis tailCandidatesAvoid selected member

mutual

  /-- Every successful presentation of a complete branch-valued argument
  scan preserves an arbitrary private-name avoidance scope. -/
  theorem ArgumentCandidateListsBranchScanRel.successes_avoid
      {formals : List Atom} {candidateLists : List (List Atom)}
      {position : Nat} {incoming : TypeSubst}
      {outcome : ArgumentCandidateListsBranchOutcome}
      {forbidden : List String}
      (scan : ArgumentCandidateListsBranchScanRel formals candidateLists
        position incoming outcome)
      (incomingAvoids : incoming.Avoids forbidden)
      (formalsAvoid : AtomsAvoid formals forbidden)
      (candidatesAvoid : AtomsAvoid candidateLists.flatten forbidden) :
      ∀ output ∈ outcome.successes, output.Avoids forbidden := by
    cases scan with
    | noArguments formals position incoming =>
        simpa using incomingAvoids
    | noFormal candidates remaining position incoming =>
        simpa using incomingAvoids
    | @step formal formals candidates remaining position incoming
        headSuccesses failedActuals tailOutcomes headScan tailScans =>
        have headAvoids : ∀ output ∈ headSuccesses,
            output.Avoids forbidden :=
          headScan.outputs_avoid incomingAvoids
            (formalsAvoid.atom (by simp))
            (fun name occurrence => by
              obtain ⟨candidate, candidateMember, atomOccurrence⟩ :=
                exists_mem_of_mem_typeVarsList occurrence
              apply candidatesAvoid name
              exact typeVars_mem_typeVarsList_of_mem
                (List.mem_flatten.mpr
                  ⟨candidates, by simp, candidateMember⟩)
                name atomOccurrence)
        have tailFormalsAvoid : AtomsAvoid formals forbidden := by
          intro name occurrence
          exact formalsAvoid name (by
            simp [TypeSubst.typeVarsList, occurrence])
        have remainingAvoid : AtomsAvoid remaining.flatten forbidden := by
          intro name occurrence
          obtain ⟨candidate, candidateMember, atomOccurrence⟩ :=
            exists_mem_of_mem_typeVarsList occurrence
          apply candidatesAvoid name
          exact typeVars_mem_typeVarsList_of_mem
            (by
              simp only [List.flatten_cons, List.mem_append]
              exact Or.inr candidateMember)
            name atomOccurrence
        have tailAvoids :=
          ArgumentCandidateListsBranchTailsRel.successes_avoid tailScans
            headAvoids tailFormalsAvoid remainingAvoid
        intro output member
        exact tailAvoids output (by simpa using member)

  /-- Pointwise tail scans preserve the same avoidance scope for every
  branch entering the recursive suffix. -/
  theorem ArgumentCandidateListsBranchTailsRel.successes_avoid
      {formals : List Atom} {remaining : List (List Atom)}
      {position : Nat} {incoming : List TypeSubst}
      {outcomes : List ArgumentCandidateListsBranchOutcome}
      {forbidden : List String}
      (scans : ArgumentCandidateListsBranchTailsRel formals remaining
        position incoming outcomes)
      (incomingAvoids : ∀ presentation ∈ incoming,
        presentation.Avoids forbidden)
      (formalsAvoid : AtomsAvoid formals forbidden)
      (candidatesAvoid : AtomsAvoid remaining.flatten forbidden) :
      ∀ output ∈ outcomes.flatMap (fun outcome => outcome.successes),
        output.Avoids forbidden := by
    cases scans with
    | nil => simp
    | @cons formals remaining position next nexts outcome outcomes
        head tail =>
        intro output member
        rcases List.mem_flatMap.mp member with
          ⟨branchOutcome, branchMember, outputMember⟩
        rcases List.mem_cons.mp branchMember with rfl | tailMember
        · exact ArgumentCandidateListsBranchScanRel.successes_avoid head
            (incomingAvoids next (by simp)) formalsAvoid candidatesAvoid
            output outputMember
        · exact ArgumentCandidateListsBranchTailsRel.successes_avoid tail
            (fun presentation presentationMember => incomingAvoids
              presentation (by simp [presentationMember]))
            formalsAvoid candidatesAvoid output
            (List.mem_flatMap.mpr
              ⟨branchOutcome, tailMember, outputMember⟩)

end

/-! ## Expected-return branch scan -/

/-- One rejected expected-return check.  The actual type is the declared
return after applying the private argument presentation that reached this
branch. -/
structure ExpectedReturnDiagnostic where
  expected : Atom
  actual : Atom
  deriving DecidableEq

/-- Result of filtering the complete ordered argument-presentation branch
list through the published expected-return conjunct.  The first surviving
presentation commits the function candidate; mismatches before it remain in
presentation order. -/
structure ExpectedReturnBranchOutcome where
  selected : Option TypeSubst
  errors : List ExpectedReturnDiagnostic

/-- Executable-independent expected-return filtering over the complete
argument-presentation branch list.  Matching uses the raw declared return
under each threaded private presentation, so syntactic `Atom` and
`%Undefined%` wildcards are decided before presentation application. -/
inductive ExpectedReturnBranchScanRel (expected returnType : Atom) :
    List TypeSubst → ExpectedReturnBranchOutcome → Prop where
  | nil : ExpectedReturnBranchScanRel expected returnType [] ⟨none, []⟩
  | matched {incoming output : TypeSubst} {branches : List TypeSubst} :
      CorePlusR2TypePresentationMatchRel incoming expected returnType output →
      ExpectedReturnBranchScanRel expected returnType (incoming :: branches)
        ⟨some output, []⟩
  | failed {incoming : TypeSubst} {branches : List TypeSubst}
      {tail : ExpectedReturnBranchOutcome} :
      (∀ output,
        ¬CorePlusR2TypePresentationMatchRel incoming expected returnType
          output) →
      ExpectedReturnBranchScanRel expected returnType branches tail →
      ExpectedReturnBranchScanRel expected returnType (incoming :: branches)
        ⟨tail.selected,
          { expected := expected
            actual := incoming.apply returnType } :: tail.errors⟩

/-- A selected return outcome identifies the incoming argument presentation
and the exact return constraint that produced the committed output. -/
theorem ExpectedReturnBranchScanRel.exists_match_of_selected
    {expected returnType : Atom} {branches : List TypeSubst}
    {outcome : ExpectedReturnBranchOutcome} {output : TypeSubst}
    (scan : ExpectedReturnBranchScanRel expected returnType branches outcome)
    (selected : outcome.selected = some output) :
    ∃ incoming, incoming ∈ branches ∧
      CorePlusR2TypePresentationMatchRel incoming expected returnType output := by
  induction scan with
  | nil => simp at selected
  | @matched incoming matchedOutput branches matched =>
      have outputEquation : matchedOutput = output := by simpa using selected
      subst output
      exact ⟨incoming, by simp, matched⟩
  | @failed incoming branches tail noMatch tailScan inductionHypothesis =>
      obtain ⟨selectedIncoming, member, matched⟩ :=
        inductionHypothesis selected
      exact ⟨selectedIncoming, by simp [member], matched⟩

/-- If any incoming branch has a model for the expected-return constraint,
the ordered return scan selects some branch.  Earlier matching branches may
commit first, so this theorem deliberately promises existence rather than the
identity of the selected presentation. -/
theorem ExpectedReturnBranchScanRel.exists_selected_of_consistent_branch
    {expected returnType : Atom} {branches : List TypeSubst}
    {outcome : ExpectedReturnBranchOutcome}
    (scan : ExpectedReturnBranchScanRel expected returnType branches outcome)
    {branch : TypeSubst} (member : branch ∈ branches)
    {valuation : String → Atom}
    (normal : branch.Normal)
    (satisfied : TypeSubstSatisfied valuation branch)
    (consistent : CorePlusR2TypeConsistent valuation expected returnType) :
    ∃ output, outcome.selected = some output := by
  induction scan with
  | nil => simp at member
  | @matched incoming output branches matched =>
      exact ⟨output, rfl⟩
  | @failed incoming branches tail noMatch tailScan inductionHypothesis =>
      rcases List.mem_cons.mp member with rfl | tailMember
      · obtain ⟨output, derivation, _outputNormal, _outputSatisfied⟩ :=
          CorePlusR2TypePresentationMatchRel.exists_of_satisfied
            normal satisfied expected returnType consistent
        exact (noMatch output derivation).elim
      · exact inductionHypothesis tailMember

/-- Exhausting a nonempty return-branch list records at least one return
diagnostic.  Each rejected head contributes exactly one entry before the
tail, while a matched head cannot have `selected = none`. -/
theorem ExpectedReturnBranchScanRel.errors_nonempty_of_selected_none
    {expected returnType : Atom} {branches : List TypeSubst}
    {outcome : ExpectedReturnBranchOutcome}
    (scan : ExpectedReturnBranchScanRel expected returnType branches outcome)
    (branchesNonempty : branches ≠ [])
    (notSelected : outcome.selected = none) :
    outcome.errors ≠ [] := by
  cases scan with
  | nil => exact (branchesNonempty rfl).elim
  | matched matched => simp at notSelected
  | failed noMatch tail => simp

/-- A selected expected-return branch preserves every private-name scope
avoided by all incoming branch presentations and by the raw expected/return
constraint.  Failed prefixes do not affect the selected presentation. -/
theorem ExpectedReturnBranchScanRel.selected_avoids
    {expected returnType : Atom} {branches : List TypeSubst}
    {outcome : ExpectedReturnBranchOutcome} {forbidden : List String}
    (scan : ExpectedReturnBranchScanRel expected returnType branches outcome)
    (branchesAvoid : ∀ presentation ∈ branches,
      presentation.Avoids forbidden)
    (expectedAvoid : AtomAvoids expected forbidden)
    (returnAvoid : AtomAvoids returnType forbidden)
    {selected : TypeSubst} (selectedEquation : outcome.selected = some selected) :
    selected.Avoids forbidden := by
  induction scan with
  | nil => simp at selectedEquation
  | @matched incoming output branches matched =>
      cases selectedEquation
      exact corePlusR2TypePresentationMatch_output_avoids matched
        (branchesAvoid incoming (by simp)) expectedAvoid returnAvoid
  | @failed incoming branches tail noMatch tailScan inductionHypothesis =>
      exact inductionHypothesis
        (fun presentation member =>
          branchesAvoid presentation (by simp [member]))
        selectedEquation

/-- The exact scan together with the one finite-scope contract used by the
localization and observational-inertness theorems.  Candidate lists are
flattened only to reuse `AtomsAvoid`; their order and grouping remain in the
scan relation. -/
def FreshArgumentCandidateListsScanRel
    (forbidden : List String) (formals : List Atom)
    (candidateLists : List (List Atom)) (position : Nat)
    (incoming : TypeSubst) (outcome : ArgumentCandidateListsScanOutcome) :
    Prop :=
  incoming.Avoids forbidden ∧
    AtomsAvoid formals forbidden ∧
    AtomsAvoid candidateLists.flatten forbidden ∧
    ArgumentCandidateListsScanRel formals candidateLists
      position incoming outcome

/-! ## Boundary examples -/

private theorem distinctSymbolsDoNotMatch
    {incoming output : TypeSubst} {left right : String}
    (leftNotUndefined : left ≠ "%Undefined%")
    (rightNotUndefined : right ≠ "%Undefined%")
    (leftNotAtom : left ≠ "Atom") (rightNotAtom : right ≠ "Atom")
    (distinct : left ≠ right) :
    ¬CorePlusR2TypePresentationMatchRel incoming
      (.symbol left) (.symbol right) output := by
  intro matched
  have reduced := matched.reduced_of_nonWildcard
    (by simpa [Atom.undefinedType]) (by simpa [Atom.undefinedType])
    (by simpa [Atom.atomType]) (by simpa [Atom.atomType])
  obtain ⟨resolvedLeft, resolvedRight, leftEquation, rightEquation, applied⟩ :=
    reduced.ordinary_of_nonUndefined
      (by simpa [Atom.undefinedType]) (by simpa [Atom.undefinedType])
      (by simp [ReducedTypeLeafShape])
  simp [TypeSubst.apply] at leftEquation rightEquation
  rw [← leftEquation, ← rightEquation] at applied
  exact AppliedReducedTypeMatchRel.no_distinct_symbols distinct applied

private theorem A_matches_A :
    CorePlusR2TypePresentationMatchRel []
      (.symbol "A") (.symbol "A") [] := by
  exact .reduced
    (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
    (by simp [Atom.atomType]) (by simp [Atom.atomType])
    (.ordinary
      (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
      (by simp [ReducedTypeLeafShape])
      (TypeSubst.apply_empty _) (TypeSubst.apply_empty _)
      (.identical [] (.symbol "A")))

/-- Positive return-gate canary: the published `%Undefined%` expected type
accepts the first private branch without changing its presentation. -/
theorem expected_return_branch_accepts_undefined :
    ExpectedReturnBranchScanRel Atom.undefinedType (.symbol "R") [[]]
      ⟨some [], []⟩ := by
  exact .matched (.undefinedLeft [] (.symbol "R"))

/-- Negative return-gate canary: distinct concrete return types cannot
fabricate a successful presentation, and the rejected displayed return is
retained. -/
theorem expected_return_branch_rejects_distinct_symbols :
    ExpectedReturnBranchScanRel (.symbol "B") (.symbol "C") [[]]
      ⟨none, [{ expected := .symbol "B", actual := .symbol "C" }]⟩ := by
  have rejected : ExpectedReturnBranchScanRel (.symbol "B") (.symbol "C")
      [[]]
      ⟨none,
        [{ expected := .symbol "B",
           actual := TypeSubst.apply [] (.symbol "C") }]⟩ := by
    exact ExpectedReturnBranchScanRel.failed
      (incoming := []) (branches := [])
      (tail := ⟨none, []⟩)
      (fun output => distinctSymbolsDoNotMatch (output := output)
        (by decide) (by decide) (by decide) (by decide) (by decide))
      (.nil (expected := .symbol "B") (returnType := .symbol "C"))
  simpa [TypeSubst.apply] using rejected

/-- Positive: the first matching `A` selects the presentation, while the
failed `B` before it and failed `C` after it both remain latent in declaration
order. -/
theorem ordered_actual_scan_selects_first_success :
    ActualTypeCandidateScanRel [] (.symbol "A")
      [.symbol "B", .symbol "A", .symbol "C"]
      (.success [] [.symbol "B", .symbol "C"]) := by
  apply ActualTypeCandidateScanRel.firstSuccess
      (before := [.symbol "B"]) (candidate := .symbol "A")
      (suffix := [.symbol "C"]) (suffixClassifications := [.failed])
  · intro earlier member output
    simp at member
    subst earlier
    exact distinctSymbolsDoNotMatch (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact A_matches_A
  · exact .cons (.failed fun output =>
      distinctSymbolsDoNotMatch (by decide) (by decide)
        (by decide) (by decide) (by decide)) .nil

/-- Negative: when every candidate fails, every actual type is retained in
declaration order. -/
theorem ordered_actual_scan_all_failed_keeps_all :
    ActualTypeCandidateScanRel [] (.symbol "A")
      [.symbol "B", .symbol "C"]
      (.failure [.symbol "B", .symbol "C"]) := by
  apply ActualTypeCandidateScanRel.allFailed
  intro candidate member output
  simp at member
  rcases member with rfl | rfl
  · exact distinctSymbolsDoNotMatch (by decide) (by decide)
      (by decide) (by decide) (by decide)
  · exact distinctSymbolsDoNotMatch (by decide) (by decide)
      (by decide) (by decide) (by decide)

/-- Negative candidate outcome order: when a later argument fails, its whole
diagnostic block precedes latent failures from earlier successful arguments;
within each block, actual-type declaration order is unchanged. -/
theorem later_argument_failure_precedes_earlier_latent_error :
    ArgumentCandidateListsScanRel
      [.symbol "A", .symbol "A"]
      [[.symbol "A", .symbol "C"], [.symbol "B"]]
      0 []
      (.failure
        [{ position := 2, expected := .symbol "A", actual := .symbol "B" },
         { position := 1, expected := .symbol "A", actual := .symbol "C" }]) := by
  have first : ActualTypeCandidateScanRel [] (.symbol "A")
      [.symbol "A", .symbol "C"]
      (.success [] [.symbol "C"]) := by
    exact ActualTypeCandidateScanRel.firstSuccess
      (before := []) (candidate := .symbol "A") (suffix := [.symbol "C"])
      (suffixClassifications := [.failed]) (by simp) A_matches_A
      (.cons (.failed fun output =>
        distinctSymbolsDoNotMatch (by decide) (by decide)
          (by decide) (by decide) (by decide)) .nil)
  have second : ActualTypeCandidateScanRel [] (.symbol "A")
      [.symbol "B"] (.failure [.symbol "B"]) := by
    exact ActualTypeCandidateScanRel.allFailed fun candidate member output => by
      simp at member
      subst candidate
      exact distinctSymbolsDoNotMatch (by decide) (by decide)
        (by decide) (by decide) (by decide)
  have tail : ArgumentCandidateListsScanRel [.symbol "A"]
      [[.symbol "B"]] 1 []
      (.failure
        [{ position := 2, expected := .symbol "A", actual := .symbol "B" }]) := by
    simpa [argumentTypeDiagnosticBlock] using
      ArgumentCandidateListsScanRel.stepFailure (formals := [])
        (remaining := []) second
  simpa [ArgumentCandidateListsScanOutcome.appendEarlierErrors,
    argumentTypeDiagnosticBlock] using
    ArgumentCandidateListsScanRel.stepSuccess first tail

/-- Positive freshness canary: a closed one-argument scan satisfies the same
scope contract consumed by localization. -/
theorem closed_scan_is_fresh :
    FreshArgumentCandidateListsScanRel ["public"]
      [.symbol "A"] [[.symbol "A"]] 0 [] (.success [] []) := by
  refine ⟨TypeSubst.avoids_empty _, ?_, ?_, ?_⟩
  · simp [AtomsAvoid, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · simp [AtomsAvoid, TypeSubst.typeVars, TypeSubst.typeVarsList]
  · have current : ActualTypeCandidateScanRel [] (.symbol "A")
        [.symbol "A"] (.success [] []) := by
      exact ActualTypeCandidateScanRel.firstSuccess
        (before := []) (candidate := .symbol "A") (suffix := [])
        (suffixClassifications := []) (by simp) A_matches_A .nil
    have tail : ArgumentCandidateListsScanRel [] [] 1 []
        (.success [] []) :=
      ArgumentCandidateListsScanRel.noArguments [] 1 []
    simpa [ArgumentCandidateListsScanOutcome.appendEarlierErrors,
      argumentTypeDiagnosticBlock] using
      ArgumentCandidateListsScanRel.stepSuccess current tail

/-- Positive branch canary: the successful `A` presentation is retained and
the failing `B` alternative remains latent in the same outcome. -/
theorem branch_scan_retains_success_and_failure :
    ArgumentCandidateListsBranchScanRel [.symbol "A"]
      [[.symbol "A", .symbol "B"]] 0 []
      ⟨[[]],
        [{ position := 1, expected := .symbol "A", actual := .symbol "B" }]⟩ := by
  have candidates : ActualTypeCandidateBranchesRel [] (.symbol "A")
      [.symbol "A", .symbol "B"] [[]] [.symbol "B"] := by
    apply ActualTypeCandidateBranchesRel.matched A_matches_A
    apply ActualTypeCandidateBranchesRel.failed
    · intro output
      exact distinctSymbolsDoNotMatch (by decide) (by decide)
        (by decide) (by decide) (by decide)
    · exact .nil
  have tails : ArgumentCandidateListsBranchTailsRel [] [] 1
      [[]] [⟨[[]], []⟩] :=
    .cons (ArgumentCandidateListsBranchScanRel.noArguments [] 1 []) .nil
  simpa [argumentTypeDiagnosticBlock] using
    ArgumentCandidateListsBranchScanRel.step candidates tails

/-- Negative branch canary: a distinct ground type cannot be fabricated as a
successful presentation. -/
theorem branch_scan_distinct_symbol_has_no_success
    (outcome : ArgumentCandidateListsBranchOutcome)
    (scan : ArgumentCandidateListsBranchScanRel [.symbol "A"]
      [[.symbol "B"]] 0 [] outcome) :
    outcome.successes = [] := by
  cases scan with
  | step candidates tails =>
      cases candidates with
      | matched headMatch tail =>
          exact False.elim
            (distinctSymbolsDoNotMatch (by decide) (by decide)
              (by decide) (by decide) (by decide) headMatch)
      | failed noMatch tail =>
          cases tail
          cases tails
          rfl

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Selection
