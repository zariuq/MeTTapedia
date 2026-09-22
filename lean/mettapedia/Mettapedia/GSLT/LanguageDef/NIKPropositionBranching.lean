import Mettapedia.GSLT.LanguageDef.NIKServiceResumption
import Mettapedia.GSLT.LanguageDef.NIKPolarizedAuthority
import Mettapedia.GSLT.LanguageDef.InferenceSearch
import Mettapedia.TypeTheory.Authority

/-!
# Evidence-conditioned proposition branches

The proposition's meaning is fixed at an explicit scope. Accepted support
selects the then body; accepted evidence for its semantic negation selects
the else body. These are the existing authority outcomes, not three-valued
truth. Failed submitted evidence and a bounded search with no proof retain
their attempted inputs as residuals. Neither establishes semantic negation.

The service adapter retains all four NIK request faces and checks the exact
returned claim. A native operation still needs its original source-admission
premise. The adapter observes positive acceptance in the selected polarity;
an independently supplied complete decision kernel has a separate exact
specialization, where its negative decision really does justify else.

Effectful bodies use the existing contextual free programs and isolated-world
handler. A residual runs neither body and retains state, branch and reason.
The finite SAT controls use actual assignment and complete-refutation
checkers. No global proof search, Need policy, textual syntax, C refinement
or authored backend is supplied here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NIKPropositionBranching

open Mettapedia.TypeTheory.AuthorityTheory
open Mettapedia.GSLT.LanguageDef.KernelAuthority
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.GSLT.LanguageDef.NIKPolarizedAuthority (Polarity)
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe uScope uClaim uEvidence uBoundary uIncomplete uState uAnswer uIntent

variable {Scope : Type uScope} {Claim : Type uClaim}

/-- Scope may retain a theory, context, valuation or revision. A different
scope is not silently supplied by a successful checker response. -/
abbrev target (meaning : Scope → Claim → Prop) (scope : Scope) (side : Polarity) :
    AdmissionObject.{uClaim} where
  Carrier := Claim
  Meaning claim := match side with
    | .support => meaning scope claim
    | .refutation => ¬ meaning scope claim

/-- The actual packed request and its original operation source premise.
The returned-value equation binds it to this exact scoped proposition. -/
structure Accepted (meaning : Scope → Claim → Prop) (scope : Scope)
    (claim : Claim) (side : Polarity) where
  submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side)
  input : NIKServiceInvocation.InputAdmission submitted.2
  returned : (NIKServiceResumption.invoke submitted).acceptedValue = some claim

theorem Accepted.meaning {meaning : Scope → Claim → Prop} {scope : Scope}
    {claim : Claim} {side : Polarity} (accepted : Accepted.{uScope, uClaim, uEvidence}
      meaning scope claim side) : (target meaning scope side).Meaning claim :=
  NIKServiceInvocation.accepted_meaning accepted.submitted.2 accepted.input accepted.returned

/-- This authority is derived from existing NIK soundness; it adds no new
checker and no claim that either polarity can always be produced. -/
def serviceAuthority (meaning : Scope → Claim → Prop) (scope : Scope) : Authority Claim where
  Holds := meaning scope
  Evidence claim := Accepted.{uScope, uClaim, uEvidence} meaning scope claim .support
  Obstruction claim := Accepted.{uScope, uClaim, uEvidence} meaning scope claim .refutation
  evidenceSound _ accepted := accepted.meaning
  obstructionSound _ accepted := accepted.meaning

/-- Failed evidence retains both the requested claim and the submitted
service request, including when an operation returns a different claim.
Its checked response is recoverable by invocation, not replaced by False. -/
abbrev ServiceResidual (meaning : Scope → Claim → Prop) (scope : Scope) :=
  Claim × (Σ side : Polarity, NIKServiceResumption.PackedRequest.{uClaim, uEvidence}
    (target meaning scope side))

def checkSubmission [DecidableEq Claim] (meaning : Scope → Claim → Prop)
    (scope : Scope) (claim : Claim) (side : Polarity)
    (submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side))
    (input : NIKServiceInvocation.InputAdmission submitted.2) :
    Outcome ((serviceAuthority meaning scope).Evidence claim)
      ((serviceAuthority meaning scope).Obstruction claim) PEmpty.{1}
      (ServiceResidual.{uScope, uClaim, uEvidence} meaning scope) :=
  match side with
  | .support =>
      if accepted : (NIKServiceResumption.invoke submitted).acceptedValue = some claim then
        .established ⟨submitted, input, accepted⟩
      else .incomplete (claim, ⟨.support, submitted⟩)
  | .refutation =>
      if accepted : (NIKServiceResumption.invoke submitted).acceptedValue = some claim then
        .refuted ⟨submitted, input, accepted⟩
      else .incomplete (claim, ⟨.refutation, submitted⟩)

theorem checkSubmission_asBool [DecidableEq Claim] (meaning : Scope → Claim → Prop)
    (scope : Scope) (claim : Claim) (side : Polarity)
    (submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side))
    (input : NIKServiceInvocation.InputAdmission submitted.2) :
    (checkSubmission meaning scope claim side submitted input).asBool =
      if (NIKServiceResumption.invoke submitted).acceptedValue = some claim then
        some (match side with | .support => true | .refutation => false)
      else none := by
  cases side <;> simp only [checkSubmission] <;> split <;> rfl

theorem checkSubmission_rejected [DecidableEq Claim] (meaning : Scope → Claim → Prop)
    (scope : Scope) (claim : Claim) (side : Polarity)
    (submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side))
    (input : NIKServiceInvocation.InputAdmission submitted.2)
    (rejected : (NIKServiceResumption.invoke submitted).acceptedValue = none) :
    checkSubmission meaning scope claim side submitted input = .incomplete (claim, ⟨side, submitted⟩) := by
  cases side <;> simp [checkSubmission, rejected]

theorem checkSubmission_wrong_claim [DecidableEq Claim] (meaning : Scope → Claim → Prop)
    (scope : Scope) (claim other : Claim) (side : Polarity)
    (submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side))
    (input : NIKServiceInvocation.InputAdmission submitted.2)
    (returned : (NIKServiceResumption.invoke submitted).acceptedValue = some other)
    (different : other ≠ claim) :
    checkSubmission meaning scope claim side submitted input = .incomplete (claim, ⟨side, submitted⟩) := by
  cases side <;> simp [checkSubmission, returned, different]

/-! ## Sound branching and exact complete decisions -/

theorem established_meaning {Judgment : Type*} (authority : Authority Judgment)
    {judgment : Judgment} {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    (outcome : Outcome (authority.Evidence judgment) (authority.Obstruction judgment)
      Boundary Incomplete) (positive : outcome.asBool = some true) : authority.Holds judgment := by
  obtain ⟨evidence, rfl⟩ := outcome.asBool_eq_true_iff.mp positive
  exact authority.evidenceSound judgment evidence

theorem refuted_meaning {Judgment : Type*} (authority : Authority Judgment)
    {judgment : Judgment} {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
    (outcome : Outcome (authority.Evidence judgment) (authority.Obstruction judgment)
      Boundary Incomplete) (negative : outcome.asBool = some false) : ¬ authority.Holds judgment := by
  obtain ⟨obstruction, rfl⟩ := outcome.asBool_eq_false_iff.mp negative
  exact authority.obstructionSound judgment obstruction

theorem checkSubmission_then_sound [DecidableEq Claim] (meaning : Scope → Claim → Prop)
    (scope : Scope) (claim : Claim) (side : Polarity)
    (submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side))
    (input : NIKServiceInvocation.InputAdmission submitted.2)
    (positive : (checkSubmission meaning scope claim side submitted input).asBool = some true) :
    meaning scope claim :=
  established_meaning (serviceAuthority meaning scope)
    (checkSubmission meaning scope claim side submitted input) positive

theorem checkSubmission_else_sound [DecidableEq Claim] (meaning : Scope → Claim → Prop)
    (scope : Scope) (claim : Claim) (side : Polarity)
    (submitted : NIKServiceResumption.PackedRequest.{uClaim, uEvidence} (target meaning scope side))
    (input : NIKServiceInvocation.InputAdmission submitted.2)
    (negative : (checkSubmission meaning scope claim side submitted input).asBool = some false) :
    ¬ meaning scope claim :=
  refuted_meaning (serviceAuthority meaning scope)
    (checkSubmission meaning scope claim side submitted input) negative

/-- Independent checkers cannot provide both polarities at this same scope
and claim. This uses semantic soundness, not an arbitration priority. -/
theorem accepted_polarities_incompatible {meaning : Scope → Claim → Prop} {scope : Scope}
    {claim : Claim} (positive : Accepted.{uScope, uClaim, uEvidence}
      meaning scope claim .support) (negative : Accepted.{uScope, uClaim, uEvidence}
      meaning scope claim .refutation) : False :=
  negative.meaning positive.meaning

/-- The actual response of a fixed direct decision, with its verdict bound.
This is not a guessed Boolean or a proof-search result. -/
abbrev DecisionEvidence {meaning : Scope → Claim → Prop} (scope : Scope)
    (kernel : Checker.DecisionKernel Claim (meaning scope)) (claim : Claim) (value : Bool) :=
  { response : NIKServiceInvocation.Response
      (NIKServiceInvocation.Request.directDecision.{uClaim, 0} (target := target meaning scope .support)
        (kernel := kernel) claim) //
    response = NIKServiceInvocation.invoke (.directDecision
      (target := target meaning scope .support) (kernel := kernel) claim) ∧
      response = .decided value }

def decisionAuthority (meaning : Scope → Claim → Prop) (scope : Scope)
    (kernel : Checker.DecisionKernel Claim (meaning scope)) : Authority Claim where
  Holds := meaning scope
  Evidence claim := DecisionEvidence scope kernel claim true
  Obstruction claim := DecisionEvidence scope kernel claim false
  evidenceSound claim evidence :=
    (NIKServiceInvocation.direct_decision_true_iff
      (target := target meaning scope .support) kernel claim).mp
      (evidence.2.1.symm.trans evidence.2.2)
  obstructionSound claim evidence :=
    (NIKServiceInvocation.direct_decision_false_iff
      (target := target meaning scope .support) kernel claim).mp
      (evidence.2.1.symm.trans evidence.2.2)

def decideOutcome (meaning : Scope → Claim → Prop) (scope : Scope)
    (kernel : Checker.DecisionKernel Claim (meaning scope)) (claim : Claim) :
    Outcome ((decisionAuthority meaning scope kernel).Evidence claim)
      ((decisionAuthority meaning scope kernel).Obstruction claim) PEmpty.{1} PEmpty.{1} :=
  if positive : kernel.decide claim = true then
    .established ⟨.decided true, by simp [NIKServiceInvocation.invoke, positive], rfl⟩
  else
    .refuted ⟨.decided false, by simp [NIKServiceInvocation.invoke, positive], rfl⟩

theorem decideOutcome_asBool (meaning : Scope → Claim → Prop) (scope : Scope)
    (kernel : Checker.DecisionKernel Claim (meaning scope)) (claim : Claim) :
    (decideOutcome meaning scope kernel claim).asBool = some (kernel.decide claim) := by
  cases answer : kernel.decide claim <;> simp [decideOutcome, answer, Outcome.asBool]

theorem decideOutcome_true_iff (meaning : Scope → Claim → Prop) (scope : Scope)
    (kernel : Checker.DecisionKernel Claim (meaning scope)) (claim : Claim) :
    (decideOutcome meaning scope kernel claim).asBool = some true ↔ meaning scope claim := by
  rw [decideOutcome_asBool, Option.some.injEq, kernel.correct]

theorem decideOutcome_false_iff (meaning : Scope → Claim → Prop) (scope : Scope)
    (kernel : Checker.DecisionKernel Claim (meaning scope)) (claim : Claim) :
    (decideOutcome meaning scope kernel claim).asBool = some false ↔ ¬ meaning scope claim := by
  rw [decideOutcome_asBool, Option.some.injEq, ← kernel.correct]
  cases kernel.decide claim <;> simp

/-! ## Bounded authored search remains an attempt -/

open Mettapedia.OSLF.MeTTaIL.Syntax
open InferenceChecker

/-- The two actual authored goals may contain their theory/context as data.
Soundness below is an independent interpretation of these exact goals. -/
abbrev CheckedRaw (definition : ValidatedCalculusLanguageDef) (goal : Pattern) :=
  { proof : RawProof // checkRaw definition goal proof = true }

def searchAuthority (meaning : Scope → Claim → Prop) (scope : Scope)
    (definition : ValidatedCalculusLanguageDef) (goal : Polarity → Claim → Pattern)
    (sound : ∀ side claim proof, checkRaw definition (goal side claim) proof = true →
      (target meaning scope side).Meaning claim) : Authority Claim where
  Holds := meaning scope
  Evidence claim := CheckedRaw definition (goal .support claim)
  Obstruction claim := CheckedRaw definition (goal .refutation claim)
  evidenceSound claim proof := sound .support claim proof.1 proof.2
  obstructionSound claim proof := sound .refutation claim proof.1 proof.2

/-- The exact submitted search judgment and its original result. This does
not claim to retain an execution history or a fuel budget. -/
abbrev SearchResidual (Claim : Type uClaim) :=
  Claim × Polarity × Pattern × InferenceSearch.SearchOutcome

/-- Even a supplied `found` is checked. Closed traversal and exhausted fuel
retain distinct source outcomes, neither interpreted as evidence for else. -/
def checkSearch (definition : ValidatedCalculusLanguageDef)
    (goal : Polarity → Claim → Pattern) (claim : Claim) (side : Polarity)
    (result : InferenceSearch.SearchOutcome) :
    Outcome (CheckedRaw definition (goal .support claim))
      (CheckedRaw definition (goal .refutation claim)) PEmpty.{1} (SearchResidual Claim) :=
  match side, result with
  | .support, .found proof =>
      if checked : checkRaw definition (goal .support claim) proof = true then
        .established ⟨proof, checked⟩ else .incomplete (claim, side, goal side claim, result)
  | .refutation, .found proof =>
      if checked : checkRaw definition (goal .refutation claim) proof = true then
        .refuted ⟨proof, checked⟩ else .incomplete (claim, side, goal side claim, result)
  | _, .closed | _, .exhausted => .incomplete (claim, side, goal side claim, result)

theorem checkSearch_closed (definition : ValidatedCalculusLanguageDef)
    (goal : Polarity → Claim → Pattern) (claim : Claim) (side : Polarity) :
    checkSearch definition goal claim side .closed =
      .incomplete (claim, side, goal side claim, .closed) := by
  cases side <;> rfl

theorem checkSearch_exhausted (definition : ValidatedCalculusLanguageDef)
    (goal : Polarity → Claim → Pattern) (claim : Claim) (side : Polarity) :
    checkSearch definition goal claim side .exhausted =
      .incomplete (claim, side, goal side claim, .exhausted) := by
  cases side <;> rfl

theorem checkSearch_rejected (definition : ValidatedCalculusLanguageDef)
    (goal : Polarity → Claim → Pattern) (claim : Claim) (side : Polarity) (proof : RawProof)
    (rejected : checkRaw definition (goal side claim) proof = false) :
    checkSearch definition goal claim side (.found proof) =
      .incomplete (claim, side, goal side claim, .found proof) := by
  cases side <;> simp [checkSearch, rejected]

theorem search_zero_residual (definition : ValidatedCalculusLanguageDef)
    (goal : Polarity → Claim → Pattern) (claim : Claim) (side : Polarity) :
    checkSearch definition goal claim side
      (InferenceSearch.searchGoal definition 0 (goal side claim)) =
      .incomplete (claim, side, goal side claim, .exhausted) := by
  simp only [InferenceSearch.searchGoal]
  exact checkSearch_exhausted definition goal claim side

theorem search_found_checked (definition : ValidatedCalculusLanguageDef)
    (goal : Polarity → Claim → Pattern) (claim : Claim) (side : Polarity) (fuel : Nat)
    {proof : RawProof}
    (found : InferenceSearch.searchGoal definition fuel (goal side claim) = .found proof) :
    (checkSearch definition goal claim side (.found proof)).asBool =
      some (match side with | .support => true | .refutation => false) := by
  have checked := InferenceSearch.searchGoal_found_checkRaw found
  cases side <;> simp [checkSearch, checked, Outcome.asBool]

/-! ## Only the selected contextual body executes -/

variable {Established : Type uEvidence} {Refuted : Type uClaim}
  {Boundary : Type uBoundary} {Incomplete : Type uIncomplete}
  {State : Type uState} {Answer : Type uAnswer} {Intent : Type uIntent}

/-- Branches consume their actual evidence. Residuals remain outcomes of the
program, rather than being erased to an empty result collection. -/
def branchProgram (outcome : Outcome Established Refuted Boundary Incomplete)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) :
    Program State (Outcome (Established × Answer) (Refuted × Answer) Boundary Incomplete) Intent :=
  match outcome with
  | .established evidence => (thenBody evidence).map fun answer => .established (evidence, answer)
  | .refuted evidence => (elseBody evidence).map fun answer => .refuted (evidence, answer)
  | .outsideFragment boundary => .pure (.outsideFragment boundary)
  | .incomplete residual => .pure (.incomplete residual)

theorem branchProgram_established (evidence : Established)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) :
    branchProgram (Boundary := Boundary) (Incomplete := Incomplete)
      (.established evidence) thenBody elseBody =
      (thenBody evidence).map (fun answer => .established (evidence, answer)) := rfl

theorem branchProgram_refuted (evidence : Refuted)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) :
    branchProgram (Boundary := Boundary) (Incomplete := Incomplete)
      (.refuted evidence) thenBody elseBody =
      (elseBody evidence).map (fun answer => .refuted (evidence, answer)) := rfl

/-- Every produced world is a world of the selected body, with precisely
its branch, state and deferred intents; only its answer gains the evidence. -/
theorem established_worlds (evidence : Established)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (branchProgram (Boundary := Boundary) (Incomplete := Incomplete)
      (.established evidence) thenBody elseBody) state branch =
      (runWorldsAt (thenBody evidence) state branch).map
        (Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer
          (fun answer => .established (evidence, answer))) := by
  rw [branchProgram]
  exact Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_map _ _ _ _

theorem refuted_worlds (evidence : Refuted)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (branchProgram (Boundary := Boundary) (Incomplete := Incomplete)
      (.refuted evidence) thenBody elseBody) state branch =
      (runWorldsAt (elseBody evidence) state branch).map
        (Mettapedia.TypeTheory.ContextualDependentSequencing.WorldResult.mapAnswer
          (fun answer => .refuted (evidence, answer))) := by
  rw [branchProgram]
  exact Mettapedia.TypeTheory.ContextualDependentSequencing.runWorldsAt_map _ _ _ _

theorem incomplete_runs_neither (residual : Incomplete)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (branchProgram (Boundary := Boundary) (.incomplete residual) thenBody elseBody)
      state branch =
      [{ branch := branch, answer := .incomplete residual, state := state, intents := [] }] := rfl

theorem outside_runs_neither (boundary : Boundary)
    (thenBody : Established → Program State Answer Intent)
    (elseBody : Refuted → Program State Answer Intent) (state : State) (branch : BranchTrace) :
    runWorldsAt (branchProgram (Incomplete := Incomplete) (.outsideFragment boundary) thenBody elseBody)
      state branch =
      [{ branch := branch, answer := .outsideFragment boundary, state := state, intents := [] }] := rfl

/-! ## Actual finite SAT and effect controls -/

namespace Controls

open CompletenessSpectrum.SAT
open CompletenessSpectrum.SAT.Canary

/-- The actual assumption formula is part of the scope: the question is
whether that theory and the submitted query have a joint Boolean model. -/
def meaning (theory query : CNF OneVar) : Prop := Satisfiable (theory ++ query)

def support (theory : CNF OneVar) : NIK.Service.{0, 0} (target meaning theory .support) :=
  .certificateBoundary (Assignment OneVar)
    ⟨fun query assignment => assignmentChecker.check (theory ++ query) assignment⟩
    { sound := fun _ assignment checked => ⟨assignment, checked⟩
      complete := fun _ evidence => evidence }

def opposition (theory : CNF OneVar) : NIK.Service.{0, 0} (target meaning theory .refutation) :=
  .certificateBoundary (TruthTableCertificate OneVar)
    ⟨fun query rows => truthTableChecker.check (theory ++ query) rows⟩
    { sound := fun query rows checked =>
        (unsatisfiable_iff_not_satisfiable (theory ++ query)).mp
          (truthTableChecker_authority.sound _ rows checked)
      complete := fun query negative => truthTableChecker_authority.complete _
        ((unsatisfiable_iff_not_satisfiable (theory ++ query)).mpr negative) }

def supportRequest (theory query : CNF OneVar) (assignment : Assignment OneVar) :
    NIKServiceResumption.PackedRequest.{0, 0} (target meaning theory .support) :=
  ⟨support theory, .certificateBoundary query assignment⟩

def oppositionRequest (theory query : CNF OneVar) (rows : TruthTableCertificate OneVar) :
    NIKServiceResumption.PackedRequest.{0, 0} (target meaning theory .refutation) :=
  ⟨opposition theory, .certificateBoundary query rows⟩

def acceptedThen := checkSubmission meaning [] positiveFormula .support
  (supportRequest [] positiveFormula trueAssignment) .certificateBoundary

def badSupport := checkSubmission meaning [] positiveFormula .support
  (supportRequest [] positiveFormula falseAssignment) .certificateBoundary

def partialOpposition := checkSubmission meaning [] contradictionFormula .refutation
  (oppositionRequest [] contradictionFormula [trueAssignment]) .certificateBoundary

def completeRows : TruthTableCertificate OneVar := [falseAssignment, trueAssignment]

theorem completeRows_checked :
    truthTableChecker.check contradictionFormula completeRows = true := by
  change decide (TruthTableValid contradictionFormula completeRows) = true
  apply decide_eq_true
  constructor
  · intro assignment
    cases value : assignment 0 with
    | false =>
        have same : assignment = falseAssignment := by
          funext index
          have : index = 0 := Fin.eq_zero index
          simpa [this, falseAssignment] using value
        simp [completeRows, same]
    | true =>
        have same : assignment = trueAssignment := by
          funext index
          have : index = 0 := Fin.eq_zero index
          simpa [this, trueAssignment] using value
        simp [completeRows, same]
  · intro assignment _
    exact contradiction_unsatisfiable assignment

def acceptedElse := checkSubmission meaning [] contradictionFormula .refutation
  (oppositionRequest [] contradictionFormula completeRows) .certificateBoundary

theorem then_selected : acceptedThen.asBool = some true := rfl

theorem rejected_proof_is_not_else :
    badSupport.asBool = none ∧ meaning [] positiveFormula :=
  ⟨rfl, trueAssignment, rfl⟩

theorem incomplete_refutation_is_not_else : partialOpposition.asBool = none := by
  simp [partialOpposition, checkSubmission, oppositionRequest, opposition, NIKServiceResumption.invoke,
    NIKServiceInvocation.invoke, NIKServiceInvocation.Response.acceptedValue,
    incomplete_truth_table_rejected, Outcome.asBool]

theorem else_selected : acceptedElse.asBool = some false := by
  simp [acceptedElse, checkSubmission, oppositionRequest, opposition, NIKServiceResumption.invoke,
    NIKServiceInvocation.invoke, NIKServiceInvocation.Response.acceptedValue,
    completeRows_checked, Outcome.asBool]

/-- A supplied finite candidate list is a search attempt, not a completeness
certificate. Its empty result is retained verbatim as a residual. -/
def sampleAssignments (theory query : CNF OneVar) (candidates : List (Assignment OneVar)) :
    Outcome ((serviceAuthority.{0, 0, 0} meaning theory).Evidence query)
      ((serviceAuthority.{0, 0, 0} meaning theory).Obstruction query) PEmpty.{1}
      (List (Assignment OneVar)) :=
  match found : candidates.find? (fun assignment => (theory ++ query).eval assignment) with
  | none => .incomplete candidates
  | some assignment =>
      .established
        { submitted := supportRequest theory query assignment
          input := .certificateBoundary
          returned := by
            have checked := List.find?_some found
            simp [supportRequest, support, NIKServiceResumption.invoke,
              NIKServiceInvocation.invoke, NIKServiceInvocation.Response.acceptedValue,
              assignmentChecker, checked] }

theorem empty_search_is_not_else :
    (sampleAssignments [] positiveFormula []).asBool = none ∧ meaning [] positiveFormula :=
  ⟨rfl, trueAssignment, rfl⟩

theorem unsuccessful_sample_is_not_else :
    (sampleAssignments [] positiveFormula [falseAssignment]).asBool = none ∧
      meaning [] positiveFormula := ⟨rfl, trueAssignment, rfl⟩

theorem successful_sample_selects_then :
    (sampleAssignments [] positiveFormula [falseAssignment, trueAssignment]).asBool = some true := rfl

def decision (theory : CNF OneVar) : Checker.DecisionKernel (CNF OneVar) (meaning theory) where
  decide query := satisfiabilityDecisionKernel.decide (theory ++ query)
  correct query := satisfiabilityDecisionKernel.correct (theory ++ query)

theorem exact_decision_selects_then :
    (decideOutcome meaning [] (decision []) positiveFormula).asBool = some true :=
  (decideOutcome_true_iff meaning [] (decision []) positiveFormula).mpr ⟨trueAssignment, rfl⟩

theorem exact_decision_selects_else :
    (decideOutcome meaning [] (decision []) contradictionFormula).asBool = some false :=
  (decideOutcome_false_iff meaning [] (decision []) contradictionFormula).mpr
    contradiction_not_satisfiable

/-- The same query and assignment cannot move across a changed theory. -/
theorem changed_scope_rejects_old_assignment :
    (checkSubmission meaning [[negative]] positiveFormula .support
      (supportRequest [[negative]] positiveFormula trueAssignment) .certificateBoundary).asBool = none := rfl

def thenEffect {Evidence : Type*} (_ : Evidence) : Program Nat Nat String :=
  .read fun state => .write (state + 1) (.intent "then" (.pure (state + 10)))

def elseEffect {Evidence : Type*} (_ : Evidence) : Program Nat Nat String :=
  .read fun state => .write (state + 100) (.intent "else" (.pure (state + 20)))

theorem rejected_evidence_executes_neither :
    runWorldsAt (branchProgram badSupport thenEffect elseEffect) 7 [true] =
      [{ branch := [true], answer := .incomplete (positiveFormula, ⟨.support,
           supportRequest [] positiveFormula falseAssignment⟩),
         state := 7, intents := [] }] := rfl

theorem empty_search_executes_neither :
    runWorldsAt (branchProgram (sampleAssignments [] positiveFormula []) thenEffect elseEffect) 7 [true] =
      [{ branch := [true], answer := .incomplete [], state := 7, intents := [] }] := rfl

theorem accepted_then_effects :
    (runWorldsAt (branchProgram acceptedThen thenEffect elseEffect) 7 [true]).map
      (fun world => (world.state, world.intents)) = [(8, ["then"])] := rfl

theorem accepted_else_effects :
    (runWorldsAt (branchProgram acceptedElse thenEffect elseEffect) 7 [true]).map
      (fun world => (world.state, world.intents)) = [(107, ["else"])] := by
  have selected := else_selected
  obtain ⟨evidence, returned⟩ := acceptedElse.asBool_eq_false_iff.mp selected
  rw [returned]
  rfl

end Controls

end Mettapedia.GSLT.LanguageDef.NIKPropositionBranching
