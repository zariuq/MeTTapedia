-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologNestedCallReadyRegression
Purpose: Inhabit the state-indexed nested-call bridge with one concrete,
  source-ordered p -> q -> r local-resolution prefix.
Trusted boundary: none
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologRootCallReadyBridge

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyRegression

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.GoalSemantics
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Resolver
open DemandDrivenStep
open PrologAlphaFreshFrontierBridge
open PrologActivationMacro
open PrologCallEntryBridge
open PrologCallStepBridge
open PrologControlSegmentSpineBridge
open PrologCurrentSessionPayloadBridge
open PrologNestedCallChainBridge
open PrologNestedCallReadyBridge
open PrologMguTopology
open PrologMguVariant
open PrologMguBridge
open PrologOrdinaryStepBridge
open PrologPrefilterCallBridge
open PrologPrefilterScanBridge
open PrologProductResourceContextBridge
open PrologRepresentativeCallFrontierBridge
open PrologRepresentativeProductActivationBridge
open PrologRecursiveCallPayloadBridge
open PrologRootCallReadyBridge
open PrologRetainedPayloadSnapshotBridge
open PrologSourceProductContextBridge
open PrologStateBridge
open OpenBindingAgreement
open SourceControlResourcePayloadContextAgrees

/-! ## Ground source and executable program -/

def resultTerm : Term := .integer 7

def resultAtom : Atom := .gnd (.int 7)

def pReferenceClause : LocalClause :=
  { predicate := "p"
    arguments := [resultTerm]
    body := [.call "q" [resultTerm]] }

def qReferenceClause : LocalClause :=
  { predicate := "q"
    arguments := [resultTerm]
    body := [.call "r" [resultTerm]] }

def rReferenceClause : LocalClause :=
  { predicate := "r"
    arguments := [resultTerm]
    body := [] }

def pExecutableClause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [.call "q" [] resultAtom] }

def qExecutableClause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [.call "r" [] resultAtom] }

def rExecutableClause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause :=
  { params := []
    result := resultAtom
    body := [] }

def referenceDatabase : Database :=
  ((Database.empty.assertz pReferenceClause).assertz qReferenceClause).assertz
    rReferenceClause

def executableWorld : PWorld :=
  (((default : PWorld).reindexClauses.appendProgClause
      ("p", pExecutableClause)).appendProgClause
      ("q", qExecutableClause)).appendProgClause
      ("r", rExecutableClause)

/-! ## Empty cumulative valuation and ground control -/

private def emptyRuntimeTopological : Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological [] := by
  refine
    { order := []
      nodup := by simp
      domain := ?_
      decreases := ?_ }
  · intro name
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup]
  · intro source value dependency lookup
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup] at lookup

private theorem emptyTaskData :
    TaskDataAgrees [] [] [] [] [] [] := by
  refine
    { alphaShared := ?_
      canonicalWellFormed := TreeSubstitution.wellFormed_nil
      bindingShape := rfl
      valuation := ?_ }
  · constructor <;> intro <;> simp_all
  · refine
      ⟨[], TreeSubstitutionVariants.refl [],
        TreeSubstitutionTopological.nil, ?_,
        ⟨emptyRuntimeTopological⟩, ?_⟩
    · intro entry member
      simp at member
    · intro identity name member
      simp at member

private theorem groundCallControl (barrier : Nat) (predicate : String) :
    NormalizedAlphaGoalsAgree [] barrier
      [.call predicate [resultTerm]]
      [.call predicate [] resultAtom] := by
  exact
    .cons
      (.definedCall AlphaTermsAgree.nil
        (AlphaTermAgrees.integer (alpha := []) 7))
      .nil

private theorem groundCallPayload (barrier : Nat) (predicate : String) :
    TaskPayloadAgrees [] [] barrier [] [] [] []
      [.call predicate [resultTerm]]
      [.call predicate [] resultAtom] :=
  emptyTaskData.withControl (groundCallControl barrier predicate)

private theorem groundPayloadSupported :
    AlphaTermsSupported [] [] [resultTerm] := by
  intro term member
  simp only [List.mem_singleton] at member
  subst term
  simp [resultTerm, AlphaTreeSupported, Term.denote,
    PrologMguOpenAgreement.TreeVariablesSatisfy,
    PrologMguOpenAgreement.TreesVariablesSatisfy]

/-! ## Exact database/world correspondence -/

private theorem pClauseAgrees :
    LocalClauseAgrees pReferenceClause ("p", pExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := ?_
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · exact
      .cons
        (.definedCall CompilerAdequacy.TermsAgree.nil
          (CompilerAdequacy.TermAgrees.integer 7))
        .nil
  · intro name
    simp [pReferenceClause, pExecutableClause, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem qClauseAgrees :
    LocalClauseAgrees qReferenceClause ("q", qExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := ?_
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · exact
      .cons
        (.definedCall CompilerAdequacy.TermsAgree.nil
          (CompilerAdequacy.TermAgrees.integer 7))
        .nil
  · intro name
    simp [qReferenceClause, qExecutableClause, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.vars,
      specializationGoalsVars, specializationGoalVars, termsVariables,
      termVariables, goalsVariables, goalVariables]

private theorem rClauseAgrees :
    LocalClauseAgrees rReferenceClause ("r", rExecutableClause) := by
  refine
    { predicate := rfl
      outputLast := ?_
      body := .nil
      support := ?_ }
  · exact
      ⟨[], resultTerm, rfl, CompilerAdequacy.TermsAgree.nil,
        CompilerAdequacy.TermAgrees.integer 7⟩
  · intro name
    simp [rReferenceClause, rExecutableClause, resultTerm, resultAtom,
      LocalClause.variables, resolutionClauseVars, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.vars,
      specializationGoalsVars, termsVariables, termVariables, goalsVariables]

private theorem emptyDatabaseRelatesIndexedWorld :
    DatabaseRelatesWorld Database.empty
      ((default : PWorld).reindexClauses) := by
  refine
    { reachable := DatabaseActions.DatabaseReachable.empty
      liveClauses := ?_
      clauseIndex := PWorld.reindexClauses_coherent _ }
  exact .nil

theorem referenceDatabase_relates_executableWorld :
    DatabaseRelatesWorld referenceDatabase executableWorld := by
  have p := emptyDatabaseRelatesIndexedWorld.assertz pClauseAgrees
  have q := p.assertz qClauseAgrees
  have r := q.assertz rClauseAgrees
  simpa [referenceDatabase, executableWorld] using r

/-! ## Concrete root runtime -/

def initialSession : Session :=
  { resolver :=
      { database := referenceDatabase
        nextFresh := 0 } }

def initialOpenConf : OpenConf :=
  { persistent :=
      { world := executableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "p" [] resultAtom], [])
        alts := []
        qterm := resultAtom } }

private theorem executableWorldCoherent :
    executableWorld.ClauseIndexCoherent := by
  have root := PWorld.reindexClauses_coherent (default : PWorld)
  have p := PWorld.appendProgClause_coherent _ ("p", pExecutableClause) root
  have q := PWorld.appendProgClause_coherent _ ("q", qExecutableClause) p
  have r := PWorld.appendProgClause_coherent _ ("r", rExecutableClause) q
  simpa [executableWorld] using r

private theorem pResolutionCandidates :
    executableWorld.resolutionCandidates "p" 0 = [pExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, pExecutableClause, emptyClauses]

private theorem qResolutionCandidates :
    executableWorld.resolutionCandidates "q" 0 = [qExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, qExecutableClause, emptyClauses]

private theorem rResolutionCandidates :
    executableWorld.resolutionCandidates "r" 0 = [rExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ executableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [executableWorld, PWorld.reindexClauses, PWorld.appendProgClause,
    PWorld.clausesOf, rExecutableClause, emptyClauses]

private theorem pVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1 =
      [((Database.empty.allocate pReferenceClause))] := by
  rfl

private theorem qVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "q" 1 =
      [(((Database.empty.assertz pReferenceClause).allocate
        qReferenceClause))] := by
  rfl

private theorem rVisibleClauses :
    referenceDatabase.visibleClausesAt referenceDatabase.generation "r" 1 =
      [((((Database.empty.assertz pReferenceClause).assertz
        qReferenceClause).allocate rReferenceClause))] := by
  rfl

-- This proof witness stays transparent for the dependent support laws.
set_option linter.defProp false in
private def groundDefinedCallHeadAgrees (predicate : String) :
    CompilerAdequacy.GoalAgrees
      (.call predicate [resultTerm])
      (.call predicate [] resultAtom) :=
  .definedCall CompilerAdequacy.TermsAgree.nil
    (CompilerAdequacy.TermAgrees.integer 7)

-- This proof witness stays transparent for the dependent support laws.
set_option linter.defProp false in
private def groundDefinedCallGoalsAgrees (predicate : String) :
    CompilerAdequacy.GoalsAgree
      [.call predicate [resultTerm]]
      [.call predicate [] resultAtom] :=
  .cons (groundDefinedCallHeadAgrees predicate) .nil

private theorem groundDefinedCallHeadSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalAgreesSupported [] []
      (groundDefinedCallHeadAgrees predicate) := by
  unfold groundDefinedCallHeadAgrees
  refine
    @CompilerGoalSubstitutionAdequacy.GoalAgreesSupported.definedCall
      [] [] predicate predicate [] resultTerm [] resultAtom
      CompilerAdequacy.TermsAgree.nil
      (CompilerAdequacy.TermAgrees.integer 7) ?_ ?_
  · simp [CompilerGoalSubstitutionAdequacy.TermsAgreeSupported,
      CompilerSubstitutionAdequacy.termsVariablesIn]
  · simp [CompilerGoalSubstitutionAdequacy.TermAgreesSupported,
      CompilerSubstitutionAdequacy.termVariablesIn, resultTerm]

private theorem groundDefinedCallGoalsSupported (predicate : String) :
    CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      (groundDefinedCallGoalsAgrees predicate) := by
  unfold groundDefinedCallGoalsAgrees
  exact .cons (groundDefinedCallHeadSupported predicate) .nil

private theorem pCandidateBank :
    SupportedCandidateBank "p"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "p" 1)
      (executableWorld.resolutionCandidates "p" 0) := by
  rw [pVisibleClauses, pResolutionCandidates]
  let head : CandidateClauseAgrees "p"
      (Database.empty.allocate pReferenceClause) pExecutableClause := by
    change LocalClauseAgrees pReferenceClause ("p", pExecutableClause)
    exact pClauseAgrees
  have encoding :
      EncodingInjectiveOn
        (Database.empty.allocate pReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, Database.allocate, pReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, resultTerm]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (Database.empty.allocate pReferenceClause).clause.variables
        (Database.empty.allocate pReferenceClause).clause.variables
        head.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] [] head.body
    have bodyEq : head.body = groundDefinedCallGoalsAgrees "q" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "q"
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

private theorem qCandidateBank :
    SupportedCandidateBank "q"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "q" 1)
      (executableWorld.resolutionCandidates "q" 0) := by
  rw [qVisibleClauses, qResolutionCandidates]
  let previous := Database.empty.assertz pReferenceClause
  let head : CandidateClauseAgrees "q"
      (previous.allocate qReferenceClause) qExecutableClause := by
    change LocalClauseAgrees qReferenceClause ("q", qExecutableClause)
    exact qClauseAgrees
  have encoding :
      EncodingInjectiveOn (previous.allocate qReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, previous, Database.allocate, qReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, resultTerm]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (previous.allocate qReferenceClause).clause.variables
        (previous.allocate qReferenceClause).clause.variables head.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] [] head.body
    have bodyEq : head.body = groundDefinedCallGoalsAgrees "r" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "r"
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

private theorem rCandidateBank :
    SupportedCandidateBank "r"
      (referenceDatabase.visibleClausesAt referenceDatabase.generation "r" 1)
      (executableWorld.resolutionCandidates "r" 0) := by
  rw [rVisibleClauses, rResolutionCandidates]
  let previous :=
    (Database.empty.assertz pReferenceClause).assertz qReferenceClause
  let head : CandidateClauseAgrees "r"
      (previous.allocate rReferenceClause) rExecutableClause := by
    change LocalClauseAgrees rReferenceClause ("r", rExecutableClause)
    exact rClauseAgrees
  have encoding :
      EncodingInjectiveOn (previous.allocate rReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, previous, Database.allocate, rReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      resultTerm]
  have body :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (previous.allocate rReferenceClause).clause.variables
        (previous.allocate rReferenceClause).clause.variables head.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] [] head.body
    have bodyEq :
        head.body = (CompilerAdequacy.GoalsAgree.nil :
          CompilerAdequacy.GoalsAgree [] []) := Subsingleton.elim _ _
    rw [bodyEq]
    exact .nil
  refine ⟨List.Forall₂.cons head .nil, ?_⟩
  exact .cons (head := head) encoding body .nil

/-! ## Root `p` entry and activation -/

private def pScan : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt × Nat :=
  resolveAlts
    (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
    [] [] resultAtom [] [] initialOpenConf.control.qterm
    (barrierDepth initialOpenConf.toConf + 1)
    initialOpenConf.toConf.counter

private def pPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf initialOpenConf pScan.1 pScan.2

private theorem pEntry :
    RepresentativeSupportedCallEntryRelates []
      (openedFor initialSession "p" [resultTerm] []) initialOpenConf pPending
      [] [] resultAtom [] [] resultAtom
      (barrierDepth initialOpenConf.toConf + 1)
      initialOpenConf.toConf.counter := by
  have database :
      DatabaseRelatesWorld initialSession.resolver.database
        initialOpenConf.persistent.world := by
    simpa [initialSession, initialOpenConf] using
      referenceDatabase_relates_executableWorld
  have ready : initialOpenConf.persistent.world.clauseIndexReady = true := by
    rfl
  have scanned :
      resolveAlts
          (initialOpenConf.persistent.world.resolutionCandidates "p" 0)
          [] [] resultAtom [] [] initialOpenConf.control.qterm
          (barrierDepth initialOpenConf.toConf + 1)
          initialOpenConf.toConf.counter = pScan := by
    rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (groundCallPayload (barrierDepth initialOpenConf.toConf + 1) "p")
      groundPayloadSupported
      (openedFor initialSession "p" [resultTerm] []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "p" [resultTerm] [] [] [] resultAtom [] []
      pScan.1 pScan.2 (by rfl) (by rfl)
      (by
        calc
          _ = pScan := by
            simpa only [List.length_nil, List.map_nil] using scanned
          _ = (pScan.1, pScan.2) := (Prod.eta pScan).symm) query pCandidateBank
  simpa [pPending, initialOpenConf] using constructed

private theorem initialBelow :
    ConfBelowResolutionCounter initialOpenConf.toConf := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  simp [resolutionLiveVars, initialOpenConf, OpenConf.toConf, Control.toConf,
    specializationGoalsVars, specializationGoalVars, resolutionSubstVars,
    resultAtom, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.vars] at member

private def pCopied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause :=
  Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause [] [] resultAtom [] []
    initialOpenConf.control.qterm initialOpenConf.toConf.counter
    (barrierDepth initialOpenConf.toConf + 1) pExecutableClause

private def pAlt : Mettapedia.Languages.MeTTa.PLeaTTa.Alt :=
  .br
    (.eq (.expr [resultAtom])
        (.expr (pCopied.params ++ [pCopied.result])) ::
      pCopied.body)
    []

private theorem pScanExact :
    pScan = ([pAlt], initialOpenConf.toConf.counter + 1) := by
  unfold pScan
  change
    resolveAlts (executableWorld.resolutionCandidates "p" 0) [] [] resultAtom
        [] [] resultAtom 1 0 =
      ([pAlt], 1)
  rw [pResolutionCandidates]
  have argumentsMatch : Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList [] [] = true := rfl
  have resultMatch :
      Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat
        (.gnd (.int 7)) (.gnd (.int 7)) = true := by
    rfl
  simp [resolveAlts, pExecutableClause, resultAtom, pAlt, pCopied,
    initialOpenConf, OpenConf.toConf, Control.toConf, barrierDepth,
    argumentsMatch, resultMatch]

private theorem pPendingPulledCur :
    pPending.pulled.toConf.cur =
      some
        (.eq (.expr [resultAtom])
            (.expr (pCopied.params ++ [pCopied.result])) ::
          pCopied.body,
          []) := by
  rw [pPending, pScanExact]
  rfl

private theorem pScanNonempty : pPending.branches ≠ [] := by
  rw [pPending, pScanExact]
  exact List.cons_ne_nil _ _

/-! ## Exact retained source occurrence -/

/-- The literal standardized source occurrence opened for the ground `p/1`
call.  The clause has no variables, so eager standardization reserves the
empty interval `[0,0)` and leaves its head and body unchanged. -/
private def pPreparedBranch : ClauseBranch :=
  { sourceId := (Database.empty.allocate pReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "q" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem pOpenedRemaining :
    (openedFor initialSession "p" [resultTerm] []).cursor.remaining =
      [pPreparedBranch] := by
  rfl

private theorem pPreparedBranch_unifies :
    DenotationalUnifiesEquations []
      pPreparedBranch.normalizedHeadEquations := by
  intro equation member
  simp [pPreparedBranch, ClauseBranch.normalizedHeadEquations] at member
  subst equation
  rfl

/-- Reflexive ground head matching computes exactly the empty extension. -/
private theorem pPreparedBranch_resolves_empty :
    HeadResolution pPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [pPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [pPreparedBranch]

/-- The literal standardized source occurrence opened for the nested ground
`q/1` call. -/
private def qPreparedBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz pReferenceClause).allocate qReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "r" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem qPreparedBranch_resolves_empty :
    HeadResolution qPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [qPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [qPreparedBranch]

/-- The literal standardized source occurrence opened for the second nested
ground `r/1` call. -/
private def rPreparedBranch : ClauseBranch :=
  { sourceId :=
      (((Database.empty.assertz pReferenceClause).assertz qReferenceClause).allocate
        rReferenceClause).id
    callGeneration := referenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem rPreparedBranch_resolves_empty :
    HeadResolution rPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [rPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [rPreparedBranch]

/-- Root cut scope used by the concrete nested-call regressions. -/
def rootScope : CutScopeId := 0

/-- The same literal root activation, now factored through the reusable root
certificate.  Every fixture-specific identity is recovered from the returned
source/executable banks rather than supplied to the constructor. -/
private theorem pActive
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ state : ActivePayloadState,
      state.index.bodyReferences = [.call "q" [resultTerm]] ∧
      state.index.bodyExecutables = [.call "q" [] resultAtom] ∧
      state.index.alpha = [] ∧
      state.index.freshFrontier = AlphaFreshFrontier state.index.alpha ∧
      state.index.support = [] ∧
      state.index.current = [] ∧
      state.index.runtime = [] ∧
      state.index.qterm = resultAtom ∧
      state.index.callerReferences = [] ∧
      state.index.outer = [] ∧
      state.index.resources = [] ∧
      state.index.active.alts = [] ∧
      state.index.baseAlts = [] ∧
      state.index.session.resolver.database = referenceDatabase ∧
      state.index.session.resolver.nextFresh = 0 ∧
      state.index.openConf.persistent.world = executableWorld ∧
      ConfBelowResolutionCounter state.index.openConf.toConf ∧
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) state.fineState ∧
      ∃ representative : RepresentativeActivePayloadState,
        representative.carrier = state ∧
          MaterializedLocalCallHeadsAgreeWith state.index.alpha
            state.index.current state.index.bodyReferences
            state.index.bodyExecutables state.index.runtime
            representative.representative state.index.referenceBase := by
  have beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier []) ExactControlFrontiers
        initialSession initialOpenConf := by
    refine ⟨?_, rfl, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [initialSession, initialOpenConf] using
        referenceDatabase_relates_executableWorld
    · simpa [initialSession, initialOpenConf] using
        (AlphaFreshFrontier.empty 0 0)
  have preHeadPayload :
      TaskSpinePayloadAgrees [] [] [] [] [] []
        [{ barrier := 0
           references := [.call "p" [resultTerm]]
           executables := [.call "p" [] resultAtom] }] :=
    TaskSpinePayloadAgrees.singleton (groundCallPayload 0 "p")
  have selected :
      ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
        {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {branchTail : List ClauseBranch}
        {clauseTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {altTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
        {copied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause},
        RejectedPullsN count
            (openedFor initialSession "p" [resultTerm] []).cursor finish →
          RepresentativeRetainedCallFrontier []
            (openedFor initialSession "p" [resultTerm] []) initialOpenConf
            pPending finish branch clause branchTail clauseTail altTail copied
            [] [] resultAtom [] [] resultAtom
            (barrierDepth initialOpenConf.toConf + 1)
            initialOpenConf.toConf.counter →
          ∃ independentResult : Substitution,
            HeadResolution branch independentResult ∧
              AlphaRuntimeNamesLive [] copied.body resultAtom := by
    intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    have finishNonempty : finish.remaining ≠ [] := by
      rw [frontier.finishRemaining]
      simp
    obtain ⟨_countZero, finishExact⟩ :=
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
        pOpenedRemaining pulls finishNonempty
    subst finish
    have branchExact : branch = pPreparedBranch := by
      have exact :
          pPreparedBranch :: [] = branch :: branchTail := by
        simpa [pOpenedRemaining] using frontier.finishRemaining
      exact (List.cons.inj exact).1.symm
    refine ⟨[], ?_, ?_⟩
    · simpa [branchExact] using pPreparedBranch_resolves_empty
    · intro identity name member
      simp at member
  have pNotThrow : ¬ BuiltinThrowCall "p" [resultTerm] := by
    simp [BuiltinThrowCall]
  have pNotDatabase :
      DatabaseActions.recognizeDatabaseAction "p" [resultTerm] = none := by
    rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, _independentResult,
        _representative, _nextAlpha, _sourceCanonical,
        _flattenedRepresentative, installed, after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := rootScope) (callerBarrier := 0)
      pEntry preHeadPayload groundPayloadSupported beforeSession (by rfl)
      (by rfl) initialBelow pScanNonempty selected pNotThrow pNotDatabase
  have sourceShape := facts.sourceBank
  rw [pOpenedRemaining] at sourceShape
  have sourceLengths := congrArg List.length sourceShape
  simp only [List.length_cons, List.length_nil, List.length_append] at sourceLengths
  have skippedBranchesLength : skippedBranches.length = 0 := by omega
  have branchTailLength : branchTail.length = 0 := by omega
  have skippedBranchesNil : skippedBranches = [] :=
    List.eq_nil_of_length_eq_zero skippedBranchesLength
  have branchTailNil : branchTail = [] :=
    List.eq_nil_of_length_eq_zero branchTailLength
  have branchExact : branch = pPreparedBranch := by
    subst skippedBranches
    subst branchTail
    simpa using sourceShape.symm
  have rejectsZero : rejects = 0 := by
    rw [← facts.sourceSkipCount]
    exact skippedBranchesLength
  have executableShape := facts.executableBank
  change
    executableWorld.resolutionCandidates "p" 0 =
      skippedClauses ++ clause :: clauseTail at executableShape
  rw [pResolutionCandidates] at executableShape
  have executableLengths := congrArg List.length executableShape
  simp only [List.length_cons, List.length_nil, List.length_append] at executableLengths
  have skippedClausesLength : skippedClauses.length = 0 := by omega
  have clauseTailLength : clauseTail.length = 0 := by omega
  have skippedClausesNil : skippedClauses = [] :=
    List.eq_nil_of_length_eq_zero skippedClausesLength
  have clauseTailNil : clauseTail = [] :=
    List.eq_nil_of_length_eq_zero clauseTailLength
  have clauseExact : clause = pExecutableClause := by
    subst skippedClauses
    subst clauseTail
    simpa using executableShape.symm
  have altTailNil : altTail = [] := by
    have scan := facts.frontier.tailScan
    rw [clauseTailNil] at scan
    exact (scan.deterministic (ResolutionScan.nil _)).1
  have copiedExact : copied = pCopied := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have exactResolution : HeadResolution branch [] := by
    simpa [branchExact] using pPreparedBranch_resolves_empty
  have currentExact : after.carrier.index.current = [] :=
    HeadResolution.deterministic facts.resolution exactResolution
  have nextAlphaBelowFirst :
      GeneratedBelow branch.firstFresh
        (after.carrier.index.alpha.map Prod.fst) := by
    simpa [branchExact, pPreparedBranch] using facts.selectionFresh.1
  have alphaExact : after.carrier.index.alpha = [] := by
    have exact :=
      facts.alphaExtension.eq_of_generatedBelow nextAlphaBelowFirst
    simpa using exact
  have runtimeExact : after.carrier.index.runtime = [] := by
    obtain
      ⟨base, args, headResult, pulledExact, generated, generatedExact,
        generatedAgrees⟩ := facts.activation.headMgu
    change pPending.pulled.toConf.cur = _ at pulledExact
    have pairExact :=
      Option.some.inj (pPendingPulledCur.symm.trans pulledExact)
    have baseNil : base = [] := (congrArg Prod.snd pairExact).symm
    have goalsExact := congrArg Prod.fst pairExact
    rw [copiedExact] at goalsExact
    simp only [List.nil_append] at goalsExact
    have firstGoalExact := (List.cons.inj goalsExact).1
    have expressionExact :
        (.expr [resultAtom] : Atom) = .expr (args ++ [headResult]) := by
      injection firstGoalExact
    subst base
    have generatedNil : generated = [] := by
      have exact := generatedExact
      have mapSubstNil (atoms : List Atom) :
          atoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst []) = atoms := by
        induction atoms with
        | nil => rfl
        | cons atom atoms ih => simp [Mettapedia.Languages.MeTTa.PLeaTTa.subst_nil, ih]
      rw [mapSubstNil, mapSubstNil] at exact
      rw [← expressionExact, copiedExact] at exact
      simpa [pCopied, pExecutableClause, initialOpenConf, resultAtom,
        Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, Mettapedia.Languages.MeTTa.PLeaTTa.renameAtomSuffix_gnd,
        Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_self] using exact
    have installedNil : installed = [] := by
      rw [generatedAgrees.installedShape, generatedNil]
      rfl
    have openConfExact :
        after.carrier.index.openConf =
          PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            pPending copied [] initialOpenConf.control.qterm installed := by
      exact DemandDrivenCallStep.FineConf.ready.inj facts.fineStateExact
    have currentControl :=
      after.carrier.agreement.core.control.ready.2.1
    rw [openConfExact] at currentControl
    have runtimeTrim :
        after.carrier.index.runtime =
          Mettapedia.Languages.MeTTa.PLeaTTa.trimFor copied.body initialOpenConf.control.qterm installed := by
      simpa [facts.bodyExecutables, facts.callerExecutablesEmpty,
        facts.outerEmpty] using (Option.some.inj currentControl).symm
    rw [runtimeTrim, installedNil, copiedExact]
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.trimFor, Mettapedia.Languages.MeTTa.PLeaTTa.trimSubst, Mettapedia.Languages.MeTTa.PLeaTTa.filterLiveSubst]
  refine
    ⟨after.carrier, ?_, ?_, alphaExact, facts.freshFrontierExact,
      facts.supportPreserved, currentExact, runtimeExact, facts.qtermPreserved,
      facts.callerReferencesEmpty, facts.outerEmpty, facts.resourcesEmpty, ?_,
      facts.baseAltsEmpty, ?_, ?_, ?_, facts.below,
      ?_, facts.fineSteps,
      ⟨after, rfl, facts.materializedBodyHeads⟩⟩
  · rw [facts.bodyReferences, branchExact]
    rfl
  · rw [facts.bodyExecutables, copiedExact]
    simp [pCopied, pExecutableClause, resultAtom,
      Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, Mettapedia.Languages.MeTTa.PLeaTTa.renameGoalSuffix,
      Mettapedia.Languages.MeTTa.PLeaTTa.renameAtomSuffix_gnd]
  · rw [facts.activeAltsExact, altTailNil]
  · rw [facts.sessionExact]
    rfl
  · rw [facts.sessionExact]
    rfl
  · simpa [initialOpenConf] using facts.worldPreserved
  · simpa [rejectsZero] using facts.sourceSteps

/-! ## State-indexed nested `q/1` readiness -/

private abbrev groundCallHead (state : ActivePayloadState) (predicate : String)
    (referenceHead : state.index.bodyReferences = [.call predicate [resultTerm]])
    (executableHead : state.index.bodyExecutables = [.call predicate [] resultAtom]) :
    NestedCallHead state :=
  ⟨predicate, [resultTerm], [], [], resultAtom, [], referenceHead, executableHead⟩

private theorem groundCall_opened_of_reservation (state : ActivePayloadState)
    (predicate : String) (database : Database) (branch : ClauseBranch)
    (currentNil : state.index.current = [])
    (databaseExact : state.index.session.resolver.database = database)
    (nextFreshZero : state.index.session.resolver.nextFresh = 0)
    (reserved : (reserveVisible database.generation [resultTerm] [] 0
      (database.visibleClausesAt database.generation predicate 1)).1 = [branch]) :
    (openedFor state.index.session predicate [resultTerm] state.index.current).cursor.remaining =
      [branch] := by
  rw [currentNil]
  change (prepareCall state.index.session.resolver (requestFor predicate [resultTerm] [])).1.remaining =
    [branch]
  simp only [prepareCall, requestFor]
  rw [databaseExact, nextFreshZero]
  exact reserved

/-- A singleton cursor fixes the selected occurrence. The head resolution
remains tied to that occurrence and the carrier retains its whole frame. -/
private theorem groundCall_ready (state : ActivePayloadState) (head : NestedCallHead state)
    (fresh : state.index.freshFrontier = AlphaFreshFrontier state.index.alpha)
    (supportNil : state.index.support = [])
    (below : ConfBelowResolutionCounter state.index.openConf.toConf)
    (indexReady : state.index.openConf.persistent.world.clauseIndexReady = true)
    (candidateSupported : SupportedCandidateBank head.predicate
      (state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation head.predicate head.referencePayload.length)
      (state.index.openConf.persistent.world.resolutionCandidates
        head.predicate head.arguments.length))
    (sourceNonempty : state.index.session.resolver.database.visibleClausesAt
      state.index.session.resolver.database.generation head.predicate head.referencePayload.length ≠ [])
    (scanNonempty : head.scan.1 ≠ [])
    {only : ClauseBranch} {binding : Substitution}
    (openedSingleton : (openedFor state.index.session head.predicate head.referencePayload
      state.index.current).cursor.remaining = [only])
    (resolves : HeadResolution only binding)
    (notThrow : ¬ BuiltinThrowCall head.predicate head.referencePayload)
    (notDatabase : DatabaseActions.recognizeDatabaseAction head.predicate head.referencePayload = none)
    (payloadSupported : AlphaTermsSupported state.index.alpha state.index.support head.referencePayload) :
    NestedCallReady state head := by
  refine ⟨⟨fresh, indexReady, below, candidateSupported, sourceNonempty, scanNonempty,
    ?_, notThrow, notDatabase⟩, payloadSupported⟩
  intro _ finish branch _ _ _ _ _ pulls frontier
  have finishNonempty : finish.remaining ≠ [] := by
    rw [frontier.finishRemaining]
    simp
  have pathExact := RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
    openedSingleton pulls finishNonempty
  have remaining := frontier.finishRemaining
  rw [pathExact.2, openedSingleton] at remaining
  have branchExact : branch = only := (List.cons.inj remaining).1.symm
  refine ⟨binding, ?_, ?_⟩
  · simpa only [branchExact] using resolves
  · rw [supportNil]
    intro identity name member
    simp at member

/-- The literal successor of the ground `p/1` activation is ready to enter
and select the unique ground `q/1` occurrence.  No payload, session, frontier,
or endpoint is supplied independently of that successor. -/
theorem qReadyAfterP
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ state : ActivePayloadState, ∃ head : NestedCallHead state,
      NestedCallReady state head ∧
      head.predicate = "q" ∧
      head.referencePayload = [resultTerm] ∧
      head.referenceRest = [] ∧
      head.arguments = [] ∧
      head.result = resultAtom ∧
      head.executableRest = [] ∧
      state.index.alpha = [] ∧
      state.index.support = [] ∧
      state.index.current = [] ∧
      state.index.runtime = [] ∧
      state.index.qterm = resultAtom ∧
      state.index.callerReferences = [] ∧
      state.index.outer = [] ∧
      state.index.resources = [] ∧
      state.index.active.alts = [] ∧
      state.index.baseAlts = [] ∧
      state.index.session.resolver.database = referenceDatabase ∧
      state.index.session.resolver.nextFresh = 0 ∧
      state.index.openConf.persistent.world = executableWorld ∧
      StepsN 2
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready initialOpenConf) state.fineState ∧
      (∃ representative : RepresentativeActivePayloadState,
        representative.carrier = state ∧
          MaterializedCallAgreesWith state.index.alpha state.index.current
            head.referencePayload
            (head.arguments.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime))
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime head.result)
            representative.representative state.index.referenceBase) ∧
      ∃ only : ClauseBranch,
        (openedFor state.index.session "q" [resultTerm]
          state.index.current).cursor.remaining = [only] := by
  obtain
    ⟨state, referenceHead, executableHead, alphaNil, freshExact, supportNil,
      currentNil, runtimeNil, qtermExact, callerReferencesEmpty, outerEmpty,
      resourcesEmpty, activeAltsEmpty, baseAltsEmpty, databaseExact,
      nextFreshZero, worldExact, below,
      rootSourceSteps,
      rootFineSteps, representative, representativeCarrier,
      materializedHeads⟩ :=
    pActive (prog := prog) (gt := gt)
  let head := groundCallHead state "q" referenceHead executableHead
  have headMaterialized :
      MaterializedCallAgreesWith state.index.alpha state.index.current
        head.referencePayload
        (head.arguments.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime head.result)
        representative.representative state.index.referenceBase :=
    materializedHeads referenceHead executableHead
  have openedSingleton :
      (openedFor state.index.session "q" [resultTerm]
        state.index.current).cursor.remaining = [qPreparedBranch] := by
    apply groundCall_opened_of_reservation state "q" referenceDatabase qPreparedBranch
      currentNil databaseExact nextFreshZero
    rw [qVisibleClauses]
    rfl
  refine
    ⟨state, head, ?_, rfl, rfl, rfl, rfl, rfl, rfl, alphaNil, supportNil,
      currentNil, runtimeNil, qtermExact, callerReferencesEmpty, outerEmpty,
      resourcesEmpty, activeAltsEmpty, baseAltsEmpty, databaseExact,
      nextFreshZero, worldExact, rootSourceSteps, rootFineSteps,
      ⟨representative, representativeCarrier, headMaterialized⟩,
      ⟨qPreparedBranch, openedSingleton⟩⟩
  refine groundCall_ready state head freshExact supportNil below ?_ ?_ ?_ ?_
    openedSingleton qPreparedBranch_resolves_empty ?_ ?_ ?_
  · rw [worldExact]
    rfl
  · change
      SupportedCandidateBank "q"
        (state.index.session.resolver.database.visibleClausesAt
          state.index.session.resolver.database.generation "q" 1)
        (state.index.openConf.persistent.world.resolutionCandidates "q" 0)
    simpa [databaseExact, worldExact] using qCandidateBank
  · change
      state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation "q" 1 ≠ []
    rw [databaseExact, qVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.index.openConf.persistent.world.resolutionCandidates "q" 0)
        [] [] resultAtom head.executableTail state.index.runtime
        state.index.openConf.toConf.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, qResolutionCandidates]
    have argumentsMatch : Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, qExecutableClause, resultAtom, argumentsMatch,
      resultMatch]
  · simp [head, BuiltinThrowCall]
  · rfl
  · simpa [alphaNil, supportNil] using groundPayloadSupported

/-- Any literal active carrier with the preserved ground substrate and an
`r(7)` body head is ready for the unique local `r/1` occurrence. -/
private theorem rReadyFromGroundState
    (state : ActivePayloadState)
    (referenceHead :
      state.index.bodyReferences = [.call "r" [resultTerm]])
    (executableHead :
      state.index.bodyExecutables = [.call "r" [] resultAtom])
    (alphaNil : state.index.alpha = [])
    (freshExact :
      state.index.freshFrontier = AlphaFreshFrontier state.index.alpha)
    (supportNil : state.index.support = [])
    (currentNil : state.index.current = [])
    (databaseExact :
      state.index.session.resolver.database = referenceDatabase)
    (nextFreshZero : state.index.session.resolver.nextFresh = 0)
    (worldExact :
      state.index.openConf.persistent.world = executableWorld)
    (below : ConfBelowResolutionCounter state.index.openConf.toConf) :
    ∃ head : NestedCallHead state,
      NestedCallReady state head ∧
        head.predicate = "r" ∧
        head.referencePayload = [resultTerm] ∧
        head.referenceRest = [] ∧
        head.arguments = [] ∧
        head.result = resultAtom ∧
        head.executableRest = [] := by
  let head := groundCallHead state "r" referenceHead executableHead
  have openedSingleton :
      (openedFor state.index.session "r" [resultTerm]
        state.index.current).cursor.remaining = [rPreparedBranch] := by
    apply groundCall_opened_of_reservation state "r" referenceDatabase rPreparedBranch
      currentNil databaseExact nextFreshZero
    rw [rVisibleClauses]
    rfl
  refine ⟨head, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine groundCall_ready state head freshExact supportNil below ?_ ?_ ?_ ?_
    openedSingleton rPreparedBranch_resolves_empty ?_ ?_ ?_
  · rw [worldExact]
    rfl
  · change
      SupportedCandidateBank "r"
        (state.index.session.resolver.database.visibleClausesAt
          state.index.session.resolver.database.generation "r" 1)
        (state.index.openConf.persistent.world.resolutionCandidates "r" 0)
    simpa [databaseExact, worldExact] using rCandidateBank
  · change
      state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation "r" 1 ≠ []
    rw [databaseExact, rVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.index.openConf.persistent.world.resolutionCandidates "r" 0)
        [] [] resultAtom head.executableTail state.index.runtime
        state.index.openConf.toConf.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, rResolutionCandidates]
    have argumentsMatch : Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, rExecutableClause, resultAtom, argumentsMatch,
      resultMatch]
  · simp [head, BuiltinThrowCall]
  · rfl
  · simpa [alphaNil, supportNil] using groundPayloadSupported

/-! ## Literal depth-two successor -/

/-- The actual ground `q/1` push selected from the `p/1` successor produces
the literal carrier on which the unique ground `r/1` call is ready.  The
source pull path and executable candidate bank force the selected occurrences;
the successor facts then force its substitution, bodies, alpha graph,
persistent state, and sealed counter invariant. -/
theorem ground_p_q_r_two_nested_pushes
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ before : ActivePayloadState, ∃ qHead : NestedCallHead before,
      ∃ middle : ActivePayloadState,
        NestedCallReady before qHead ∧
          qHead.predicate = "q" ∧
          qHead.referencePayload = [resultTerm] ∧
          before.index.bodyReferences = [.call "q" [resultTerm]] ∧
          before.index.bodyExecutables = [.call "q" [] resultAtom] ∧
          StepsN 2
            (.running initialSession
              (.task rootScope [.call "p" [resultTerm]] []))
            [.opened (requestFor "p" [resultTerm] [])]
            before.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 3
            (.ready initialOpenConf) before.fineState ∧
          NestedCallPushCertificate prog gt 0
            (requestFor "q" [resultTerm] []) before middle ∧
          ∃ rHead : NestedCallHead middle, ∃ after : ActivePayloadState,
            NestedCallReady middle rHead ∧
              rHead.predicate = "r" ∧
              rHead.referencePayload = [resultTerm] ∧
              NestedCallPushCertificate prog gt 0
                (requestFor "r" [resultTerm] []) middle after ∧
              after.index.bodyReferences = [] ∧
              after.index.bodyExecutables = [] ∧
              after.index.callerReferences = [] ∧
              after.index.baseAlts = [] ∧
              after.index.active.alts = [] ∧
              after.index.resources =
                [middle.index.active, before.index.active] ∧
              middle.index.active.alts = [] ∧
              before.index.active.alts = [] ∧
              after.index.outer.length = 2 ∧
              (∀ segment ∈ after.index.outer,
                segment.references = []) := by
  obtain
    ⟨before, qHead, qReady, qPredicate, qPayload, qReferenceRest,
      qArguments, qResult, qExecutableRest, beforeAlphaNil,
      beforeSupportNil, beforeCurrentNil, _beforeRuntimeNil, beforeQterm,
      beforeCallerReferencesEmpty, beforeOuterEmpty, beforeResourcesEmpty,
      beforeActiveEmpty, beforeBaseAltsEmpty, beforeDatabase,
      beforeNextFresh, beforeWorld, rootSourceSteps, rootFineSteps,
      _beforeRepresentative, _beforeSingleton⟩ :=
    qReadyAfterP (prog := prog) (gt := gt)
  obtain
    ⟨count, skippedBranches, skippedClauses, finish, branch, clause,
      branchTail, clauseTail, altTail, copied, qInstalled, middle, facts⟩ :=
    qReady.pushDetailed (prog := prog) (gt := gt)
  have openedSingleton :
      (openedFor before.index.session "q" [resultTerm]
        before.index.current).cursor.remaining = [qPreparedBranch] := by
    rw [beforeCurrentNil]
    change
      (prepareCall before.index.session.resolver
        (requestFor "q" [resultTerm] [])).1.remaining = [qPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).1 = [qPreparedBranch]
    rw [qVisibleClauses]
    rfl
  have finishNonempty : finish.remaining ≠ [] := by
    rw [facts.frontier.finishRemaining]
    simp
  have pullsConcrete :
      RejectedPullsN count
        (openedFor before.index.session "q" [resultTerm]
          before.index.current).cursor
        finish := by
    simpa [qPredicate, qPayload] using facts.pulls
  have pathExact :=
    _root_.Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      openedSingleton pullsConcrete finishNonempty
  have countZero : count = 0 := pathExact.1
  have branchExact : branch = qPreparedBranch := by
    have remaining := facts.frontier.finishRemaining
    rw [pathExact.2, openedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have skippedClausesNil : skippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.executableSkipCount, countZero]
  have executableShape := facts.executableBank
  rw [qPredicate, qArguments, beforeWorld, skippedClausesNil] at executableShape
  simp only [List.length_nil] at executableShape
  rw [qResolutionCandidates] at executableShape
  have clauseExact : clause = qExecutableClause :=
    (List.cons.inj executableShape).1.symm
  have clauseTailNil : clauseTail = [] :=
    (List.cons.inj executableShape).2.symm
  have altTailNil : altTail = [] := by
    have scan := facts.frontier.tailScan
    rw [clauseTailNil] at scan
    exact (scan.deterministic (ResolutionScan.nil _)).1
  have copiedBody : copied.body = [.call "r" [] resultAtom] := by
    rw [facts.frontier.copiedExact, clauseExact]
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, qExecutableClause, resultAtom,
      Mettapedia.Languages.MeTTa.PLeaTTa.renameGoalSuffix, Mettapedia.Languages.MeTTa.PLeaTTa.renameAtomSuffix_gnd]
  have middleReferences :
      middle.index.bodyReferences = [.call "r" [resultTerm]] := by
    rw [facts.bodyReferences, branchExact]
    rfl
  have middleExecutables :
      middle.index.bodyExecutables = [.call "r" [] resultAtom] := by
    rw [facts.bodyExecutables, copiedBody]
  have middleGeneratedBelow :
      GeneratedBelow branch.firstFresh (middle.index.alpha.map Prod.fst) := by
    simpa [branchExact, qPreparedBranch] using facts.selectionFresh.1
  have middleAlphaBefore : middle.index.alpha = before.index.alpha :=
    facts.alphaExtension.eq_of_generatedBelow middleGeneratedBelow
  have middleAlphaNil : middle.index.alpha = [] :=
    middleAlphaBefore.trans beforeAlphaNil
  have branchResolvesEmpty : HeadResolution branch [] := by
    simpa [branchExact] using qPreparedBranch_resolves_empty
  have middleCurrentNil : middle.index.current = [] :=
    HeadResolution.deterministic facts.resolution branchResolvesEmpty
  have middleSupportNil : middle.index.support = [] :=
    facts.supportPreserved.trans beforeSupportNil
  have middleDatabase :
      middle.index.session.resolver.database = referenceDatabase := by
    rw [facts.sessionExact]
    simpa [qPredicate, qPayload, beforeCurrentNil, openedFor, openLocalCall]
      using beforeDatabase
  have middleNextFresh : middle.index.session.resolver.nextFresh = 0 := by
    rw [facts.sessionExact]
    change
      (prepareCall before.index.session.resolver
        (requestFor qHead.predicate qHead.referencePayload
          before.index.current)).2.nextFresh = 0
    rw [qPredicate, qPayload, beforeCurrentNil]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "q" 1)).2 = 0
    rw [qVisibleClauses]
    rfl
  have middleWorld :
      middle.index.openConf.persistent.world = executableWorld :=
    facts.worldPreserved.trans beforeWorld
  have middleActiveEmpty : middle.index.active.alts = [] := by
    rw [facts.activeAltsExact, altTailNil]
  have middleResourcesExact :
      middle.index.resources = [before.index.active] := by
    rw [facts.resourcesExact, beforeResourcesEmpty]
  obtain
    ⟨rHead, rReady, rPredicate, rPayload, rReferenceRest, rArguments,
      rResult, rExecutableRest⟩ :=
    rReadyFromGroundState middle middleReferences middleExecutables
      middleAlphaNil facts.freshFrontierExact middleSupportNil
      middleCurrentNil middleDatabase middleNextFresh middleWorld facts.below
  have qCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "q" [resultTerm] []) before middle := by
    simpa [countZero, qPredicate, qPayload, beforeCurrentNil] using
      facts.certificate
  have beforeReferences :
      before.index.bodyReferences = [.call "q" [resultTerm]] := by
    simpa [qPredicate, qPayload, qReferenceRest] using qHead.referenceHead
  have beforeExecutables :
      before.index.bodyExecutables = [.call "q" [] resultAtom] := by
    simpa [qPredicate, qArguments, qResult, qExecutableRest] using
      qHead.executableHead
  obtain
    ⟨rCount, rSkippedBranches, rSkippedClauses, rFinish, rBranch, rClause,
      rBranchTail, rClauseTail, rAltTail, rCopied, rInstalled, after,
      rFacts⟩ :=
    rReady.pushDetailed (prog := prog) (gt := gt)
  have rOpenedSingleton :
      (openedFor middle.index.session "r" [resultTerm]
        middle.index.current).cursor.remaining = [rPreparedBranch] := by
    rw [middleCurrentNil]
    change
      (prepareCall middle.index.session.resolver
        (requestFor "r" [resultTerm] [])).1.remaining = [rPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [middleDatabase, middleNextFresh]
    change
      (reserveVisible referenceDatabase.generation [resultTerm] [] 0
        (referenceDatabase.visibleClausesAt referenceDatabase.generation
          "r" 1)).1 = [rPreparedBranch]
    rw [rVisibleClauses]
    rfl
  have rFinishNonempty : rFinish.remaining ≠ [] := by
    rw [rFacts.frontier.finishRemaining]
    simp
  have rPullsConcrete :
      RejectedPullsN rCount
        (openedFor middle.index.session "r" [resultTerm]
          middle.index.current).cursor
        rFinish := by
    simpa [rPredicate, rPayload] using rFacts.pulls
  have rPathExact :=
    _root_.Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      rOpenedSingleton rPullsConcrete rFinishNonempty
  have rCountZero : rCount = 0 := rPathExact.1
  have rBranchExact : rBranch = rPreparedBranch := by
    have remaining := rFacts.frontier.finishRemaining
    rw [rPathExact.2, rOpenedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have rSkippedClausesNil : rSkippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [rFacts.executableSkipCount, rCountZero]
  have rExecutableShape := rFacts.executableBank
  rw [rPredicate, rArguments, middleWorld, rSkippedClausesNil] at rExecutableShape
  simp only [List.length_nil] at rExecutableShape
  rw [rResolutionCandidates] at rExecutableShape
  have rClauseExact : rClause = rExecutableClause :=
    (List.cons.inj rExecutableShape).1.symm
  have rClauseTailNil : rClauseTail = [] :=
    (List.cons.inj rExecutableShape).2.symm
  have rAltTailNil : rAltTail = [] := by
    have scan := rFacts.frontier.tailScan
    rw [rClauseTailNil] at scan
    exact (scan.deterministic (ResolutionScan.nil _)).1
  have rCopiedBody : rCopied.body = [] := by
    rw [rFacts.frontier.copiedExact, rClauseExact]
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, rExecutableClause]
  have afterBodyReferences : after.index.bodyReferences = [] := by
    rw [rFacts.bodyReferences, rBranchExact]
    rfl
  have afterBodyExecutables : after.index.bodyExecutables = [] := by
    rw [rFacts.bodyExecutables, rCopiedBody]
  have middleCallerReferencesEmpty : middle.index.callerReferences = [] :=
    facts.callerReferences.trans qReferenceRest
  have afterCallerReferencesEmpty : after.index.callerReferences = [] :=
    rFacts.callerReferences.trans rReferenceRest
  have afterBaseAltsEmpty : after.index.baseAlts = [] :=
    rFacts.baseAltsPreserved.trans
      (facts.baseAltsPreserved.trans beforeBaseAltsEmpty)
  have afterActiveEmpty : after.index.active.alts = [] := by
    rw [rFacts.activeAltsExact, rAltTailNil]
  have afterResourcesExact :
      after.index.resources =
        [middle.index.active, before.index.active] := by
    rw [rFacts.resourcesExact, middleResourcesExact]
  have afterOuterLength : after.index.outer.length = 2 := by
    rw [rFacts.outerSegments, facts.outerSegments, beforeOuterEmpty]
    rfl
  have afterOuterAllEmpty :
      ∀ segment ∈ after.index.outer, segment.references = [] := by
    intro segment member
    rw [rFacts.outerSegments, facts.outerSegments, beforeOuterEmpty] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact middleCallerReferencesEmpty
    · exact beforeCallerReferencesEmpty
  have rCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "r" [resultTerm] []) middle after := by
    simpa [rCountZero, rPredicate, rPayload, middleCurrentNil] using
      rFacts.certificate
  exact
    ⟨before, qHead, middle, qReady, qPredicate, qPayload,
      beforeReferences, beforeExecutables, rootSourceSteps, rootFineSteps,
      qCertificate, rHead, after, rReady, rPredicate, rPayload, rCertificate,
      afterBodyReferences, afterBodyExecutables, afterCallerReferencesEmpty,
      afterBaseAltsEmpty, afterActiveEmpty, afterResourcesExact,
      middleActiveEmpty, beforeActiveEmpty, afterOuterLength,
      afterOuterAllEmpty⟩

/-- The root activation and both dependent push certificates compose to one
exact finite prefix.  Source observations retain call order; the fine lane
retains all three install/pull/head-equality microsteps per call. -/
theorem ground_p_q_r_exact_prefix
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ after : ActivePayloadState,
      StepsN 6
        (.running initialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] []),
          .opened (requestFor "q" [resultTerm] []),
          .opened (requestFor "r" [resultTerm] [])]
        after.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 9
        (.ready initialOpenConf) after.fineState := by
  obtain
    ⟨before, qHead, middle, _qReady, _qPredicate, _qPayload,
      _beforeReferences, _beforeExecutables, rootSourceSteps, rootFineSteps,
      qCertificate, rHead, after, _rReady, _rPredicate, _rPayload,
      rCertificate, _afterBodyReferences, _afterBodyExecutables,
      _afterCallerReferences, _afterBaseAlts, _afterActiveAlts,
      _afterResources, _middleActiveAlts, _beforeActiveAlts,
      _afterOuterLength, _afterOuterAllEmpty⟩ :=
    ground_p_q_r_two_nested_pushes (prog := prog) (gt := gt)
  have sourceSteps :=
    StepsN.trans rootSourceSteps
      (StepsN.trans qCertificate.sourceSteps rCertificate.sourceSteps)
  have fineSteps :=
    DemandDrivenCallStep.StepsN.trans rootFineSteps
      (DemandDrivenCallStep.StepsN.trans qCertificate.fineSteps
        rCertificate.fineSteps)
  refine ⟨after, ?_, ?_⟩
  · simpa using sourceSteps
  · simpa using fineSteps

/-! ## Reachable outer-sibling variant

The single-clause fixture above is intentionally terminal after the `r/1`
answer.  For positional pull anti-vacuity we also need a reachable run whose
two innermost banks are exhausted while an older bank remains live.  Appending
one duplicate `p/1` clause after the existing `p/q/r` program changes only
that retained outer bank: the selected first `p/1` clause still enters
`q/1`, while the duplicate remains as its ordered sibling.
-/

private def siblingReferenceDatabase : Database :=
  referenceDatabase.assertz pReferenceClause

private def siblingExecutableWorld : PWorld :=
  executableWorld.appendProgClause ("p", pExecutableClause)

/-- Initial source session for the reachable duplicate-`p/1` fixture. -/
def siblingInitialSession : Session :=
  { resolver :=
      { database := siblingReferenceDatabase
        nextFresh := 0 } }

/-- Initial fine configuration for the reachable duplicate-`p/1` fixture. -/
def siblingInitialOpenConf : OpenConf :=
  { persistent :=
      { world := siblingExecutableWorld
        counter := 0 }
    control :=
      { cur := some ([.call "p" [] resultAtom], [])
        alts := []
        qterm := resultAtom } }

private theorem siblingDatabaseRelatesWorld :
    DatabaseRelatesWorld siblingReferenceDatabase siblingExecutableWorld := by
  simpa [siblingReferenceDatabase, siblingExecutableWorld] using
    referenceDatabase_relates_executableWorld.assertz pClauseAgrees

private theorem siblingExecutableWorldCoherent :
    siblingExecutableWorld.ClauseIndexCoherent := by
  exact
    PWorld.appendProgClause_coherent _ ("p", pExecutableClause)
      executableWorldCoherent

private theorem siblingPResolutionCandidates :
    siblingExecutableWorld.resolutionCandidates "p" 0 =
      [pExecutableClause, pExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ siblingExecutableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [siblingExecutableWorld, executableWorld, PWorld.reindexClauses,
    PWorld.appendProgClause, PWorld.clausesOf, pExecutableClause,
    emptyClauses]

private theorem siblingQResolutionCandidates :
    siblingExecutableWorld.resolutionCandidates "q" 0 =
      [qExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ siblingExecutableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [siblingExecutableWorld, executableWorld, PWorld.reindexClauses,
    PWorld.appendProgClause, PWorld.clausesOf, qExecutableClause,
    emptyClauses]

private theorem siblingRResolutionCandidates :
    siblingExecutableWorld.resolutionCandidates "r" 0 =
      [rExecutableClause] := by
  rw [PWorld.resolutionCandidates_eq _ _ _ siblingExecutableWorldCoherent]
  have emptyClauses : (default : PWorld).progClauses = [] := rfl
  simp [siblingExecutableWorld, executableWorld, PWorld.reindexClauses,
    PWorld.appendProgClause, PWorld.clausesOf, rExecutableClause,
    emptyClauses]

private theorem siblingPVisibleClauses :
    siblingReferenceDatabase.visibleClausesAt
        siblingReferenceDatabase.generation "p" 1 =
      [Database.empty.allocate pReferenceClause,
        referenceDatabase.allocate pReferenceClause] := by
  rfl

private theorem siblingQVisibleClauses :
    siblingReferenceDatabase.visibleClausesAt
        siblingReferenceDatabase.generation "q" 1 =
      [((Database.empty.assertz pReferenceClause).allocate
        qReferenceClause)] := by
  rfl

private theorem siblingRVisibleClauses :
    siblingReferenceDatabase.visibleClausesAt
        siblingReferenceDatabase.generation "r" 1 =
      [(((Database.empty.assertz pReferenceClause).assertz
        qReferenceClause).allocate rReferenceClause)] := by
  rfl

private theorem siblingPCandidateBank :
    SupportedCandidateBank "p"
      (siblingReferenceDatabase.visibleClausesAt
        siblingReferenceDatabase.generation "p" 1)
      (siblingExecutableWorld.resolutionCandidates "p" 0) := by
  rw [siblingPVisibleClauses, siblingPResolutionCandidates]
  let first : CandidateClauseAgrees "p"
      (Database.empty.allocate pReferenceClause) pExecutableClause := by
    change LocalClauseAgrees pReferenceClause ("p", pExecutableClause)
    exact pClauseAgrees
  let second : CandidateClauseAgrees "p"
      (referenceDatabase.allocate pReferenceClause) pExecutableClause := by
    change LocalClauseAgrees pReferenceClause ("p", pExecutableClause)
    exact pClauseAgrees
  have firstEncoding :
      EncodingInjectiveOn
        (Database.empty.allocate pReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, Database.allocate, pReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, resultTerm]
  have secondEncoding :
      EncodingInjectiveOn
        (referenceDatabase.allocate pReferenceClause).clause.variables := by
    simp [EncodingInjectiveOn, Database.allocate, pReferenceClause,
      LocalClause.variables, termsVariables, termVariables, goalsVariables,
      goalVariables, resultTerm]
  have firstBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (Database.empty.allocate pReferenceClause).clause.variables
        (Database.empty.allocate pReferenceClause).clause.variables
        first.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      first.body
    have bodyEq : first.body = groundDefinedCallGoalsAgrees "q" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "q"
  have secondBody :
      CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported
        (referenceDatabase.allocate pReferenceClause).clause.variables
        (referenceDatabase.allocate pReferenceClause).clause.variables
        second.body := by
    change CompilerGoalSubstitutionAdequacy.GoalsAgreeSupported [] []
      second.body
    have bodyEq : second.body = groundDefinedCallGoalsAgrees "q" :=
      Subsingleton.elim _ _
    rw [bodyEq]
    exact groundDefinedCallGoalsSupported "q"
  refine
    ⟨List.Forall₂.cons first (List.Forall₂.cons second .nil), ?_⟩
  exact
    .cons (head := first) firstEncoding firstBody
      (.cons (head := second) secondEncoding secondBody .nil)

private theorem siblingQCandidateBank :
    SupportedCandidateBank "q"
      (siblingReferenceDatabase.visibleClausesAt
        siblingReferenceDatabase.generation "q" 1)
      (siblingExecutableWorld.resolutionCandidates "q" 0) := by
  rw [siblingQVisibleClauses, siblingQResolutionCandidates]
  simpa [qVisibleClauses, qResolutionCandidates] using qCandidateBank

private theorem siblingRCandidateBank :
    SupportedCandidateBank "r"
      (siblingReferenceDatabase.visibleClausesAt
        siblingReferenceDatabase.generation "r" 1)
      (siblingExecutableWorld.resolutionCandidates "r" 0) := by
  rw [siblingRVisibleClauses, siblingRResolutionCandidates]
  simpa [rVisibleClauses, rResolutionCandidates] using rCandidateBank

private def siblingPScan : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt × Nat :=
  resolveAlts
    (siblingInitialOpenConf.persistent.world.resolutionCandidates "p" 0)
    [] [] resultAtom [] [] siblingInitialOpenConf.control.qterm
    (barrierDepth siblingInitialOpenConf.toConf + 1)
    siblingInitialOpenConf.toConf.counter

private def siblingPPending : DemandDrivenCallStep.PendingCall :=
  DemandDrivenCallStep.pendingCallOf siblingInitialOpenConf siblingPScan.1
    siblingPScan.2

private theorem siblingPEntry :
    RepresentativeSupportedCallEntryRelates []
      (openedFor siblingInitialSession "p" [resultTerm] [])
      siblingInitialOpenConf siblingPPending [] [] resultAtom [] [] resultAtom
      (barrierDepth siblingInitialOpenConf.toConf + 1)
      siblingInitialOpenConf.toConf.counter := by
  have database :
      DatabaseRelatesWorld siblingInitialSession.resolver.database
        siblingInitialOpenConf.persistent.world := by
    simpa [siblingInitialSession, siblingInitialOpenConf] using
      siblingDatabaseRelatesWorld
  have ready :
      siblingInitialOpenConf.persistent.world.clauseIndexReady = true := by
    rfl
  have scanned :
      resolveAlts
          (siblingInitialOpenConf.persistent.world.resolutionCandidates "p" 0)
          [] [] resultAtom [] [] siblingInitialOpenConf.control.qterm
          (barrierDepth siblingInitialOpenConf.toConf + 1)
          siblingInitialOpenConf.toConf.counter = siblingPScan := by
    rfl
  have query :=
    PrologRecursiveCallPayloadBridge.TaskPayloadAgrees.representativeNormalizedCallAgrees
      (groundCallPayload
        (barrierDepth siblingInitialOpenConf.toConf + 1) "p")
      groundPayloadSupported
      (openedFor siblingInitialSession "p" [resultTerm] []).cursor
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
      (by simp [openedFor, openLocalCall, requestFor, prepareCall])
  have constructed :=
    openedFor_pendingCallOf_representative_supported_relates
      database ready "p" [resultTerm] [] [] [] resultAtom [] []
      siblingPScan.1 siblingPScan.2 (by rfl) (by rfl)
      (by
        calc
          _ = siblingPScan := by
            simpa only [List.length_nil, List.map_nil] using scanned
          _ = (siblingPScan.1, siblingPScan.2) :=
            (Prod.eta siblingPScan).symm)
      query siblingPCandidateBank
  simpa [siblingPPending, siblingInitialOpenConf] using constructed

private theorem siblingInitialBelow :
    ConfBelowResolutionCounter siblingInitialOpenConf.toConf := by
  apply ConfBelowResolutionCounter.of_names
  intro name member
  simp [resolutionLiveVars, siblingInitialOpenConf, OpenConf.toConf,
    Control.toConf, specializationGoalsVars, specializationGoalVars,
    resolutionSubstVars, resultAtom, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Atom.vars] at member

private def siblingPCopiedAt (counter : Nat) : Mettapedia.Languages.MeTTa.PLeaTTa.Clause :=
  Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause [] [] resultAtom [] []
    siblingInitialOpenConf.control.qterm counter
    (barrierDepth siblingInitialOpenConf.toConf + 1) pExecutableClause

private def siblingPAltAt (counter : Nat) : Mettapedia.Languages.MeTTa.PLeaTTa.Alt :=
  .br
    (.eq (.expr [resultAtom])
        (.expr
          ((siblingPCopiedAt counter).params ++
            [(siblingPCopiedAt counter).result])) ::
      (siblingPCopiedAt counter).body)
    []

private theorem siblingPScanExact :
    siblingPScan =
      ([siblingPAltAt 0, siblingPAltAt 1], 2) := by
  unfold siblingPScan
  change
    resolveAlts
        (siblingExecutableWorld.resolutionCandidates "p" 0) [] [] resultAtom
        [] [] resultAtom 1 0 =
      ([siblingPAltAt 0, siblingPAltAt 1], 2)
  rw [siblingPResolutionCandidates]
  have argumentsMatch : Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList [] [] = true := rfl
  have resultMatch :
      Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat
        (.gnd (.int 7)) (.gnd (.int 7)) = true := by
    rfl
  simp [resolveAlts, pExecutableClause, resultAtom, siblingPAltAt,
    siblingPCopiedAt, siblingInitialOpenConf, OpenConf.toConf, Control.toConf,
    barrierDepth, argumentsMatch, resultMatch]

private theorem siblingPPendingPulledCur :
    siblingPPending.pulled.toConf.cur =
      some
        (.eq (.expr [resultAtom])
            (.expr
              ((siblingPCopiedAt 0).params ++
                [(siblingPCopiedAt 0).result])) ::
          (siblingPCopiedAt 0).body,
          []) := by
  rw [siblingPPending, siblingPScanExact]
  rfl

private theorem siblingPScanNonempty : siblingPPending.branches ≠ [] := by
  rw [siblingPPending, siblingPScanExact]
  exact List.cons_ne_nil _ _

private def siblingPFirstBranch : ClauseBranch :=
  { sourceId := (Database.empty.allocate pReferenceClause).id
    callGeneration := siblingReferenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "q" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private def siblingPSecondBranch : ClauseBranch :=
  { sourceId := (referenceDatabase.allocate pReferenceClause).id
    callGeneration := siblingReferenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "q" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem siblingPOpenedRemaining :
    (openedFor siblingInitialSession "p" [resultTerm] []).cursor.remaining =
      [siblingPFirstBranch, siblingPSecondBranch] := by
  rfl

private theorem siblingPFirstBranch_resolves_empty :
    HeadResolution siblingPFirstBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [siblingPFirstBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [siblingPFirstBranch]

private theorem siblingPSecondBranch_resolves_empty :
    HeadResolution siblingPSecondBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [siblingPSecondBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [siblingPSecondBranch]

theorem siblingPActive
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ state : ActivePayloadState,
      state.index.bodyReferences = [.call "q" [resultTerm]] ∧
      state.index.bodyExecutables = [.call "q" [] resultAtom] ∧
      state.index.alpha = [] ∧
      state.index.freshFrontier = AlphaFreshFrontier state.index.alpha ∧
      state.index.support = [] ∧
      state.index.current = [] ∧
      state.index.runtime = [] ∧
      state.index.qterm = resultAtom ∧
      state.index.callerReferences = [] ∧
      state.index.outer = [] ∧
      state.index.resources = [] ∧
      state.index.baseAlts = [] ∧
      state.index.active.alts = [siblingPAltAt 1] ∧
      state.index.session.resolver.database = siblingReferenceDatabase ∧
      state.index.session.resolver.nextFresh = 0 ∧
      state.index.openConf.persistent.world = siblingExecutableWorld ∧
      ConfBelowResolutionCounter state.index.openConf.toConf ∧
      StepsN 2
        (.running siblingInitialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready siblingInitialOpenConf) state.fineState ∧
      ∃ representative : RepresentativeActivePayloadState,
        representative.carrier = state ∧
          MaterializedLocalCallHeadsAgreeWith state.index.alpha
            state.index.current state.index.bodyReferences
            state.index.bodyExecutables state.index.runtime
            representative.representative state.index.referenceBase := by
  have beforeSession :
      SessionRelatesOpenConf (AlphaFreshFrontier []) ExactControlFrontiers
        siblingInitialSession siblingInitialOpenConf := by
    refine ⟨?_, rfl, rfl, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa [siblingInitialSession, siblingInitialOpenConf] using
        siblingDatabaseRelatesWorld
    · simpa [siblingInitialSession, siblingInitialOpenConf] using
        (AlphaFreshFrontier.empty 0 0)
  have preHeadPayload :
      TaskSpinePayloadAgrees [] [] [] [] [] []
        [{ barrier := 0
           references := [.call "p" [resultTerm]]
           executables := [.call "p" [] resultAtom] }] :=
    TaskSpinePayloadAgrees.singleton (groundCallPayload 0 "p")
  have selected :
      ∀ {count : Nat} {finish : PreparedCursor} {branch : ClauseBranch}
        {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {branchTail : List ClauseBranch}
        {clauseTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {altTail : List Mettapedia.Languages.MeTTa.PLeaTTa.Alt}
        {copied : Mettapedia.Languages.MeTTa.PLeaTTa.Clause},
        RejectedPullsN count
            (openedFor siblingInitialSession "p" [resultTerm] []).cursor
            finish →
          RepresentativeRetainedCallFrontier []
            (openedFor siblingInitialSession "p" [resultTerm] [])
            siblingInitialOpenConf siblingPPending finish branch clause
            branchTail clauseTail altTail copied [] [] resultAtom [] []
            resultAtom (barrierDepth siblingInitialOpenConf.toConf + 1)
            siblingInitialOpenConf.toConf.counter →
          ∃ independentResult : Substitution,
            HeadResolution branch independentResult ∧
              AlphaRuntimeNamesLive [] copied.body resultAtom := by
    intro count finish branch clause branchTail clauseTail altTail copied
      pulls frontier
    cases pulls with
    | zero cursor =>
        have branchExact : branch = siblingPFirstBranch := by
          have exact :
              [siblingPFirstBranch, siblingPSecondBranch] =
                branch :: branchTail := by
            exact siblingPOpenedRemaining.symm.trans
              frontier.finishRemaining
          exact (List.cons.inj exact).1.symm
        refine ⟨[], ?_, ?_⟩
        · simpa [branchExact] using siblingPFirstBranch_resolves_empty
        · intro identity name member
          simp at member
    | succ count cursor first branches tailFinish remaining clash tail =>
        have firstExact : first = siblingPFirstBranch := by
          have exact :
              [siblingPFirstBranch, siblingPSecondBranch] =
                first :: branches :=
            siblingPOpenedRemaining.symm.trans remaining
          exact (List.cons.inj exact).1.symm
        exact False.elim
          (clash ⟨[], by simpa [firstExact] using
            siblingPFirstBranch_resolves_empty⟩)
  have pNotThrow : ¬ BuiltinThrowCall "p" [resultTerm] := by
    simp [BuiltinThrowCall]
  have pNotDatabase :
      DatabaseActions.recognizeDatabaseAction "p" [resultTerm] = none := by
    rfl
  obtain
      ⟨rejects, skippedBranches, skippedClauses, finish, branch, clause,
        branchTail, clauseTail, altTail, copied, _independentResult,
        _representative, _nextAlpha, _sourceCanonical,
        _flattenedRepresentative, installed, after, facts⟩ :=
    RepresentativeSupportedCallEntryRelates.activate_literal_root
      (prog := prog) (gt := gt) (scope := rootScope) (callerBarrier := 0)
      siblingPEntry preHeadPayload groundPayloadSupported beforeSession
      (by rfl) (by rfl) siblingInitialBelow siblingPScanNonempty selected
      pNotThrow pNotDatabase
  have rejectsZero : rejects = 0 := by
    cases facts.pulls with
    | zero cursor => rfl
    | succ count cursor first branches tailFinish remaining clash tail =>
        have firstExact : first = siblingPFirstBranch := by
          have exact :
              [siblingPFirstBranch, siblingPSecondBranch] =
                first :: branches :=
            siblingPOpenedRemaining.symm.trans remaining
          exact (List.cons.inj exact).1.symm
        exact False.elim
          (clash ⟨[], by simpa [firstExact] using
            siblingPFirstBranch_resolves_empty⟩)
  have skippedBranchesNil : skippedBranches = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.sourceSkipCount, rejectsZero]
  have sourceShape := facts.sourceBank
  rw [siblingPOpenedRemaining, skippedBranchesNil] at sourceShape
  have branchExact : branch = siblingPFirstBranch :=
    (List.cons.inj sourceShape).1.symm
  have branchTailExact : branchTail = [siblingPSecondBranch] :=
    (List.cons.inj sourceShape).2.symm
  have skippedClausesNil : skippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [facts.executableSkipCount, rejectsZero]
  have executableShape := facts.executableBank
  change
    siblingExecutableWorld.resolutionCandidates "p" 0 =
      skippedClauses ++ clause :: clauseTail at executableShape
  rw [siblingPResolutionCandidates, skippedClausesNil] at executableShape
  have clauseExact : clause = pExecutableClause :=
    (List.cons.inj executableShape).1.symm
  have clauseTailExact : clauseTail = [pExecutableClause] :=
    (List.cons.inj executableShape).2.symm
  have copiedExact : copied = siblingPCopiedAt 0 := by
    rw [facts.frontier.copiedExact, clauseExact]
    rfl
  have tailScan :
      ResolutionScan [] [] resultAtom [] [] resultAtom 1
        [pExecutableClause] 1 altTail 2 := by
    simpa [siblingPPending, siblingPScanExact, siblingInitialOpenConf,
      OpenConf.toConf, Control.toConf, barrierDepth, clauseTailExact] using
      facts.frontier.tailScan
  have expectedTailScan :
      ResolutionScan [] [] resultAtom [] [] resultAtom 1
        [pExecutableClause] 1 [siblingPAltAt 1] 2 :=
    .retained pExecutableClause [] 1 2 []
      (by
        simp [resolutionClauseRetained, resultAtom, pExecutableClause,
          Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical, Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat,
          Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList])
      (.nil 2)
  have altTailExact : altTail = [siblingPAltAt 1] :=
    (tailScan.deterministic expectedTailScan).1
  have exactResolution : HeadResolution branch [] := by
    simpa [branchExact] using siblingPFirstBranch_resolves_empty
  have currentExact : after.carrier.index.current = [] :=
    HeadResolution.deterministic facts.resolution exactResolution
  have nextAlphaBelowFirst :
      GeneratedBelow branch.firstFresh
        (after.carrier.index.alpha.map Prod.fst) := by
    simpa [branchExact, siblingPFirstBranch] using facts.selectionFresh.1
  have alphaExact : after.carrier.index.alpha = [] := by
    have exact := facts.alphaExtension.eq_of_generatedBelow nextAlphaBelowFirst
    simpa using exact
  have runtimeExact : after.carrier.index.runtime = [] := by
    obtain
      ⟨base, args, headResult, pulledExact, generated, generatedExact,
        generatedAgrees⟩ := facts.activation.headMgu
    change siblingPPending.pulled.toConf.cur = _ at pulledExact
    have pairExact :=
      Option.some.inj (siblingPPendingPulledCur.symm.trans pulledExact)
    have baseNil : base = [] := (congrArg Prod.snd pairExact).symm
    have goalsExact := congrArg Prod.fst pairExact
    rw [copiedExact] at goalsExact
    simp only [List.nil_append] at goalsExact
    have firstGoalExact := (List.cons.inj goalsExact).1
    have expressionExact :
        (.expr [resultAtom] : Atom) = .expr (args ++ [headResult]) := by
      injection firstGoalExact
    subst base
    have generatedNil : generated = [] := by
      have exact := generatedExact
      have mapSubstNil (atoms : List Atom) :
          atoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst []) = atoms := by
        induction atoms with
        | nil => rfl
        | cons atom atoms ih => simp [Mettapedia.Languages.MeTTa.PLeaTTa.subst_nil, ih]
      rw [mapSubstNil, mapSubstNil] at exact
      rw [← expressionExact, copiedExact] at exact
      simpa [siblingPCopiedAt, pExecutableClause, siblingInitialOpenConf,
        resultAtom, Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause,
        Mettapedia.Languages.MeTTa.PLeaTTa.renameAtomSuffix_gnd, Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_self] using exact
    have installedNil : installed = [] := by
      rw [generatedAgrees.installedShape, generatedNil]
      rfl
    have openConfExact :
        after.carrier.index.openConf =
          PrologRepresentativeStepActivationBridge.activatedOpenSuccessor
            siblingPPending copied []
              siblingInitialOpenConf.control.qterm installed :=
      DemandDrivenCallStep.FineConf.ready.inj facts.fineStateExact
    have currentControl := after.carrier.agreement.core.control.ready.2.1
    rw [openConfExact] at currentControl
    have runtimeTrim :
        after.carrier.index.runtime =
          Mettapedia.Languages.MeTTa.PLeaTTa.trimFor copied.body siblingInitialOpenConf.control.qterm
            installed := by
      simpa [facts.bodyExecutables, facts.callerExecutablesEmpty,
        facts.outerEmpty] using (Option.some.inj currentControl).symm
    rw [runtimeTrim, installedNil, copiedExact]
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.trimFor, Mettapedia.Languages.MeTTa.PLeaTTa.trimSubst,
      Mettapedia.Languages.MeTTa.PLeaTTa.filterLiveSubst]
  refine
    ⟨after.carrier, ?_, ?_, alphaExact, facts.freshFrontierExact,
      facts.supportPreserved, currentExact, runtimeExact,
      facts.qtermPreserved, facts.callerReferencesEmpty, facts.outerEmpty,
      facts.resourcesEmpty, facts.baseAltsEmpty, ?_, ?_, ?_, ?_,
      facts.below, ?_, facts.fineSteps,
      ⟨after, rfl, facts.materializedBodyHeads⟩⟩
  · rw [facts.bodyReferences, branchExact]
    rfl
  · rw [facts.bodyExecutables, copiedExact]
    simp [siblingPCopiedAt, pExecutableClause, resultAtom,
      Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, Mettapedia.Languages.MeTTa.PLeaTTa.renameGoalSuffix,
      Mettapedia.Languages.MeTTa.PLeaTTa.renameAtomSuffix_gnd]
  · rw [facts.activeAltsExact, altTailExact]
  · rw [facts.sessionExact]
    rfl
  · rw [facts.sessionExact]
    rfl
  · simpa [siblingInitialOpenConf] using facts.worldPreserved
  · simpa [rejectsZero] using facts.sourceSteps

private def siblingQPreparedBranch : ClauseBranch :=
  { sourceId :=
      ((Database.empty.assertz pReferenceClause).allocate qReferenceClause).id
    callGeneration := siblingReferenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := [.call "r" [resultTerm]]
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem siblingQPreparedBranch_resolves_empty :
    HeadResolution siblingQPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [siblingQPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [siblingQPreparedBranch]

private def siblingRPreparedBranch : ClauseBranch :=
  { sourceId :=
      (((Database.empty.assertz pReferenceClause).assertz
        qReferenceClause).allocate rReferenceClause).id
    callGeneration := siblingReferenceDatabase.generation
    freshSubstitution := []
    headEquations := [(resultTerm, resultTerm)]
    body := []
    bindings := []
    firstFresh := 0
    nextFresh := 0 }

private theorem siblingRPreparedBranch_resolves_empty :
    HeadResolution siblingRPreparedBranch [] := by
  refine ⟨[], ?_, ?_⟩
  · refine ⟨[], ?_, rfl⟩
    simpa [siblingRPreparedBranch, ClauseBranch.normalizedHeadEquations,
      denoteEquations] using
      (OrderedTreeMgu.cons (Term.denote resultTerm) (Term.denote resultTerm)
        [] [] [] (.reflexive (Term.denote resultTerm)) OrderedTreeMgu.nil)
  · simp [siblingRPreparedBranch]

private theorem siblingQReadyAfterP
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ state : ActivePayloadState, ∃ head : NestedCallHead state,
      NestedCallReady state head ∧
      head.predicate = "q" ∧
      head.referencePayload = [resultTerm] ∧
      head.referenceRest = [] ∧
      head.arguments = [] ∧
      head.result = resultAtom ∧
      head.executableRest = [] ∧
      state.index.alpha = [] ∧
      state.index.support = [] ∧
      state.index.current = [] ∧
      state.index.runtime = [] ∧
      state.index.qterm = resultAtom ∧
      state.index.callerReferences = [] ∧
      state.index.outer = [] ∧
      state.index.resources = [] ∧
      state.index.baseAlts = [] ∧
      state.index.active.alts = [siblingPAltAt 1] ∧
      state.index.session.resolver.database = siblingReferenceDatabase ∧
      state.index.session.resolver.nextFresh = 0 ∧
      state.index.openConf.persistent.world = siblingExecutableWorld ∧
      StepsN 2
        (.running siblingInitialSession
          (.task rootScope [.call "p" [resultTerm]] []))
        [.opened (requestFor "p" [resultTerm] [])]
        state.sourceState ∧
      DemandDrivenCallStep.StepsN prog gt 3
        (.ready siblingInitialOpenConf) state.fineState ∧
      (∃ representative : RepresentativeActivePayloadState,
        representative.carrier = state ∧
          MaterializedCallAgreesWith state.index.alpha state.index.current
            head.referencePayload
            (head.arguments.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime))
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime head.result)
            representative.representative state.index.referenceBase) ∧
      ∃ only : ClauseBranch,
        (openedFor state.index.session "q" [resultTerm]
          state.index.current).cursor.remaining = [only] := by
  obtain
    ⟨state, referenceHead, executableHead, alphaNil, freshExact,
      supportNil, currentNil, runtimeNil, qtermExact,
      callerReferencesEmpty, outerEmpty, resourcesEmpty, baseAltsEmpty,
      activeAltsExact, databaseExact, nextFreshZero, worldExact, below,
      rootSourceSteps, rootFineSteps, representative,
      representativeCarrier, materializedHeads⟩ :=
    siblingPActive (prog := prog) (gt := gt)
  let head := groundCallHead state "q" referenceHead executableHead
  have headMaterialized :
      MaterializedCallAgreesWith state.index.alpha state.index.current
        head.referencePayload
        (head.arguments.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst state.index.runtime head.result)
        representative.representative state.index.referenceBase :=
    materializedHeads referenceHead executableHead
  have openedSingleton :
      (openedFor state.index.session "q" [resultTerm]
        state.index.current).cursor.remaining = [siblingQPreparedBranch] := by
    apply groundCall_opened_of_reservation state "q" siblingReferenceDatabase siblingQPreparedBranch
      currentNil databaseExact nextFreshZero
    rw [siblingQVisibleClauses]
    rfl
  refine
    ⟨state, head, ?_, rfl, rfl, rfl, rfl, rfl, rfl, alphaNil,
      supportNil, currentNil, runtimeNil, qtermExact,
      callerReferencesEmpty, outerEmpty, resourcesEmpty, baseAltsEmpty,
      activeAltsExact, databaseExact, nextFreshZero, worldExact,
      rootSourceSteps, rootFineSteps,
      ⟨representative, representativeCarrier, headMaterialized⟩,
      ⟨siblingQPreparedBranch, openedSingleton⟩⟩
  refine groundCall_ready state head freshExact supportNil below ?_ ?_ ?_ ?_
    openedSingleton siblingQPreparedBranch_resolves_empty ?_ ?_ ?_
  · rw [worldExact]
    rfl
  · change
      SupportedCandidateBank "q"
        (state.index.session.resolver.database.visibleClausesAt
          state.index.session.resolver.database.generation "q" 1)
        (state.index.openConf.persistent.world.resolutionCandidates "q" 0)
    simpa [databaseExact, worldExact] using siblingQCandidateBank
  · change
      state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation "q" 1 ≠ []
    rw [databaseExact, siblingQVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.index.openConf.persistent.world.resolutionCandidates "q" 0)
        [] [] resultAtom head.executableTail state.index.runtime
        state.index.openConf.toConf.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, siblingQResolutionCandidates]
    have argumentsMatch : Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, qExecutableClause, resultAtom, argumentsMatch,
      resultMatch]
  · simp [head, BuiltinThrowCall]
  · rfl
  · simpa [alphaNil, supportNil] using groundPayloadSupported

private theorem siblingRReadyFromGroundState
    (state : ActivePayloadState)
    (referenceHead :
      state.index.bodyReferences = [.call "r" [resultTerm]])
    (executableHead :
      state.index.bodyExecutables = [.call "r" [] resultAtom])
    (alphaNil : state.index.alpha = [])
    (freshExact :
      state.index.freshFrontier = AlphaFreshFrontier state.index.alpha)
    (supportNil : state.index.support = [])
    (currentNil : state.index.current = [])
    (databaseExact :
      state.index.session.resolver.database = siblingReferenceDatabase)
    (nextFreshZero : state.index.session.resolver.nextFresh = 0)
    (worldExact :
      state.index.openConf.persistent.world = siblingExecutableWorld)
    (below : ConfBelowResolutionCounter state.index.openConf.toConf) :
    ∃ head : NestedCallHead state,
      NestedCallReady state head ∧
        head.predicate = "r" ∧
        head.referencePayload = [resultTerm] ∧
        head.referenceRest = [] ∧
        head.arguments = [] ∧
        head.result = resultAtom ∧
        head.executableRest = [] := by
  let head := groundCallHead state "r" referenceHead executableHead
  have openedSingleton :
      (openedFor state.index.session "r" [resultTerm]
        state.index.current).cursor.remaining = [siblingRPreparedBranch] := by
    apply groundCall_opened_of_reservation state "r" siblingReferenceDatabase siblingRPreparedBranch
      currentNil databaseExact nextFreshZero
    rw [siblingRVisibleClauses]
    rfl
  refine ⟨head, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine groundCall_ready state head freshExact supportNil below ?_ ?_ ?_ ?_
    openedSingleton siblingRPreparedBranch_resolves_empty ?_ ?_ ?_
  · rw [worldExact]
    rfl
  · change
      SupportedCandidateBank "r"
        (state.index.session.resolver.database.visibleClausesAt
          state.index.session.resolver.database.generation "r" 1)
        (state.index.openConf.persistent.world.resolutionCandidates "r" 0)
    simpa [databaseExact, worldExact] using siblingRCandidateBank
  · change
      state.index.session.resolver.database.visibleClausesAt
        state.index.session.resolver.database.generation "r" 1 ≠ []
    rw [databaseExact, siblingRVisibleClauses]
    simp
  · unfold NestedCallHead.scan
    change
      (resolveAlts
        (state.index.openConf.persistent.world.resolutionCandidates "r" 0)
        [] [] resultAtom head.executableTail state.index.runtime
        state.index.openConf.toConf.qterm
        (barrierDepth state.index.openConf.toConf + 1)
        state.index.openConf.toConf.counter).1 ≠ []
    rw [worldExact, siblingRResolutionCandidates]
    have argumentsMatch : Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompatList [] [] = true := rfl
    have resultMatch :
        Mettapedia.Languages.MeTTa.PLeaTTa.prologMatchCompat (.gnd (.int 7)) (.gnd (.int 7)) = true :=
      rfl
    simp [resolveAlts, rExecutableClause, resultAtom, argumentsMatch,
      resultMatch]
  · simp [head, BuiltinThrowCall]
  · rfl
  · simpa [alphaNil, supportNil] using groundPayloadSupported

/-- A fully reachable depth-two activation whose current and immediately
enclosing retained banks are exhausted while the oldest bank still owns the
duplicate `p/1` sibling.

This lower-layer regression deliberately exposes the concrete resource spine,
not the later dependent payload-cell view.  A payload-path theorem can consume
the witness without making call activation depend on scheduled-answer
machinery.

[SPEC metta.pl:251-256] -/
theorem ground_p_q_r_outer_sibling_resources_are_reachable
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable} :
    ∃ after : ActivePayloadState,
      ∃ middle outer : RetainedAlternativeSegment,
        after.index.alpha = [] ∧
          after.index.support = [] ∧
          after.index.active.alts = [] ∧
          after.index.resources = [middle, outer] ∧
          middle.alts = [] ∧
          outer.alts ≠ [] ∧
          after.index.bodyReferences = [] ∧
          after.index.bodyExecutables = [] ∧
          StepsN 6
            (.running siblingInitialSession
              (.task rootScope [.call "p" [resultTerm]] []))
            [.opened (requestFor "p" [resultTerm] []),
              .opened (requestFor "q" [resultTerm] []),
              .opened (requestFor "r" [resultTerm] [])]
            after.sourceState ∧
          DemandDrivenCallStep.StepsN prog gt 9
            (.ready siblingInitialOpenConf) after.fineState := by
  obtain
    ⟨before, qHead, qReady, qPredicate, qPayload, qReferenceRest,
      qArguments, qResult, qExecutableRest, beforeAlphaNil,
      beforeSupportNil, beforeCurrentNil, _beforeRuntimeNil, beforeQterm,
      beforeCallerReferencesEmpty, beforeOuterEmpty, beforeResourcesEmpty,
      beforeBaseAltsEmpty, beforeActiveLive, beforeDatabase,
      beforeNextFresh, beforeWorld, rootSourceSteps, rootFineSteps,
      _beforeRepresentative, _beforeSingleton⟩ :=
    siblingQReadyAfterP (prog := prog) (gt := gt)
  obtain
    ⟨qCount, qSkippedBranches, qSkippedClauses, qFinish, qBranch, qClause,
      qBranchTail, qClauseTail, qAltTail, qCopied, qInstalled, middle,
      qFacts⟩ := qReady.pushDetailed (prog := prog) (gt := gt)
  have qOpenedSingleton :
      (openedFor before.index.session "q" [resultTerm]
        before.index.current).cursor.remaining = [siblingQPreparedBranch] := by
    rw [beforeCurrentNil]
    change
      (prepareCall before.index.session.resolver
        (requestFor "q" [resultTerm] [])).1.remaining =
          [siblingQPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible siblingReferenceDatabase.generation [resultTerm] [] 0
        (siblingReferenceDatabase.visibleClausesAt
          siblingReferenceDatabase.generation "q" 1)).1 =
        [siblingQPreparedBranch]
    rw [siblingQVisibleClauses]
    rfl
  have qFinishNonempty : qFinish.remaining ≠ [] := by
    rw [qFacts.frontier.finishRemaining]
    simp
  have qPullsConcrete :
      RejectedPullsN qCount
        (openedFor before.index.session "q" [resultTerm]
          before.index.current).cursor qFinish := by
    simpa [qPredicate, qPayload] using qFacts.pulls
  have qPathExact :=
    _root_.Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      qOpenedSingleton qPullsConcrete qFinishNonempty
  have qCountZero : qCount = 0 := qPathExact.1
  have qBranchExact : qBranch = siblingQPreparedBranch := by
    have remaining := qFacts.frontier.finishRemaining
    rw [qPathExact.2, qOpenedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have qSkippedClausesNil : qSkippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [qFacts.executableSkipCount, qCountZero]
  have qExecutableShape := qFacts.executableBank
  rw [qPredicate, qArguments, beforeWorld, qSkippedClausesNil] at qExecutableShape
  simp only [List.length_nil] at qExecutableShape
  rw [siblingQResolutionCandidates] at qExecutableShape
  have qClauseExact : qClause = qExecutableClause :=
    (List.cons.inj qExecutableShape).1.symm
  have qClauseTailNil : qClauseTail = [] :=
    (List.cons.inj qExecutableShape).2.symm
  have qCopiedBody : qCopied.body = [.call "r" [] resultAtom] := by
    rw [qFacts.frontier.copiedExact, qClauseExact]
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, qExecutableClause, resultAtom,
      Mettapedia.Languages.MeTTa.PLeaTTa.renameGoalSuffix, Mettapedia.Languages.MeTTa.PLeaTTa.renameAtomSuffix_gnd]
  have qAltTailNil : qAltTail = [] := by
    have scan := qFacts.frontier.tailScan
    rw [qClauseTailNil] at scan
    exact (scan.deterministic (ResolutionScan.nil _)).1
  have middleReferences :
      middle.index.bodyReferences = [.call "r" [resultTerm]] := by
    rw [qFacts.bodyReferences, qBranchExact]
    rfl
  have middleExecutables :
      middle.index.bodyExecutables = [.call "r" [] resultAtom] := by
    rw [qFacts.bodyExecutables, qCopiedBody]
  have middleGeneratedBelow :
      GeneratedBelow qBranch.firstFresh (middle.index.alpha.map Prod.fst) := by
    simpa [qBranchExact, siblingQPreparedBranch] using
      qFacts.selectionFresh.1
  have middleAlphaBefore : middle.index.alpha = before.index.alpha :=
    qFacts.alphaExtension.eq_of_generatedBelow middleGeneratedBelow
  have middleAlphaNil : middle.index.alpha = [] :=
    middleAlphaBefore.trans beforeAlphaNil
  have qBranchResolvesEmpty : HeadResolution qBranch [] := by
    simpa [qBranchExact] using siblingQPreparedBranch_resolves_empty
  have middleCurrentNil : middle.index.current = [] :=
    HeadResolution.deterministic qFacts.resolution qBranchResolvesEmpty
  have middleSupportNil : middle.index.support = [] :=
    qFacts.supportPreserved.trans beforeSupportNil
  have middleDatabase :
      middle.index.session.resolver.database = siblingReferenceDatabase := by
    rw [qFacts.sessionExact]
    simpa [qPredicate, qPayload, beforeCurrentNil, openedFor, openLocalCall]
      using beforeDatabase
  have middleNextFresh : middle.index.session.resolver.nextFresh = 0 := by
    rw [qFacts.sessionExact]
    change
      (prepareCall before.index.session.resolver
        (requestFor qHead.predicate qHead.referencePayload
          before.index.current)).2.nextFresh = 0
    rw [qPredicate, qPayload, beforeCurrentNil]
    simp only [prepareCall, requestFor]
    rw [beforeDatabase, beforeNextFresh]
    change
      (reserveVisible siblingReferenceDatabase.generation [resultTerm] [] 0
        (siblingReferenceDatabase.visibleClausesAt
          siblingReferenceDatabase.generation "q" 1)).2 = 0
    rw [siblingQVisibleClauses]
    rfl
  have middleWorld :
      middle.index.openConf.persistent.world = siblingExecutableWorld :=
    qFacts.worldPreserved.trans beforeWorld
  have middleActiveEmpty : middle.index.active.alts = [] := by
    rw [qFacts.activeAltsExact, qAltTailNil]
  have middleResourcesExact :
      middle.index.resources = [before.index.active] := by
    rw [qFacts.resourcesExact, beforeResourcesEmpty]
  obtain
    ⟨rHead, rReady, rPredicate, rPayload, rReferenceRest, rArguments,
      rResult, rExecutableRest⟩ :=
    siblingRReadyFromGroundState middle middleReferences middleExecutables
      middleAlphaNil qFacts.freshFrontierExact middleSupportNil
      middleCurrentNil middleDatabase middleNextFresh middleWorld qFacts.below
  have qCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "q" [resultTerm] []) before middle := by
    simpa [qCountZero, qPredicate, qPayload, beforeCurrentNil] using
      qFacts.certificate
  obtain
    ⟨rCount, rSkippedBranches, rSkippedClauses, rFinish, rBranch, rClause,
      rBranchTail, rClauseTail, rAltTail, rCopied, rInstalled, after,
      rFacts⟩ := rReady.pushDetailed (prog := prog) (gt := gt)
  have rOpenedSingleton :
      (openedFor middle.index.session "r" [resultTerm]
        middle.index.current).cursor.remaining = [siblingRPreparedBranch] := by
    rw [middleCurrentNil]
    change
      (prepareCall middle.index.session.resolver
        (requestFor "r" [resultTerm] [])).1.remaining =
          [siblingRPreparedBranch]
    simp only [prepareCall, requestFor]
    rw [middleDatabase, middleNextFresh]
    change
      (reserveVisible siblingReferenceDatabase.generation [resultTerm] [] 0
        (siblingReferenceDatabase.visibleClausesAt
          siblingReferenceDatabase.generation "r" 1)).1 =
        [siblingRPreparedBranch]
    rw [siblingRVisibleClauses]
    rfl
  have rFinishNonempty : rFinish.remaining ≠ [] := by
    rw [rFacts.frontier.finishRemaining]
    simp
  have rPullsConcrete :
      RejectedPullsN rCount
        (openedFor middle.index.session "r" [resultTerm]
          middle.index.current).cursor rFinish := by
    simpa [rPredicate, rPayload] using rFacts.pulls
  have rPathExact :=
    _root_.Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyBridge.RejectedPullsN.eq_zero_of_singleton_of_finish_nonempty
      rOpenedSingleton rPullsConcrete rFinishNonempty
  have rCountZero : rCount = 0 := rPathExact.1
  have rBranchExact : rBranch = siblingRPreparedBranch := by
    have remaining := rFacts.frontier.finishRemaining
    rw [rPathExact.2, rOpenedSingleton] at remaining
    exact (List.cons.inj remaining).1.symm
  have rSkippedClausesNil : rSkippedClauses = [] := by
    apply List.eq_nil_of_length_eq_zero
    rw [rFacts.executableSkipCount, rCountZero]
  have rExecutableShape := rFacts.executableBank
  rw [rPredicate, rArguments, middleWorld, rSkippedClausesNil] at rExecutableShape
  simp only [List.length_nil] at rExecutableShape
  rw [siblingRResolutionCandidates] at rExecutableShape
  have rClauseExact : rClause = rExecutableClause :=
    (List.cons.inj rExecutableShape).1.symm
  have rClauseTailNil : rClauseTail = [] :=
    (List.cons.inj rExecutableShape).2.symm
  have rCopiedBody : rCopied.body = [] := by
    rw [rFacts.frontier.copiedExact, rClauseExact]
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.freshenResolutionClause, rExecutableClause]
  have rAltTailNil : rAltTail = [] := by
    have scan := rFacts.frontier.tailScan
    rw [rClauseTailNil] at scan
    exact (scan.deterministic (ResolutionScan.nil _)).1
  have afterBodyReferences : after.index.bodyReferences = [] := by
    rw [rFacts.bodyReferences, rBranchExact]
    rfl
  have afterBodyExecutables : after.index.bodyExecutables = [] := by
    rw [rFacts.bodyExecutables, rCopiedBody]
  have afterActiveEmpty : after.index.active.alts = [] := by
    rw [rFacts.activeAltsExact, rAltTailNil]
  have afterGeneratedBelow :
      GeneratedBelow rBranch.firstFresh (after.index.alpha.map Prod.fst) := by
    simpa [rBranchExact, siblingRPreparedBranch] using
      rFacts.selectionFresh.1
  have afterAlphaMiddle : after.index.alpha = middle.index.alpha :=
    rFacts.alphaExtension.eq_of_generatedBelow afterGeneratedBelow
  have afterAlphaNil : after.index.alpha = [] :=
    afterAlphaMiddle.trans middleAlphaNil
  have afterSupportNil : after.index.support = [] :=
    rFacts.supportPreserved.trans middleSupportNil
  have afterResourcesExact :
      after.index.resources = [middle.index.active, before.index.active] := by
    rw [rFacts.resourcesExact, middleResourcesExact]
  have rCertificate :
      NestedCallPushCertificate prog gt 0
        (requestFor "r" [resultTerm] []) middle after := by
    simpa [rCountZero, rPredicate, rPayload, middleCurrentNil] using
      rFacts.certificate
  have sourceSteps :=
    StepsN.trans rootSourceSteps
      (StepsN.trans qCertificate.sourceSteps rCertificate.sourceSteps)
  have fineSteps :=
    DemandDrivenCallStep.StepsN.trans rootFineSteps
      (DemandDrivenCallStep.StepsN.trans qCertificate.fineSteps
        rCertificate.fineSteps)
  refine
    ⟨after, middle.index.active, before.index.active, afterAlphaNil,
      afterSupportNil, afterActiveEmpty, afterResourcesExact,
      middleActiveEmpty, ?_, afterBodyReferences, afterBodyExecutables, ?_, ?_⟩
  · rw [beforeActiveLive]
    simp
  · simpa using sourceSteps
  · simpa using fineSteps

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologNestedCallReadyRegression
