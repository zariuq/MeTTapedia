import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.DeploymentAcceptance
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Path

/-!
# Exhaustive static deployment analysis

The concrete cost-rho calculus is Turing complete, so deployment sufficiency
cannot depend on a total termination oracle.  This module instead computes the
complete finite call tree up to an explicit depth.  It returns a certificate
only when every leaf is genuinely quiescent; a live leaf at the depth bound
returns no analysis.

The analysis follows the independent raw-syntax frontier and preserves exact
purse-head occurrences.  Literal `drop (quote term)` remains inert, matching
the concrete runtime: only COMM substitution opens a bound drop.  A different
paper-level resolver would therefore require a separately named analysis and a
new soundness bridge.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

/-- One raw located purse-head occurrence, before decoding to typed syntax. -/
abbrev RawFundingCell := RawCostName × RawCostSig

namespace RawRuntimeStep

/-- Exact located purse-head demand of one executable candidate. -/
def fundingDemand (step : RawRuntimeStep) : Multiset RawFundingCell :=
  step.selectedPurses.map fun purse => (purse.surface, purse.head)

end RawRuntimeStep

namespace RawEmittedEvent

/-- Erase causal metadata while retaining every emitted funding occurrence. -/
def fundingDemand (event : RawEmittedEvent) : Multiset RawFundingCell :=
  event.funding.map fun contribution => (contribution.surface, contribution.spend)

@[simp]
theorem fundingDemand_eventFor (components : List RawTraceComponent)
    (step : RawRuntimeStep) (eventId : Nat) :
    (eventFor components step eventId).fundingDemand = step.fundingDemand := by
  unfold fundingDemand RawRuntimeStep.fundingDemand eventFor
  apply Quot.sound
  simp [Function.comp_def]

end RawEmittedEvent

namespace RawReceipt

/-- Total occurrence-preserving funding demand emitted by a raw receipt. -/
def fundingDemand (receipt : RawReceipt) : Multiset RawFundingCell :=
  (receipt.map RawEmittedEvent.fundingDemand).sum

end RawReceipt

/-- A finite exhaustive tree of concrete runtime choices.  A branch node keeps
the exact candidate occurrence and its recursively analyzed successor. -/
inductive StaticCallTree where
  | quiescent
  | branch (children : List (RawRuntimeStep × StaticCallTree))
  deriving Repr

namespace StaticCallTree

/-- Sum the exact purse-head demand along a candidate sequence. -/
def stepsDemand : List RawRuntimeStep → Multiset RawFundingCell
  | [] => 0
  | step :: rest => step.fundingDemand + stepsDemand rest

/-- All complete branch demands represented by a static call tree. -/
def branchDemands : StaticCallTree → List (Multiset RawFundingCell)
  | .quiescent => [0]
  | .branch children =>
      children.flatMap fun child =>
        child.2.branchDemands.map fun tail => child.1.fundingDemand + tail
termination_by tree => sizeOf tree
decreasing_by
  have child_lt := List.sizeOf_lt_of_mem ‹_ ∈ children›
  have component_lt : sizeOf child.2 < sizeOf child := by
    rcases child with ⟨step, subtree⟩
    simp
  simp_wf
  omega

/-- Structural induction principle for the finite rose tree.  Lean's default
recursor does not descend through the nested child list. -/
theorem inductionOn {motive : StaticCallTree → Prop}
    (tree : StaticCallTree)
    (quiescent : motive .quiescent)
    (branch : ∀ children,
      (∀ child, child ∈ children → motive child.2) →
      motive (.branch children)) : motive tree := by
  cases tree with
  | quiescent => exact quiescent
  | branch children =>
      apply branch children
      intro child member
      exact inductionOn child.2 quiescent branch
termination_by sizeOf tree
decreasing_by
  have child_lt := List.sizeOf_lt_of_mem member
  have component_lt : sizeOf child.2 < sizeOf child := by
    rcases child with ⟨step, subtree⟩
    simp
  simp_wf
  omega

/-- A maximal path through the call tree.  Its only terminal constructor is a
quiescent leaf, so it cannot certify a prefix cut off by the analysis bound. -/
inductive Branch : StaticCallTree → List RawRuntimeStep → Prop where
  | quiescent : Branch .quiescent []
  | select {children step subtree rest}
      (member : (step, subtree) ∈ children)
      (tail : Branch subtree rest) :
      Branch (.branch children) (step :: rest)

/-- The tree is an exact finite unfolding of the independent runtime frontier,
with well-formedness and causal-provenance bounds preserved at every node. -/
inductive Valid : Nat → List RawTraceComponent → StaticCallTree → Prop where
  | quiescent
      {nextId components}
      (supported : TraceComponentsWellFormed components)
      (bounded : TraceComponentsBefore nextId components)
      (frontier_empty :
        runtimeCostCandidatesFromConfig
          (components.map RawTraceComponent.term) = []) :
      Valid nextId components .quiescent
  | branch
      {nextId components children}
      (supported : TraceComponentsWellFormed components)
      (bounded : TraceComponentsBefore nextId components)
      (children_nonempty : children ≠ [])
      (frontier_exact :
        children.map Prod.fst = runtimeCostCandidatesFromConfig
          (components.map RawTraceComponent.term))
      (children_valid : ∀ {step subtree}, (step, subtree) ∈ children →
        Valid (nextId + 1) (applyTracedStep components step nextId) subtree) :
      Valid nextId components (.branch children)

/-- Sequence a list of candidates whose child analyses may have failed,
retaining the candidate attached to every successful child. -/
private def collectChildren {α β : Type}
    : List (α × Option β) → Option (List (α × β))
  | [] => some []
  | (key, some value) :: rest =>
      ((key, value) :: ·) <$> collectChildren rest
  | (_, none) :: _ => none

private theorem collectChildren_fst {α β : Type}
    {source : List (α × Option β)} {target : List (α × β)}
    (collected : collectChildren source = some target) :
    target.map Prod.fst = source.map Prod.fst := by
  induction source generalizing target with
  | nil =>
      simp [collectChildren] at collected
      simp [collected]
  | cons head tail induction =>
      rcases head with ⟨key, value⟩
      cases value with
      | none => simp [collectChildren] at collected
      | some child =>
          simp only [collectChildren, Option.map_eq_map] at collected
          cases tailResult : collectChildren tail with
          | none => simp [tailResult] at collected
          | some children =>
              simp [tailResult] at collected
              subst target
              simp [induction tailResult]

private theorem collectChildren_member {α β : Type}
    {source : List (α × Option β)} {target : List (α × β)}
    (collected : collectChildren source = some target)
    {key : α} {value : β} (member : (key, value) ∈ target) :
    (key, some value) ∈ source := by
  induction source generalizing target with
  | nil =>
      simp [collectChildren] at collected
      subst target
      simp at member
  | cons head tail induction =>
      rcases head with ⟨headKey, headValue⟩
      cases headValue with
      | none => simp [collectChildren] at collected
      | some headChild =>
          simp only [collectChildren, Option.map_eq_map] at collected
          cases tailResult : collectChildren tail with
          | none => simp [tailResult] at collected
          | some children =>
              simp [tailResult] at collected
              subst target
              rcases List.mem_cons.mp member with equality | tailMember
              · injection equality with keyEq valueEq
                subst keyEq
                subst valueEq
                simp
              · exact List.mem_cons_of_mem _
                  (induction tailResult tailMember)

/-- Compute a complete call tree when every runtime branch reaches quiescence
within the supplied depth.  `none` means only that this bound did not certify
completion; it is not a negative claim about termination. -/
def analyze : Nat → Nat → List RawTraceComponent → Option StaticCallTree
  | 0, _, components =>
      if runtimeCostCandidatesFromConfig
          (components.map RawTraceComponent.term) = [] then
        some .quiescent
      else
        none
  | fuel + 1, nextId, components =>
      let frontier := runtimeCostCandidatesFromConfig
        (components.map RawTraceComponent.term)
      if frontier = [] then
        some .quiescent
      else
        let attempted := frontier.map fun step =>
          (step, analyze fuel (nextId + 1)
            (applyTracedStep components step nextId))
        .branch <$> collectChildren attempted

/-- A successful exhaustive analysis is a valid, exact unfolding of the
runtime frontier. -/
theorem analyze_sound :
    ∀ {fuel nextId components tree},
      TraceComponentsWellFormed components →
      TraceComponentsBefore nextId components →
      analyze fuel nextId components = some tree →
      Valid nextId components tree := by
  intro fuel
  induction fuel with
  | zero =>
      intro nextId components tree supported bounded analyzed
      simp only [analyze] at analyzed
      split at analyzed
      next frontierEmpty =>
        injection analyzed with treeEq
        subst treeEq
        exact .quiescent supported bounded frontierEmpty
      next _ => simp at analyzed
  | succ fuel induction =>
      intro nextId components tree supported bounded analyzed
      simp only [analyze] at analyzed
      let frontier := runtimeCostCandidatesFromConfig
        (components.map RawTraceComponent.term)
      change (if frontier = [] then some .quiescent else _) = some tree at analyzed
      split at analyzed
      next frontierEmpty =>
        injection analyzed with treeEq
        subst treeEq
        exact .quiescent supported bounded frontierEmpty
      next frontierNonempty =>
        let attempted := frontier.map fun step =>
          (step, analyze fuel (nextId + 1)
            (applyTracedStep components step nextId))
        change StaticCallTree.branch <$> collectChildren attempted = some tree at analyzed
        cases collectedEq : collectChildren attempted with
        | none => simp [collectedEq] at analyzed
        | some children =>
            simp [collectedEq] at analyzed
            subst tree
            have fstEq : children.map Prod.fst = frontier := by
              calc
                children.map Prod.fst = attempted.map Prod.fst :=
                  collectChildren_fst collectedEq
                _ = frontier := by
                  simp [attempted, Function.comp_def]
            apply Valid.branch supported bounded
              (fun empty => frontierNonempty (fstEq ▸ congrArg (List.map Prod.fst) empty))
              fstEq
            intro step subtree member
            have attemptedMember := collectChildren_member collectedEq member
            obtain ⟨sourceStep, sourceMember, sourceEq⟩ :=
              List.mem_map.mp attemptedMember
            simp only [Prod.mk.injEq] at sourceEq
            rcases sourceEq with ⟨stepEq, treeEq⟩
            subst sourceStep
            have enabled : step ∈ runtimeCostCandidatesFromConfig
                (components.map RawTraceComponent.term) := by
              simpa [frontier] using sourceMember
            exact induction
              (applyTracedStep_wellFormed supported enabled nextId)
              (applyTracedStep_before bounded step)
              treeEq

/-- Every valid tree contains at least its quiescent empty branch. -/
theorem branchDemands_nonempty {nextId components tree}
    (valid : Valid nextId components tree) : tree.branchDemands ≠ [] := by
  induction valid with
  | quiescent =>
      rw [branchDemands]
      simp
  | @branch _ _ children _ _ childrenNonempty _ childrenValid induction =>
      obtain ⟨child, rest, childrenEq⟩ := List.exists_cons_of_ne_nil childrenNonempty
      subst childrenEq
      rcases child with ⟨step, subtree⟩
      have subtreeNonempty : subtree.branchDemands ≠ [] :=
        induction (step := step) (subtree := subtree) (by simp)
      rw [branchDemands]
      simp [subtreeNonempty]

/-- A represented branch has exactly the demand recorded in the tree. -/
theorem branch_stepsDemand_mem {tree steps}
    (branch : Branch tree steps) : stepsDemand steps ∈ tree.branchDemands := by
  induction branch with
  | quiescent =>
      rw [stepsDemand, branchDemands]
      simp
  | @select children step subtree rest member tail induction =>
      rw [branchDemands]
      simp only [List.mem_flatMap]
      refine ⟨(step, subtree), member, ?_⟩
      simp only [List.mem_map]
      exact ⟨stepsDemand rest, induction, by simp [stepsDemand]⟩

/-- The analyzer invents no branch demand: every entry is generated by a
maximal quiescent path through the exact call tree. -/
theorem mem_branchDemands_iff {tree demand} :
    demand ∈ tree.branchDemands ↔
      ∃ steps, Branch tree steps ∧ stepsDemand steps = demand := by
  constructor
  · intro member
    have allTrees : ∀ candidate : StaticCallTree,
        ∀ candidateDemand,
          candidateDemand ∈ candidate.branchDemands →
          ∃ steps, Branch candidate steps ∧
            stepsDemand steps = candidateDemand := by
      intro candidate
      apply inductionOn candidate
      · intro candidateDemand candidateMember
        rw [branchDemands] at candidateMember
        simp only [List.mem_singleton] at candidateMember
        exact ⟨[], .quiescent, by simpa [stepsDemand] using candidateMember.symm⟩
      · intro children induction candidateDemand candidateMember
        rw [branchDemands] at candidateMember
        simp only [List.mem_flatMap, List.mem_map] at candidateMember
        obtain ⟨⟨step, subtree⟩, childMember,
          tailDemand, tailMember, demandEq⟩ := candidateMember
        obtain ⟨tailSteps, tailBranch, tailEq⟩ :=
          induction (step, subtree) childMember tailDemand tailMember
        refine ⟨step :: tailSteps, Branch.select childMember tailBranch, ?_⟩
        simpa [stepsDemand, tailEq] using demandEq
    exact allTrees tree demand member
  · rintro ⟨steps, branch, rfl⟩
    exact branch_stepsDemand_mem branch

/-- A branch of a valid exhaustive tree is an actual occurrence-bearing cost
path ending at a state whose independent runtime frontier is empty. -/
theorem Branch.toCostPath {tree steps nextId components}
    (branch : Branch tree steps) (valid : Valid nextId components tree) :
    ∃ finalId finalComponents,
      ∃ path : CostPath nextId components finalId finalComponents,
      path.steps = steps ∧
      runtimeCostCandidatesFromConfig
        (finalComponents.map RawTraceComponent.term) = [] := by
  induction branch generalizing nextId components with
  | quiescent =>
      cases valid with
      | quiescent supported bounded frontierEmpty =>
          exact ⟨nextId, components, .done supported bounded, rfl, frontierEmpty⟩
  | @select children step subtree rest member tail induction =>
      cases valid with
      | branch supported bounded _ frontierExact childrenValid =>
          have enabled : step ∈ runtimeCostCandidatesFromConfig
              (components.map RawTraceComponent.term) := by
            rw [← frontierExact]
            exact List.mem_map.mpr ⟨(step, subtree), member, rfl⟩
          obtain ⟨finalId, finalComponents, path, stepsEq, frontierEmpty⟩ :=
            induction (childrenValid member)
          exact ⟨finalId, finalComponents,
            .fire supported bounded step enabled path,
            by simp [CostPath.steps, stepsEq], frontierEmpty⟩

/-- Receipt demand and selected-step demand agree for every actual cost path. -/
theorem CostPath.rawEmission_fundingDemand_eq_stepsDemand
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.rawEmission.fundingDemand = stepsDemand path.steps := by
  induction path with
  | done => rfl
  | fire _ _ step _ rest induction =>
      change (eventFor _ step _).fundingDemand +
          rest.rawEmission.fundingDemand =
        step.fundingDemand + stepsDemand rest.steps
      rw [RawEmittedEvent.fundingDemand_eventFor, induction]

/-- Every demand reported by a valid static analysis is witnessed by a real
complete path with an identical occurrence-preserving receipt demand. -/
theorem demand_realized_by_complete_path {tree nextId components demand}
    (valid : Valid nextId components tree)
    (member : demand ∈ tree.branchDemands) :
    ∃ finalId finalComponents,
      ∃ path : CostPath nextId components finalId finalComponents,
      runtimeCostCandidatesFromConfig
          (finalComponents.map RawTraceComponent.term) = [] ∧
      path.rawEmission.fundingDemand = demand := by
  obtain ⟨steps, branch, stepsEq⟩ := mem_branchDemands_iff.mp member
  obtain ⟨finalId, finalComponents, path, pathSteps, frontierEmpty⟩ :=
    branch.toCostPath valid
  refine ⟨finalId, finalComponents, path, frontierEmpty, ?_⟩
  rw [CostPath.rawEmission_fundingDemand_eq_stepsDemand path, pathSteps, stepsEq]

/-- Every complete concrete path in the analyzed call tree contributes its
exact receipt demand to the deployment envelope. -/
theorem complete_path_demand_mem {tree nextId components finalId finalComponents}
    (valid : Valid nextId components tree)
    (path : CostPath nextId components finalId finalComponents)
    (quiescent : runtimeCostCandidatesFromConfig
      (finalComponents.map RawTraceComponent.term) = []) :
    path.rawEmission.fundingDemand ∈ tree.branchDemands := by
  induction path generalizing tree with
  | done =>
      cases valid with
      | quiescent =>
          rw [CostPath.rawEmission, RawReceipt.fundingDemand, branchDemands]
          simp
      | @branch _ _ children _ _ childrenNonempty frontierExact _ =>
          have mappedEmpty : List.map Prod.fst children = [] :=
            frontierExact.trans quiescent
          have childrenEmpty : children = [] := by
            simpa only [List.map_eq_nil_iff] using mappedEmpty
          exact False.elim (childrenNonempty childrenEmpty)
  | @fire start components finish finalComponents supported bounded step enabled rest induction =>
      cases valid with
      | quiescent _ _ frontierEmpty =>
          simp [frontierEmpty] at enabled
      | @branch _ _ children _ _ _ frontierExact childrenValid =>
          have childStep : step ∈ children.map Prod.fst := by
            rw [frontierExact]
            exact enabled
          obtain ⟨child, childMember, childFst⟩ := List.mem_map.mp childStep
          rcases child with ⟨childStep, subtree⟩
          dsimp at childFst
          subst childStep
          have tailMember := induction (childrenValid childMember)
            quiescent
          change (eventFor components step start).fundingDemand +
              rest.rawEmission.fundingDemand ∈
            (StaticCallTree.branch children).branchDemands
          rw [RawEmittedEvent.fundingDemand_eventFor, branchDemands]
          apply List.mem_flatMap.mpr
          exact ⟨(step, subtree), childMember,
            List.mem_map.mpr ⟨rest.rawEmission.fundingDemand, tailMember, rfl⟩⟩

/-- Convert a valid call tree into the generic linear acceptance input. -/
def Valid.toAnalyzedDeployment {nextId components tree}
    (valid : Valid nextId components tree) :
    AnalyzedDeployment RawFundingCell where
  branches := tree.branchDemands
  branches_nonempty := branchDemands_nonempty valid

/-- Public exhaustive static analyzer.  It rejects malformed syntax and
returns no certificate when the chosen depth leaves any live branch. -/
def analyzeDeployment? (fuel : Nat) (term : RawCostTerm) :
    Option (AnalyzedDeployment RawFundingCell) :=
  if supported : term.wellFormed = true then
    let components := initialTraceComponents term
    match analyzed : analyze fuel 0 components with
    | none => none
    | some _tree =>
        some ((analyze_sound
          (initialTraceComponents_wellFormed supported)
          (initialTraceComponents_before term) analyzed).toAnalyzedDeployment)
  else
    none

/-- Three-way deployment result.  Failure to close the call tree is distinct
from a completed analysis whose resource envelope is insufficient. -/
inductive StaticDeploymentCheck (supply : Multiset RawFundingCell) where
  | analysisIncomplete
  | accepted (deployment : AnalyzedDeployment RawFundingCell)
      (reservation : DeploymentReservation deployment supply)
  | insufficient (deployment : AnalyzedDeployment RawFundingCell)
      (proof : ¬deployment.conservativeDemand ≤ supply)

/-- Analyze all concrete branches and, only after a complete call tree exists,
run the linear reservation checker. -/
def checkDeployment (fuel : Nat) (term : RawCostTerm)
    (supply : Multiset RawFundingCell) : StaticDeploymentCheck supply :=
  match analyzeDeployment? fuel term with
  | none => .analysisIncomplete
  | some deployment =>
      match DeploymentDecision.check deployment supply with
      | .accepted reservation => .accepted deployment reservation
      | .rejected insufficient => .insufficient deployment insufficient

/-- Analysis exhaustion and funding insufficiency are observably distinct. -/
theorem checkDeployment_analysisIncomplete_iff
    (fuel : Nat) (term : RawCostTerm) (supply : Multiset RawFundingCell) :
    checkDeployment fuel term supply = .analysisIncomplete ↔
      analyzeDeployment? fuel term = none := by
  unfold checkDeployment
  cases analyzed : analyzeDeployment? fuel term with
  | none => simp
  | some deployment =>
      cases decision : DeploymentDecision.check deployment supply <;>
        simp [decision]

/-- Once analysis succeeds, reserving its own conservative envelope is always
accepted and returns an explicit linear reservation certificate. -/
theorem checkDeployment_accepts_conservativeDemand
    {fuel : Nat} {term : RawCostTerm}
    {deployment : AnalyzedDeployment RawFundingCell}
    (analyzed : analyzeDeployment? fuel term = some deployment) :
    ∃ reservation : DeploymentReservation deployment
        deployment.conservativeDemand,
      checkDeployment fuel term deployment.conservativeDemand =
        .accepted deployment reservation := by
  let reservation : DeploymentReservation deployment
      deployment.conservativeDemand :=
    DeploymentReservation.of_le (le_refl deployment.conservativeDemand)
  refine ⟨reservation, ?_⟩
  simp [checkDeployment, analyzed, DeploymentDecision.check, reservation]

/-- A completed analysis with an insufficient supplied inventory reports
resource failure, never analysis exhaustion. -/
theorem checkDeployment_reports_insufficient
    {fuel : Nat} {term : RawCostTerm} {supply : Multiset RawFundingCell}
    {deployment : AnalyzedDeployment RawFundingCell}
    (analyzed : analyzeDeployment? fuel term = some deployment)
    (insufficient : ¬deployment.conservativeDemand ≤ supply) :
    checkDeployment fuel term supply =
      .insufficient deployment insufficient := by
  simp [checkDeployment, analyzed, DeploymentDecision.check, insufficient]

/-- A complete accepted analysis carries enough supply for each concrete
reachable branch. -/
theorem checkDeployment_acceptance_sound
    {fuel : Nat} {term : RawCostTerm} {supply : Multiset RawFundingCell}
    {deployment : AnalyzedDeployment RawFundingCell}
    {reservation : DeploymentReservation deployment supply}
    (_checked : checkDeployment fuel term supply =
      .accepted deployment reservation)
    {branch : Multiset RawFundingCell}
    (member : branch ∈ deployment.branches) : branch ≤ supply :=
  reservation.branch_le_supply member

/-- Applying a checked result is atomic: only an accepted reservation changes
the validator state. -/
def StaticDeploymentCheck.apply
    {supply : Multiset RawFundingCell}
    (checked : StaticDeploymentCheck supply)
    (acceptedCount : Nat) : FundingValidatorState RawFundingCell :=
  match checked with
  | .analysisIncomplete => ⟨supply, acceptedCount⟩
  | .accepted _ reservation =>
      ⟨reservation.remaining, acceptedCount + 1⟩
  | .insufficient _ _ => ⟨supply, acceptedCount⟩

@[simp]
theorem StaticDeploymentCheck.apply_analysisIncomplete
    (supply : Multiset RawFundingCell) (acceptedCount : Nat) :
    (StaticDeploymentCheck.analysisIncomplete (supply := supply)).apply
      acceptedCount = ⟨supply, acceptedCount⟩ := rfl

@[simp]
theorem StaticDeploymentCheck.apply_insufficient
    {supply : Multiset RawFundingCell}
    (deployment : AnalyzedDeployment RawFundingCell)
    (insufficient : ¬deployment.conservativeDemand ≤ supply)
    (acceptedCount : Nat) :
    (StaticDeploymentCheck.insufficient deployment insufficient).apply
      acceptedCount = ⟨supply, acceptedCount⟩ := rfl

end StaticCallTree

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
