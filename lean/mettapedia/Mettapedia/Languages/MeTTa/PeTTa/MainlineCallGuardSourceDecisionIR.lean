import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardFusedDecisionProgram
import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceMatchPlan

/-!
# Source-derived decision IR for the PeTTa call guard

This pass traverses the complete fused source decision program.  Constructor
switches, projection drops, fallback order, residual structural patterns, and
source occurrences are copied structurally.  Each selected leaf is enriched
by compiling its complete left-hand side to a typed state matcher and its
ordered premises and right-hand side to a StructuredC action block.

The compiler does not inspect occurrence numbers or require an exact rule
inventory.  Unsupported matcher or target structure rejects the containing
program.  Erasure reconstructs the fused source program exactly, and the
independent residual evaluator preserves its complete ordered semantics.
Lowering the typed matchers to physical StructuredC tests is a subsequent
pass; this module does not claim target execution adequacy prematurely.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDecisionIR

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardOperational
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPatternMatrixCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardRulePlanCompilation
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardFusedDecisionProgram
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceMatchPlan

namespace Matrix

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
  (Pattern Subject ConstructorKey DecisionTree DecisionBranches)

end Matrix

namespace Fusion

export Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
  (CompiledRule Program Branches)

end Fusion

namespace FusionSemantics

export Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program
  (evalAll evalBranchAll)

end FusionSemantics

namespace FirstOrder

export Mettapedia.GSLT.LanguageDef.MeTTaILFirstOrderRuleCompilation
  (RulePlan)

end FirstOrder

universe uHead uResult

variable {Head : Type uHead} {Result : Type uResult}

/-! ## Residual decision data -/

/-- Forget target-specific leaf enrichments while retaining the exact fused
source occurrence and rule plan. -/
def eraseLeaf (branch : CompiledBranch) :
    Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan :=
  { occurrence := branch.occurrence, plan := branch.rule }

/-- Compile one selected fused leaf from the rule data already stored there.
No occurrence-indexed lookup or rule-family dispatch occurs in this pass. -/
def compileLeaf? (source :
    Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan) :
    Option CompiledBranch :=
  compileSelectedRule? source.occurrence source.plan

/-- Successful leaf compilation erases to the exact selected source leaf. -/
theorem sourceRule_of_compileLeaf?
    {source : Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan}
    {target : CompiledBranch}
    (compiled : compileLeaf? source = some target) :
    eraseLeaf target = source := by
  rcases compileSelectedRule?_exact compiled with
    ⟨occurrenceExact, ruleExact⟩
  cases source with
  | mk occurrence rule =>
      simp only [eraseLeaf]
      cases occurrenceExact
      cases ruleExact
      rfl

/-- A fused leaf produced from an authored occurrence compiles to that
occurrence's independently validated target leaf. -/
theorem compileLeaf?_of_planOptionAt
    {occurrence : SourceOccurrence} {plan : FirstOrder.RulePlan}
    (compiled : planOptionAt occurrence = some plan) :
    compileLeaf? ⟨occurrence, plan⟩ = some (branchAt occurrence) := by
  have branchCompiled := branchAt_compilation_exact occurrence
  unfold compileBranch? at branchCompiled
  simpa [compileLeaf?, compiled] using branchCompiled

mutual
  /-- Backend-neutral decision structure with source-derived target leaves. -/
  inductive Program (Head : Type uHead) where
    | failure
    | drop (next : Program Head)
    | tryRule (compiled : CompiledBranch)
        (patterns : List (Matrix.Pattern Head))
        (onFailure : Program Head)
    | switch (branches : Branches Head) (default : Program Head)

  /-- Ordered constructor branches of a source-derived residual program. -/
  inductive Branches (Head : Type uHead) where
    | nil
    | cons (key : Matrix.ConstructorKey Head) (program : Program Head)
        (rest : Branches Head)
end

mutual
  /-- Compile every node of a fused decision program. -/
  def compile? :
      Fusion.Program Head SourceOccurrence FirstOrder.RulePlan →
        Option (Program Head)
    | .failure => some .failure
    | .drop next =>
        match compile? next with
        | none => none
        | some compiledNext => some (.drop compiledNext)
    | .tryRule source patterns onFailure =>
        match compileLeaf? source with
        | none => none
        | some compiledLeaf =>
            match compile? onFailure with
            | none => none
            | some compiledFailure =>
                some (.tryRule compiledLeaf patterns compiledFailure)
    | .switch branches default =>
        match compileBranches? branches with
        | none => none
        | some compiledBranches =>
            match compile? default with
            | none => none
            | some compiledDefault =>
                some (.switch compiledBranches compiledDefault)

  /-- Compile every constructor branch without reordering it. -/
  def compileBranches? :
      Fusion.Branches Head SourceOccurrence FirstOrder.RulePlan →
        Option (Branches Head)
    | .nil => some .nil
    | .cons key program rest =>
        match compile? program with
        | none => none
        | some compiledProgram =>
            match compileBranches? rest with
            | none => none
            | some compiledRest =>
                some (.cons key compiledProgram compiledRest)
end

mutual
  /-- Structural leaf compilation succeeds for every program obtained by
  fusing an authored source tree.  Unsupported foreign leaves still fail;
  success follows here from the source-fusion certificate. -/
  theorem compile?_exists_of_fusion
      (tree : Matrix.DecisionTree Head SourceOccurrence)
      (fused : Fusion.Program Head SourceOccurrence FirstOrder.RulePlan)
      (fusedCompiled :
        Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?
          planOptionAt tree = some fused) :
      ∃ target, compile? fused = some target := by
    cases tree with
    | failure =>
        simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?]
          at fusedCompiled
        subst fused
        exact ⟨Program.failure, rfl⟩
    | tryRule occurrence patterns onFailure =>
        cases planCompiled : planOptionAt occurrence with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?,
              planCompiled] at fusedCompiled
        | some plan =>
            cases failureFused :
                Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?
                  planOptionAt onFailure with
            | none =>
                simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?,
                  planCompiled, failureFused] at fusedCompiled
            | some fusedFailure =>
                simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?,
                  planCompiled, failureFused] at fusedCompiled
                subst fused
                obtain ⟨compiledFailure, failureExact⟩ :=
                  compile?_exists_of_fusion onFailure fusedFailure failureFused
                refine ⟨Program.tryRule (branchAt occurrence) patterns
                  compiledFailure, ?_⟩
                simp [compile?, compileLeaf?_of_planOptionAt planCompiled,
                  failureExact]
    | switch branches default =>
        cases branchesFused :
            Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?
              planOptionAt branches with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?,
              branchesFused] at fusedCompiled
        | some fusedBranches =>
            cases defaultFused :
                Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?
                  planOptionAt default with
            | none =>
                simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?,
                  branchesFused, defaultFused] at fusedCompiled
            | some fusedDefault =>
                simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?,
                  branchesFused, defaultFused] at fusedCompiled
                subst fused
                obtain ⟨compiledBranches, branchesExact⟩ :=
                  compileBranches?_exists_of_fusion branches fusedBranches
                    branchesFused
                obtain ⟨compiledDefault, defaultExact⟩ :=
                  compile?_exists_of_fusion default fusedDefault defaultFused
                exact ⟨Program.switch compiledBranches compiledDefault, by
                  simp [compile?, branchesExact, defaultExact]⟩
  termination_by sizeOf tree

  /-- Branch companion to `compile?_exists_of_fusion`. -/
  theorem compileBranches?_exists_of_fusion
      (branches : Matrix.DecisionBranches Head SourceOccurrence)
      (fused : Fusion.Branches Head SourceOccurrence FirstOrder.RulePlan)
      (fusedCompiled :
        Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?
          planOptionAt branches = some fused) :
      ∃ target, compileBranches? fused = some target := by
    cases branches with
    | nil =>
        simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?]
          at fusedCompiled
        subst fused
        exact ⟨Branches.nil, rfl⟩
    | cons key tree rest =>
        cases treeFused :
            Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compile?
              planOptionAt tree with
        | none =>
            simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?,
              treeFused] at fusedCompiled
        | some fusedTree =>
            cases restFused :
                Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?
                  planOptionAt rest with
            | none =>
                simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?,
                  treeFused, restFused] at fusedCompiled
            | some fusedRest =>
                simp [Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.compileBranches?,
                  treeFused, restFused] at fusedCompiled
                subst fused
                obtain ⟨compiledTree, treeExact⟩ :=
                  compile?_exists_of_fusion tree fusedTree treeFused
                obtain ⟨compiledRest, restExact⟩ :=
                  compileBranches?_exists_of_fusion rest fusedRest restFused
                exact ⟨Branches.cons key compiledTree compiledRest, by
                  simp [compileBranches?, treeExact, restExact]⟩
  termination_by sizeOf branches
end

namespace Program

mutual
  /-- Erase target leaf data back to the fused source decision program. -/
  def erase : Program Head →
      Fusion.Program Head SourceOccurrence FirstOrder.RulePlan
    | .failure => .failure
    | .drop next => .drop next.erase
    | .tryRule compiled patterns onFailure =>
        .tryRule (eraseLeaf compiled) patterns onFailure.erase
    | .switch branches default =>
        .switch (Program.Branches.erase branches) default.erase

  /-- Erase an ordered residual branch sequence. -/
  def Branches.erase : Branches Head →
      Fusion.Branches Head SourceOccurrence FirstOrder.RulePlan
    | .nil => .nil
    | .cons key program rest =>
        .cons key program.erase (Program.Branches.erase rest)
end

mutual
  /-- Evaluate every successful residual leaf in authored order. -/
  def evalAll [DecidableEq Head]
      (runLeaf : CompiledBranch → List Result) :
      Program Head → List (Matrix.Subject Head) → List Result
    | .failure, _ => []
    | .drop _, [] => []
    | .drop next, _ :: subjects => evalAll runLeaf next subjects
    | .tryRule compiled patterns onFailure, subjects =>
        let tail := evalAll runLeaf onFailure subjects
        if Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.structuralMatchList
            patterns subjects then
          runLeaf compiled ++ tail
        else
          tail
    | .switch branches default, subjects =>
        match subjects with
        | [] => evalAll runLeaf default []
        | .node head children :: rest =>
            evalBranchAll runLeaf { head, arity := children.length }
                (children ++ rest) branches ++
              evalAll runLeaf default subjects

  /-- Evaluate the unique constructor branch selected by a query. -/
  def evalBranchAll [DecidableEq Head]
      (runLeaf : CompiledBranch → List Result)
      (query : Matrix.ConstructorKey Head)
      (subjects : List (Matrix.Subject Head)) :
      Branches Head → List Result
    | .nil => []
    | .cons key program rest =>
        if query = key then evalAll runLeaf program subjects
        else evalBranchAll runLeaf query subjects rest
end

end Program

/-! ## Exact structural and semantic preservation -/

mutual
  /-- A successful structural compilation erases to its complete input tree. -/
  theorem erase_of_compile?
      (source : Fusion.Program Head SourceOccurrence FirstOrder.RulePlan)
      (target : Program Head) (compiled : compile? source = some target) :
      target.erase = source := by
    cases source with
    | failure =>
        simp [compile?] at compiled
        subst target
        rfl
    | drop next =>
        cases nextCompiled : compile? next with
        | none => simp [compile?, nextCompiled] at compiled
        | some compiledNext =>
            simp [compile?, nextCompiled] at compiled
            subst target
            simp [Program.erase,
              erase_of_compile? next compiledNext nextCompiled]
    | tryRule sourceLeaf patterns onFailure =>
        cases leafCompiled : compileLeaf? sourceLeaf with
        | none => simp [compile?, leafCompiled] at compiled
        | some compiledLeaf =>
            cases failureCompiled : compile? onFailure with
            | none =>
                simp [compile?, leafCompiled, failureCompiled] at compiled
            | some compiledFailure =>
                simp [compile?, leafCompiled, failureCompiled] at compiled
                subst target
                simp [Program.erase, sourceRule_of_compileLeaf? leafCompiled,
                  erase_of_compile? onFailure compiledFailure failureCompiled]
    | switch sourceBranches default =>
        cases branchesCompiled : compileBranches? sourceBranches with
        | none => simp [compile?, branchesCompiled] at compiled
        | some compiledBranches =>
            cases defaultCompiled : compile? default with
            | none =>
                simp [compile?, branchesCompiled, defaultCompiled] at compiled
            | some compiledDefault =>
                simp [compile?, branchesCompiled, defaultCompiled] at compiled
                subst target
                simp [Program.erase,
                  eraseBranches_of_compileBranches? sourceBranches
                    compiledBranches branchesCompiled,
                  erase_of_compile? default compiledDefault defaultCompiled]
  termination_by sizeOf source

  /-- Branch companion to `erase_of_compile?`. -/
  theorem eraseBranches_of_compileBranches?
      (source : Fusion.Branches Head SourceOccurrence FirstOrder.RulePlan)
      (target : Branches Head)
      (compiled : compileBranches? source = some target) :
      Program.Branches.erase target = source := by
    cases source with
    | nil =>
        simp [compileBranches?] at compiled
        subst target
        rfl
    | cons key program rest =>
        cases programCompiled : compile? program with
        | none => simp [compileBranches?, programCompiled] at compiled
        | some compiledProgram =>
            cases restCompiled : compileBranches? rest with
            | none =>
                simp [compileBranches?, programCompiled, restCompiled] at compiled
            | some compiledRest =>
                simp [compileBranches?, programCompiled, restCompiled] at compiled
                subst target
                simp [Program.Branches.erase,
                  erase_of_compile? program compiledProgram programCompiled,
                  eraseBranches_of_compileBranches? rest compiledRest
                    restCompiled]
  termination_by sizeOf source
end

mutual
  /-- Residual evaluation is exactly fused-source evaluation when leaf
  interpreters agree after erasure. -/
  theorem evalAll_eq_erase
      [DecidableEq Head]
      (runTarget : CompiledBranch → List Result)
      (runSource :
        Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan →
          List Result)
      (leafExact : ∀ leaf, runTarget leaf = runSource (eraseLeaf leaf))
      (program : Program Head) (subjects : List (Matrix.Subject Head)) :
      program.evalAll runTarget subjects =
        program.erase.evalAll runSource subjects := by
    cases program with
    | failure => rfl
    | drop next =>
        cases subjects with
        | nil => rfl
        | cons subject subjects =>
            exact evalAll_eq_erase runTarget runSource leafExact next subjects
    | tryRule leaf patterns onFailure =>
        simp only [Program.evalAll, Program.erase,
          FusionSemantics.evalAll]
        rw [leafExact leaf,
          evalAll_eq_erase runTarget runSource leafExact onFailure subjects]
    | switch branches default =>
        cases subjects with
        | nil =>
            simpa [Program.evalAll, Program.erase,
              FusionSemantics.evalAll] using
              evalAll_eq_erase runTarget runSource leafExact default []
        | cons subject subjects =>
            cases subject with
            | node head children =>
                simp only [Program.evalAll, Program.erase,
                  FusionSemantics.evalAll]
                rw [evalBranchAll_eq_erase runTarget runSource leafExact
                    branches { head, arity := children.length }
                    (children ++ subjects),
                  evalAll_eq_erase runTarget runSource leafExact default
                    (.node head children :: subjects)]
  termination_by sizeOf program

  /-- Branch companion to `evalAll_eq_erase`. -/
  theorem evalBranchAll_eq_erase
      [DecidableEq Head]
      (runTarget : CompiledBranch → List Result)
      (runSource :
        Fusion.CompiledRule SourceOccurrence FirstOrder.RulePlan →
          List Result)
      (leafExact : ∀ leaf, runTarget leaf = runSource (eraseLeaf leaf))
      (branches : Branches Head) (query : Matrix.ConstructorKey Head)
      (subjects : List (Matrix.Subject Head)) :
      Program.evalBranchAll runTarget query subjects branches =
        FusionSemantics.evalBranchAll runSource query subjects
          (Program.Branches.erase branches) := by
    cases branches with
    | nil => rfl
    | cons key program rest =>
        by_cases selected : query = key
        · simp [Program.evalBranchAll, Program.Branches.erase,
            Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll,
            selected,
            evalAll_eq_erase runTarget runSource leafExact program subjects]
        · simp [Program.evalBranchAll, Program.Branches.erase,
            Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion.Program.evalBranchAll,
            selected,
            evalBranchAll_eq_erase runTarget runSource leafExact rest query
              subjects]
  termination_by sizeOf branches
end

/-! ## PeTTa call-guard instantiation -/

/-- Structural compilation of the actual fused call-guard source program. -/
def sourceDecisionProgram? : Option (Program SourceCompiler.Head) :=
  compile? fusedProgram

theorem sourceDecisionProgram?_isSome :
    sourceDecisionProgram?.isSome = true := by
  obtain ⟨program, compiled⟩ :=
    compile?_exists_of_fusion decisionTree fusedProgram
      fusedProgram_compilation_exact
  simp [sourceDecisionProgram?, compiled]

/-- The unique source-derived residual decision program. -/
def sourceDecisionProgram : Program SourceCompiler.Head :=
  sourceDecisionProgram?.get sourceDecisionProgram?_isSome

theorem sourceDecisionProgram_compilation_exact :
    compile? fusedProgram = some sourceDecisionProgram := by
  exact (Option.some_get sourceDecisionProgram?_isSome).symm

/-- The concrete residual decision program erases exactly to the independently
fused source decision program. -/
theorem sourceDecisionProgram_erase :
    sourceDecisionProgram.erase = fusedProgram :=
  erase_of_compile? fusedProgram sourceDecisionProgram
    sourceDecisionProgram_compilation_exact

/-- Interpret a residual leaf through the exact first-order rule plan it
retains.  StructuredC realization of `leaf.body` is proved in a later pass. -/
def runLeaf (source : Pattern) (leaf : CompiledBranch) : List Pattern :=
  leaf.rule.run relationEnv sourceLanguage source

/-- Execute the structurally compiled residual decision program. -/
def sourceDecisionReducts (_recursiveFuel : Nat) (source : Pattern) :
    List Pattern :=
  sourceDecisionProgram.evalAll (runLeaf source)
    [SourceCompiler.lowerSubject source]

/-- Structural leaf enrichment changes no source result, order, or
multiplicity. -/
theorem sourceDecisionReducts_eq_fusedReducts
    (recursiveFuel : Nat) (source : Pattern) :
    sourceDecisionReducts recursiveFuel source =
      fusedReducts recursiveFuel source := by
  unfold sourceDecisionReducts fusedReducts
  rw [evalAll_eq_erase
    (runLeaf source) (runCompiledOccurrence source)
    (fun _ => rfl) sourceDecisionProgram
    [SourceCompiler.lowerSubject source],
    sourceDecisionProgram_erase]

/-- The residual decision IR has exactly the authored contextual call-guard
semantics. -/
theorem sourceDecisionReducts_eq_contextualRewriteAt
    (recursiveFuel : Nat) (source : Pattern) :
    sourceDecisionReducts recursiveFuel source =
      Mettapedia.OSLF.MeTTaIL.ContextualStep.rewriteAt
        premiseBase sourceLanguage (recursiveFuel + 1) source := by
  rw [sourceDecisionReducts_eq_fusedReducts,
    fusedReducts_eq_contextualRewriteAt]

/-- Reverse adequacy: structural leaf enrichment cannot invent a source
transition. -/
theorem sourceDecisionReducts_no_invention
    (recursiveFuel : Nat) {source target : Pattern}
    (member : target ∈ sourceDecisionReducts recursiveFuel source) :
    TypeSynthesis.langReducesUsing relationEnv sourceLanguage source target := by
  rw [sourceDecisionReducts_eq_fusedReducts] at member
  exact fusedReducts_no_invention recursiveFuel member

/-- On the cold-control image, the first residual result is the independent
typed compiler successor. -/
theorem sourceDecision_first_eq_compileLanguageStep
    (source : CompileLanguageControl) :
    (sourceDecisionReducts 0 (encodeCompileLanguageControl source)).head? =
      (compileLanguageStep? source).map encodeCompileLanguageControl := by
  rw [sourceDecisionReducts_eq_fusedReducts,
    fused_first_eq_compileLanguageStep]

/-! ## Discriminating controls -/

private def finishOccurrence : SourceOccurrence := ⟨0, by decide⟩

private def foreignLeftPlan : FirstOrder.RulePlan :=
  { planAt finishOccurrence with
    left := .application "petta-call-guard:foreign-state" [] }

private def foreignRightPlan : FirstOrder.RulePlan :=
  { planAt finishOccurrence with
    right := .application "petta-call-guard:foreign-target" [] }

/-- Unsupported source match structure rejects the selected leaf. -/
example :
    compileLeaf? ⟨finishOccurrence, foreignLeftPlan⟩ = none := by
  decide +kernel

/-- Unsupported source target structure rejects the selected leaf. -/
example :
    compileLeaf? ⟨finishOccurrence, foreignRightPlan⟩ = none := by
  decide +kernel

#print axioms sourceRule_of_compileLeaf?
#print axioms compileLeaf?_of_planOptionAt
#print axioms compile?_exists_of_fusion
#print axioms erase_of_compile?
#print axioms evalAll_eq_erase
#print axioms sourceDecisionProgram_erase
#print axioms sourceDecisionReducts_eq_contextualRewriteAt
#print axioms sourceDecisionReducts_no_invention
#print axioms sourceDecision_first_eq_compileLanguageStep

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardSourceDecisionIR
