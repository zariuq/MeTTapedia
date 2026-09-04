import Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation

/-!
# Fusion of ordered decision trees with compiled rule plans

Pattern-matrix compilation deliberately leaves rule meaning behind an
occurrence-indexed continuation.  This module performs the next compiler pass:
every occurrence is paired with an independently compiled rule plan, yielding
one inspectable residual program.  Compilation is partial and fails if any
reachable occurrence lacks a plan.

The fused interpreter is proved extensionally equal to the original decision
tree whenever each compiled plan implements its source occurrence.  Thus
fusion removes a runtime callback without turning the residual program into a
new semantic authority.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion

namespace OPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
  (Pattern Subject ConstructorKey DecisionTree DecisionBranches
    structuralMatchList)

end OPM

namespace WPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation
  (DecisionProgram DecisionBranches)

end WPM

universe uHead uRule uPlan uResult

variable {Head : Type uHead} {Rule : Type uRule} {Plan : Type uPlan}
  {Result : Type uResult}

/-- One compiled plan retains the exact source occurrence it implements. -/
structure CompiledRule (Rule : Type uRule) (Plan : Type uPlan) where
  occurrence : Rule
  plan : Plan

mutual
  /-- An ordered decision program whose rule continuations are first-order
  data rather than host-language callbacks. -/
  inductive Program (Head : Type uHead) (Rule : Type uRule)
      (Plan : Type uPlan) where
    | failure
    | drop (next : Program Head Rule Plan)
    | tryRule (compiled : CompiledRule Rule Plan)
        (patterns : List (OPM.Pattern Head))
        (onFailure : Program Head Rule Plan)
    | switch (branches : Branches Head Rule Plan)
        (default : Program Head Rule Plan)

  /-- Inspectable constructor branches for a fused program. -/
  inductive Branches (Head : Type uHead) (Rule : Type uRule)
      (Plan : Type uPlan) where
    | nil
    | cons (key : OPM.ConstructorKey Head) (program : Program Head Rule Plan)
        (rest : Branches Head Rule Plan)
end

mutual
  /-- Fuse a decision tree with an independently supplied partial rule
  compiler. -/
  def compile? (compileRule? : Rule → Option Plan) :
      OPM.DecisionTree Head Rule → Option (Program Head Rule Plan)
    | .failure => some .failure
    | .tryRule occurrence patterns onFailure =>
        match compileRule? occurrence with
        | none => none
        | some plan =>
            match compile? compileRule? onFailure with
            | none => none
            | some compiledFailure =>
                some (.tryRule ⟨occurrence, plan⟩ patterns compiledFailure)
    | .switch branches default =>
        match compileBranches? compileRule? branches with
        | none => none
        | some compiledBranches =>
            match compile? compileRule? default with
            | none => none
            | some compiledDefault =>
                some (.switch compiledBranches compiledDefault)

  /-- Fuse every branch of an inspectable branch sequence. -/
  def compileBranches? (compileRule? : Rule → Option Plan) :
      OPM.DecisionBranches Head Rule → Option (Branches Head Rule Plan)
    | .nil => some .nil
    | .cons key program rest =>
        match compile? compileRule? program with
        | none => none
        | some compiledProgram =>
            match compileBranches? compileRule? rest with
            | none => none
            | some compiledRest =>
                some (.cons key compiledProgram compiledRest)
end

namespace Program

mutual
  /-- Execute every successful compiled rule in authored order. -/
  def evalAll [DecidableEq Head]
      (runPlan : CompiledRule Rule Plan → List Result) :
      Program Head Rule Plan → List (OPM.Subject Head) → List Result
    | .failure, _ => []
    | .drop _, [] => []
    | .drop next, _ :: subjects => evalAll runPlan next subjects
    | .tryRule compiled patterns onFailure, subjects =>
        let tail := evalAll runPlan onFailure subjects
        if OPM.structuralMatchList patterns subjects then
          runPlan compiled ++ tail
        else
          tail
    | .switch branches default, subjects =>
        match subjects with
        | [] => evalAll runPlan default []
        | .node head children :: rest =>
            evalBranchAll runPlan
                { head, arity := children.length }
                (children ++ rest) branches ++
              evalAll runPlan default subjects

  /-- Execute the unique matching fused constructor branch, if present. -/
  def evalBranchAll [DecidableEq Head]
      (runPlan : CompiledRule Rule Plan → List Result)
      (query : OPM.ConstructorKey Head) (subjects : List (OPM.Subject Head)) :
      Branches Head Rule Plan → List Result
    | .nil => []
    | .cons key program rest =>
        if query = key then evalAll runPlan program subjects
        else evalBranchAll runPlan query subjects rest
end

end Program

mutual
  /-- Fuse a wildcard-column decision program with an independently supplied
  partial rule compiler.  A common-column projection remains explicit in the
  residual artifact. -/
  def compileWildcard? (compileRule? : Rule → Option Plan) :
      WPM.DecisionProgram Head Rule → Option (Program Head Rule Plan)
    | .failure => some .failure
    | .drop next =>
        match compileWildcard? compileRule? next with
        | none => none
        | some compiledNext => some (.drop compiledNext)
    | .tryRule occurrence patterns onFailure =>
        match compileRule? occurrence with
        | none => none
        | some plan =>
            match compileWildcard? compileRule? onFailure with
            | none => none
            | some compiledFailure =>
                some (.tryRule ⟨occurrence, plan⟩ patterns compiledFailure)
    | .switch branches default =>
        match compileWildcardBranches? compileRule? branches with
        | none => none
        | some compiledBranches =>
            match compileWildcard? compileRule? default with
            | none => none
            | some compiledDefault =>
                some (.switch compiledBranches compiledDefault)

  /-- Fuse every branch of a wildcard-column decision program. -/
  def compileWildcardBranches? (compileRule? : Rule → Option Plan) :
      WPM.DecisionBranches Head Rule → Option (Branches Head Rule Plan)
    | .nil => some .nil
    | .cons key program rest =>
        match compileWildcard? compileRule? program with
        | none => none
        | some compiledProgram =>
            match compileWildcardBranches? compileRule? rest with
            | none => none
            | some compiledRest =>
                some (.cons key compiledProgram compiledRest)
end

mutual
  /-- If every retained occurrence has a plan, every finite wildcard-column
  decision program fuses. -/
  theorem compileWildcard?_exists
      (compileRule? : Rule → Option Plan)
      (complete : ∀ occurrence, ∃ plan, compileRule? occurrence = some plan)
      (tree : WPM.DecisionProgram Head Rule) :
      ∃ program, compileWildcard? compileRule? tree = some program := by
    cases tree with
    | failure => exact ⟨.failure, rfl⟩
    | drop next =>
        obtain ⟨compiledNext, nextCompiled⟩ :=
          compileWildcard?_exists compileRule? complete next
        exact ⟨.drop compiledNext, by
          simp [compileWildcard?, nextCompiled]⟩
    | tryRule occurrence patterns onFailure =>
        obtain ⟨plan, planCompiled⟩ := complete occurrence
        obtain ⟨compiledFailure, failureCompiled⟩ :=
          compileWildcard?_exists compileRule? complete onFailure
        exact ⟨.tryRule ⟨occurrence, plan⟩ patterns compiledFailure, by
          simp [compileWildcard?, planCompiled, failureCompiled]⟩
    | switch branches default =>
        obtain ⟨compiledBranches, branchesCompiled⟩ :=
          compileWildcardBranches?_exists compileRule? complete branches
        obtain ⟨compiledDefault, defaultCompiled⟩ :=
          compileWildcard?_exists compileRule? complete default
        exact ⟨.switch compiledBranches compiledDefault, by
          simp [compileWildcard?, branchesCompiled, defaultCompiled]⟩
  termination_by sizeOf tree

  /-- Branch companion to `compileWildcard?_exists`. -/
  theorem compileWildcardBranches?_exists
      (compileRule? : Rule → Option Plan)
      (complete : ∀ occurrence, ∃ plan, compileRule? occurrence = some plan)
      (branches : WPM.DecisionBranches Head Rule) :
      ∃ compiled,
        compileWildcardBranches? compileRule? branches = some compiled := by
    cases branches with
    | nil => exact ⟨.nil, rfl⟩
    | cons key tree rest =>
        obtain ⟨compiledTree, treeCompiled⟩ :=
          compileWildcard?_exists compileRule? complete tree
        obtain ⟨compiledRest, restCompiled⟩ :=
          compileWildcardBranches?_exists compileRule? complete rest
        exact ⟨.cons key compiledTree compiledRest, by
          simp [compileWildcardBranches?, treeCompiled, restCompiled]⟩
  termination_by sizeOf branches
end

mutual
  /-- If every source occurrence compiles, every finite decision tree fuses. -/
  theorem compile?_exists
      (compileRule? : Rule → Option Plan)
      (complete : ∀ occurrence, ∃ plan, compileRule? occurrence = some plan)
      (tree : OPM.DecisionTree Head Rule) :
      ∃ program, compile? compileRule? tree = some program := by
    cases tree with
    | failure => exact ⟨.failure, rfl⟩
    | tryRule occurrence patterns onFailure =>
        obtain ⟨plan, planCompiled⟩ := complete occurrence
        obtain ⟨compiledFailure, failureCompiled⟩ :=
          compile?_exists compileRule? complete onFailure
        exact ⟨.tryRule ⟨occurrence, plan⟩ patterns compiledFailure, by
          simp [compile?, planCompiled, failureCompiled]⟩
    | switch branches default =>
        obtain ⟨compiledBranches, branchesCompiled⟩ :=
          compileBranches?_exists compileRule? complete branches
        obtain ⟨compiledDefault, defaultCompiled⟩ :=
          compile?_exists compileRule? complete default
        exact ⟨.switch compiledBranches compiledDefault, by
          simp [compile?, branchesCompiled, defaultCompiled]⟩
  termination_by sizeOf tree

  /-- Branch companion to `compile?_exists`. -/
  theorem compileBranches?_exists
      (compileRule? : Rule → Option Plan)
      (complete : ∀ occurrence, ∃ plan, compileRule? occurrence = some plan)
      (branches : OPM.DecisionBranches Head Rule) :
      ∃ compiled, compileBranches? compileRule? branches = some compiled := by
    cases branches with
    | nil => exact ⟨.nil, rfl⟩
    | cons key tree rest =>
        obtain ⟨compiledTree, treeCompiled⟩ :=
          compile?_exists compileRule? complete tree
        obtain ⟨compiledRest, restCompiled⟩ :=
          compileBranches?_exists compileRule? complete rest
        exact ⟨.cons key compiledTree compiledRest, by
          simp [compileBranches?, treeCompiled, restCompiled]⟩
  termination_by sizeOf branches
end

mutual
  /-- Fused execution equals source decision-tree execution whenever each
  compiled plan implements its retained source occurrence. -/
  theorem evalAll_eq_of_compile?
      [DecidableEq Head]
      (compileRule? : Rule → Option Plan)
      (runSource : Rule → List Result)
      (runPlan : CompiledRule Rule Plan → List Result)
      (planExact : ∀ occurrence plan,
        compileRule? occurrence = some plan →
          runPlan ⟨occurrence, plan⟩ = runSource occurrence)
      (tree : OPM.DecisionTree Head Rule)
      (program : Program Head Rule Plan)
      (compiled : compile? compileRule? tree = some program)
      (subjects : List (OPM.Subject Head)) :
      program.evalAll runPlan subjects = tree.evalAll runSource subjects := by
    cases tree with
    | failure =>
        simp [compile?] at compiled
        subst program
        rfl
    | tryRule occurrence patterns onFailure =>
        cases planCompiled : compileRule? occurrence with
        | none => simp [compile?, planCompiled] at compiled
        | some plan =>
            cases failureCompiled : compile? compileRule? onFailure with
            | none => simp [compile?, planCompiled, failureCompiled] at compiled
            | some compiledFailure =>
                simp [compile?, planCompiled, failureCompiled] at compiled
                subst program
                simp only [Program.evalAll,
                  Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.DecisionTree.evalAll]
                rw [planExact occurrence plan planCompiled,
                  evalAll_eq_of_compile? compileRule? runSource runPlan
                    planExact onFailure compiledFailure failureCompiled subjects]
    | switch branches default =>
        cases branchesCompiled : compileBranches? compileRule? branches with
        | none => simp [compile?, branchesCompiled] at compiled
        | some compiledBranches =>
            cases defaultCompiled : compile? compileRule? default with
            | none =>
                simp [compile?, branchesCompiled, defaultCompiled] at compiled
            | some compiledDefault =>
                simp [compile?, branchesCompiled, defaultCompiled] at compiled
                subst program
                cases subjects with
                | nil =>
                    simpa [Program.evalAll,
                      Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.DecisionTree.evalAll] using
                      evalAll_eq_of_compile? compileRule? runSource runPlan
                        planExact default compiledDefault defaultCompiled []
                | cons subject subjects =>
                    cases subject with
                    | node head children =>
                        simp only [Program.evalAll,
                          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.DecisionTree.evalAll]
                        rw [evalBranchAll_eq_of_compileBranches? compileRule?
                            runSource runPlan planExact branches
                            compiledBranches branchesCompiled
                            { head, arity := children.length }
                            (children ++ subjects),
                          evalAll_eq_of_compile? compileRule? runSource runPlan
                            planExact default compiledDefault defaultCompiled
                            (.node head children :: subjects)]
  termination_by sizeOf tree

  /-- Branch companion to `evalAll_eq_of_compile?`. -/
  theorem evalBranchAll_eq_of_compileBranches?
      [DecidableEq Head]
      (compileRule? : Rule → Option Plan)
      (runSource : Rule → List Result)
      (runPlan : CompiledRule Rule Plan → List Result)
      (planExact : ∀ occurrence plan,
        compileRule? occurrence = some plan →
          runPlan ⟨occurrence, plan⟩ = runSource occurrence)
      (branches : OPM.DecisionBranches Head Rule)
      (compiledBranches : Branches Head Rule Plan)
      (compiled : compileBranches? compileRule? branches = some compiledBranches)
      (query : OPM.ConstructorKey Head)
      (subjects : List (OPM.Subject Head)) :
      Program.evalBranchAll runPlan query subjects compiledBranches =
        Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.DecisionTree.evalBranchAll
          runSource query subjects branches := by
    cases branches with
    | nil =>
        simp [compileBranches?] at compiled
        subst compiledBranches
        rfl
    | cons key tree rest =>
        cases treeCompiled : compile? compileRule? tree with
        | none => simp [compileBranches?, treeCompiled] at compiled
        | some compiledTree =>
            cases restCompiled : compileBranches? compileRule? rest with
            | none =>
                simp [compileBranches?, treeCompiled, restCompiled] at compiled
            | some compiledRest =>
                simp [compileBranches?, treeCompiled, restCompiled] at compiled
                subst compiledBranches
                by_cases selected : query = key
                · simp [Program.evalBranchAll,
                    Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.DecisionTree.evalBranchAll,
                    selected,
                    evalAll_eq_of_compile? compileRule? runSource runPlan
                      planExact tree compiledTree treeCompiled subjects]
                · simp [Program.evalBranchAll,
                    Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.DecisionTree.evalBranchAll,
                    selected,
                    evalBranchAll_eq_of_compileBranches? compileRule?
                      runSource runPlan planExact rest compiledRest restCompiled
                      query subjects]
  termination_by sizeOf branches
end

mutual
  /-- Fusion preserves the complete wildcard-column decision semantics when
  every retained plan implements its source occurrence. -/
  theorem evalAll_eq_of_compileWildcard?
      [DecidableEq Head]
      (compileRule? : Rule → Option Plan)
      (runSource : Rule → List Result)
      (runPlan : CompiledRule Rule Plan → List Result)
      (planExact : ∀ occurrence plan,
        compileRule? occurrence = some plan →
          runPlan ⟨occurrence, plan⟩ = runSource occurrence)
      (tree : WPM.DecisionProgram Head Rule)
      (program : Program Head Rule Plan)
      (compiled : compileWildcard? compileRule? tree = some program)
      (subjects : List (OPM.Subject Head)) :
      program.evalAll runPlan subjects = tree.evalAll runSource subjects := by
    cases tree with
    | failure =>
        simp [compileWildcard?] at compiled
        subst program
        rfl
    | drop next =>
        cases nextCompiled : compileWildcard? compileRule? next with
        | none => simp [compileWildcard?, nextCompiled] at compiled
        | some compiledNext =>
            simp [compileWildcard?, nextCompiled] at compiled
            subst program
            cases subjects with
            | nil => rfl
            | cons subject subjects =>
                simpa [Program.evalAll,
                  Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalAll] using
                  evalAll_eq_of_compileWildcard? compileRule? runSource runPlan
                    planExact next compiledNext nextCompiled subjects
    | tryRule occurrence patterns onFailure =>
        cases planCompiled : compileRule? occurrence with
        | none => simp [compileWildcard?, planCompiled] at compiled
        | some plan =>
            cases failureCompiled : compileWildcard? compileRule? onFailure with
            | none =>
                simp [compileWildcard?, planCompiled, failureCompiled] at compiled
            | some compiledFailure =>
                simp [compileWildcard?, planCompiled, failureCompiled] at compiled
                subst program
                simp only [Program.evalAll,
                  Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalAll]
                rw [planExact occurrence plan planCompiled,
                  evalAll_eq_of_compileWildcard? compileRule? runSource runPlan
                    planExact onFailure compiledFailure failureCompiled subjects]
    | switch branches default =>
        cases branchesCompiled :
            compileWildcardBranches? compileRule? branches with
        | none => simp [compileWildcard?, branchesCompiled] at compiled
        | some compiledBranches =>
            cases defaultCompiled : compileWildcard? compileRule? default with
            | none =>
                simp [compileWildcard?, branchesCompiled, defaultCompiled] at compiled
            | some compiledDefault =>
                simp [compileWildcard?, branchesCompiled, defaultCompiled] at compiled
                subst program
                cases subjects with
                | nil =>
                    simpa [Program.evalAll,
                      Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalAll] using
                      evalAll_eq_of_compileWildcard? compileRule? runSource
                        runPlan planExact default compiledDefault
                        defaultCompiled []
                | cons subject subjects =>
                    cases subject with
                    | node head children =>
                        simp only [Program.evalAll,
                          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalAll]
                        rw [evalBranchAll_eq_of_compileWildcardBranches?
                            compileRule? runSource runPlan planExact branches
                            compiledBranches branchesCompiled
                            { head, arity := children.length }
                            (children ++ subjects),
                          evalAll_eq_of_compileWildcard? compileRule? runSource
                            runPlan planExact default compiledDefault
                            defaultCompiled
                            (.node head children :: subjects)]
  termination_by sizeOf tree

  /-- Branch companion to `evalAll_eq_of_compileWildcard?`. -/
  theorem evalBranchAll_eq_of_compileWildcardBranches?
      [DecidableEq Head]
      (compileRule? : Rule → Option Plan)
      (runSource : Rule → List Result)
      (runPlan : CompiledRule Rule Plan → List Result)
      (planExact : ∀ occurrence plan,
        compileRule? occurrence = some plan →
          runPlan ⟨occurrence, plan⟩ = runSource occurrence)
      (branches : WPM.DecisionBranches Head Rule)
      (compiledBranches : Branches Head Rule Plan)
      (compiled : compileWildcardBranches? compileRule? branches =
        some compiledBranches)
      (query : OPM.ConstructorKey Head)
      (subjects : List (OPM.Subject Head)) :
      Program.evalBranchAll runPlan query subjects compiledBranches =
        Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalBranchAll
          runSource query subjects branches := by
    cases branches with
    | nil =>
        simp [compileWildcardBranches?] at compiled
        subst compiledBranches
        rfl
    | cons key tree rest =>
        cases treeCompiled : compileWildcard? compileRule? tree with
        | none =>
            simp [compileWildcardBranches?, treeCompiled] at compiled
        | some compiledTree =>
            cases restCompiled :
                compileWildcardBranches? compileRule? rest with
            | none =>
                simp [compileWildcardBranches?, treeCompiled,
                  restCompiled] at compiled
            | some compiledRest =>
                simp [compileWildcardBranches?, treeCompiled,
                  restCompiled] at compiled
                subst compiledBranches
                by_cases selected : query = key
                · simp [Program.evalBranchAll,
                    Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalBranchAll,
                    selected,
                    evalAll_eq_of_compileWildcard? compileRule? runSource
                      runPlan planExact tree compiledTree treeCompiled
                      subjects]
                · simp [Program.evalBranchAll,
                    Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation.DecisionProgram.evalBranchAll,
                    selected,
                    evalBranchAll_eq_of_compileWildcardBranches? compileRule?
                      runSource runPlan planExact rest compiledRest
                      restCompiled query subjects]
  termination_by sizeOf branches
end

end Mettapedia.GSLT.LanguageDef.OrderedDecisionRuleFusion
