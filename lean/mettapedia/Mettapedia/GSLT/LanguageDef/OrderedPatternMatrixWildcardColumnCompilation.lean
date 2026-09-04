import Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation

/-!
# Ordered pattern matrices with wildcard-column elimination

The basic ordered compiler stops a constructor-dispatch region at the first
wildcard row.  This companion compiler adds one standard pattern-matrix
optimization: when every remaining row begins with a wildcard, the common
subject coordinate is discarded before compilation continues.

Discarding such a column is semantic, not heuristic.  Every row accepts that
coordinate and no binding is performed by the structural selector, so source
order, multiplicity, and rule-continuation behavior are unchanged.  A `drop`
node records the operation in the residual program.  This exposes later rigid
columns without duplicating wildcard rows into every constructor branch.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation

namespace OPM

export Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
  (Pattern Subject Row Matrix ConstructorKey structuralMatchList runMatrixAll
    structuralMatch
    rigidPrefixKeys specializePrefix defaultMatrix
    runMatrixAll_constructor_decomposition runMatrixAll_nil_eq_default)

end OPM

universe uHead uRule uResult

variable {Head : Type uHead} {Rule : Type uRule} {Result : Type uResult}

/-- Does one residual row begin with an unconstrained coordinate? -/
def firstIsWildcard (row : OPM.Row Head Rule) : Bool :=
  match row.patterns with
  | .wildcard :: _ => true
  | _ => false

/-- A nonempty residual matrix may discard its first coordinate exactly when
every row begins with a wildcard. -/
def allFirstWildcard : OPM.Matrix Head Rule → Bool
  | [] => false
  | rows => rows.all firstIsWildcard

/-- Remove the first residual coordinate from every row.  Compilation invokes
this operation only after `allFirstWildcard` has accepted the matrix. -/
def dropFirstColumn (matrix : OPM.Matrix Head Rule) : OPM.Matrix Head Rule :=
  matrix.map fun row => { row with patterns := row.patterns.tail }

mutual
  /-- Residual ordered decision program with an explicit common-wildcard
  projection step. -/
  inductive DecisionProgram (Head : Type uHead) (Rule : Type uRule) where
    | failure
    | drop (next : DecisionProgram Head Rule)
    | tryRule (rule : Rule) (patterns : List (OPM.Pattern Head))
        (onFailure : DecisionProgram Head Rule)
    | switch (branches : DecisionBranches Head Rule)
        (default : DecisionProgram Head Rule)

  /-- Inspectable constructor branches. -/
  inductive DecisionBranches (Head : Type uHead) (Rule : Type uRule) where
    | nil
    | cons (key : OPM.ConstructorKey Head)
        (program : DecisionProgram Head Rule)
        (rest : DecisionBranches Head Rule)
end

namespace DecisionProgram

mutual
  /-- Execute every successful rule continuation in authored order. -/
  def evalAll [DecidableEq Head] (attempt : Rule → List Result) :
      DecisionProgram Head Rule → List (OPM.Subject Head) → List Result
    | .failure, _ => []
    | .drop _, [] => []
    | .drop next, _ :: subjects => evalAll attempt next subjects
    | .tryRule rule patterns onFailure, subjects =>
        let tail := evalAll attempt onFailure subjects
        if OPM.structuralMatchList patterns subjects then
          attempt rule ++ tail
        else
          tail
    | .switch branches default, subjects =>
        match subjects with
        | [] => evalAll attempt default []
        | .node head children :: rest =>
            evalBranchAll attempt
                { head, arity := children.length }
                (children ++ rest) branches ++
              evalAll attempt default subjects

  /-- Execute the unique branch having the observed constructor key. -/
  def evalBranchAll [DecidableEq Head] (attempt : Rule → List Result)
      (query : OPM.ConstructorKey Head)
      (subjects : List (OPM.Subject Head)) :
      DecisionBranches Head Rule → List Result
    | .nil => []
    | .cons key program rest =>
        if query = key then evalAll attempt program subjects
        else evalBranchAll attempt query subjects rest
end

end DecisionProgram

/-- Compile every requested constructor branch using the recursive pass. -/
def compileBranches [DecidableEq Head]
    (compileRecursive : OPM.Matrix Head Rule →
      Option (DecisionProgram Head Rule))
    (matrix : OPM.Matrix Head Rule) :
    List (OPM.ConstructorKey Head) →
      Option (DecisionBranches Head Rule)
  | [] => some .nil
  | key :: keys => do
      let program ← compileRecursive (OPM.specializePrefix key matrix)
      let rest ← compileBranches compileRecursive matrix keys
      pure (.cons key program rest)

/-- One compiler layer.  Common wildcard elimination precedes ordinary
ordered constructor-prefix compilation. -/
def compileStep [DecidableEq Head]
    (compileRecursive : OPM.Matrix Head Rule →
      Option (DecisionProgram Head Rule))
    (matrix : OPM.Matrix Head Rule) : Option (DecisionProgram Head Rule) :=
  if allFirstWildcard matrix then
    (compileRecursive (dropFirstColumn matrix)).map .drop
  else
    match matrix with
    | [] => some .failure
    | row :: rows =>
        match row.firstKey? with
        | none => do
            let onFailure ← compileRecursive rows
            pure (.tryRule row.rule row.patterns onFailure)
        | some _ => do
            let branches ← compileBranches compileRecursive matrix
              (OPM.rigidPrefixKeys matrix)
            let default ← compileRecursive (OPM.defaultMatrix matrix)
            pure (.switch branches default)

/-- Fuel-bounded, fail-closed compilation. -/
def compile? [DecidableEq Head] : Nat → OPM.Matrix Head Rule →
    Option (DecisionProgram Head Rule)
  | 0, _ => none
  | fuel + 1, matrix => compileStep (compile? fuel) matrix

private theorem firstIsWildcard_eq_true_iff (row : OPM.Row Head Rule) :
    firstIsWildcard row = true ↔
      ∃ patterns, row.patterns = .wildcard :: patterns := by
  cases rowPatterns : row.patterns with
  | nil => simp [firstIsWildcard, rowPatterns]
  | cons pattern patterns =>
      cases pattern with
      | wildcard => simp [firstIsWildcard, rowPatterns]
      | node head children => simp [firstIsWildcard, rowPatterns]

private theorem allFirstWildcard_cons
    (row : OPM.Row Head Rule) (rows : OPM.Matrix Head Rule)
    (accepted : allFirstWildcard (row :: rows) = true) :
    firstIsWildcard row = true ∧ rows.all firstIsWildcard = true := by
  simpa [allFirstWildcard] using accepted

/-- On a present subject coordinate, deleting a universally wildcard column
preserves the complete source result list. -/
theorem runMatrixAll_dropFirstColumn
    [DecidableEq Head] (attempt : Rule → List Result)
    (matrix : OPM.Matrix Head Rule) (subject : OPM.Subject Head)
    (subjects : List (OPM.Subject Head))
    (accepted : allFirstWildcard matrix = true) :
    OPM.runMatrixAll attempt matrix (subject :: subjects) =
      OPM.runMatrixAll attempt (dropFirstColumn matrix) subjects := by
  induction matrix with
  | nil => simp [allFirstWildcard] at accepted
  | cons row rows inductionHypothesis =>
      have components := allFirstWildcard_cons row rows accepted
      obtain ⟨patterns, rowPatterns⟩ :=
        (firstIsWildcard_eq_true_iff row).mp components.1
      cases rows with
      | nil =>
          simp [OPM.runMatrixAll, dropFirstColumn, rowPatterns,
            OPM.structuralMatchList, OPM.structuralMatch]
      | cons next rest =>
          have tailAccepted : allFirstWildcard (next :: rest) = true := by
            simpa [allFirstWildcard] using components.2
          calc
            OPM.runMatrixAll attempt (row :: next :: rest)
                (subject :: subjects) =
              if OPM.structuralMatchList row.patterns
                  (subject :: subjects) then
                attempt row.rule ++
                  OPM.runMatrixAll attempt (next :: rest)
                    (subject :: subjects)
              else
                OPM.runMatrixAll attempt (next :: rest)
                  (subject :: subjects) := rfl
            _ =
              if OPM.structuralMatchList patterns subjects then
                attempt row.rule ++
                  OPM.runMatrixAll attempt (next :: rest)
                    (subject :: subjects)
              else
                OPM.runMatrixAll attempt (next :: rest)
                  (subject :: subjects) := by
                    simp [rowPatterns, OPM.structuralMatchList,
                      OPM.structuralMatch]
            _ =
              if OPM.structuralMatchList patterns subjects then
                attempt row.rule ++
                  OPM.runMatrixAll attempt
                    (dropFirstColumn (next :: rest)) subjects
              else
                OPM.runMatrixAll attempt
                  (dropFirstColumn (next :: rest)) subjects := by
                    rw [inductionHypothesis tailAccepted]
            _ = OPM.runMatrixAll attempt
                (dropFirstColumn (row :: next :: rest)) subjects := by
                  simp [dropFirstColumn, rowPatterns, OPM.runMatrixAll]

/-- With no subject coordinate, a universally wildcard matrix has no
structurally eligible row. -/
theorem runMatrixAll_nil_of_allFirstWildcard
    [DecidableEq Head] (attempt : Rule → List Result)
    (matrix : OPM.Matrix Head Rule)
    (accepted : allFirstWildcard matrix = true) :
    OPM.runMatrixAll attempt matrix [] = [] := by
  induction matrix with
  | nil => simp [allFirstWildcard] at accepted
  | cons row rows inductionHypothesis =>
      have components := allFirstWildcard_cons row rows accepted
      obtain ⟨patterns, rowPatterns⟩ :=
        (firstIsWildcard_eq_true_iff row).mp components.1
      cases rows with
      | nil =>
          simp [OPM.runMatrixAll, rowPatterns,
            OPM.structuralMatchList]
      | cons next rest =>
          have tailAccepted : allFirstWildcard (next :: rest) = true := by
            simpa [allFirstWildcard] using components.2
          calc
            OPM.runMatrixAll attempt (row :: next :: rest) [] =
                OPM.runMatrixAll attempt (next :: rest) [] := by
                  simp [OPM.runMatrixAll, rowPatterns,
                    OPM.structuralMatchList]
            _ = [] := inductionHypothesis tailAccepted

/-- Compiled branches have exactly the selected source specialization. -/
theorem evalBranchAll_compileBranches
    [DecidableEq Head]
    (compileRecursive : OPM.Matrix Head Rule →
      Option (DecisionProgram Head Rule))
    (attempt : Rule → List Result) (matrix : OPM.Matrix Head Rule)
    (keys : List (OPM.ConstructorKey Head))
    (branches : DecisionBranches Head Rule)
    (compiled : compileBranches compileRecursive matrix keys = some branches)
    (recursiveExact : ∀ residual program,
      compileRecursive residual = some program →
      ∀ subjects,
        program.evalAll attempt subjects =
          OPM.runMatrixAll attempt residual subjects)
    (query : OPM.ConstructorKey Head)
    (subjects : List (OPM.Subject Head)) :
    DecisionProgram.evalBranchAll attempt query subjects branches =
      if query ∈ keys then
        OPM.runMatrixAll attempt (OPM.specializePrefix query matrix) subjects
      else [] := by
  induction keys generalizing branches with
  | nil =>
      simp [compileBranches] at compiled
      subst branches
      rfl
  | cons key keys inductionHypothesis =>
      cases programCompiled :
          compileRecursive (OPM.specializePrefix key matrix) with
      | none => simp [compileBranches, programCompiled] at compiled
      | some program =>
          cases restCompiled : compileBranches compileRecursive matrix keys with
          | none =>
              simp [compileBranches, programCompiled, restCompiled] at compiled
          | some rest =>
              simp [compileBranches, programCompiled, restCompiled] at compiled
              subst branches
              by_cases same : query = key
              · subst key
                simp [DecisionProgram.evalBranchAll,
                  recursiveExact _ program programCompiled subjects]
              · simp [DecisionProgram.evalBranchAll, same,
                  inductionHypothesis rest restCompiled]

/-- Every successful optimized compilation preserves the complete ordered and
multiplicity-sensitive source behavior. -/
theorem compile?_all_correct
    [DecidableEq Head] (fuel : Nat) (matrix : OPM.Matrix Head Rule)
    (program : DecisionProgram Head Rule)
    (compiled : compile? fuel matrix = some program)
    (attempt : Rule → List Result)
    (subjects : List (OPM.Subject Head)) :
    program.evalAll attempt subjects =
      OPM.runMatrixAll attempt matrix subjects := by
  induction fuel generalizing matrix program subjects with
  | zero => simp [compile?] at compiled
  | succ fuel inductionHypothesis =>
      by_cases all : allFirstWildcard matrix = true
      · cases nextCompiled : compile? fuel (dropFirstColumn matrix) with
        | none => simp [compile?, compileStep, all, nextCompiled] at compiled
        | some next =>
            simp [compile?, compileStep, all, nextCompiled] at compiled
            subst program
            cases subjects with
            | nil =>
                simp [DecisionProgram.evalAll,
                  runMatrixAll_nil_of_allFirstWildcard attempt matrix all]
            | cons subject subjects =>
                simp only [DecisionProgram.evalAll]
                rw [inductionHypothesis (dropFirstColumn matrix) next
                  nextCompiled subjects]
                exact (runMatrixAll_dropFirstColumn
                  attempt matrix subject subjects all).symm
      · have allFalse : allFirstWildcard matrix = false :=
          by cases equation : allFirstWildcard matrix <;> simp_all
        cases matrix with
        | nil =>
            simp [compile?, compileStep, allFalse] at compiled
            subst program
            rfl
        | cons row rows =>
            cases rowPatterns : row.patterns with
            | nil =>
                cases tailCompiled : compile? fuel rows with
                | none =>
                    simp [compile?, compileStep, allFalse,
                      Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                      rowPatterns, tailCompiled] at compiled
                | some tail =>
                    simp [compile?, compileStep, allFalse,
                      Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                      rowPatterns, tailCompiled] at compiled
                    subst program
                    simp [DecisionProgram.evalAll, OPM.runMatrixAll,
                      rowPatterns,
                      inductionHypothesis rows tail tailCompiled]
            | cons pattern patterns =>
                cases pattern with
                | wildcard =>
                    cases tailCompiled : compile? fuel rows with
                    | none =>
                        simp [compile?, compileStep, allFalse,
                          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                          rowPatterns,
                          tailCompiled] at compiled
                    | some tail =>
                        simp [compile?, compileStep, allFalse,
                          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                          rowPatterns,
                          tailCompiled] at compiled
                        subst program
                        simp [DecisionProgram.evalAll, OPM.runMatrixAll,
                          rowPatterns,
                          inductionHypothesis rows tail tailCompiled]
                | node head children =>
                    cases branchesCompiled :
                        compileBranches (compile? fuel) (row :: rows)
                          (OPM.rigidPrefixKeys (row :: rows)) with
                    | none =>
                        simp [compile?, compileStep, allFalse,
                          Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                          rowPatterns,
                          branchesCompiled] at compiled
                    | some branches =>
                        cases defaultCompiled :
                            compile? fuel (OPM.defaultMatrix (row :: rows)) with
                        | none =>
                            simp [compile?, compileStep, allFalse,
                              Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                              rowPatterns,
                              branchesCompiled, defaultCompiled] at compiled
                        | some default =>
                            simp [compile?, compileStep, allFalse,
                              Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.Row.firstKey?,
                              rowPatterns,
                              branchesCompiled, defaultCompiled] at compiled
                            subst program
                            cases subjects with
                            | nil =>
                                simp only [DecisionProgram.evalAll]
                                rw [inductionHypothesis
                                  (OPM.defaultMatrix (row :: rows)) default
                                  defaultCompiled []]
                                exact (OPM.runMatrixAll_nil_eq_default attempt
                                  (row :: rows)).symm
                            | cons subject subjects =>
                                cases subject with
                                | node subjectHead subjectChildren =>
                                    let query : OPM.ConstructorKey Head :=
                                      { head := subjectHead,
                                        arity := subjectChildren.length }
                                    have branchExact :=
                                      evalBranchAll_compileBranches
                                        (compile? fuel) attempt (row :: rows)
                                        (OPM.rigidPrefixKeys (row :: rows))
                                        branches branchesCompiled
                                        (fun residual branch branchCompiled
                                            branchSubjects =>
                                          inductionHypothesis residual branch
                                            branchCompiled branchSubjects)
                                        query (subjectChildren ++ subjects)
                                    have defaultExact := inductionHypothesis
                                      (OPM.defaultMatrix (row :: rows)) default
                                      defaultCompiled
                                      (.node subjectHead subjectChildren ::
                                        subjects)
                                    by_cases present :
                                        query ∈ OPM.rigidPrefixKeys (row :: rows)
                                    · simp only [DecisionProgram.evalAll]
                                      rw [branchExact, if_pos present,
                                        defaultExact]
                                      exact
                                        (OPM.runMatrixAll_constructor_decomposition
                                          attempt (row :: rows) subjectHead
                                          subjectChildren subjects).symm
                                    · have emptySpecialization :=
                                        Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation.specializePrefix_eq_nil_of_not_mem_keys
                                          query (row :: rows) present
                                      simp only [DecisionProgram.evalAll]
                                      rw [branchExact, if_neg present,
                                        defaultExact]
                                      have decomposition :=
                                        OPM.runMatrixAll_constructor_decomposition
                                          attempt (row :: rows) subjectHead
                                          subjectChildren subjects
                                      have emptySpecialization' :
                                          OPM.specializePrefix
                                            { head := subjectHead,
                                              arity := subjectChildren.length }
                                            (row :: rows) = [] := by
                                        simpa [query] using emptySpecialization
                                      rw [emptySpecialization'] at decomposition
                                      exact decomposition.symm

/-- Successful optimized compilation enumerates exactly the structurally
eligible source occurrences. -/
theorem compile?_candidate_rules_exact
    [DecidableEq Head] (fuel : Nat) (matrix : OPM.Matrix Head Rule)
    (program : DecisionProgram Head Rule)
    (compiled : compile? fuel matrix = some program)
    (subjects : List (OPM.Subject Head)) :
    program.evalAll (fun rule => [rule]) subjects =
      OPM.runMatrixAll (fun rule => [rule]) matrix subjects :=
  compile?_all_correct fuel matrix program compiled (fun rule => [rule])
    subjects

/-! ## Independent controls -/

private inductive DemoHead where
  | atom (name : String)
  | pair
deriving DecidableEq, Repr

private def leaf (name : String) : OPM.Subject DemoHead :=
  .node (.atom name) []

private def demoMatrix : OPM.Matrix DemoHead String :=
  [ { rule := "left"
      patterns := [.wildcard, .node (.atom "left") []] }
  , { rule := "right"
      patterns := [.wildcard, .node (.atom "right") []] }
  ]

/-- The compiler crosses a common wildcard column and exposes the later
constructor discriminator. -/
example :
    (compile? 20 demoMatrix).map (fun program =>
      program.evalAll (fun rule => [rule])
        [leaf "ignored", leaf "right"]) = some ["right"] := by
  decide

/-- Removing the required second subject cannot be mistaken for a wildcard
match after column elimination. -/
example :
    (compile? 20 demoMatrix).map (fun program =>
      program.evalAll (fun rule => [rule]) [leaf "ignored"]) = some [] := by
  decide

#print axioms runMatrixAll_dropFirstColumn
#print axioms compile?_all_correct
#print axioms compile?_candidate_rules_exact

end Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixWildcardColumnCompilation
