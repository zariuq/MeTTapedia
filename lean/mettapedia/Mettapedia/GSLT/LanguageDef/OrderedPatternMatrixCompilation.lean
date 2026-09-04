import Mathlib.Data.List.Basic

/-!
# Ordered pattern-matrix compilation

This module compiles an ordered family of constructor patterns to a small
decision program.  Source execution and target execution are independent:

* `runMatrix` scans authored rows and tests their residual patterns directly;
* `DecisionTree.eval` interprets `tryRule`, `switch`, and `failure` nodes;
* a supplied continuation performs guards, binding, and rule effects.

The compiler therefore accelerates structural selection without becoming a
second definition of rule meaning.  A failed continuation resumes at the next
authored row, so ordered fallthrough remains observable.

Constructor switches share one observation across the rigid prefix preceding
the first wildcard row.  Wildcards remain in the default continuation rather
than being copied into every branch.  Compilation is fuel-bounded and fails
closed; successful compilation carries an exact source/target theorem.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation

universe uHead uRule uResult

variable {Head : Type uHead} {Rule : Type uRule} {Result : Type uResult}

/-- Constructor patterns.  `wildcard` delegates all binding and equality
constraints to the canonical rule continuation. -/
inductive Pattern (Head : Type uHead) where
  | wildcard
  | node (head : Head) (children : List (Pattern Head))

/-- Constructor trees observed by the decision program. -/
inductive Subject (Head : Type uHead) where
  | node (head : Head) (children : List (Subject Head))

mutual
  /-- Direct structural matching for one residual pattern. -/
  def structuralMatch [DecidableEq Head] :
      Pattern Head -> Subject Head -> Bool
    | .wildcard, _ => true
    | .node patternHead patternChildren,
        .node subjectHead subjectChildren =>
      decide (patternHead = subjectHead) &&
        structuralMatchList patternChildren subjectChildren

  /-- Pairwise structural matching for a pattern vector. -/
  def structuralMatchList [DecidableEq Head] :
      List (Pattern Head) -> List (Subject Head) -> Bool
    | [], [] => true
    | pattern :: patterns, subject :: subjects =>
      structuralMatch pattern subject &&
        structuralMatchList patterns subjects
    | _, _ => false
end

/-- An authored row couples an opaque rule occurrence to its structural
pattern vector.  Occurrence identity and duplicates remain in the list. -/
structure Row (Head : Type uHead) (Rule : Type uRule) where
  rule : Rule
  patterns : List (Pattern Head)

abbrev Matrix (Head : Type uHead) (Rule : Type uRule) :=
  List (Row Head Rule)

/-- Source semantics: scan rows in authored order.  Structural matching only
licenses an attempt; the continuation remains authoritative for guards,
bindings, and effects. -/
def runMatrix [DecidableEq Head]
    (attempt : Rule -> Option Result) :
    Matrix Head Rule -> List (Subject Head) -> Option Result
  | [], _ => none
  | row :: rows, subjects =>
      if structuralMatchList row.patterns subjects then
        match attempt row.rule with
        | some result => some result
        | none => runMatrix attempt rows subjects
      else
        runMatrix attempt rows subjects

/-- Nondeterministic source semantics: retain every rule result in authored
order, including duplicates. -/
def runMatrixAll [DecidableEq Head]
    (attempt : Rule -> List Result) :
    Matrix Head Rule -> List (Subject Head) -> List Result
  | [], _ => []
  | row :: rows, subjects =>
      let tail := runMatrixAll attempt rows subjects
      if structuralMatchList row.patterns subjects then
        attempt row.rule ++ tail
      else
        tail

/-- A switch key includes immediate arity, so taking a branch licenses exact
replacement of the observed root by its children. -/
structure ConstructorKey (Head : Type uHead) where
  head : Head
  arity : Nat
deriving DecidableEq, Repr

mutual
  /-- Residual ordered decision program. -/
  inductive DecisionTree (Head : Type uHead) (Rule : Type uRule) where
    | failure
    | tryRule (rule : Rule) (patterns : List (Pattern Head))
        (onFailure : DecisionTree Head Rule)
    | switch (branches : DecisionBranches Head Rule)
        (default : DecisionTree Head Rule)

  /-- Finite constructor branches.  This is an inspectable sequence rather
  than an opaque host-language function. -/
  inductive DecisionBranches (Head : Type uHead) (Rule : Type uRule) where
    | nil
    | cons (key : ConstructorKey Head) (tree : DecisionTree Head Rule)
        (rest : DecisionBranches Head Rule)
end

namespace DecisionTree

mutual
  /-- Interpret a residual decision program. -/
  def eval [DecidableEq Head]
      (attempt : Rule -> Option Result) :
      DecisionTree Head Rule -> List (Subject Head) -> Option Result
    | .failure, _ => none
    | .tryRule rule patterns onFailure, subjects =>
        if structuralMatchList patterns subjects then
          match attempt rule with
          | some result => some result
          | none => eval attempt onFailure subjects
        else
          eval attempt onFailure subjects
    | .switch branches default, subjects =>
        match subjects with
        | [] => eval attempt default []
        | .node head children :: rest =>
            match evalBranch attempt
                { head, arity := children.length }
                (children ++ rest) branches with
            | some result => some result
            | none => eval attempt default subjects

  /-- Select and execute the first branch with the observed constructor key. -/
  def evalBranch [DecidableEq Head]
      (attempt : Rule -> Option Result)
      (query : ConstructorKey Head) (subjects : List (Subject Head)) :
      DecisionBranches Head Rule -> Option Result
    | .nil => none
    | .cons key tree rest =>
        if query = key then eval attempt tree subjects
        else evalBranch attempt query subjects rest
end

mutual
  /-- Interpret every successful residual rule in authored order. -/
  def evalAll [DecidableEq Head]
      (attempt : Rule -> List Result) :
      DecisionTree Head Rule -> List (Subject Head) -> List Result
    | .failure, _ => []
    | .tryRule rule patterns onFailure, subjects =>
        let tail := evalAll attempt onFailure subjects
        if structuralMatchList patterns subjects then
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

  /-- Interpret the unique matching constructor branch, if present. -/
  def evalBranchAll [DecidableEq Head]
      (attempt : Rule -> List Result)
      (query : ConstructorKey Head) (subjects : List (Subject Head)) :
      DecisionBranches Head Rule -> List Result
    | .nil => []
    | .cons key tree rest =>
        if query = key then evalAll attempt tree subjects
        else evalBranchAll attempt query subjects rest
end

end DecisionTree

/-- Does a row expose a rigid first coordinate? -/
def Row.firstKey? (row : Row Head Rule) : Option (ConstructorKey Head) :=
  match row.patterns with
  | .node head children :: _ => some { head, arity := children.length }
  | _ => none

/-- Constructor keys in the consecutive rigid prefix, with duplicates still
visible. -/
def rigidPrefixKeysRaw (matrix : Matrix Head Rule) :
    List (ConstructorKey Head) :=
  match matrix with
  | [] => []
  | row :: rows =>
      match row.firstKey? with
      | none => []
      | some key => key :: rigidPrefixKeysRaw rows

/-- Keys in the consecutive rigid prefix, before the first wildcard or empty
row.  Duplicate keys are erased without changing their first occurrence. -/
def rigidPrefixKeys [DecidableEq Head]
    (matrix : Matrix Head Rule) : List (ConstructorKey Head) :=
  (rigidPrefixKeysRaw matrix).eraseDups

/-- Residual matrix for one constructor branch.  It contains precisely the
matching rows in the rigid prefix, with the tested root replaced by its
children. -/
def specializePrefix [DecidableEq Head]
    (query : ConstructorKey Head) :
    Matrix Head Rule -> Matrix Head Rule
  | [] => []
  | row :: rows =>
      match row.patterns with
      | .node head children :: patterns =>
          let rest := specializePrefix query rows
          if query = ({ head, arity := children.length } : ConstructorKey Head)
          then { row with patterns := children ++ patterns } :: rest
          else rest
      | _ => []

/-- Default continuation beginning at the first wildcard or empty row. -/
def defaultMatrix : Matrix Head Rule -> Matrix Head Rule
  | [] => []
  | row :: rows =>
      match row.firstKey? with
      | some _ => defaultMatrix rows
      | none => row :: rows

/-! ## Structural compilation bound -/

mutual
  /-- Number of pattern nodes still available to inspect. -/
  def Pattern.work : Pattern Head -> Nat
    | .wildcard => 1
    | .node _ children => 1 + patternListWork children

  /-- Additive work of a residual pattern vector. -/
  def patternListWork : List (Pattern Head) -> Nat
    | [] => 0
    | pattern :: patterns => pattern.work + patternListWork patterns
end

/-- Every authored row contributes one occurrence unit in addition to its
remaining pattern work. -/
def Row.work (row : Row Head Rule) : Nat :=
  1 + patternListWork row.patterns

/-- Additive work of a residual matrix. -/
def matrixWork : Matrix Head Rule -> Nat
  | [] => 0
  | row :: rows => row.work + matrixWork rows

@[simp] theorem patternListWork_append
    (first second : List (Pattern Head)) :
    patternListWork (first ++ second) =
      patternListWork first + patternListWork second := by
  induction first with
  | nil => simp [patternListWork]
  | cons pattern patterns inductionHypothesis =>
      simp [patternListWork, inductionHypothesis, Nat.add_assoc]

@[simp] theorem row_work_positive (row : Row Head Rule) :
    0 < row.work := by
  unfold Row.work
  omega

theorem matrixWork_specializePrefix_le [DecidableEq Head]
    (query : ConstructorKey Head) (matrix : Matrix Head Rule) :
    matrixWork (specializePrefix query matrix) <= matrixWork matrix := by
  induction matrix with
  | nil => exact Nat.le_refl _
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [specializePrefix, matrixWork, Row.work, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard =>
              simp [specializePrefix, matrixWork, Row.work, rowPatterns]
          | node head children =>
              by_cases sameKey :
                  query = ({ head, arity := children.length } :
                    ConstructorKey Head)
              · subst query
                have tailLe := inductionHypothesis
                simp [specializePrefix, matrixWork, Row.work, Pattern.work,
                  patternListWork, rowPatterns]
                omega
              · simp [specializePrefix, matrixWork, Row.work, Pattern.work,
                  patternListWork, rowPatterns, sameKey] at *
                omega

private theorem matrixWork_specializePrefix_lt_of_mem_raw
    [DecidableEq Head]
    (query : ConstructorKey Head) (matrix : Matrix Head Rule)
    (present : query ∈ rigidPrefixKeysRaw matrix) :
    matrixWork (specializePrefix query matrix) < matrixWork matrix := by
  induction matrix with
  | nil => simp [rigidPrefixKeysRaw] at present
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil =>
          simp [rigidPrefixKeysRaw, Row.firstKey?, rowPatterns] at present
      | cons pattern patterns =>
          cases pattern with
          | wildcard =>
              simp [rigidPrefixKeysRaw, Row.firstKey?, rowPatterns] at present
          | node head children =>
              let key : ConstructorKey Head :=
                { head, arity := children.length }
              have presentCases : query = key ∨
                  query ∈ rigidPrefixKeysRaw rows := by
                simpa [rigidPrefixKeysRaw, Row.firstKey?, rowPatterns, key]
                  using present
              by_cases sameKey : query = key
              · subst query
                have tailLe := matrixWork_specializePrefix_le key rows
                dsimp [key] at tailLe
                simp [specializePrefix, matrixWork, Row.work, Pattern.work,
                  patternListWork, patternListWork_append, rowPatterns,
                  key]
                omega
              · have tailPresent : query ∈ rigidPrefixKeysRaw rows :=
                  presentCases.resolve_left sameKey
                have tailLt := inductionHypothesis tailPresent
                simp [specializePrefix, matrixWork, Row.work, Pattern.work,
                  patternListWork, rowPatterns, key, sameKey]
                omega

/-- Every branch key emitted from a rigid prefix has a strictly smaller
residual matrix. -/
theorem matrixWork_specializePrefix_lt_of_mem
    [DecidableEq Head]
    (query : ConstructorKey Head) (matrix : Matrix Head Rule)
    (present : query ∈ rigidPrefixKeys matrix) :
    matrixWork (specializePrefix query matrix) < matrixWork matrix := by
  apply matrixWork_specializePrefix_lt_of_mem_raw query matrix
  simpa [rigidPrefixKeys] using present

theorem matrixWork_defaultMatrix_le (matrix : Matrix Head Rule) :
    matrixWork (defaultMatrix matrix) <= matrixWork matrix := by
  induction matrix with
  | nil => exact Nat.le_refl _
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [defaultMatrix, Row.firstKey?, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard => simp [defaultMatrix, Row.firstKey?, rowPatterns]
          | node head children =>
              simp [defaultMatrix, Row.firstKey?, matrixWork, rowPatterns]
              omega

/-- Taking the default from a rigid first row strictly decreases work. -/
theorem matrixWork_defaultMatrix_lt_of_firstKey
    (row : Row Head Rule) (rows : Matrix Head Rule)
    (key : ConstructorKey Head) (rigid : row.firstKey? = some key) :
    matrixWork (defaultMatrix (row :: rows)) <
      matrixWork (row :: rows) := by
  have tailLe := matrixWork_defaultMatrix_le rows
  have rowPositive := row_work_positive row
  rw [show defaultMatrix (row :: rows) = defaultMatrix rows by
    simp [defaultMatrix, rigid]]
  change matrixWork (defaultMatrix rows) < row.work + matrixWork rows
  omega

/-- Removing an authored row strictly decreases matrix work. -/
theorem matrixWork_tail_lt (row : Row Head Rule) (rows : Matrix Head Rule) :
    matrixWork rows < matrixWork (row :: rows) := by
  have positive := row_work_positive row
  simp only [matrixWork]
  omega

/-- Compile every finite constructor key to a branch. -/
def compileBranches [DecidableEq Head]
    (compileRecursive : Matrix Head Rule ->
      Option (DecisionTree Head Rule))
    (matrix : Matrix Head Rule) :
    List (ConstructorKey Head) ->
      Option (DecisionBranches Head Rule)
  | [] => some .nil
  | key :: keys => do
      let tree <- compileRecursive (specializePrefix key matrix)
      let rest <- compileBranches compileRecursive matrix keys
      some (.cons key tree rest)

/-- One fuel layer of ordered pattern-matrix compilation. -/
def compileStep [DecidableEq Head]
    (compileRecursive : Matrix Head Rule ->
      Option (DecisionTree Head Rule))
    (matrix : Matrix Head Rule) : Option (DecisionTree Head Rule) :=
  match matrix with
  | [] => some .failure
  | row :: rows =>
      match row.firstKey? with
      | none => do
          let onFailure <- compileRecursive rows
          some (.tryRule row.rule row.patterns onFailure)
      | some _ => do
          let branches <- compileBranches compileRecursive matrix
            (rigidPrefixKeys matrix)
          let default <- compileRecursive (defaultMatrix matrix)
          some (.switch branches default)

/-- Fuel-bounded compiler.  Exhaustion is an explicit admission failure. -/
def compile? [DecidableEq Head] :
    Nat -> Matrix Head Rule -> Option (DecisionTree Head Rule)
  | 0, _ => none
  | fuel + 1, matrix => compileStep (compile? fuel) matrix

private theorem compileBranches_exists_of_each [DecidableEq Head]
    (fuel : Nat) (matrix : Matrix Head Rule)
    (keys : List (ConstructorKey Head))
    (each : forall key, key ∈ keys ->
      exists tree, compile? fuel (specializePrefix key matrix) = some tree) :
    exists branches,
      compileBranches (compile? fuel) matrix keys = some branches := by
  induction keys with
  | nil => exact ⟨.nil, rfl⟩
  | cons key keys inductionHypothesis =>
      obtain ⟨tree, treeCompiled⟩ := each key (by simp)
      obtain ⟨branches, branchesCompiled⟩ := inductionHypothesis
        (fun tailKey membership => each tailKey (by simp [membership]))
      exact ⟨.cons key tree branches, by
        simp [compileBranches, treeCompiled, branchesCompiled]⟩

/-- Any fuel strictly above the structural matrix work is sufficient.  This
is a theorem about the generic compiler, so individual languages do not need
large normalization certificates merely to obtain a decision program. -/
theorem compile?_exists_of_work_lt [DecidableEq Head] :
    forall (fuel : Nat) (matrix : Matrix Head Rule),
      matrixWork matrix < fuel ->
      exists tree, compile? fuel matrix = some tree := by
  intro fuel
  induction fuel with
  | zero =>
      intro matrix bound
      omega
  | succ fuel inductionHypothesis =>
      intro matrix bound
      cases matrix with
      | nil =>
          exact ⟨.failure, rfl⟩
      | cons row rows =>
          cases rowPatterns : row.patterns with
          | nil =>
              have tailBound : matrixWork rows < fuel := by
                have tailLt := matrixWork_tail_lt row rows
                omega
              obtain ⟨tail, tailCompiled⟩ :=
                inductionHypothesis rows tailBound
              refine ⟨.tryRule row.rule [] tail, ?_⟩
              simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                tailCompiled]
          | cons pattern patterns =>
              cases pattern with
              | wildcard =>
                  have tailBound : matrixWork rows < fuel := by
                    have tailLt := matrixWork_tail_lt row rows
                    omega
                  obtain ⟨tail, tailCompiled⟩ :=
                    inductionHypothesis rows tailBound
                  refine ⟨.tryRule row.rule (.wildcard :: patterns) tail, ?_⟩
                  simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                    tailCompiled]
              | node head children =>
                  have branchCompilation :=
                    compileBranches_exists_of_each fuel (row :: rows)
                      (rigidPrefixKeys (row :: rows)) (fun key membership => by
                        apply inductionHypothesis
                        have residualLt :=
                          matrixWork_specializePrefix_lt_of_mem
                            key (row :: rows) membership
                        omega)
                  obtain ⟨branches, branchesCompiled⟩ := branchCompilation
                  have firstKey : row.firstKey? = some
                      ({ head, arity := children.length } : ConstructorKey Head) := by
                    simp [Row.firstKey?, rowPatterns]
                  have defaultLt := matrixWork_defaultMatrix_lt_of_firstKey
                    row rows
                    ({ head, arity := children.length } : ConstructorKey Head)
                    firstKey
                  have defaultBound :
                      matrixWork (defaultMatrix (row :: rows)) < fuel := by
                    omega
                  obtain ⟨default, defaultCompiled⟩ :=
                    inductionHypothesis (defaultMatrix (row :: rows))
                      defaultBound
                  refine ⟨.switch branches default, ?_⟩
                  simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                    branchesCompiled,
                    defaultCompiled]

/-- The canonical structural work bound always produces a decision tree. -/
theorem compile?_bounded_isSome [DecidableEq Head]
    (matrix : Matrix Head Rule) :
    (compile? (matrixWork matrix + 1) matrix).isSome = true := by
  obtain ⟨tree, compiled⟩ :=
    compile?_exists_of_work_lt (matrixWork matrix + 1) matrix (by omega)
  simp [compiled]

/-- Total ordered pattern-matrix compiler using the proved structural bound. -/
def compile [DecidableEq Head]
    (matrix : Matrix Head Rule) : DecisionTree Head Rule :=
  (compile? (matrixWork matrix + 1) matrix).get
    (compile?_bounded_isSome matrix)

/-- The total compiler is exactly the successful bounded compiler result. -/
theorem compile?_bounded_eq_some [DecidableEq Head]
    (matrix : Matrix Head Rule) :
    compile? (matrixWork matrix + 1) matrix = some (compile matrix) :=
  (Option.some_get (compile?_bounded_isSome matrix)).symm

/-! ## Semantic preservation -/

/-- Left-biased choice, used to state ordered fallthrough independently of
the target evaluator. -/
def firstSuccess (first second : Option Result) : Option Result :=
  match first with
  | some result => some result
  | none => second

theorem structuralMatchList_append
    [DecidableEq Head]
    (leftPatterns rightPatterns : List (Pattern Head))
    (leftSubjects rightSubjects : List (Subject Head))
    (sameLength : leftPatterns.length = leftSubjects.length) :
    structuralMatchList (leftPatterns ++ rightPatterns)
        (leftSubjects ++ rightSubjects) =
      (structuralMatchList leftPatterns leftSubjects &&
        structuralMatchList rightPatterns rightSubjects) := by
  induction leftPatterns generalizing leftSubjects with
  | nil =>
      cases leftSubjects <;> simp_all [structuralMatchList]
  | cons pattern patterns inductionHypothesis =>
      cases leftSubjects with
      | nil => simp at sameLength
      | cons subject subjects =>
          simp only [List.length_cons, Nat.succ.injEq] at sameLength
          simp [structuralMatchList,
            inductionHypothesis subjects sameLength, Bool.and_assoc]

theorem structuralMatchList_eq_false_of_length_ne
    [DecidableEq Head]
    (patterns : List (Pattern Head)) (subjects : List (Subject Head))
    (differentLength : patterns.length ≠ subjects.length) :
    structuralMatchList patterns subjects = false := by
  induction patterns generalizing subjects with
  | nil =>
      cases subjects with
      | nil => exact absurd rfl differentLength
      | cons subject subjects => rfl
  | cons pattern patterns inductionHypothesis =>
      cases subjects with
      | nil => rfl
      | cons subject subjects =>
          have tailDifferent : patterns.length ≠ subjects.length := by
            intro same
            apply differentLength
            simp [same]
          simp [structuralMatchList,
            inductionHypothesis subjects tailDifferent]

theorem structuralMatchList_node_eq_specialized
    [DecidableEq Head]
    (patternHead subjectHead : Head)
    (patternChildren : List (Pattern Head))
    (subjectChildren : List (Subject Head))
    (patterns : List (Pattern Head))
    (subjects : List (Subject Head))
    (sameKey :
      ({ head := subjectHead, arity := subjectChildren.length } :
          ConstructorKey Head) =
        { head := patternHead, arity := patternChildren.length }) :
    structuralMatchList
        (.node patternHead patternChildren :: patterns)
        (.node subjectHead subjectChildren :: subjects) =
      structuralMatchList (patternChildren ++ patterns)
        (subjectChildren ++ subjects) := by
  have sameHead : subjectHead = patternHead :=
    congrArg ConstructorKey.head sameKey
  have sameLength : subjectChildren.length = patternChildren.length :=
    congrArg ConstructorKey.arity sameKey
  subst subjectHead
  simp [structuralMatchList, structuralMatch,
    structuralMatchList_append patternChildren patterns
      subjectChildren subjects sameLength.symm]

theorem structuralMatchList_node_eq_false_of_key_ne
    [DecidableEq Head]
    (patternHead subjectHead : Head)
    (patternChildren : List (Pattern Head))
    (subjectChildren : List (Subject Head))
    (patterns : List (Pattern Head))
    (subjects : List (Subject Head))
    (differentKey :
      ({ head := subjectHead, arity := subjectChildren.length } :
          ConstructorKey Head) ≠
        { head := patternHead, arity := patternChildren.length }) :
    structuralMatchList
        (.node patternHead patternChildren :: patterns)
        (.node subjectHead subjectChildren :: subjects) = false := by
  by_cases sameHead : subjectHead = patternHead
  · subst subjectHead
    have differentLength :
        patternChildren.length ≠ subjectChildren.length := by
      intro sameLength
      apply differentKey
      simp [sameLength]
    simp [structuralMatchList, structuralMatch,
      structuralMatchList_eq_false_of_length_ne
        patternChildren subjectChildren differentLength]
  · have reverse : patternHead ≠ subjectHead := Ne.symm sameHead
    simp [structuralMatchList, structuralMatch, reverse]

/-- A constructor observation splits source execution into the matching rigid
prefix branch followed by the untouched wildcard default. -/
theorem runMatrix_constructor_decomposition
    [DecidableEq Head]
    (attempt : Rule -> Option Result)
    (matrix : Matrix Head Rule) (head : Head)
    (children : List (Subject Head)) (subjects : List (Subject Head)) :
    runMatrix attempt matrix (.node head children :: subjects) =
      firstSuccess
        (runMatrix attempt
          (specializePrefix { head, arity := children.length } matrix)
          (children ++ subjects))
        (runMatrix attempt (defaultMatrix matrix)
          (.node head children :: subjects)) := by
  induction matrix with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [specializePrefix, defaultMatrix, Row.firstKey?,
          runMatrix, firstSuccess, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard =>
              simp [specializePrefix, defaultMatrix, Row.firstKey?,
                runMatrix, firstSuccess, rowPatterns]
          | node patternHead patternChildren =>
              by_cases sameKey :
                  ({ head, arity := children.length } : ConstructorKey Head) =
                    { head := patternHead,
                      arity := patternChildren.length }
              · have structural := structuralMatchList_node_eq_specialized
                  patternHead head patternChildren children patterns subjects
                  sameKey
                cases matchResult : structuralMatchList
                    (patternChildren ++ patterns) (children ++ subjects) <;>
                  cases attemptResult : attempt row.rule <;>
                  cases tailResult : runMatrix attempt
                    (specializePrefix
                      { head := patternHead,
                        arity := patternChildren.length } rows)
                    (children ++ subjects) <;>
                  simp [specializePrefix, defaultMatrix, Row.firstKey?,
                    runMatrix, firstSuccess, rowPatterns, sameKey,
                    structural, inductionHypothesis, matchResult,
                    attemptResult, tailResult]
              · have structural :=
                  structuralMatchList_node_eq_false_of_key_ne
                    patternHead head patternChildren children patterns subjects
                    sameKey
                simp [specializePrefix, defaultMatrix, Row.firstKey?,
                  runMatrix, firstSuccess, rowPatterns, sameKey,
                  structural, inductionHypothesis]

/-- With no subject coordinate, every row in the rigid prefix fails and
execution begins at the default matrix. -/
theorem runMatrix_nil_eq_default
    [DecidableEq Head]
    (attempt : Rule -> Option Result) (matrix : Matrix Head Rule) :
    runMatrix attempt matrix [] =
      runMatrix attempt (defaultMatrix matrix) [] := by
  induction matrix with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [defaultMatrix, Row.firstKey?, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard => simp [defaultMatrix, Row.firstKey?, rowPatterns]
          | node head children =>
              simp [runMatrix, defaultMatrix, Row.firstKey?, rowPatterns,
                inductionHypothesis, structuralMatchList]

private theorem specializePrefix_eq_nil_of_not_mem_rawKeys
    [DecidableEq Head]
    (query : ConstructorKey Head) (matrix : Matrix Head Rule)
    (missing : query ∉ rigidPrefixKeysRaw matrix) :
    specializePrefix query matrix = [] := by
  induction matrix with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [specializePrefix, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard => simp [specializePrefix, rowPatterns]
          | node head children =>
              let key : ConstructorKey Head :=
                { head, arity := children.length }
              have components :
                  query ≠ key ∧ query ∉ rigidPrefixKeysRaw rows := by
                simpa [rigidPrefixKeysRaw, Row.firstKey?, rowPatterns, key]
                  using missing
              simp [specializePrefix, rowPatterns, key,
                inductionHypothesis components.2, components.1]

theorem specializePrefix_eq_nil_of_not_mem_keys
    [DecidableEq Head]
    (query : ConstructorKey Head) (matrix : Matrix Head Rule)
    (missing : query ∉ rigidPrefixKeys matrix) :
    specializePrefix query matrix = [] := by
  apply specializePrefix_eq_nil_of_not_mem_rawKeys query matrix
  simpa [rigidPrefixKeys] using missing

/-- Branch compilation preserves the exact source meaning of every requested
key, assuming the recursive compiler does so for each residual matrix. -/
theorem evalBranch_compileBranches
    [DecidableEq Head]
    (compileRecursive : Matrix Head Rule ->
      Option (DecisionTree Head Rule))
    (attempt : Rule -> Option Result)
    (matrix : Matrix Head Rule)
    (keys : List (ConstructorKey Head))
    (branches : DecisionBranches Head Rule)
    (compiled : compileBranches compileRecursive matrix keys = some branches)
    (recursiveExact : forall residual tree,
      compileRecursive residual = some tree ->
      forall subjects,
        tree.eval attempt subjects = runMatrix attempt residual subjects)
    (query : ConstructorKey Head) (subjects : List (Subject Head)) :
    DecisionTree.evalBranch attempt query subjects branches =
      if query ∈ keys then
        runMatrix attempt (specializePrefix query matrix) subjects
      else none := by
  induction keys generalizing branches with
  | nil =>
      simp [compileBranches] at compiled
      subst branches
      rfl
  | cons key keys inductionHypothesis =>
      cases treeCompiled : compileRecursive (specializePrefix key matrix) with
      | none => simp [compileBranches, treeCompiled] at compiled
      | some tree =>
          cases restCompiled :
              compileBranches compileRecursive matrix keys with
          | none =>
              simp [compileBranches, treeCompiled, restCompiled] at compiled
          | some rest =>
              simp [compileBranches, treeCompiled, restCompiled] at compiled
              subst branches
              by_cases same : query = key
              · subst key
                simp [DecisionTree.evalBranch,
                  recursiveExact _ tree treeCompiled subjects]
              · simp [DecisionTree.evalBranch, same,
                  inductionHypothesis rest restCompiled]

/-- Every successfully compiled decision program has exactly the authored
ordered source behavior, for every independent rule continuation. -/
theorem compile?_correct
    [DecidableEq Head]
    (fuel : Nat) (matrix : Matrix Head Rule)
    (tree : DecisionTree Head Rule)
    (compiled : compile? fuel matrix = some tree)
    (attempt : Rule -> Option Result)
    (subjects : List (Subject Head)) :
    tree.eval attempt subjects = runMatrix attempt matrix subjects := by
  induction fuel generalizing matrix tree subjects with
  | zero => simp [compile?] at compiled
  | succ fuel inductionHypothesis =>
      cases matrix with
      | nil =>
          simp [compile?, compileStep] at compiled
          subst tree
          rfl
      | cons row rows =>
          cases rowPatterns : row.patterns with
          | nil =>
              cases tailCompiled : compile? fuel rows with
              | none =>
                  simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                    tailCompiled] at compiled
              | some tail =>
                  simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                    tailCompiled] at compiled
                  subst tree
                  simp [DecisionTree.eval, runMatrix, rowPatterns,
                    inductionHypothesis rows tail tailCompiled]
          | cons pattern patterns =>
              cases pattern with
              | wildcard =>
                  cases tailCompiled : compile? fuel rows with
                  | none =>
                      simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                        tailCompiled] at compiled
                  | some tail =>
                      simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                        tailCompiled] at compiled
                      subst tree
                      simp [DecisionTree.eval, runMatrix, rowPatterns,
                        inductionHypothesis rows tail tailCompiled]
              | node head children =>
                  cases branchesCompiled :
                      compileBranches (compile? fuel) (row :: rows)
                        (rigidPrefixKeys (row :: rows)) with
                  | none =>
                      simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                        branchesCompiled] at compiled
                  | some branches =>
                      cases defaultCompiled :
                          compile? fuel (defaultMatrix (row :: rows)) with
                      | none =>
                          simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                            branchesCompiled, defaultCompiled] at compiled
                      | some default =>
                          simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                            branchesCompiled, defaultCompiled] at compiled
                          subst tree
                          cases subjects with
                          | nil =>
                              simp only [DecisionTree.eval]
                              rw [inductionHypothesis
                                (defaultMatrix (row :: rows)) default
                                defaultCompiled []]
                              exact (runMatrix_nil_eq_default attempt
                                (row :: rows)).symm
                          | cons subject subjects =>
                              cases subject with
                              | node subjectHead subjectChildren =>
                                  let query : ConstructorKey Head :=
                                    { head := subjectHead,
                                      arity := subjectChildren.length }
                                  have branchExact := evalBranch_compileBranches
                                    (compile? fuel) attempt (row :: rows)
                                    (rigidPrefixKeys (row :: rows)) branches
                                    branchesCompiled
                                    (fun residual branch branchCompiled branchSubjects =>
                                      inductionHypothesis residual branch
                                        branchCompiled branchSubjects)
                                    query (subjectChildren ++ subjects)
                                  have defaultExact := inductionHypothesis
                                    (defaultMatrix (row :: rows)) default
                                    defaultCompiled
                                    (.node subjectHead subjectChildren :: subjects)
                                  by_cases present :
                                      query ∈ rigidPrefixKeys (row :: rows)
                                  · simp only [DecisionTree.eval]
                                    rw [branchExact, if_pos present, defaultExact]
                                    exact (runMatrix_constructor_decomposition
                                      attempt (row :: rows) subjectHead
                                      subjectChildren subjects).symm
                                  · have emptySpecialization :=
                                      specializePrefix_eq_nil_of_not_mem_keys
                                        query (row :: rows) present
                                    simp only [DecisionTree.eval]
                                    rw [branchExact, if_neg present, defaultExact]
                                    have decomposition :=
                                      runMatrix_constructor_decomposition
                                        attempt (row :: rows) subjectHead
                                        subjectChildren subjects
                                    have emptySpecialization' :
                                        specializePrefix
                                          { head := subjectHead,
                                            arity := subjectChildren.length }
                                          (row :: rows) = [] := by
                                      simpa [query] using emptySpecialization
                                    rw [emptySpecialization'] at decomposition
                                    simp [firstSuccess] at decomposition
                                    exact decomposition.symm

/-- Constructor branching preserves the complete ordered result list. -/
theorem runMatrixAll_constructor_decomposition
    [DecidableEq Head]
    (attempt : Rule -> List Result)
    (matrix : Matrix Head Rule) (head : Head)
    (children : List (Subject Head)) (subjects : List (Subject Head)) :
    runMatrixAll attempt matrix (.node head children :: subjects) =
      runMatrixAll attempt
          (specializePrefix { head, arity := children.length } matrix)
          (children ++ subjects) ++
        runMatrixAll attempt (defaultMatrix matrix)
          (.node head children :: subjects) := by
  induction matrix with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [specializePrefix, defaultMatrix, Row.firstKey?,
          runMatrixAll, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard =>
              simp [specializePrefix, defaultMatrix, Row.firstKey?,
                runMatrixAll, rowPatterns]
          | node patternHead patternChildren =>
              by_cases sameKey :
                  ({ head, arity := children.length } : ConstructorKey Head) =
                    { head := patternHead,
                      arity := patternChildren.length }
              · have structural := structuralMatchList_node_eq_specialized
                  patternHead head patternChildren children patterns subjects
                  sameKey
                cases matchResult : structuralMatchList
                    (patternChildren ++ patterns) (children ++ subjects) <;>
                  simp [specializePrefix, defaultMatrix, Row.firstKey?,
                    runMatrixAll, rowPatterns, sameKey, structural,
                    inductionHypothesis, matchResult, List.append_assoc]
              · have structural :=
                  structuralMatchList_node_eq_false_of_key_ne
                    patternHead head patternChildren children patterns subjects
                    sameKey
                simp [specializePrefix, defaultMatrix, Row.firstKey?,
                  runMatrixAll, rowPatterns, sameKey, structural,
                  inductionHypothesis]

theorem runMatrixAll_nil_eq_default
    [DecidableEq Head]
    (attempt : Rule -> List Result) (matrix : Matrix Head Rule) :
    runMatrixAll attempt matrix [] =
      runMatrixAll attempt (defaultMatrix matrix) [] := by
  induction matrix with
  | nil => rfl
  | cons row rows inductionHypothesis =>
      cases rowPatterns : row.patterns with
      | nil => simp [defaultMatrix, Row.firstKey?, rowPatterns]
      | cons pattern patterns =>
          cases pattern with
          | wildcard => simp [defaultMatrix, Row.firstKey?, rowPatterns]
          | node head children =>
              simp [runMatrixAll, defaultMatrix, Row.firstKey?, rowPatterns,
                inductionHypothesis, structuralMatchList]

theorem evalBranchAll_compileBranches
    [DecidableEq Head]
    (compileRecursive : Matrix Head Rule ->
      Option (DecisionTree Head Rule))
    (attempt : Rule -> List Result)
    (matrix : Matrix Head Rule)
    (keys : List (ConstructorKey Head))
    (branches : DecisionBranches Head Rule)
    (compiled : compileBranches compileRecursive matrix keys = some branches)
    (recursiveExact : forall residual tree,
      compileRecursive residual = some tree ->
      forall subjects,
        tree.evalAll attempt subjects = runMatrixAll attempt residual subjects)
    (query : ConstructorKey Head) (subjects : List (Subject Head)) :
    DecisionTree.evalBranchAll attempt query subjects branches =
      if query ∈ keys then
        runMatrixAll attempt (specializePrefix query matrix) subjects
      else [] := by
  induction keys generalizing branches with
  | nil =>
      simp [compileBranches] at compiled
      subst branches
      rfl
  | cons key keys inductionHypothesis =>
      cases treeCompiled : compileRecursive (specializePrefix key matrix) with
      | none => simp [compileBranches, treeCompiled] at compiled
      | some tree =>
          cases restCompiled :
              compileBranches compileRecursive matrix keys with
          | none =>
              simp [compileBranches, treeCompiled, restCompiled] at compiled
          | some rest =>
              simp [compileBranches, treeCompiled, restCompiled] at compiled
              subst branches
              by_cases same : query = key
              · subst key
                simp [DecisionTree.evalBranchAll,
                  recursiveExact _ tree treeCompiled subjects]
              · simp [DecisionTree.evalBranchAll, same,
                  inductionHypothesis rest restCompiled]

/-- Successful compilation preserves the complete ordered and
multiplicity-sensitive result list for every independent rule continuation. -/
theorem compile?_all_correct
    [DecidableEq Head]
    (fuel : Nat) (matrix : Matrix Head Rule)
    (tree : DecisionTree Head Rule)
    (compiled : compile? fuel matrix = some tree)
    (attempt : Rule -> List Result)
    (subjects : List (Subject Head)) :
    tree.evalAll attempt subjects = runMatrixAll attempt matrix subjects := by
  induction fuel generalizing matrix tree subjects with
  | zero => simp [compile?] at compiled
  | succ fuel inductionHypothesis =>
      cases matrix with
      | nil =>
          simp [compile?, compileStep] at compiled
          subst tree
          rfl
      | cons row rows =>
          cases rowPatterns : row.patterns with
          | nil =>
              cases tailCompiled : compile? fuel rows with
              | none =>
                  simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                    tailCompiled] at compiled
              | some tail =>
                  simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                    tailCompiled] at compiled
                  subst tree
                  simp [DecisionTree.evalAll, runMatrixAll, rowPatterns,
                    inductionHypothesis rows tail tailCompiled]
          | cons pattern patterns =>
              cases pattern with
              | wildcard =>
                  cases tailCompiled : compile? fuel rows with
                  | none =>
                      simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                        tailCompiled] at compiled
                  | some tail =>
                      simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                        tailCompiled] at compiled
                      subst tree
                      simp [DecisionTree.evalAll, runMatrixAll, rowPatterns,
                        inductionHypothesis rows tail tailCompiled]
              | node head children =>
                  cases branchesCompiled :
                      compileBranches (compile? fuel) (row :: rows)
                        (rigidPrefixKeys (row :: rows)) with
                  | none =>
                      simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                        branchesCompiled] at compiled
                  | some branches =>
                      cases defaultCompiled :
                          compile? fuel (defaultMatrix (row :: rows)) with
                      | none =>
                          simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                            branchesCompiled, defaultCompiled] at compiled
                      | some default =>
                          simp [compile?, compileStep, Row.firstKey?, rowPatterns,
                            branchesCompiled, defaultCompiled] at compiled
                          subst tree
                          cases subjects with
                          | nil =>
                              simp only [DecisionTree.evalAll]
                              rw [inductionHypothesis
                                (defaultMatrix (row :: rows)) default
                                defaultCompiled []]
                              exact (runMatrixAll_nil_eq_default attempt
                                (row :: rows)).symm
                          | cons subject subjects =>
                              cases subject with
                              | node subjectHead subjectChildren =>
                                  let query : ConstructorKey Head :=
                                    { head := subjectHead,
                                      arity := subjectChildren.length }
                                  have branchExact :=
                                    evalBranchAll_compileBranches
                                      (compile? fuel) attempt (row :: rows)
                                      (rigidPrefixKeys (row :: rows)) branches
                                      branchesCompiled
                                      (fun residual branch branchCompiled
                                          branchSubjects =>
                                        inductionHypothesis residual branch
                                          branchCompiled branchSubjects)
                                      query (subjectChildren ++ subjects)
                                  have defaultExact := inductionHypothesis
                                    (defaultMatrix (row :: rows)) default
                                    defaultCompiled
                                    (.node subjectHead subjectChildren :: subjects)
                                  by_cases present :
                                      query ∈ rigidPrefixKeys (row :: rows)
                                  · simp only [DecisionTree.evalAll]
                                    rw [branchExact, if_pos present, defaultExact]
                                    exact (runMatrixAll_constructor_decomposition
                                      attempt (row :: rows) subjectHead
                                      subjectChildren subjects).symm
                                  · have emptySpecialization :=
                                      specializePrefix_eq_nil_of_not_mem_keys
                                        query (row :: rows) present
                                    simp only [DecisionTree.evalAll]
                                    rw [branchExact, if_neg present, defaultExact]
                                    have decomposition :=
                                      runMatrixAll_constructor_decomposition
                                        attempt (row :: rows) subjectHead
                                        subjectChildren subjects
                                    have emptySpecialization' :
                                        specializePrefix
                                          { head := subjectHead,
                                            arity := subjectChildren.length }
                                          (row :: rows) = [] := by
                                      simpa [query] using emptySpecialization
                                    rw [emptySpecialization'] at decomposition
                                    exact decomposition.symm

/-- The compiled program enumerates exactly the structurally eligible rule
occurrences, in source order and with duplicates intact. -/
theorem compile?_candidate_rules_exact
    [DecidableEq Head]
    (fuel : Nat) (matrix : Matrix Head Rule)
    (tree : DecisionTree Head Rule)
    (compiled : compile? fuel matrix = some tree)
    (subjects : List (Subject Head)) :
    tree.evalAll (fun rule => [rule]) subjects =
      runMatrixAll (fun rule => [rule]) matrix subjects :=
  compile?_all_correct fuel matrix tree compiled (fun rule => [rule]) subjects


/-! ## Executable positive and negative controls -/

private inductive DemoHead where
  | atom (name : String)
  | pair
deriving DecidableEq, Repr

private def leaf (name : String) : Subject DemoHead :=
  .node (.atom name) []

private def demoMatrix : Matrix DemoHead String :=
  [ { rule := "left-pair"
      patterns := [.node .pair [.node (.atom "left") [], .wildcard]] }
  , { rule := "any-pair"
      patterns := [.node .pair [.wildcard, .wildcard]] }
  , { rule := "fallback", patterns := [.wildcard] } ]

private def demoAttempt (reject : String) (rule : String) : Option String :=
  if rule == reject then none else some rule

/-- A constructor branch selects the first matching authored row. -/
example :
    (compile? 20 demoMatrix).map (fun tree =>
      tree.eval (demoAttempt "") [.node .pair [leaf "left", leaf "x"]]) =
      some (some "left-pair") := by
  decide

/-- Guard failure falls through in source order to the next matching row. -/
example :
    (compile? 20 demoMatrix).map (fun tree =>
      tree.eval (demoAttempt "left-pair")
        [.node .pair [leaf "left", leaf "x"]]) =
      some (some "any-pair") := by
  decide

/-- A different constructor reaches the wildcard default. -/
example :
    (compile? 20 demoMatrix).map (fun tree =>
      tree.eval (demoAttempt "") [leaf "outside"]) =
      some (some "fallback") := by
  decide

/-- Zero fuel does not silently fall back to a fabricated program. -/
example : (compile? 0 demoMatrix).isNone = true := by
  decide

#print axioms compile?_bounded_eq_some
#print axioms compile?_correct
#print axioms compile?_all_correct
#print axioms compile?_candidate_rules_exact

end Mettapedia.GSLT.LanguageDef.OrderedPatternMatrixCompilation
