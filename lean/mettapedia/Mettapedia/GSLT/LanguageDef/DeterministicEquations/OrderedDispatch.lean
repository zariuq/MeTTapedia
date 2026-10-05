import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Norm

/-!
# Ordered equation dispatch over argument vectors

The compiler groups all arities of a source head into one ordered branch
table. Every row retains its original equation and occurrence index. Case-row
selection independently scans this table and matches one argument vector.
After selection, the body is evaluated once; its outcome never retries a
later row.

This is the dispatch component of lowering. It does not identify the source
matcher with a concrete MeTTa matcher, establish lexical renaming, or prove
the data, control, parser or runtime boundary.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.DeterministicEquations.OrderedDispatch

/-- One source occurrence, including its name, head, patterns and body. -/
structure CaseRow where
  sourceIndex : Nat
  equation : Equation

/-- All source arities are represented by one vector-pattern position. -/
def CaseRow.vectorPattern (row : CaseRow) : Term := .list row.equation.params

/-- Stable grouping. Indices count foreign-head occurrences as well. -/
def compileHeadFrom (firstIndex : Nat) : Program → String → List CaseRow
  | [], _ => []
  | equation :: rest, head =>
      if equation.head = head then
        { sourceIndex := firstIndex, equation } :: compileHeadFrom (firstIndex + 1) rest head
      else compileHeadFrom (firstIndex + 1) rest head

def compileHead (program : Program) (head : String) : List CaseRow :=
  compileHeadFrom 0 program head

/-- A case table scans in row order; a successful match commits to that row. -/
def selectCase : List CaseRow → List Term → Option (CaseRow × Env)
  | [], _ => none
  | row :: rest, arguments =>
      match matchTerm row.vectorPattern (.list arguments) with
      | some environment => some (row, environment)
      | none => selectCase rest arguments

/-- Drop only the occurrence index when comparing source selection. -/
def forgetIndex (selected : Option (CaseRow × Env)) : Option (Equation × Env) :=
  selected.map (fun hit => (hit.1.equation, hit.2))

/-- The selected body has no continuation to the remaining case rows. -/
def dispatchCaseWith (evaluateBody : Env → Term → Outcome)
    (rows : List CaseRow) (arguments : List Term) : Outcome :=
  match selectCase rows arguments with
  | none => .failure
  | some (row, environment) => evaluateBody environment row.equation.body

theorem vector_match (row : CaseRow) (arguments : List Term) :
    matchTerm row.vectorPattern (.list arguments) = matchTerms row.equation.params arguments := rfl

theorem vector_wrong_arity (row : CaseRow) (arguments : List Term)
    (wrong : row.equation.params.length ≠ arguments.length) :
    matchTerm row.vectorPattern (.list arguments) = none := by
  rw [vector_match]
  cases matched : matchTerms row.equation.params arguments with
  | none => rfl
  | some environment => exact False.elim (wrong (matchTerms_length matched))

/-- Stable filtering preserves original equations, including duplicates. -/
theorem compileHeadFrom_equations (program : Program) (head : String) (firstIndex : Nat) :
    (compileHeadFrom firstIndex program head).map (·.equation) =
      program.filter (fun equation => decide (equation.head = head)) := by
  induction program generalizing firstIndex with
  | nil => rfl
  | cons equation rest ih =>
      by_cases same : equation.head = head <;>
        simp [compileHeadFrom, same, ih]

/-- Each index identifies an actual source occurrence, rather than its name. -/
theorem compileHeadFrom_origin {program : Program} {head : String} {firstIndex : Nat}
    {row : CaseRow} (member : row ∈ compileHeadFrom firstIndex program head) :
    ∃ before after, program = before ++ row.equation :: after ∧
      row.sourceIndex = firstIndex + before.length ∧ row.equation.head = head := by
  induction program generalizing firstIndex with
  | nil => simp [compileHeadFrom] at member
  | cons equation rest ih =>
      by_cases same : equation.head = head
      · simp only [compileHeadFrom, same, if_pos, List.mem_cons] at member
        rcases member with equal | member
        · subst row
          exact ⟨[], rest, rfl, by simp, same⟩
        · obtain ⟨before, after, original, index, rowHead⟩ := ih member
          refine ⟨equation :: before, after, ?_, ?_, rowHead⟩
          · simp [original]
          · simp only [List.length_cons]
            omega
      · simp only [compileHeadFrom, same] at member
        obtain ⟨before, after, original, index, rowHead⟩ := ih member
        refine ⟨equation :: before, after, ?_, ?_, rowHead⟩
        · simp [original]
        · simp only [List.length_cons]
          omega

theorem compileHeadFrom_index_ge {program : Program} {head : String} {firstIndex : Nat}
    {row : CaseRow} (member : row ∈ compileHeadFrom firstIndex program head) :
    firstIndex ≤ row.sourceIndex := by
  obtain ⟨before, _, _, index, _⟩ := compileHeadFrom_origin member
  omega

/-- Grouping never reorders or merges source occurrence identities. -/
theorem compileHeadFrom_indices_increasing (program : Program) (head : String) (firstIndex : Nat) :
    (compileHeadFrom firstIndex program head).Pairwise
      (fun left right => left.sourceIndex < right.sourceIndex) := by
  induction program generalizing firstIndex with
  | nil => exact List.Pairwise.nil
  | cons equation rest ih =>
      by_cases same : equation.head = head
      · simp only [compileHeadFrom, same, if_pos, List.pairwise_cons]
        constructor
        · intro row member
          have bound := compileHeadFrom_index_ge member
          change firstIndex < row.sourceIndex
          omega
        · exact ih (firstIndex + 1)
      · simpa only [compileHeadFrom, same, if_false] using ih (firstIndex + 1)

private theorem source_select_cons (equation : Equation) (rest : Program)
    (head : String) (arguments : List Term) :
    Program.select (equation :: rest) head arguments =
      if equation.head = head then
        match matchTerms equation.params arguments with
        | some environment => some (equation, environment)
        | none => rest.select head arguments
      else rest.select head arguments := by
  by_cases same : equation.head = head
  · cases matched : matchTerms equation.params arguments with
    | none => simp [Program.select, same, matched]
    | some environment =>
        have arity := matchTerms_length matched
        simp [Program.select, same, arity, matched]
  · simp [Program.select, same]

/-- Complete source-selection equality, retaining its exact bindings. -/
theorem selectCase_compileHeadFrom (program : Program) (head : String)
    (arguments : List Term) (firstIndex : Nat) :
    forgetIndex (selectCase (compileHeadFrom firstIndex program head) arguments) =
      program.select head arguments := by
  induction program generalizing firstIndex with
  | nil => rfl
  | cons equation rest ih =>
      rw [source_select_cons]
      by_cases same : equation.head = head
      · simp only [compileHeadFrom, same, if_pos, selectCase, vector_match]
        cases matched : matchTerms equation.params arguments with
        | none => exact ih (firstIndex + 1)
        | some environment => rfl
      · simpa only [compileHeadFrom, same, if_false] using ih (firstIndex + 1)

theorem selectCase_compileHead (program : Program) (head : String) (arguments : List Term) :
    forgetIndex (selectCase (compileHead program head) arguments) =
      program.select head arguments := selectCase_compileHeadFrom program head arguments 0

theorem selectCase_append (earlierRows suffix : List CaseRow) (arguments : List Term) :
    selectCase (earlierRows ++ suffix) arguments =
      match selectCase earlierRows arguments with
      | some selected => some selected
      | none => selectCase suffix arguments := by
  induction earlierRows with
  | nil => rfl
  | cons row rest ih =>
      simp only [List.cons_append, selectCase]
      cases matched : matchTerm row.vectorPattern (.list arguments) <;> simp [ih]

theorem selectCase_wrong_arity (rows : List CaseRow) (arguments : List Term)
    (wrong : ∀ row ∈ rows, row.equation.params.length ≠ arguments.length) :
    selectCase rows arguments = none := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
      rw [selectCase, vector_wrong_arity row arguments (wrong row (by simp))]
      exact ih (fun later member => wrong later (by simp [member]))

theorem compiled_missing_arity (program : Program) (head : String) (arguments : List Term)
    (missing : program.definesAt head arguments.length = false) :
    selectCase (compileHead program head) arguments = none := by
  apply selectCase_wrong_arity
  intro row member sameLength
  obtain ⟨before, after, original, _, sameHead⟩ := compileHeadFrom_origin member
  have equationMember : row.equation ∈ program := by simp [original]
  have absent := (List.any_eq_false.mp missing) row.equation equationMember
  simp [sameHead, sameLength] at absent

theorem dispatchCaseWith_selected (evaluateBody : Env → Term → Outcome)
    (rows : List CaseRow) (arguments : List Term) (row : CaseRow) (environment : Env)
    (selected : selectCase rows arguments = some (row, environment)) :
    dispatchCaseWith evaluateBody rows arguments = evaluateBody environment row.equation.body := by
  simp only [dispatchCaseWith, selected]

theorem dispatchCaseWith_no_match (evaluateBody : Env → Term → Outcome)
    (rows : List CaseRow) (arguments : List Term)
    (unmatched : selectCase rows arguments = none) :
    dispatchCaseWith evaluateBody rows arguments = .failure := by
  simp only [dispatchCaseWith, unmatched]

/-- Any body outcome commits; the suffix is not an alternative evaluator. -/
theorem dispatchCaseWith_commit (evaluateBody : Env → Term → Outcome)
    (earlierRows suffix : List CaseRow) (arguments : List Term) (row : CaseRow) (environment : Env)
    (selected : selectCase earlierRows arguments = some (row, environment)) :
    dispatchCaseWith evaluateBody (earlierRows ++ suffix) arguments =
      evaluateBody environment row.equation.body := by
  apply dispatchCaseWith_selected
  simp only [selectCase_append, selected]

theorem selected_failure_does_not_fall_through (evaluateBody : Env → Term → Outcome)
    (earlierRows suffix : List CaseRow) (arguments : List Term) (row : CaseRow) (environment : Env)
    (selected : selectCase earlierRows arguments = some (row, environment))
    (failed : evaluateBody environment row.equation.body = .failure) :
    dispatchCaseWith evaluateBody (earlierRows ++ suffix) arguments = .failure :=
  (dispatchCaseWith_commit evaluateBody earlierRows suffix arguments row environment selected).trans failed

theorem selected_exhaustion_does_not_fall_through (evaluateBody : Env → Term → Outcome)
    (earlierRows suffix : List CaseRow) (arguments : List Term) (row : CaseRow) (environment : Env)
    (selected : selectCase earlierRows arguments = some (row, environment))
    (exhausted : evaluateBody environment row.equation.body = .exhausted) :
    dispatchCaseWith evaluateBody (earlierRows ++ suffix) arguments = .exhausted :=
  (dispatchCaseWith_commit evaluateBody earlierRows suffix arguments row environment selected).trans exhausted

/-- For a declared head, vector dispatch agrees with the full source call,
including wrong arity, no match, body failure and body exhaustion. -/
theorem compileHead_dispatch_eq (program : Program) (host : Host)
    (evaluateBody : Env → Term → Outcome) (head : String) (arguments : List Term)
    (declared : program.defines head = true) :
    dispatchCaseWith evaluateBody (compileHead program head) arguments =
      applyWith program host evaluateBody head arguments := by
  cases arity : program.definesAt head arguments.length with
  | false =>
      simp [dispatchCaseWith, compiled_missing_arity program head arguments arity,
        applyWith, arity, declared]
  | true =>
      have sourceSelection := selectCase_compileHead program head arguments
      cases selected : selectCase (compileHead program head) arguments with
      | none =>
          have sourceNone : program.select head arguments = none := by
            simpa only [selected, forgetIndex, Option.map_none] using sourceSelection.symm
          simp only [dispatchCaseWith, selected, applyWith, arity, if_true, sourceNone]
      | some hit =>
          rcases hit with ⟨row, environment⟩
          have sourceSome : program.select head arguments = some (row.equation, environment) := by
            simpa only [selected, forgetIndex, Option.map_some] using sourceSelection.symm
          simp only [dispatchCaseWith, selected, applyWith, arity, if_true, sourceSome]

end Mettapedia.GSLT.LanguageDef.DeterministicEquations.OrderedDispatch
