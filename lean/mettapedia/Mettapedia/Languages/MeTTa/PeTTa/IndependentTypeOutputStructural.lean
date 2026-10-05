import Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutputAdmission

/-!
# Independent structural type fields

An intrinsic structural field uses its own requirement and allocation
subtree. Its actual recursive query and matcher cannot change caller terms,
other row fields or answers allocated by another field. These frame laws
supply the independence needed to compare sequential bound traversal with
the ordered fresh Cartesian product.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Structural

open Mettapedia.Logic.LP
open IntrinsicTypeFacts (signature TypeTerm Declaration)
open Admission

/-- Matching one returned intrinsic type leaves every term outside that
query's output and allocation namespace unchanged. The statement uses the
actual recursive service and actual total matcher. -/
theorem query_match_preserves_external_term (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (output : Nat) (answers : List TypeTerm)
    (returned : run library freshSupply fuel path subject (some (.var output)) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var output)] = some refinement)
    (term : TypeTerm) (outputAbsent : output ∉ term.freeVars)
    (allocatedAbsent : ∀ stem slot, freshSupply (stem ++ path) slot ∉ term.freeVars) :
    refinement.applyTerm term = term := by
  apply Subst.applyTerm_eq_self
  intro name occurs
  apply (unifyTotal_relevantIdempotent _ _ accepted).fixes
  have different : name ≠ output := fun same => outputAbsent (same ▸ occurs)
  have notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ name := by
    intro stem slot same
    exact allocatedAbsent stem slot (same ▸ occurs)
  have candidateAbsent := run_output_excludes_name library fuel path subject (some (.var output))
    answers name notAllocated (by simpa [Term.freeVars] using different) returned candidate present
  simpa only [eqVars, Term.freeVars, Finset.union_empty, Finset.mem_union,
    Finset.mem_singleton, not_or] using And.intro candidateAbsent different

/-- A completed variable-required query cannot return a cyclic requirement,
so matching each of its answers back to the field always succeeds. -/
theorem query_variable_match_succeeds (library : List Declaration) (fuel : Nat)
    (path : Path) (subject : TypeTerm) (output : Nat)
    (notAllocated : ∀ stem slot, freshSupply (stem ++ path) slot ≠ output)
    (answers : List TypeTerm)
    (returned : run library freshSupply fuel path subject (some (.var output)) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) :
    ∃ refinement, unifyTotal [(candidate, .var output)] = some refinement := by
  have solved := run_bound_variable_solved_form library fuel path subject output
    notAllocated answers returned candidate present
  rcases solved with rfl | absent
  · exact ⟨Subst.id signature, by simp [unifyTotal]⟩
  · cases candidate with
    | var name =>
        have different : name ≠ output := by
          simpa only [Term.freeVars, Finset.mem_singleton, ne_eq, eq_comm] using absent
        exact ⟨_, IndependentOutputUnification.variable_output_match name output different⟩
    | const value =>
        exact ⟨_, IndependentOutputUnification.nonvariable_output_match output (.const value)
          (by simp) absent⟩
    | app arity children =>
        exact ⟨_, IndependentOutputUnification.nonvariable_output_match output (.app arity children)
          (by simp) absent⟩

/-- A row-field name is allocated outside every field-query subtree. -/
theorem field_name_ne_child_allocation (path stem : Path) (field position slot : Nat) :
    freshSupply (3 :: path) field ≠ freshSupply (stem ++ 0 :: position :: 4 :: path) slot := by
  intro equal
  have paths := ((fresh_supply_injective _ _ _ _).mp equal).1
  have lengths := congrArg List.length paths
  simp only [List.length_cons, List.length_append] at lengths
  omega

/-- Allocation subtrees of distinct row positions are disjoint, regardless
of recursion depth inside either child. -/
theorem different_fields_allocate_separately (path leftStem rightStem : Path)
    (left right leftSlot rightSlot : Nat) (different : left ≠ right) :
    freshSupply (leftStem ++ 0 :: left :: 4 :: path) leftSlot ≠
      freshSupply (rightStem ++ 0 :: right :: 4 :: path) rightSlot := by
  intro equal
  have paths := ((fresh_supply_injective _ _ _ _).mp equal).1
  have reversed := congrArg List.reverse paths
  simp only [List.reverse_append, List.reverse_cons] at reversed
  have tails : [4, left, 0] ++ leftStem.reverse = [4, right, 0] ++ rightStem.reverse := by
    apply List.append_cancel_left (as := path.reverse)
    simpa only [List.append_assoc, List.singleton_append, List.cons_append, List.nil_append] using reversed
  simp only [List.cons_append, List.nil_append, List.cons.injEq, true_and] at tails
  exact different tails.1

/-- Actual field matching preserves every different row-field variable. -/
theorem field_match_preserves_other_field (library : List Declaration) (fuel : Nat)
    (path : Path) (position other : Nat) (different : position ≠ other)
    (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement) :
    refinement (freshSupply (3 :: path) other) = .var (freshSupply (3 :: path) other) := by
  apply query_match_preserves_external_term library fuel (0 :: position :: 4 :: path)
    subject (freshSupply (3 :: path) position) answers returned candidate present refinement accepted
    (.var (freshSupply (3 :: path) other))
  · simpa only [Term.freeVars, Finset.mem_singleton, fresh_supply_injective, true_and] using different
  · intro stem slot
    simpa only [Term.freeVars, Finset.mem_singleton] using
      Ne.symm (field_name_ne_child_allocation path stem other position slot)

/-- A field's refinement cannot alter an already returned answer of another
field. This includes shared variables inside that earlier answer. -/
theorem field_match_preserves_sibling_answer (library : List Declaration) (fuel siblingFuel : Nat)
    (path : Path) (position sibling : Nat) (different : position ≠ sibling)
    (subject siblingSubject : TypeTerm) (answers siblingAnswers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) = some answers)
    (siblingReturned : run library freshSupply siblingFuel (0 :: sibling :: 4 :: path) siblingSubject
      (some (.var (freshSupply (3 :: path) sibling))) = some siblingAnswers)
    (candidate previous : TypeTerm) (present : candidate ∈ answers) (previousPresent : previous ∈ siblingAnswers)
    (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement) :
    refinement.applyTerm previous = previous := by
  apply query_match_preserves_external_term library fuel (0 :: position :: 4 :: path)
    subject (freshSupply (3 :: path) position) answers returned candidate present refinement accepted previous
  · apply run_output_excludes_name library siblingFuel (0 :: sibling :: 4 :: path)
      siblingSubject (some (.var (freshSupply (3 :: path) sibling))) siblingAnswers
      (freshSupply (3 :: path) position) _ _ siblingReturned previous previousPresent
    · intro stem slot
      exact Ne.symm (field_name_ne_child_allocation path stem position sibling slot)
    · simpa only [Option.toList_some, List.mem_singleton, forall_eq, Term.freeVars,
        Finset.mem_singleton, fresh_supply_injective, true_and] using different
  · intro stem slot
    apply run_output_excludes_name library siblingFuel (0 :: sibling :: 4 :: path)
      siblingSubject (some (.var (freshSupply (3 :: path) sibling))) siblingAnswers
      (freshSupply (stem ++ 0 :: position :: 4 :: path) slot) _ _
      siblingReturned previous previousPresent
    · intro more otherSlot
      exact Ne.symm (different_fields_allocate_separately path stem more position sibling
        slot otherSlot different)
    · simpa only [Option.toList_some, List.mem_singleton, forall_eq, Term.freeVars,
        Finset.mem_singleton] using
        Ne.symm (field_name_ne_child_allocation path stem sibling position slot)

/-- Names belonging to one independent structural field. -/
def FieldName (path : Path) (position name : Nat) : Prop :=
  name = freshSupply (3 :: path) position ∨
    ∃ stem slot, name = freshSupply (stem ++ 0 :: position :: 4 :: path) slot

/-- Every name in a completed field answer belongs to that field. -/
theorem field_answer_names (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) = some answers)
    (answer : TypeTerm) (present : answer ∈ answers) :
    ∀ name ∈ answer.freeVars, FieldName path position name := by
  intro name occurs
  by_contra outside
  have notField : name ≠ freshSupply (3 :: path) position :=
    fun equal => outside (Or.inl equal)
  have notAllocated : ∀ stem slot,
      freshSupply (stem ++ 0 :: position :: 4 :: path) slot ≠ name :=
    fun stem slot equal => outside (Or.inr ⟨stem, slot, equal.symm⟩)
  exact run_output_excludes_name library fuel (0 :: position :: 4 :: path) subject
    (some (.var (freshSupply (3 :: path) position))) answers name notAllocated
    (by simpa [Term.freeVars] using notField) returned answer present occurs

/-- Fields have separate supports even when a field's result remains an
unconstrained alias rather than a proper type. -/
theorem field_names_disjoint (path : Path) (left right name : Nat) (different : left ≠ right)
    (inLeft : FieldName path left name) : ¬ FieldName path right name := by
  intro inRight
  rcases inLeft with leftField | ⟨leftStem, leftSlot, leftAllocated⟩
  · rcases inRight with rightField | ⟨rightStem, rightSlot, rightAllocated⟩
    · have equal := leftField.symm.trans rightField
      exact different ((fresh_supply_injective _ _ _ _).mp equal).2
    · exact field_name_ne_child_allocation path rightStem left right rightSlot
        (leftField.symm.trans rightAllocated)
  · rcases inRight with rightField | ⟨rightStem, rightSlot, rightAllocated⟩
    · exact field_name_ne_child_allocation path leftStem right left leftSlot
        (rightField.symm.trans leftAllocated)
    · exact different_fields_allocate_separately path leftStem rightStem left right
        leftSlot rightSlot different (leftAllocated.symm.trans rightAllocated)

/-- A successful field matcher fixes any term whose names belong to a
different field. It does not require a second evaluator invocation as a
hypothesis. -/
theorem field_match_preserves_other_support (library : List Declaration) (fuel : Nat)
    (path : Path) (position other : Nat) (different : position ≠ other)
    (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement)
    (term : TypeTerm) (supported : ∀ name ∈ term.freeVars, FieldName path other name) :
    refinement.applyTerm term = term := by
  apply query_match_preserves_external_term library fuel (0 :: position :: 4 :: path)
    subject (freshSupply (3 :: path) position) answers returned candidate present refinement accepted term
  · intro occurs
    exact field_names_disjoint path position other _ different (Or.inl rfl) (supported _ occurs)
  · intro stem slot occurs
    exact field_names_disjoint path position other _ different (Or.inr ⟨stem, slot, rfl⟩)
      (supported _ occurs)

/-- Terms outside all current and later field namespaces. Source terms
and caller observations satisfy this admission; the row template need not. -/
def FieldsApart (path : Path) (position : Nat) (term : TypeTerm) : Prop :=
  ∀ later, position ≤ later → ∀ name ∈ term.freeVars, ¬ FieldName path later name

theorem FieldsApart.later {path : Path} {position later : Nat} {term : TypeTerm}
    (apart : FieldsApart path position term) (after : position ≤ later) :
    FieldsApart path later term := fun next follows => apart next (after.trans follows)

private theorem match_preserves_apart (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement)
    (term : TypeTerm) (apart : FieldsApart path position term) :
    refinement.applyTerm term = term := by
  apply query_match_preserves_external_term library fuel (0 :: position :: 4 :: path)
    subject (freshSupply (3 :: path) position) answers returned candidate present refinement accepted term
  · intro occurs
    exact apart position (Nat.le_refl _) _ occurs (Or.inl rfl)
  · intro stem slot occurs
    exact apart position (Nat.le_refl _) _ occurs (Or.inr ⟨stem, slot, rfl⟩)

/-- The field requirements in source position order. -/
def fieldVariables (path : Path) (position : Nat) : Nat → List TypeTerm
  | 0 => []
  | count + 1 => .var (freshSupply (3 :: path) position) :: fieldVariables path (position + 1) count

/-- One branch of field constraints, retaining shared names inside each
candidate and keeping the original position order. -/
def fieldEquations (path : Path) (position : Nat) : List TypeTerm → List (TypeTerm × TypeTerm)
  | [] => []
  | candidate :: rest => (candidate, .var (freshSupply (3 :: path) position)) ::
      fieldEquations path (position + 1) rest

/-- Independent field alternatives. The source variable case commits
without invoking the recursive service, just as bound structural traversal. -/
def fieldAnswers (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (subject : TypeTerm) : Result :=
  if isVariable subject then some [.var (freshSupply (3 :: path) position)]
  else run library freshSupply fuel (0 :: position :: 4 :: path) subject
    (some (.var (freshSupply (3 :: path) position)))

/-- Ordered independent products of bound field answers. No substitution
from one field is passed into another field's query. -/
def fieldRows (library : List Declaration) (fuel : Nat) (path : Path) (position : Nat) :
    List TypeTerm → Option (List (List TypeTerm))
  | [] => some [[]]
  | subject :: rest => do
      let first ← fieldAnswers library fuel path position subject
      collect first fun candidate =>
        (fieldRows library fuel path (position + 1) rest).map (List.map (candidate :: ·))

private def SupportedRow (path : Path) (position : Nat) : List TypeTerm → Prop
  | [] => True
  | candidate :: rest => (∀ name ∈ candidate.freeVars, FieldName path position name) ∧
      SupportedRow path (position + 1) rest

private theorem field_answers_supported (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers) :
    ∀ candidate ∈ answers, ∀ name ∈ candidate.freeVars, FieldName path position name := by
  unfold fieldAnswers at returned
  split at returned
  · simp only [Option.some.injEq] at returned
    subst answers
    intro candidate present name occurs
    simp only [List.mem_singleton] at present
    subst candidate
    exact Or.inl ((Term.mem_freeVars_var (σ := signature)).mp occurs)
  · exact field_answer_names library fuel path position subject answers returned

private theorem field_rows_supported (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (items : List TypeTerm) (rows : List (List TypeTerm))
    (returned : fieldRows library fuel path position items = some rows) :
    ∀ row ∈ rows, SupportedRow path position row := by
  induction items generalizing position rows with
  | nil => simp [fieldRows] at returned; subst rows; simp [SupportedRow]
  | cons subject rest ih =>
      obtain ⟨first, firstRun, product⟩ := Option.bind_eq_some_iff.mp returned
      intro row present
      obtain ⟨candidate, member, values, branch, inBranch⟩ :=
        collect_member first _ rows product present
      cases laterRun : fieldRows library fuel path (position + 1) rest with
      | none => simp [laterRun] at branch
      | some later =>
          simp only [laterRun, Option.map_some, Option.some.injEq] at branch
          subst values
          obtain ⟨tail, inTail, rfl⟩ := List.mem_map.mp inBranch
          exact ⟨field_answers_supported library fuel path position subject first firstRun candidate member,
            ih (position + 1) later laterRun tail inTail⟩

private theorem field_equations_fixed (library : List Declaration) (fuel : Nat)
    (path : Path) (position later : Nat) (after : position < later)
    (subject : TypeTerm) (answers : List TypeTerm)
    (returned : run library freshSupply fuel (0 :: position :: 4 :: path) subject
      (some (.var (freshSupply (3 :: path) position))) = some answers)
    (candidate : TypeTerm) (present : candidate ∈ answers) (refinement : Subst signature)
    (accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] = some refinement)
    (row : List TypeTerm) (supported : SupportedRow path later row) :
    refinement.applyEqs (fieldEquations path later row) = fieldEquations path later row := by
  induction row generalizing later with
  | nil => rfl
  | cons value rest ih =>
      have distinct := Nat.ne_of_lt after
      have valueFixed := field_match_preserves_other_support library fuel path position later distinct
        subject answers returned candidate present refinement accepted value supported.1
      have fieldFixed := field_match_preserves_other_field library fuel path position later distinct
        subject answers returned candidate present refinement accepted
      simp only [fieldEquations, Subst.applyEqs, List.map_cons]
      rw [valueFixed, show refinement.applyTerm (.var (freshSupply (3 :: path) later)) =
        .var (freshSupply (3 :: path) later) from fieldFixed]
      congr 1
      exact ih (later + 1) (by omega) supported.2

private theorem field_variable_member (path : Path) (position count : Nat) (term : TypeTerm)
    (present : term ∈ fieldVariables path position count) :
    ∃ index, position ≤ index ∧ term = .var (freshSupply (3 :: path) index) := by
  induction count generalizing position with
  | zero => simp [fieldVariables] at present
  | succ count ih =>
      rcases List.mem_cons.mp present with rfl | later
      · exact ⟨position, Nat.le_refl _, rfl⟩
      · obtain ⟨index, after, same⟩ := ih (position + 1) later
        exact ⟨index, by omega, same⟩

/-- Sequential bound traversal and independent Cartesian field queries
publish the same ordered constraint families. All queries and matchers are
executed by the original model; source and observer noncapture are the
only namespace admission. The template may itself share field variables. -/
theorem arguments_independent_product (library : List Declaration) (fuel : Nat)
    (path : Path) (position : Nat) (items : List TypeTerm) (result : TypeTerm)
    (output : Nat) (observations : List TypeTerm)
    (sourceApart : ∀ item ∈ items, FieldsApart path position item)
    (outputApart : FieldsApart path position (.var output))
    (observationsApart : ∀ term ∈ observations, FieldsApart path position term) :
    (Resolution.argumentsResolved (run library freshSupply fuel) (4 :: path) position
      (items.zip (fieldVariables path position items.length)) result).map
      (List.map fun answer =>
        IndependentOutputUnification.solutions [(answer, .var output)] observations) =
    (fieldRows library fuel path position items).map
      (List.map fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path position candidates ++ [(result, .var output)]) observations) := by
  induction items generalizing position result with
  | nil => simp [fieldVariables, Resolution.argumentsResolved, fieldRows, fieldEquations]
  | cons subject rest ih =>
      have restApart : ∀ item ∈ rest, FieldsApart path (position + 1) item := by
        intro item member
        exact (sourceApart item (List.mem_cons_of_mem _ member)).later (by omega)
      have outputLater := outputApart.later (show position ≤ position + 1 by omega)
      have observationsLater : ∀ term ∈ observations, FieldsApart path (position + 1) term :=
        fun term member => (observationsApart term member).later (by omega)
      simp only [List.length_cons, fieldVariables, List.zip_cons_cons,
        Resolution.argumentsResolved, fieldRows, fieldAnswers]
      by_cases rootVariable : isVariable subject = true
      · simp only [rootVariable, ↓reduceIte]
        rw [ih (position + 1) result restApart outputLater observationsLater]
        cases later : fieldRows library fuel path (position + 1) rest with
        | none => rfl
        | some rows =>
            simp only [collect, bind, Option.bind, Option.map_some, Option.pure_def, List.append_nil,
              List.map_map, Option.some.injEq]
            apply List.map_congr_left
            intro row _
            exact (IndependentOutputUnification.solutions_reflexive_equation _ _ _).symm
      · simp only [rootVariable, Bool.false_eq_true, ↓reduceIte]
        cases got : run library freshSupply fuel (0 :: position :: 4 :: path) subject
            (some (.var (freshSupply (3 :: path) position))) with
        | none => rfl
        | some first =>
            dsimp only [bind, Option.bind]
            simp only [← Coordinates.collect_results]
            apply Coordinates.collect_congr
            intro candidate member
            cases accepted : unifyTotal [(candidate, .var (freshSupply (3 :: path) position))] with
            | none =>
                obtain ⟨refinement, success⟩ := query_variable_match_succeeds library fuel
                  (0 :: position :: 4 :: path) subject (freshSupply (3 :: path) position)
                  (fun stem slot => Ne.symm
                    (field_name_ne_child_allocation path stem position position slot)) first got candidate member
                rw [accepted] at success
                cases success
            | some refinement =>
                dsimp only
                have pendingFixed :
                    (rest.zip (fieldVariables path (position + 1) rest.length)).map
                      (fun pair => (refinement.applyTerm pair.1, refinement.applyTerm pair.2)) =
                    rest.zip (fieldVariables path (position + 1) rest.length) := by
                  conv_rhs => rw [← List.map_id (rest.zip (fieldVariables path (position + 1) rest.length))]
                  apply List.map_congr_left
                  intro pair present
                  obtain ⟨inSource, inFields⟩ := List.of_mem_zip present
                  have sourceFixed := match_preserves_apart library fuel path position subject first got
                    candidate member refinement accepted pair.1
                    (sourceApart pair.1 (List.mem_cons_of_mem _ inSource))
                  obtain ⟨index, after, same⟩ := field_variable_member path (position + 1) rest.length
                    pair.2 inFields
                  have fieldFixed : refinement.applyTerm pair.2 = pair.2 := by
                    rw [same]
                    exact field_match_preserves_other_field library fuel path position index
                      (by omega) subject first got candidate member refinement accepted
                  exact Prod.ext sourceFixed fieldFixed
                rw [pendingFixed, ih (position + 1) (refinement.applyTerm result)
                  restApart outputLater observationsLater]
                cases later : fieldRows library fuel path (position + 1) rest with
                | none => rfl
                | some rows =>
                    simp only [Option.map_some, List.map_map, Option.some.injEq]
                    apply List.map_congr_left
                    intro row present
                    have rowsFixed := field_equations_fixed library fuel path position (position + 1)
                      (by omega) subject first got candidate member refinement accepted row
                      (field_rows_supported library fuel path (position + 1) rest rows later row present)
                    have outputFixed := match_preserves_apart library fuel path position subject first got
                      candidate member refinement accepted (.var output) outputApart
                    have observationsFixed : observations.map refinement.applyTerm = observations := by
                      conv_rhs => rw [← List.map_id observations]
                      apply List.map_congr_left
                      intro term inObservations
                      exact match_preserves_apart library fuel path position subject first got
                        candidate member refinement accepted term (observationsApart term inObservations)
                    have contextFixed : refinement.applyEqs
                        (fieldEquations path (position + 1) row ++ [(result, .var output)]) =
                        fieldEquations path (position + 1) row ++ [(refinement.applyTerm result, .var output)] := by
                      simp only [Subst.applyEqs, List.map_append, List.map_cons, List.map_nil]
                      change refinement.applyEqs (fieldEquations path (position + 1) row) ++
                        [(refinement.applyTerm result, refinement.applyTerm (.var output))] = _
                      rw [rowsFixed, outputFixed]
                    have publication := IndependentOutputUnification.solutions_after_unifyTotal
                      [(candidate, .var (freshSupply (3 :: path) position))]
                      (fieldEquations path (position + 1) row ++ [(result, .var output)])
                      refinement accepted observations
                    rw [contextFixed, observationsFixed] at publication
                    exact publication.symm

private theorem field_variables_range (path : Path) (position count : Nat) :
    fieldVariables path position count =
      (List.range' position count).map (fun index => .var (freshSupply (3 :: path) index)) := by
  induction count generalizing position with
  | zero => rfl
  | succ count ih => simp only [fieldVariables, List.range'_succ, List.map_cons, ih]

/-- The original bound structural branch is an independent ordered product
of its recursive field queries, observed through their joint constraints.
This accounts for the initial output match as well as every later match. -/
theorem structural_independent_product (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat) (observations : List TypeTerm)
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (sourceApart : ∀ item ∈ items, FieldsApart path 0 item)
    (outputApart : FieldsApart path 0 (.var output))
    (observationsApart : ∀ term ∈ observations, FieldsApart path 0 term) :
    (structural freshSupply (run library freshSupply fuel) path items (some (.var output))).map
      (List.map fun answer =>
        IndependentOutputUnification.solutions [(answer, .var output)] observations) =
    (fieldRows library fuel path 0 items).map
      (List.map fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path 0 candidates ++
          [(row (fieldVariables path 0 items.length), .var output)]) observations) := by
  let fields := fieldVariables path 0 items.length
  have actualFields : (List.range items.length).map
      (fun index => (Term.var (freshSupply (3 :: path) index) : TypeTerm)) = fields := by
    simpa only [List.range'_eq_map_range, List.map_map, Function.comp_def, Nat.zero_add, fields] using
      (field_variables_range path 0 items.length).symm
  have fieldsAbsent : ∀ field ∈ fields, output ∉ field.freeVars := by
    intro field member occurs
    obtain ⟨index, _, rfl⟩ := field_variable_member path 0 items.length field member
    have equal := (Term.mem_freeVars_var (σ := signature)).mp occurs
    exact outputApart index (Nat.zero_le _) output (by simp [Term.freeVars]) (Or.inl equal)
  have resultAbsent : output ∉ (row fields).freeVars := by
    intro occurs
    obtain ⟨index, occurs⟩ := (Term.mem_freeVars_app (σ := signature)).mp occurs
    exact fieldsAbsent fields[index] (List.getElem_mem _) occurs
  have pendingAbsent : ∀ pair ∈ items.zip fields,
      output ∉ pair.1.freeVars ∧ output ∉ pair.2.freeVars := by
    intro pair member
    have present := List.of_mem_zip member
    exact ⟨independent pair.1 present.1, fieldsAbsent pair.2 present.2⟩
  have proper : ∀ name, row fields ≠ .var name := by intro name same; cases same
  have matching := IndependentOutputUnification.nonvariable_output_match output (row fields)
    proper resultAbsent
  have same := nonvariable_codomain_arguments (run library freshSupply fuel) (4 :: path) 0
    (items.zip fields) (row fields) output proper pendingAbsent resultAbsent
  rw [matching] at same
  simp only [Option.bind_some] at same
  simp only [structural, actualFields, matching]
  rw [same, Resolution.arguments_id]
  exact arguments_independent_product library fuel path 0 items (row fields) output observations
    sourceApart outputApart observationsApart

/-- The caller namespace discharges structural noncapture without
renaming any observable caller variable. -/
theorem caller_term_fields_apart (path : Path) (position : Nat) (term : TypeTerm)
    (callerNames : ∀ name ∈ term.freeVars, ∃ slot, name = callerName slot) :
    FieldsApart path position term := by
  intro later _ name occurs member
  obtain ⟨caller, rfl⟩ := callerNames name occurs
  rcases member with field | ⟨stem, slot, allocated⟩
  · exact fresh_supply_separate _ _ caller field.symm
  · exact fresh_supply_separate _ _ caller allocated.symm

private theorem row_substitute (refinement : Subst signature) (items : List TypeTerm) :
    refinement.applyTerm (row items) = row (items.map refinement.applyTerm) := by
  simp only [row, Subst.applyTerm, Term.app.injEq, List.length_map, true_and]
  apply (Fin.heq_fun_iff (List.length_map refinement.applyTerm).symm).mpr
  intro index
  simp

private theorem single_fixes_absent (name : Nat) (value term : TypeTerm)
    (absent : name ∉ term.freeVars) : (Subst.single name value).applyTerm term = term := by
  apply Subst.applyTerm_eq_self
  intro other occurs
  exact Subst.single_ne value (fun same => absent (same ▸ occurs))

private theorem single_field_fixes_later_equations (path : Path) (position later : Nat)
    (after : position < later) (value : TypeTerm) (candidates : List TypeTerm)
    (absent : ∀ candidate ∈ candidates, freshSupply (3 :: path) position ∉ candidate.freeVars) :
    (Subst.single (freshSupply (3 :: path) position) value).applyEqs
      (fieldEquations path later candidates) = fieldEquations path later candidates := by
  induction candidates generalizing later with
  | nil => rfl
  | cons candidate rest ih =>
      have different : freshSupply (3 :: path) later ≠ freshSupply (3 :: path) position := by
        intro same
        have equal := ((fresh_supply_injective _ _ _ _).mp same).2
        omega
      simp only [fieldEquations, Subst.applyEqs, List.map_cons]
      rw [single_fixes_absent _ _ candidate (absent candidate List.mem_cons_self)]
      rw [Subst.applyTerm_var, Subst.single_ne value different]
      congr 1
      exact ih (later + 1) (by omega)
        (fun term member => absent term (List.mem_cons_of_mem _ member))

private theorem single_field_fixes_later_variables (path : Path) (position later count : Nat)
    (after : position < later) (value : TypeTerm) :
    (fieldVariables path later count).map
      (Subst.single (freshSupply (3 :: path) position) value).applyTerm =
        fieldVariables path later count := by
  conv_rhs => rw [← List.map_id (fieldVariables path later count)]
  apply List.map_congr_left
  intro term present
  obtain ⟨index, following, rfl⟩ := field_variable_member path later count term present
  apply Subst.single_ne
  intro same
  have equal := ((fresh_supply_injective _ _ _ _).mp same).2
  omega

/-- Eliminating freshly allocated field requirements reconstructs the
whole row while preserving sharing inside and between its candidate types.
The proof compares joint solution families, not independent marginals. -/
theorem eliminate_field_equations (path : Path) (position : Nat)
    (candidates initialFields : List TypeTerm) (output : Nat) (observations : List TypeTerm)
    (fresh : ∀ index, position ≤ index → ∀ term ∈ initialFields ++ candidates ++ observations ++ [.var output],
      freshSupply (3 :: path) index ∉ term.freeVars) :
    IndependentOutputUnification.solutions
      (fieldEquations path position candidates ++
        [(row (initialFields ++ fieldVariables path position candidates.length), .var output)]) observations =
    IndependentOutputUnification.solutions [(row (initialFields ++ candidates), .var output)] observations := by
  induction candidates generalizing position initialFields with
  | nil => simp [fieldEquations, fieldVariables]
  | cons candidate rest ih =>
      let field := freshSupply (3 :: path) position
      let refinement := Subst.single field candidate
      have candidateAbsent : field ∉ candidate.freeVars :=
        fresh position (Nat.le_refl _) candidate (by simp)
      have observationAbsent : ∀ term ∈ observations, field ∉ term.freeVars := by
        intro term member
        exact fresh position (Nat.le_refl _) term (by simp [member])
      have outputAbsent : field ∉ (Term.var output : TypeTerm).freeVars :=
        fresh position (Nat.le_refl _) (.var output) (by simp)
      have initialFieldsFixed : initialFields.map refinement.applyTerm = initialFields := by
        conv_rhs => rw [← List.map_id initialFields]
        apply List.map_congr_left
        intro term member
        exact single_fixes_absent field candidate term
          (fresh position (Nat.le_refl _) term (by simp [member]))
      have restFixed := single_field_fixes_later_equations path position (position + 1)
        (by omega) candidate rest
        (fun term member => fresh position (Nat.le_refl _) term (by simp [member]))
      have fieldsFixed := single_field_fixes_later_variables path position (position + 1) rest.length
        (by omega) candidate
      have outputFixed := single_fixes_absent field candidate (.var output) outputAbsent
      have nextFresh : ∀ index, position + 1 ≤ index →
          ∀ term ∈ (initialFields ++ [candidate]) ++ rest ++ observations ++ [.var output],
          freshSupply (3 :: path) index ∉ term.freeVars := by
        intro index after term member
        exact fresh index (by omega) term (by simpa [List.append_assoc] using member)
      simp only [fieldEquations, List.cons_append, List.length_cons, fieldVariables]
      rw [IndependentOutputUnification.solutions_eliminate_fresh field candidate _ observations
        candidateAbsent observationAbsent]
      have templateFixed : refinement.applyTerm
          (row (initialFields ++ .var field :: fieldVariables path (position + 1) rest.length)) =
          row ((initialFields ++ [candidate]) ++ fieldVariables path (position + 1) rest.length) := by
        rw [row_substitute]
        simp only [List.map_append, List.map_cons, Subst.applyTerm_var, initialFieldsFixed]
        simp only [refinement, field, Subst.single_eq, fieldsFixed,
          List.append_assoc, List.singleton_append]
      have contextFixed : refinement.applyEqs
          (fieldEquations path (position + 1) rest ++
            [(row (initialFields ++ .var field :: fieldVariables path (position + 1) rest.length), .var output)]) =
          fieldEquations path (position + 1) rest ++
            [(row ((initialFields ++ [candidate]) ++ fieldVariables path (position + 1) rest.length), .var output)] := by
        simp only [Subst.applyEqs, List.map_append, List.map_cons, List.map_nil]
        change refinement.applyEqs (fieldEquations path (position + 1) rest) ++
          [(refinement.applyTerm (row (initialFields ++ .var field :: fieldVariables path (position + 1) rest.length)),
            refinement.applyTerm (.var output))] = _
        rw [restFixed, templateFixed, outputFixed]
      rw [contextFixed, ih (position + 1) (initialFields ++ [candidate]) nextFresh]
      simp only [List.append_assoc, List.singleton_append]

private theorem fresh_rows_shape (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (rows : List (List TypeTerm))
    (returned : freshRows (run library freshSupply fuel) (4 :: path) position items = some rows) :
    ∀ candidate ∈ rows, candidate.length = items.length ∧
      ∀ term ∈ candidate, ∀ field, freshSupply (3 :: path) field ∉ term.freeVars := by
  induction items generalizing position rows with
  | nil => simp [freshRows] at returned; subst rows; simp
  | cons subject rest ih =>
      obtain ⟨first, firstRun, restRun⟩ := Option.bind_eq_some_iff.mp returned
      obtain ⟨later, laterRun, product⟩ := Option.bind_eq_some_iff.mp restRun
      have equal : first.flatMap (fun answer => later.map (answer :: ·)) = rows := Option.some.inj product
      subst rows
      intro candidate member
      obtain ⟨head, inFirst, member⟩ := List.mem_flatMap.mp member
      obtain ⟨tail, inLater, rfl⟩ := List.mem_map.mp member
      have tailShape := ih (position + 1) later laterRun tail inLater
      constructor
      · simpa only [List.length_cons] using congrArg (· + 1) tailShape.1
      · intro term member field
        rcases List.mem_cons.mp member with rfl | fromTail
        · exact run_output_excludes_name library fuel (0 :: position :: 4 :: path) subject
            none first (freshSupply (3 :: path) field)
            (fun stem slot => Ne.symm (field_name_ne_child_allocation path stem field position slot))
            (by simp) firstRun term inFirst
        · exact tailShape.2 term fromTail field

/-- Fresh structural inference admits the same field-equation presentation
as bound traversal. Fresh allocation makes elimination exact, with one
constraint family per original Cartesian-product occurrence. -/
theorem fresh_structural_constraint_publication (library : List Declaration) (fuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat) (observations : List TypeTerm)
    (outputApart : FieldsApart path 0 (.var output))
    (observationsApart : ∀ term ∈ observations, FieldsApart path 0 term) :
    (structural freshSupply (run library freshSupply fuel) path items none).map
      (List.map fun answer =>
        IndependentOutputUnification.solutions [(answer, .var output)] observations) =
    (freshRows (run library freshSupply fuel) (4 :: path) 0 items).map
      (List.map fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path 0 candidates ++
          [(row (fieldVariables path 0 items.length), .var output)]) observations) := by
  simp only [structural]
  cases returned : freshRows (run library freshSupply fuel) (4 :: path) 0 items with
  | none => rfl
  | some rows =>
      simp only [Option.map_some, List.map_map, Option.some.injEq]
      apply List.map_congr_left
      intro candidates member
      have shape := fresh_rows_shape library fuel path 0 items rows returned candidates member
      rw [← shape.1]
      symm
      apply eliminate_field_equations path 0 candidates [] output observations
      intro index _ term present
      simp only [List.nil_append, List.mem_append, List.mem_singleton] at present
      rcases present with (fromCandidate | fromObservation) | rfl
      · exact shape.2 term fromCandidate index
      · intro occurs
        exact observationsApart term fromObservation index (Nat.zero_le _) _ occurs (Or.inl rfl)
      · intro occurs
        exact outputApart index (Nat.zero_le _) _ occurs (Or.inl rfl)

private theorem collect_product_nonempty {α β γ : Type} (first : List α) (nonempty : first ≠ [])
    (later : Option (List β)) (combine : α → β → γ) :
    collect first (fun item => later.map (List.map (combine item))) =
      later.map (fun rest => first.flatMap (fun item => rest.map (combine item))) := by
  cases later with
  | none => cases first with
    | nil => exact False.elim (nonempty rfl)
    | cons item rest => rfl
  | some rest =>
      induction first with
      | nil => rfl
      | cons item remaining ih =>
          simp only [collect, Option.map_some, bind, Option.bind, Option.pure_def,
            List.flatMap_cons]
          cases remaining with
          | nil => rfl
          | cons next tail =>
              have same := ih (by simp)
              simp only [Option.map_some] at same
              rw [same]

private theorem field_answers_nonempty (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (subject : TypeTerm) (answers : List TypeTerm)
    (returned : fieldAnswers library fuel path position subject = some answers) : answers ≠ [] := by
  unfold fieldAnswers at returned
  split at returned
  · simp only [Option.some.injEq] at returned; subst answers; simp
  · exact run_variable_nonempty library freshSupply fuel (0 :: position :: 4 :: path)
      subject _ answers returned

/-- Bound field traversal is a strict Cartesian product despite using
branch sequencing internally. Nonempty unconstrained child results are
what make both presentations propagate incompleteness in the same way. -/
theorem field_rows_product (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (subject : TypeTerm) (rest : List TypeTerm) :
    fieldRows library fuel path position (subject :: rest) = (do
      let first ← fieldAnswers library fuel path position subject
      let later ← fieldRows library fuel path (position + 1) rest
      pure (first.flatMap fun answer => later.map (answer :: ·))) := by
  rw [fieldRows]
  cases returned : fieldAnswers library fuel path position subject with
  | none => rfl
  | some first =>
      dsimp only [bind, Option.bind]
      rw [collect_product_nonempty first
        (field_answers_nonempty library fuel path position subject first returned)]
      cases fieldRows library fuel path (position + 1) rest <;> rfl

/-- An observation cannot read names allocated inside the query whose
answer it observes. It may contain the independent output and caller names. -/
def AllocationApart (path : Path) (term : TypeTerm) : Prop :=
  ∀ stem slot, freshSupply (stem ++ path) slot ∉ term.freeVars

/-- Two answer schemes expose the same joint refinements to every caller
observation. Their private allocation coordinates need not be identical. -/
def AnswerEquivalent (path : Path) (output : Nat) (left right : TypeTerm) : Prop :=
  ∀ observations, (∀ term ∈ observations, AllocationApart path term) →
    IndependentOutputUnification.solutions [(left, .var output)] observations =
      IndependentOutputUnification.solutions [(right, .var output)] observations

/-- Context terms may mention any parent row field but cannot inspect the
private allocations of the remaining children. -/
def ChildrenApart (path : Path) (position : Nat) (term : TypeTerm) : Prop :=
  ∀ later, position ≤ later → AllocationApart (0 :: later :: 4 :: path) term

theorem ChildrenApart.later {path : Path} {position later : Nat} {term : TypeTerm}
    (apart : ChildrenApart path position term) (after : position ≤ later) :
    ChildrenApart path later term := fun next follows => apart next (after.trans follows)

private theorem field_variable_children_apart (path : Path) (field position : Nat) :
    ChildrenApart path position (.var (freshSupply (3 :: path) field)) := by
  intro later _ stem slot
  simpa only [Term.freeVars, Finset.mem_singleton] using
    Ne.symm (field_name_ne_child_allocation path stem field later slot)

private theorem supported_children_apart (path : Path) (position : Nat) (term : TypeTerm)
    (supported : ∀ name ∈ term.freeVars, FieldName path position name) :
    ChildrenApart path (position + 1) term := by
  intro later after stem slot occurs
  exact field_names_disjoint path position later _ (by omega) (supported _ occurs)
    (Or.inr ⟨stem, slot, rfl⟩)

private theorem later_equations_apart (path : Path) (position later : Nat)
    (after : position < later) (candidates : List TypeTerm)
    (supported : SupportedRow path later candidates) :
    ∀ term ∈ (fieldEquations path later candidates).flatMap (fun pair => [pair.1, pair.2]),
      AllocationApart (0 :: position :: 4 :: path) term := by
  induction candidates generalizing later with
  | nil => simp [fieldEquations]
  | cons candidate rest ih =>
      intro term present
      simp only [fieldEquations, List.flatMap_cons, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false] at present
      rcases present with (rfl | rfl) | fromRest
      · intro stem slot occurs
        exact field_names_disjoint path later position _ (by omega) (supported.1 _ occurs)
          (Or.inr ⟨stem, slot, rfl⟩)
      · exact field_variable_children_apart path later 0 position (Nat.zero_le _)
      · exact ih (later + 1) (by omega) supported.2 term fromRest

/-- Pairing the head alternatives and then the later Cartesian products
preserves the whole ordered joint constraint vector. The observations used
for each replacement include every surrounding equation, not just its
individual field projection. -/
theorem combine_field_products (path : Path) (position : Nat)
    (leftHeads rightHeads : List TypeTerm) (leftRows rightRows : List (List TypeTerm))
    (heads : List.Forall₂ (AnswerEquivalent (0 :: position :: 4 :: path)
      (freshSupply (3 :: path) position)) leftHeads rightHeads)
    (headSupport : ∀ candidate ∈ leftHeads, ∀ name ∈ candidate.freeVars,
      FieldName path position name)
    (rowSupport : ∀ candidates ∈ rightRows, SupportedRow path (position + 1) candidates)
    (tails : ∀ context observations,
      (∀ term ∈ context.flatMap (fun pair => [pair.1, pair.2]) ++ observations,
        ChildrenApart path (position + 1) term) →
      leftRows.map (fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path (position + 1) candidates ++ context) observations) =
      rightRows.map (fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path (position + 1) candidates ++ context) observations))
    (context : List (TypeTerm × TypeTerm)) (observations : List TypeTerm)
    (apart : ∀ term ∈ context.flatMap (fun pair => [pair.1, pair.2]) ++ observations,
      ChildrenApart path position term) :
    (leftHeads.flatMap fun answer => leftRows.map (answer :: ·)).map
      (fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path position candidates ++ context) observations) =
    (rightHeads.flatMap fun answer => rightRows.map (answer :: ·)).map
      (fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path position candidates ++ context) observations) := by
  have one (first second : TypeTerm) (fromLeft : first ∈ leftHeads)
      (equivalent : AnswerEquivalent (0 :: position :: 4 :: path)
        (freshSupply (3 :: path) position) first second) :
      leftRows.map (fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path position (first :: candidates) ++ context) observations) =
      rightRows.map (fun candidates => IndependentOutputUnification.solutions
        (fieldEquations path position (second :: candidates) ++ context) observations) := by
    let equation := (first, (Term.var (freshSupply (3 :: path) position) : TypeTerm))
    have extendedApart : ∀ term ∈ (equation :: context).flatMap
        (fun pair => [pair.1, pair.2]) ++ observations,
        ChildrenApart path (position + 1) term := by
      intro term present
      simp only [List.flatMap_cons, List.cons_append, List.nil_append,
        List.mem_cons] at present
      rcases present with rfl | rfl | original
      · exact supported_children_apart path position _ (headSupport _ fromLeft)
      · exact field_variable_children_apart path position (position + 1)
      · exact (apart term original).later (by omega)
    have tailSame := tails (equation :: context) observations extendedApart
    have rearrange (candidate : TypeTerm) (candidates : List TypeTerm) :
        IndependentOutputUnification.solutions
          (fieldEquations path position (candidate :: candidates) ++ context) observations =
        IndependentOutputUnification.solutions
          (fieldEquations path (position + 1) candidates ++
            (candidate, .var (freshSupply (3 :: path) position)) :: context) observations := by
      apply IndependentOutputUnification.solutions_equations_congr
      intro pair
      simp only [fieldEquations, List.cons_append, List.mem_cons, List.mem_append]
      tauto
    calc
      _ = leftRows.map (fun candidates => IndependentOutputUnification.solutions
            (fieldEquations path (position + 1) candidates ++ equation :: context)
              observations) := List.map_congr_left (fun candidates _ => rearrange first candidates)
      _ = rightRows.map (fun candidates => IndependentOutputUnification.solutions
            (fieldEquations path (position + 1) candidates ++ equation :: context)
              observations) := tailSame
      _ = _ := by
        apply List.map_congr_left
        intro candidates member
        rw [← rearrange first candidates]
        change IndependentOutputUnification.solutions
          ([(first, .var (freshSupply (3 :: path) position))] ++
            (fieldEquations path (position + 1) candidates ++ context)) observations =
          IndependentOutputUnification.solutions
          ([(second, .var (freshSupply (3 :: path) position))] ++
            (fieldEquations path (position + 1) candidates ++ context)) observations
        apply IndependentOutputUnification.solutions_context_congr
        apply equivalent
        intro term present
        simp only [List.flatMap_append, List.append_assoc, List.mem_append] at present
        rcases present with fromFields | fromContext | fromObservations
        · exact later_equations_apart path position (position + 1) (by omega)
            candidates (rowSupport candidates member) term fromFields
        · exact apart term (List.mem_append_left _ fromContext) position (Nat.le_refl _)
        · exact apart term (List.mem_append_right _ fromObservations) position (Nat.le_refl _)
  simp only [List.map_flatMap, List.map_map, Function.comp_def]
  induction heads with
  | nil => rfl
  | @cons first second remainingLeft remainingRight equivalent paired ih =>
      simp only [List.flatMap_cons]
      exact congrArg₂ List.append (one first second List.mem_cons_self equivalent)
        (ih (fun candidate member => headSupport candidate (List.mem_cons_of_mem _ member))
          (fun first second member eqv => one first second (List.mem_cons_of_mem _ member) eqv))

private theorem fresh_rows_supported (library : List Declaration) (fuel : Nat) (path : Path)
    (position : Nat) (items : List TypeTerm) (rows : List (List TypeTerm))
    (returned : freshRows (run library freshSupply fuel) (4 :: path) position items = some rows) :
    ∀ candidates ∈ rows, SupportedRow path position candidates := by
  induction items generalizing position rows with
  | nil => simp [freshRows] at returned; subst rows; simp [SupportedRow]
  | cons subject rest ih =>
      obtain ⟨first, firstRun, remaining⟩ := Option.bind_eq_some_iff.mp returned
      obtain ⟨later, laterRun, product⟩ := Option.bind_eq_some_iff.mp remaining
      have same : first.flatMap (fun head => later.map (head :: ·)) = rows := Option.some.inj product
      subst rows
      intro candidates present
      obtain ⟨head, headPresent, fromTail⟩ := List.mem_flatMap.mp present
      obtain ⟨tail, tailPresent, rfl⟩ := List.mem_map.mp fromTail
      refine ⟨?_, ih (position + 1) later laterRun tail tailPresent⟩
      intro name occurs
      by_contra outside
      have notAllocated : ∀ stem slot, freshSupply (stem ++ 0 :: position :: 4 :: path) slot ≠ name :=
        fun stem slot same => outside (Or.inr ⟨stem, slot, same.symm⟩)
      exact run_output_excludes_name library fuel (0 :: position :: 4 :: path) subject none
        first name notAllocated (by simp) firstRun head headPresent occurs

/-- Whole ordered row products agree under any surrounding equations that
cannot inspect the children’s private allocation names. -/
def RowsEquivalent (path : Path) (position : Nat)
    (left right : List (List TypeTerm)) : Prop :=
  ∀ context observations,
    (∀ term ∈ context.flatMap (fun pair => [pair.1, pair.2]) ++ observations,
      ChildrenApart path position term) →
    left.map (fun candidates => IndependentOutputUnification.solutions
      (fieldEquations path position candidates ++ context) observations) =
    right.map (fun candidates => IndependentOutputUnification.solutions
      (fieldEquations path position candidates ++ context) observations)

/-- Completed bound products transfer to completed fresh products once the
recursive child queries have been related. The supplied child correspondence
is used only on actual strictly nested invocations; variable children can
be handled by the separate fresh-alias law. -/
theorem completed_field_rows_to_fresh (library : List Declaration) (boundFuel freshFuel : Nat)
    (path : Path) (position : Nat) (items : List TypeTerm) (bound : List (List TypeTerm))
    (returned : fieldRows library boundFuel path position items = some bound)
    (children : ∀ later, position ≤ later → ∀ subject ∈ items, ∀ first,
      fieldAnswers library boundFuel path later subject = some first →
      ∃ second, run library freshSupply freshFuel (0 :: later :: 4 :: path) subject none = some second ∧
        List.Forall₂ (AnswerEquivalent (0 :: later :: 4 :: path)
          (freshSupply (3 :: path) later)) first second) :
    ∃ fresh, freshRows (run library freshSupply freshFuel) (4 :: path) position items = some fresh ∧
      RowsEquivalent path position bound fresh := by
  induction items generalizing position bound with
  | nil =>
      simp only [fieldRows, Option.some.injEq] at returned
      subst bound
      exact ⟨[[]], rfl, fun _ _ _ => rfl⟩
  | cons subject rest ih =>
      rw [field_rows_product] at returned
      obtain ⟨first, firstRun, remaining⟩ := Option.bind_eq_some_iff.mp returned
      obtain ⟨later, laterRun, product⟩ := Option.bind_eq_some_iff.mp remaining
      have boundEq : first.flatMap (fun head => later.map (head :: ·)) = bound := Option.some.inj product
      subst bound
      obtain ⟨freshFirst, freshFirstRun, paired⟩ :=
        children position (Nat.le_refl _) subject List.mem_cons_self first firstRun
      obtain ⟨freshLater, freshLaterRun, tails⟩ := ih (position + 1) later laterRun
        (fun next after item member values accepted => children next (by omega) item
          (List.mem_cons_of_mem _ member) values accepted)
      refine ⟨freshFirst.flatMap (fun head => freshLater.map (head :: ·)), ?_, ?_⟩
      · simp only [freshRows, freshFirstRun, freshLaterRun, bind, Option.bind, Option.pure_def]
      · intro context observations apart
        exact combine_field_products path position first freshFirst later freshLater paired
          (field_answers_supported library boundFuel path position subject first firstRun)
          (fresh_rows_supported library freshFuel path (position + 1) rest freshLater freshLaterRun)
          tails context observations apart

/-- Conversely, a completed fresh Cartesian product transfers to the bound
field traversal without losing normal completion, multiplicity or shared
constraints. No uncompleted child is replaced by an empty answer vector. -/
theorem completed_fresh_rows_to_field (library : List Declaration) (boundFuel freshFuel : Nat)
    (path : Path) (position : Nat) (items : List TypeTerm) (fresh : List (List TypeTerm))
    (returned : freshRows (run library freshSupply freshFuel) (4 :: path) position items = some fresh)
    (children : ∀ later, position ≤ later → ∀ subject ∈ items, ∀ second,
      run library freshSupply freshFuel (0 :: later :: 4 :: path) subject none = some second →
      ∃ first, fieldAnswers library boundFuel path later subject = some first ∧
        List.Forall₂ (AnswerEquivalent (0 :: later :: 4 :: path)
          (freshSupply (3 :: path) later)) first second) :
    ∃ bound, fieldRows library boundFuel path position items = some bound ∧
      RowsEquivalent path position bound fresh := by
  induction items generalizing position fresh with
  | nil =>
      simp only [freshRows, Option.some.injEq] at returned
      subst fresh
      exact ⟨[[]], rfl, fun _ _ _ => rfl⟩
  | cons subject rest ih =>
      obtain ⟨freshFirst, freshFirstRun, remaining⟩ := Option.bind_eq_some_iff.mp returned
      obtain ⟨freshLater, freshLaterRun, product⟩ := Option.bind_eq_some_iff.mp remaining
      have freshEq : freshFirst.flatMap (fun head => freshLater.map (head :: ·)) = fresh :=
        Option.some.inj product
      subst fresh
      obtain ⟨first, firstRun, paired⟩ :=
        children position (Nat.le_refl _) subject List.mem_cons_self freshFirst freshFirstRun
      obtain ⟨later, laterRun, tails⟩ := ih (position + 1) freshLater freshLaterRun
        (fun next after item member values accepted => children next (by omega) item
          (List.mem_cons_of_mem _ member) values accepted)
      refine ⟨first.flatMap (fun head => later.map (head :: ·)), ?_, ?_⟩
      · rw [field_rows_product]
        simp only [firstRun, laterRun, bind, Option.bind, Option.pure_def]
      · intro context observations apart
        exact combine_field_products path position first freshFirst later freshLater paired
          (field_answers_supported library boundFuel path position subject first firstRun)
          (fresh_rows_supported library freshFuel path (position + 1) rest freshLater freshLaterRun)
          tails context observations apart

/-- A skipped bound variable field and its fresh private type variable
have the same observable scheme. This is also the case that requires one
additional layer of fuel in the bound-to-fresh direction. -/
theorem fresh_variable_equivalent (path : Path) (output : Nat)
    (independent : freshSupply (5 :: path) 0 ≠ output) :
    AnswerEquivalent path output (.var output) (.var (freshSupply (5 :: path) 0)) := by
  intro observations apart
  have same := IndependentOutputUnification.solved_private_output_publication
    (freshSupply (5 :: path) 0) output independent (.var (freshSupply (5 :: path) 0))
    (Or.inl rfl) (by simpa only [Term.freeVars, Finset.mem_singleton, ne_eq, eq_comm] using independent)
    observations (fun term member => apart term member [5] 0)
  simpa only [UnificationRenaming.rename_var, Equiv.swap_apply_left] using same

theorem AllocationApart.descendant {path : Path} {term : TypeTerm}
    (apart : AllocationApart path term) (stem : Path) : AllocationApart (stem ++ path) term := by
  intro more slot
  simpa only [List.append_assoc] using apart (more ++ stem) slot

theorem AllocationApart.fieldsApart {path : Path} {term : TypeTerm}
    (apart : AllocationApart path term) (position : Nat) : FieldsApart path position term := by
  intro later _ name occurs allocated
  rcases allocated with rfl | ⟨stem, slot, rfl⟩
  · exact apart [3] later occurs
  · exact apart (stem ++ [0, later, 4]) slot (by simpa only [List.append_assoc, List.cons_append, List.nil_append] using occurs)

theorem AllocationApart.childrenApart {path : Path} {term : TypeTerm}
    (apart : AllocationApart path term) (position : Nat) : ChildrenApart path position term :=
  fun later _ => apart.descendant [0, later, 4]

private theorem field_template_children_apart (path : Path) (count position : Nat) :
    ChildrenApart path position (row (fieldVariables path 0 count)) := by
  intro later after stem slot occurs
  obtain ⟨index, occurs⟩ := (Term.mem_freeVars_app (σ := signature)).mp occurs
  obtain ⟨field, _, same⟩ := field_variable_member path 0 count
    (fieldVariables path 0 count)[index] (List.getElem_mem _)
  rw [same] at occurs
  exact field_variable_children_apart path field position later after stem slot occurs

/-- The two original structural branches publish paired complete answers
whenever their independently queried fields do. Caller names, including
shared variables in observations, are fixed throughout the comparison. -/
theorem structural_completed_pairing (library : List Declaration) (boundFuel freshFuel : Nat)
    (path : Path) (items : List TypeTerm) (output : Nat)
    (sourceApart : ∀ item ∈ items, AllocationApart path item)
    (outputApart : AllocationApart path (.var output))
    (independent : ∀ item ∈ items, output ∉ item.freeVars)
    (boundRows freshRowsResult : List (List TypeTerm))
    (boundRun : fieldRows library boundFuel path 0 items = some boundRows)
    (freshRun : freshRows (run library freshSupply freshFuel) (4 :: path) 0 items = some freshRowsResult)
    (paired : RowsEquivalent path 0 boundRows freshRowsResult) :
    ∃ bound fresh,
      structural freshSupply (run library freshSupply boundFuel) path items (some (.var output)) = some bound ∧
      structural freshSupply (run library freshSupply freshFuel) path items none = some fresh ∧
      List.Forall₂ (AnswerEquivalent path output) bound fresh := by
  have boundProjection := structural_independent_product library boundFuel path items output [] independent
    (fun item present => (sourceApart item present).fieldsApart 0)
    (outputApart.fieldsApart 0) (by simp)
  rw [boundRun, Option.map_some] at boundProjection
  cases boundResult : structural freshSupply (run library freshSupply boundFuel) path items
      (some (.var output)) with
  | none => simp [boundResult] at boundProjection
  | some bound =>
      refine ⟨bound, freshRowsResult.map row, rfl, ?_, ?_⟩
      · simp only [structural, freshRun, Option.map_some]
      · apply IndependentOutputUnification.ordered_publication_pairing
          bound (freshRowsResult.map row) output
          (fun observations => ∀ term ∈ observations, AllocationApart path term) (by simp)
        intro observations observationsApart
        have left := structural_independent_product library boundFuel path items output observations independent
          (fun item present => (sourceApart item present).fieldsApart 0)
          (outputApart.fieldsApart 0)
          (fun term present => (observationsApart term present).fieldsApart 0)
        have right := fresh_structural_constraint_publication library freshFuel path items output observations
          (outputApart.fieldsApart 0)
          (fun term present => (observationsApart term present).fieldsApart 0)
        simp only [boundResult, boundRun, Option.map_some, Option.some.injEq] at left
        simp only [structural, freshRun, Option.map_some, Option.some.injEq] at right
        rw [left, right]
        apply paired
        intro term present
        simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.cons_append,
          List.nil_append, List.mem_cons] at present
        rcases present with rfl | rfl | observed
        · exact field_template_children_apart path items.length 0
        · exact outputApart.childrenApart 0
        · exact (observationsApart term observed).childrenApart 0

end Mettapedia.Languages.MeTTa.PeTTa.IndependentTypeOutput.Structural
