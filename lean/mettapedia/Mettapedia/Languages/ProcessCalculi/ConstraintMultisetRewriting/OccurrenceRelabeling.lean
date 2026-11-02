import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceStep

/-! # Structural relabeling of the existing occurrence-step data -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceRelabeling

universe uT uU uV uO
variable {T : Type uT} {U : Type uU} {V : Type uV} {O : Type uO}

def equations (change : T → U) (store : EquationStore T) : EquationStore U :=
  store.map (fun pair => (change pair.1, change pair.2))

def configuration (change : T → U) (state : Configuration T O) : Configuration U O :=
  ⟨equations change state.equations, state.present⟩

theorem check_map_comp (first : T → U) (second : U → V) (check : Check T) :
    (check.map first).map second = check.map (second ∘ first) := by
  cases check <;> rfl

theorem rule_map_comp (first : T → U) (second : U → V) (rule : RuleInstance T) :
    (rule.map first).map second = rule.map (second ∘ first) := by
  cases rule
  simp only [RuleInstance.map, List.map_map, Function.comp_def, check_map_comp]

theorem equations_append (change : T → U) (first second : EquationStore T) :
    equations change (first ++ second) = equations change first ++ equations change second :=
  List.map_append

theorem selection_equations (change : T → U) (label : O → T) (patterns : List T) (selected : List O) :
    Selection.equations (change ∘ label) (patterns.map change) selected =
      equations change (Selection.equations label patterns selected) := by
  induction patterns generalizing selected with
  | nil => rfl
  | cons head tail earlier =>
      cases selected with
      | nil => rfl
      | cons occurrence rest =>
          simpa only [Selection.equations, equations, List.map_cons, List.zipWith_cons_cons,
            Function.comp_def] using congrArg (List.cons (change head, change (label occurrence))) (earlier rest)

theorem selection_values (label : O → T) (patterns : List T) (selected : List O) :
    Selection.equations id patterns (selected.map label) = Selection.equations label patterns selected := by
  induction patterns generalizing selected with
  | nil => rfl
  | cons head tail earlier =>
      cases selected with
      | nil => rfl
      | cons occurrence rest =>
          simpa only [Selection.equations, List.map_cons, List.zipWith_cons_cons, id] using
            congrArg (List.cons (head, label occurrence)) (earlier rest)

theorem problem (change : T → U) (label : O → T) (rule : RuleInstance T)
    (selection : Selection O) (before : Configuration T O) :
    selection.problem (change ∘ label) (rule.map change) (configuration change before) =
      equations change (selection.problem label rule before) := by
  simp only [Selection.problem, RuleInstance.map, configuration, equations_append, selection_equations]
  rfl

theorem result [DecidableEq O] (change : T → U) (label : O → T) (rule : RuleInstance T)
    (selection : Selection O) (before : Configuration T O) :
    selection.result (change ∘ label) (rule.map change) (configuration change before) =
      configuration change (selection.result label rule before) := by
  apply congrArg₂ Configuration.mk
  · exact problem change label rule selection before
  · rfl

theorem selection_equations_congr (first second : O → T) (patterns : List T) (selected : List O)
    (same : ∀ occurrence ∈ selected, first occurrence = second occurrence) :
    Selection.equations first patterns selected = Selection.equations second patterns selected := by
  induction patterns generalizing selected with
  | nil => rfl
  | cons head tail earlier =>
      cases selected with
      | nil => rfl
      | cons occurrence rest =>
          simp only [Selection.equations, List.zipWith_cons_cons, same occurrence List.mem_cons_self]
          exact congrArg (List.cons (head, second occurrence))
            (earlier rest (fun item member => same item (List.mem_cons_of_mem _ member)))

theorem problem_label_congr (first second : O → T) (rule : RuleInstance T) (selection : Selection O)
    (before : Configuration T O)
    (taken : ∀ occurrence ∈ selection.taken, first occurrence = second occurrence)
    (read : ∀ occurrence ∈ selection.read, first occurrence = second occurrence) :
    selection.problem first rule before = selection.problem second rule before := by
  simp only [Selection.problem, selection_equations_congr first second _ _ taken,
    selection_equations_congr first second _ _ read]

theorem valid_label_congr [DecidableEq O] {Q : Type*} (action : SubstitutionAction T Q)
    (first second : O → T) (rule : RuleInstance T) (free : rule.checks = [])
    (selection : Selection O) (before : Configuration T O)
    (valid : selection.Valid action first rule before)
    (taken : ∀ occurrence ∈ selection.taken, first occurrence = second occurrence)
    (read : ∀ occurrence ∈ selection.read, first occurrence = second occurrence)
    (made : ∀ occurrence ∈ selection.made, first occurrence = second occurrence) :
    selection.Valid action second rule before := by
  refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, valid.read_length, ?_, ?_, ?_, ?_⟩
  · exact (List.map_congr_left made).symm.trans valid.outputs
  · refine ⟨valid.occurrences.taken_subset, valid.occurrences.kept_subset,
      valid.occurrences.apart, valid.occurrences.fresh, ?_⟩
    intro query member
    cases member
  · rw [← problem_label_congr first second rule selection before taken read]
    exact valid.consistent
  · intro check member
    rw [free] at member
    cases member

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceRelabeling
