import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.EquationWakeups
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PropagationHistory

/-!
# A standing rule's installation is a physical shared read

An already prepared rule body fires only while its installation occurrence
is present, and cannot consume that occurrence itself. Compilation adds
one read of the stored definition to the same candidate step. Its reflexive
equation changes no models or guards; no second resource step is introduced.

Repeat and once-per-read-selection are explicit profiles. The latter uses
the existing propagation history with the stable installation occurrence,
not a newly allocated output or activation scope, as its identity.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleRows

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

inductive Mode where
  | repeat
  | perSelection
  deriving DecidableEq

structure Definition (T : Type uT) where
  body : RuleInstance T
  mode : Mode

def rule (label : O → T) (installation : O) (body : RuleInstance T) : RuleInstance T :=
  ⟨body.take, label installation :: body.read, body.tell, body.checks, body.produce⟩

def selection (installation : O) (picked : Selection O) : Selection O :=
  ⟨picked.taken, installation :: picked.read, picked.made⟩

def installRule (label : O → T) (installation : O) : RuleInstance T :=
  ⟨[], [], [], [], [label installation]⟩

def installSelection (installation : O) : Selection O := ⟨[], [], [installation]⟩

/-- Installing a definition is an ordinary production, with no new opcode. -/
theorem install_valid_iff (A : SubstitutionAction T S) (label : O → T) (installation : O)
    (before : Configuration T O) :
    (installSelection installation).Valid A label (installRule label installation) before ↔
      installation ∉ before.present ∧ A.Consistent before.equations := by
  constructor
  · intro valid
    refine ⟨?_, ?_⟩
    · intro present
      exact Finset.disjoint_left.mp valid.occurrences.fresh (by simp [installSelection, Selection.commit]) present
    · simpa only [installSelection, installRule, Selection.problem, Selection.equations,
        List.zipWith_nil_left, List.append_nil] using valid.consistent
  · rintro ⟨fresh, consistent⟩
    refine ⟨by simp [installSelection], by simp [installSelection], rfl, rfl, rfl, ?_, ?_, ?_⟩
    · refine ⟨by simp [installSelection, Selection.commit], by simp [installSelection, Selection.commit],
        by simp [installSelection, Selection.commit], ?_, by intro query member; cases member⟩
      simpa [installSelection, Selection.commit, Finset.disjoint_left] using fresh
    · simpa only [installSelection, installRule, Selection.problem, Selection.equations,
        List.zipWith_nil_left, List.append_nil] using consistent
    · intro check member
      cases member

theorem installation_result (label : O → T) (installation : O) (before : Configuration T O) :
    ((installSelection installation).result label (installRule label installation) before).present =
      insert installation before.present := by
  ext occurrence
  simp [installSelection, Selection.result, Selection.commit, fire]

omit [DecidableEq O] in
theorem problem_models (A : SubstitutionAction T S) (label : O → T) (installation : O)
    (body : RuleInstance T) (picked : Selection O) (before : Configuration T O) (candidate : S) :
    A.Models candidate ((selection installation picked).problem label (rule label installation body) before) ↔
      A.Models candidate (picked.problem label body before) := by
  simp only [selection, rule, Selection.problem, Selection.equations, List.zipWith_cons_cons,
    A.models_append, A.models_cons, SubstitutionAction.Solves, A.equivalence.refl, true_and]

theorem valid_iff (A : SubstitutionAction T S) (label : O → T) (installation : O)
    (body : RuleInstance T) (picked : Selection O) (before : Configuration T O) :
    (selection installation picked).Valid A label (rule label installation body) before ↔
      installation ∈ before.present ∧ installation ∉ picked.taken ∧ picked.Valid A label body before := by
  constructor
  · intro valid
    have present : installation ∈ before.present := valid.occurrences.kept_subset (by simp [selection, Selection.commit])
    have notTaken : installation ∉ picked.taken := by
      intro member
      exact Finset.disjoint_left.mp valid.occurrences.apart (List.mem_toFinset.mpr member)
        (by simp [selection, Selection.commit])
    refine ⟨present, notTaken, valid.take_distinct, valid.output_distinct, valid.take_length,
      Nat.succ.inj valid.read_length, valid.outputs, ?_, ?_, ?_⟩
    · refine ⟨valid.occurrences.taken_subset, ?_, ?_, valid.occurrences.fresh, ?_⟩
      · intro occurrence member
        exact valid.occurrences.kept_subset (by
          simpa only [selection, Selection.commit, List.mem_toFinset, List.mem_cons] using Or.inr (List.mem_toFinset.mp member))
      · exact Finset.disjoint_of_subset_right
          (by intro occurrence member; simp only [selection, Selection.commit, List.mem_toFinset, List.mem_cons];
              exact Or.inr (List.mem_toFinset.mp member)) valid.occurrences.apart
      · intro query member
        cases member
    · obtain ⟨candidate, model⟩ := valid.consistent
      exact ⟨candidate, (problem_models A label installation body picked before candidate).mp model⟩
    · intro check member candidate model
      exact valid.checks check member candidate ((problem_models A label installation body picked before candidate).mpr model)
  · rintro ⟨present, notTaken, valid⟩
    refine ⟨valid.take_distinct, valid.output_distinct, valid.take_length, congrArg Nat.succ valid.read_length,
      valid.outputs, ?_, ?_, ?_⟩
    · refine ⟨valid.occurrences.taken_subset, ?_, ?_, valid.occurrences.fresh, ?_⟩
      · intro occurrence member
        have options : occurrence = installation ∨ occurrence ∈ picked.read := by
          simpa only [selection, Selection.commit, List.mem_toFinset, List.mem_cons] using member
        rcases options with rfl | member
        · exact present
        · exact valid.occurrences.kept_subset (List.mem_toFinset.mpr member)
      · apply Finset.disjoint_left.mpr
        intro occurrence taken read
        have options : occurrence = installation ∨ occurrence ∈ picked.read := by
          simpa only [selection, Selection.commit, List.mem_toFinset, List.mem_cons] using read
        rcases options with rfl | read
        · exact notTaken (List.mem_toFinset.mp taken)
        · exact Finset.disjoint_left.mp valid.occurrences.apart taken (List.mem_toFinset.mpr read)
      · intro query member
        cases member
    · obtain ⟨candidate, model⟩ := valid.consistent
      exact ⟨candidate, (problem_models A label installation body picked before candidate).mpr model⟩
    · intro check member candidate model
      exact valid.checks check member candidate ((problem_models A label installation body picked before candidate).mp model)

theorem installation_survives (A : SubstitutionAction T S) (label : O → T) (installation : O)
    (body : RuleInstance T) (picked : Selection O) (before : Configuration T O)
    (valid : (selection installation picked).Valid A label (rule label installation body) before) :
    installation ∈ ((selection installation picked).result label (rule label installation body) before).present :=
  valid.kept_survive (by simp [selection])

theorem same_body_resources (label : O → T) (installation : O) (body : RuleInstance T)
    (picked : Selection O) (before : Configuration T O) :
    ((selection installation picked).result label (rule label installation body) before).present =
      (picked.result label body before).present := rfl

def event (installation : O) (mode : Mode) (picked : Selection O) : PropagationHistory.Event O O :=
  ⟨installation, mode == .perSelection, picked⟩

def Fresh (installation : O) (mode : Mode) (picked : Selection O) (history : List (PropagationHistory.Key O O)) : Prop :=
  PropagationHistory.Fresh (event installation mode picked) history

def record (installation : O) (mode : Mode) (picked : Selection O) (history : List (PropagationHistory.Key O O)) :=
  PropagationHistory.record (event installation mode picked) history

omit [DecidableEq O] in
theorem repeat_fresh (installation : O) (picked : Selection O) (history : List (PropagationHistory.Key O O)) :
    Fresh installation .repeat picked history := PropagationHistory.direct_fresh rfl history

omit [DecidableEq O] in
theorem per_selection_cannot_replay (installation : O) (picked : Selection O)
    (readOnly : picked.taken = []) (history : List (PropagationHistory.Key O O)) :
    ¬ Fresh installation .perSelection picked (record installation .perSelection picked history) :=
  PropagationHistory.propagation_cannot_replay rfl readOnly history

omit [DecidableEq O] in
theorem consuming_fresh (installation : O) (mode : Mode) (picked : Selection O)
    (consumes : picked.taken ≠ []) (history : List (PropagationHistory.Key O O)) :
    Fresh installation mode picked history := PropagationHistory.consuming_fresh consumes history

omit [DecidableEq O] in
theorem record_mono (installation : O) (mode : Mode) (picked : Selection O) (history : List (PropagationHistory.Key O O)) :
    ∀ key ∈ history, key ∈ record installation mode picked history :=
  PropagationHistory.record_mono _ history

omit [DecidableEq O] in
theorem fresh_of_history_subset (installation : O) (mode : Mode) (picked : Selection O)
    {earlier later : List (PropagationHistory.Key O O)}
    (subset : ∀ key ∈ earlier, key ∈ later) (fresh : Fresh installation mode picked later) :
    Fresh installation mode picked earlier := fun tracked member => fresh tracked (subset _ member)

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.StandingRuleRows
