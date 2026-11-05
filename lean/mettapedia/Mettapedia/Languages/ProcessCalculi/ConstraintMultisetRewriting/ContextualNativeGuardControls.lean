import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardViews
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPrefixPublicationControls

/-!
# Earlier live captures and real query-data interference

The entry fact is box(X). The first clause checks absence of box(2),
and the second binds X to 1. Inspecting the later cut incorrectly accepts
that absence. The actual-row query at the first cut retains its countermodel.
A second query admits absence of symbol(8), detects a matching insertion,
and permits an unrelated insertion of symbol(9).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalGuards
open ContextualSourceSchedules
open ContextualPrefixPublicationControls
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

abbrev entry : ContextualClauseSourceState.World none Nat [] () :=
  ⟨Unit, inferInstance, captures, [], {9}, fun occurrence =>
    ofStored none captures (.live
      (if occurrence = 42 then symbol 8 else if occurrence = 43 then symbol 9
       else box (generator captures ())))⟩

local instance : DecidableEq entry.Names := entry.equality

def guardedPlan : ContextualPublication.Plan (Term (signature base actor) [] ()) :=
  ⟨{firstCode with checks := [.absent (box (symbol 2))]}, [true], rfl⟩

abbrev middle := ContextualClauseSourceState.target none none entry guardedPlan firstSelection
abbrev result := ContextualClauseSourceState.target none firstLocals middle secondPlan secondSelection

def body : Schedule base Nat [] () entry result :=
  .snoc (.snoc (.nil entry) none guardedPlan firstSelection) none secondPlan secondSelection

def earlier : body.CutIndex := ⟨0, by decide +kernel⟩
def later : body.CutIndex := ⟨1, by decide +kernel⟩

theorem shapes : body.ShapesHold := by
  erw [Schedule.shapes_snoc, Schedule.shapes_snoc]
  exact ⟨⟨by simp [Schedule.ShapesHold, Schedule.shapes],
    ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩⟩,
    ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩⟩

theorem resources : Executable Schedule.unitLabel entry.present body.commits := by
  exact .cons (by decide +kernel) (.cons (by decide +kernel) (.nil _))

theorem consistent : ContextualConditionalExecution.Solvable result.equations := second_admitted.solvable

theorem terminal_model {V : Type} (declaration : V → MetaArity base) :
    ContextualResidual.Models (secondModel declaration) result.equations := by
  change ContextualResidual.Models (secondModel declaration)
    [(observe secondX, observe (symbol 1))]
  intro equation member
  have only := List.mem_singleton.mp member
  subst equation
  rfl

def cutModel {V : Type} (declaration : V → MetaArity base) (value : Nat) : Assignment result.declarations declaration
  | .inl impossible => nomatch impossible
  | .inr (.inl ⟨_, .inl impossible⟩) => nomatch impossible
  | .inr (.inl ⟨_, .inr name⟩) => firstModel declaration value name
  | .inr (.inr name) => firstModel declaration value name

theorem earlier_model (value : Nat) : ContextualResidual.Models (cutModel none value) (body.cuts.get earlier).problem := by
  change ContextualResidual.Models (cutModel none value) []
  intro equation member
  cases member

theorem source_input : body.sourceGuardInputs 9 = ofStored none result.declarations (.live (box secondX)) := by
  with_unfolding_all rfl

theorem only_surviving_input : body.survivingGuardInputs ∅ = {9} := by
  decide +kernel

theorem earlier_entry_absence_fails :
    ¬ Ask none (body.cuts.get earlier).problem body.sourceGuardInputs
      (body.survivingGuardInputs ∅) (.absent (box (symbol 2))) := by
  intro asked
  have absent := asked Empty none (cutModel none 2) (earlier_model 2)
  apply absent 9 (by rw [only_surviving_input]; exact Finset.mem_singleton_self _)
  rw [source_input, ofStored_matches_iff, ContextualGuardMatching.live_matches_iff]
  rfl

theorem later_entry_absence_holds :
    Ask none (body.cuts.get later).problem body.sourceGuardInputs
      (body.survivingGuardInputs ∅) (.absent (box (symbol 2))) := by
  intro Future future candidate model occurrence present matched
  rw [only_surviving_input] at present
  have same : occurrence = 9 := Finset.mem_singleton.mp present
  subst occurrence
  have one := the_callers_variable_is_one future candidate model
  rw [source_input, ofStored_matches_iff, ContextualGuardMatching.live_matches_iff] at matched
  change box (symbol (decl := future) 2) = box (instantiate candidate secondX) at matched
  erw [one] at matched
  have arguments := Args.cons.inj (eq_of_heq (Term.op.inj matched).2)
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj arguments.1).1)
  omega

theorem the_actual_earlier_query_is_refused :
    ¬ ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery earlier (box (symbol 2)) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (body.nativeBindingState ∅).present := by
  exact fun observed => earlier_entry_absence_fails
    ((body.native_cut_absence_iff earlier shapes resources consistent ∅ [] [] (box (symbol 2)) ∅).mp observed)

theorem choosing_the_later_cut_would_accept :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery later (box (symbol 2)) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (body.nativeBindingState ∅).present :=
  (body.native_cut_absence_iff later shapes resources consistent ∅ [] [] (box (symbol 2)) ∅).mpr
    later_entry_absence_holds

theorem an_earlier_native_equality_keeps_its_countermodel :
    ¬ Ask body.guardNativeBank (body.nativeBindingInformation ∅ [] [])
      (ContextualConditionalExecution.guardRows body.guardNativeBank body.guardFamily (body.nativeBindingState ∅).rows)
      (body.nativeBindingState ∅).present
      (.equal (instantiate (body.nativeGuardCut earlier) secondX)
        (instantiate (body.nativeGuardCut earlier) (symbol 1))) := by
  intro observed
  have original := (body.native_entry_equal_iff earlier shapes resources consistent ∅ [] [] secondX (symbol 1)).mpr observed
  have same := original Empty none (cutModel none 2) (by
    change ContextualResidual.Models (cutModel none 2) []
    intro equation member
    cases member)
  change symbol (decl := none) 2 = symbol 1 at same
  have impossible : (2 : Nat) = 1 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj same).1)
  omega

theorem absence_of_eight :
    Ask none (body.cuts.get earlier).problem body.sourceGuardInputs
      (body.survivingGuardInputs ∅) (.absent (symbol 8)) := by
  intro Future future candidate _model occurrence present matched
  rw [only_surviving_input] at present
  have same : occurrence = 9 := Finset.mem_singleton.mp present
  subst occurrence
  rw [source_input, ofStored_matches_iff, ContextualGuardMatching.live_matches_iff] at matched
  have impossible := Sum.inl.inj (Term.op.inj matched).1
  cases impossible

theorem the_actual_unrelated_query_is_admitted :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (body.nativeBindingState ∅).present :=
  (body.native_cut_absence_iff earlier shapes resources consistent ∅ [] [] (symbol 8) ∅).mpr absence_of_eight

theorem a_matching_insertion_is_detected :
    ¬ ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (insert (some (.inl 42)) (body.nativeBindingState ∅).present) := by
  classical
  intro asked
  obtain ⟨extension, candidate, model, _fixed⟩ := body.source_model_extends_native_binding
    shapes resources ∅ [] [] (secondModel none) (terminal_model none)
  have observed := asked extension.Names extension.declarations candidate model
  let physical : Schedule.GuardPhysical Nat := some (.inl 42)
  let label := ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅)
  have matched : Matches body.guardNativeBank body.guardNativeFamily candidate
      (instantiate candidate (instantiate (body.nativeGuardCut earlier) (symbol 8)))
      (body.nativeGuardRow earlier (label physical).2) := by
    apply (body.native_guard_input_matches earlier ∅ 42 candidate _).mpr
    change Matches none entry.declarations _ _ (ofStored none entry.declarations (.live (symbol 8)))
    rw [ofStored_matches_iff, ContextualGuardMatching.live_matches_iff]
    rfl
  have present : physical ∈ regionOf label (insert physical (body.nativeBindingState ∅).present)
      ((body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅).region ⟨extension.Names, extension.declarations, candidate⟩) := by
    apply mem_regionOf.mpr
    refine ⟨Finset.mem_insert_self _ _, ?_⟩
    change decide (physical ≠ Option.none ∧ physical ∉ (∅ : Finset (Schedule.GuardPhysical Nat)) ∧ _) = true
    exact decide_eq_true ⟨by decide +kernel, Finset.notMem_empty _, matched⟩
  change regionOf label (insert physical (body.nativeBindingState ∅).present)
    ((body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅).region
      ⟨extension.Names, extension.declarations, candidate⟩) = ∅ at observed
  erw [observed] at present
  exact Finset.notMem_empty _ present

theorem an_unrelated_insertion_is_permitted :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (insert (some (.inl 43)) (body.nativeBindingState ∅).present) := by
  classical
  let writer : Selection (Schedule.GuardPhysical Nat) := ⟨[], [], [some (.inl 43)]⟩
  have outside : ∀ (Future : Type) (future : Future → MetaArity base)
      (candidate : Assignment body.guardNativeFamily future),
      ContextualResidual.Models candidate (body.nativeBindingInformation ∅ [] []) →
      ∀ physical ∈ writer.taken ++ writer.made,
        (body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅).region ⟨Future, future, candidate⟩
          (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅) physical) = false := by
    intro Future future candidate _model physical member
    have equal : physical = some (.inl 43) := List.mem_singleton.mp member
    subst physical
    change decide (some (Sum.inl 43) ≠ Option.none ∧
      some (Sum.inl 43) ∉ (∅ : Finset (Schedule.GuardPhysical Nat)) ∧
      Matches body.guardNativeBank body.guardNativeFamily candidate
        (instantiate candidate (instantiate (body.nativeGuardCut earlier) (symbol 8))) _) = false
    apply decide_eq_false
    intro accepted
    have matched := (body.native_guard_input_matches earlier ∅ 43 candidate _).mp accepted.2.2
    change Matches none entry.declarations _ _ (ofStored none entry.declarations (.live (symbol 9))) at matched
    rw [ofStored_matches_iff, ContextualGuardMatching.live_matches_iff] at matched
    change symbol (decl := future) 8 = symbol 9 at matched
    have impossible : (8 : Nat) = 9 := DataOperator.symbol.inj (Sum.inl.inj (Term.op.inj matched).1)
    omega
  have observed := ContextualPredicateQueryAdmission.ask_data_after_writes
    (body.nativeBindingInformation ∅ [] []) (body.nativeCutMatchingQuery earlier (symbol 8) ∅ ∅)
    (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
    (body.nativeBindingState ∅).present writer the_actual_unrelated_query_is_admitted outside
  simpa only [fire, Selection.commit, writer, List.toFinset_nil, Finset.sdiff_empty,
    List.toFinset_cons, Finset.union_insert, Finset.union_empty] using observed

namespace OwnEquations

def plan : ContextualPublication.Plan (Term (signature base actor) [] ()) :=
  ⟨{guardedPlan.rule with tell := [(callerX, symbol 1)]}, [true], rfl⟩

abbrev middle := ContextualClauseSourceState.target none none entry plan firstSelection
abbrev result := ContextualClauseSourceState.target none firstLocals middle secondPlan secondSelection

def body : Schedule base Nat [] () entry result :=
  .snoc (.snoc (.nil entry) none plan firstSelection) none secondPlan secondSelection

def watched : body.CutIndex := ⟨0, by decide +kernel⟩

theorem shapes : body.ShapesHold := ContextualNativeGuardControls.shapes
theorem resources : Executable Schedule.unitLabel entry.present body.commits := ContextualNativeGuardControls.resources

theorem consistent : ContextualConditionalExecution.Solvable result.equations := by
  refine ⟨Empty, none, secondModel none, ?_⟩
  change ContextualResidual.Models (secondModel none)
    [(observe secondX, observe (symbol 1)), (observe secondX, observe (symbol 1))]
  intro equation member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

/-- The current clause may establish its guard using its own tell; only
information from later clauses is excluded from that saved cut. -/
theorem the_clause_own_equation_is_retained :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery watched (box (symbol 2)) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (body.nativeBindingState ∅).present := by
  apply (body.native_cut_absence_iff watched shapes resources consistent ∅ [] [] (box (symbol 2)) ∅).mpr
  exact later_entry_absence_holds

theorem the_own_equation_also_discharges_native_equality :
    Ask body.guardNativeBank (body.nativeBindingInformation ∅ [] [])
      (ContextualConditionalExecution.guardRows body.guardNativeBank body.guardFamily (body.nativeBindingState ∅).rows)
      (body.nativeBindingState ∅).present
      (.equal (instantiate (body.nativeGuardCut watched) secondX)
        (instantiate (body.nativeGuardCut watched) (symbol 1))) := by
  apply (body.native_entry_equal_iff watched shapes resources consistent ∅ [] [] secondX (symbol 1)).mp
  intro Future future candidate model
  exact the_callers_variable_is_one future candidate model

end OwnEquations

namespace Virtual

def guardPlan : ContextualPublication.Plan (Term (signature base (queryFamily none firstFamily)) [] ()) :=
  ⟨⟨[], [], [], [.absent (box (symbol 2))], []⟩, [], rfl⟩

abbrev result := ContextualClauseSourceState.target none firstLocals afterFirst guardPlan secondSelection

def body : Schedule base Nat [] () initial result :=
  .snoc (.snoc (.nil initial) none firstPlan firstSelection) none guardPlan secondSelection

def watched : body.CutIndex := ⟨1, by decide +kernel⟩

theorem shapes : body.ShapesHold := by
  erw [Schedule.shapes_snoc, Schedule.shapes_snoc]
  exact ⟨⟨by simp [Schedule.ShapesHold, Schedule.shapes],
    ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩⟩,
    ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩⟩

theorem resources : Executable Schedule.unitLabel initial.present body.commits := by
  exact .cons (by decide +kernel) (.cons (by decide +kernel) (.nil _))

theorem consistent : ContextualConditionalExecution.Solvable result.equations := by
  refine ⟨Empty, none, secondModel none, ?_⟩
  change ContextualResidual.Models (secondModel none) []
  intro equation member
  cases member

theorem source_guard_refuses_the_internal_creation : ¬ body.Admitted := by
  intro admitted
  have asked := admitted.2.checks (.absent (box (symbol 2))) (List.mem_singleton_self _)
  have absent := asked Empty none (secondModel none) (by
    change ContextualResidual.Models (secondModel none) []
    intro equation member
    cases member)
  apply absent 0 (by decide +kernel)
  rw [ContextualConditionalSourceAdmission.sourceRows, matches_map_iff]
  apply (ContextualClauseSourceState.ordinary_output_instances first_admitted
    ⟨0, by decide +kernel⟩ rfl none _ (box (symbol 2))).mpr
  refine ⟨ContextualGuardMatching.Extension.identity none, firstModel none 2, ?_, rfl⟩
  change ContextualResidual.Models (firstModel none 2) []
  intro equation member
  cases member

/-- A query of the entry alone omits an atom made by the private prefix. -/
theorem the_entry_query_alone_is_insufficient :
    ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeCutMatchingQuery watched (box (symbol 2)) ∅ ∅)
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (body.nativeBindingState ∅).present ∧ ¬ body.Admitted := by
  refine ⟨?_, source_guard_refuses_the_internal_creation⟩
  apply (body.native_cut_absence_iff watched shapes resources consistent ∅ [] [] (box (symbol 2)) ∅).mpr
  intro Future future candidate _model occurrence member
  change occurrence ∈ (∅ : Finset Nat) at member
  exact False.elim (Finset.notMem_empty _ member)

theorem the_creation_query_restores_the_refusal :
    ¬ ContextualPredicateQueryAdmission.AskData (body.nativeBindingInformation ∅ [] [])
      (body.nativeVirtualAbsenceQuery watched (box (symbol 2)))
      (ContextualPredicateQueryAdmission.nativeLabels body.guardNativeBank (body.nativeBindingState ∅))
      (body.nativeBindingState ∅).present := by
  intro virtual
  have complete := (body.native_entry_absence_iff watched shapes resources consistent ∅ [] [] (box (symbol 2))).mpr
    ⟨the_entry_query_alone_is_insufficient.1, virtual⟩
  have held : (body.entryCutAt watched).Holds := by
    intro check member
    have only : check = .absent (box (symbol 2)) := List.mem_singleton.mp member
    subst check
    exact complete
  have original := (body.entry_cut_at_compare shapes resources watched).2.2.mp held
  have second := (clause_admitted_iff afterFirst none guardPlan secondSelection).mpr
    ⟨⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩, by decide +kernel, consistent, original⟩
  apply source_guard_refuses_the_internal_creation
  refine ⟨⟨?_, first_admitted⟩, second⟩
  exact (Schedule.snoc (Schedule.nil initial) none firstPlan firstSelection).source_solvable first_admitted.solvable

end Virtual

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeGuardControls
