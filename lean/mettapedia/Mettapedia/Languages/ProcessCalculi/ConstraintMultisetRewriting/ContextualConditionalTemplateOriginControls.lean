import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateInputModels
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateSourceControls

/-!
# Conditional entry inputs and reused occurrence identifiers

A used entry row is conditioned by X=0; an unused row is conditioned by
X=1. The source information remains consistent and the used row opens
without importing the unused condition. A separate source body consumes
occurrence 10 and later creates a different row under that logical number.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateOriginControls

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows
open ContextualConditionalTemplateControls (base Operation literal pattern body conditions)
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

local instance : DecidableEq base.Srt := inferInstanceAs (DecidableEq Unit)
local instance (sort : base.Srt) : DecidableEq (base.Op sort) := inferInstanceAs (DecidableEq Operation)

abbrev locals := ContextualConditionalTemplateControls.locals
abbrev inners := ContextualConditionalTemplateControls.inners
abbrev captures := ContextualConditionalTemplateControls.captures

def incomingRow (number : Nat) : Row locals captures [] () :=
  ⟨.shared (literal 7), [(observe (generator (ContextualSelectionViews.source locals captures) (.inr ())),
    observe (literal (Γ := []) number))]⟩

def before : ContextualClauseSourceState.World locals Nat [] () :=
  ⟨Unit, inferInstance, captures, [], {0, 1}, fun occurrence => if occurrence = 0 then incomingRow 0 else incomingRow 1⟩

def rule : ContextualConditionalTemplateSource.Rule locals inners captures [] () :=
  { ContextualConditionalTemplateControls.sourceRule with
    code := { ContextualConditionalTemplateControls.code with read := [literal 7] } }

abbrev picked := ContextualConditionalTemplateControls.chosen
abbrev result := ContextualConditionalTemplateState.resultFamily locals inners locals before
abbrev information := ContextualConditionalTemplateState.information locals inners locals before rule
  ⟨[], [0], picked.made⟩
abbrev selection : Selection Nat := ⟨[], [0], picked.made⟩

def gamma : Term (signature base result) [] () := generator result (.inr (.inr ()))

theorem information_explicit : information =
    [(observe (literal (Γ := []) 7), observe (literal (Γ := []) 7)),
      (observe gamma, observe (literal (Γ := []) 0)),
      (observe gamma, observe (literal (Γ := []) 0))] := by
  with_unfolding_all rfl

def model {V : Type} (next : V → MetaArity base) : Assignment result next
  | .inl (.inl impossible) => nomatch impossible
  | .inl (.inr (_, ())) => literal 0
  | .inr (.inl ⟨_, impossible⟩) => nomatch impossible
  | .inr (.inr ()) => literal 0

theorem models_information {V : Type} (next : V → MetaArity base) : ContextualResidual.Models (model next) information := by
  rw [information_explicit]
  intro equation member
  rcases List.mem_cons.mp member with rfl | member
  · rfl
  · rcases List.mem_cons.mp member with rfl | member
    · rfl
    · have only := List.mem_singleton.mp member
      subst equation
      rfl

theorem source_admitted : ContextualConditionalTemplateState.Admitted locals inners locals before rule selection := by
  refine ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl,
    by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    ⟨Unit, captures, model captures, models_information captures⟩, ?_⟩
  intro check member
  cases member

abbrev sourceBody := ContextualConditionalTemplateSchedules.Schedule.template before
  (ContextualConditionalTemplateSchedules.Schedule.nil before) locals inners rule selection
abbrev after := ContextualConditionalTemplateState.target locals inners locals before rule selection

theorem source_body_admitted : sourceBody.Admitted :=
  ⟨⟨Unit, captures, (fun _ => literal 0), (by intro equation member; cases member)⟩, source_admitted⟩

theorem initial_input_is_exactly_the_used_entry : sourceBody.initialInputs = {0} := by
  simp only [ContextualConditionalTemplateSchedules.Schedule.initialInputs,
    ContextualConditionalTemplateSchedules.Schedule.creations,
    ContextualConditionalTemplateSchedules.Schedule.selections]
  decide +kernel

theorem every_source_model_opens_the_used_row_jointly {V : Type} (next : V → MetaArity base)
    (candidate : Assignment result next) (modeled : ContextualResidual.Models candidate after.equations) :
    ∃ extension : ContextualGuardMatching.Extension next, ∃ _filler : Assignment locals extension.declarations,
      ∀ occurrence ∈ ([0, 0] : List Nat), ∃ value : Term (signature base extension.declarations) [] (),
        ContextualConditionalRealizations.Realizes locals captures
          (Assignment.compose extension.assignment (Assignment.compose candidate sourceBody.frame.assignment))
          value (before.rows occurrence) := by
  apply sourceBody.initial_inputs_realize_together (sourceBody.admitted_characterization.mp source_body_admitted).1
    candidate modeled [0, 0]
  intro occurrence member
  rw [initial_input_is_exactly_the_used_entry]
  simpa only [List.mem_cons, List.not_mem_nil, or_false, or_self, Finset.mem_singleton] using member

theorem the_unused_row_remains_incompatible {V : Type} (next : V → MetaArity base)
    (candidate : Assignment result next) (modeled : ContextualResidual.Models candidate after.equations)
    (value : Term (signature base next) [] ()) :
    ¬ Matches locals captures (Assignment.compose candidate sourceBody.frame.assignment) value (before.rows 1) := by
  intro matched
  obtain ⟨extension, _images, constraints, _same⟩ := matched
  have global := modeled (observe gamma, observe (literal (Γ := []) 0)) (by
    change (observe gamma, observe (literal (Γ := []) 0)) ∈ information
    rw [information_explicit]
    exact List.mem_cons_of_mem _ List.mem_cons_self)
  change observe (instantiate candidate gamma) = observe (literal (declaration := next) (Γ := []) 0) at global
  have zero := observe_injective global
  have localEquation := constraints
    (observe (generator (ContextualSelectionViews.source locals captures) (.inr ())), observe (literal (Γ := []) 1))
    (List.mem_singleton_self _)
  change observe (instantiate (ContextualGuardMatching.instanceAssignment locals _images extension.assignment
      (Assignment.compose candidate sourceBody.frame.assignment))
      (generator (ContextualSelectionViews.source locals captures) (.inr ()))) =
    observe (literal (declaration := extension.declarations) (Γ := []) 1) at localEquation
  erw [instantiate_generator] at localEquation
  change observe (instantiate extension.assignment (instantiate candidate (sourceBody.frame.assignment ()))) =
    observe (literal (declaration := extension.declarations) (Γ := []) 1) at localEquation
  have entry : sourceBody.frame.assignment () = gamma := rfl
  erw [entry, zero] at localEquation
  change observe (literal (declaration := extension.declarations) (Γ := []) 0) = observe (literal 1) at localEquation
  have clash : (0 : Nat) = 1 := Operation.literal.inj (Sum.inl.inj (Term.op.inj (observe_injective localEquation)).1)
  omega

namespace Reuse

open ContextualConditionalTemplateSourceControls (queries rowLocals privateRows)
abbrev original := ContextualConditionalTemplateSourceControls.after
abbrev firstPart := ContextualConditionalTemplateSourceControls.firstPart

abbrev OldPrivateNames := ContextualAnswerFamilies.Names
  (ContextualConditionalTemplateState.PrivateNames (Query := Empty) (Inner := Unit) rowLocals
    ContextualConditionalTemplateSourceControls.before)

local instance (side : Bool) : DecidableEq
    (ContextualConditionalTemplateState.PrivateNames (Query := Empty) (Inner := Unit) rowLocals
      ContextualConditionalTemplateSourceControls.before side) := by
  let _ : DecidableEq (Empty ⊕ (Nat × Unit)) := inferInstance
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit))) := inferInstance
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit)) ⊕ Unit) := inferInstance
  cases side
  · change DecidableEq (Empty ⊕ (Nat × Unit))
    infer_instance
  · change DecidableEq ((Empty ⊕ (Nat × Unit)) ⊕
      ((Empty ⊕ (Nat × Unit)) ⊕ (Mettapedia.Logic.LP.ScopedVar (Empty ⊕ (Nat × Unit)) ⊕ Unit)))
    infer_instance

local instance : DecidableEq OldPrivateNames := inferInstance

def takePlan : ContextualPublication.Plan (Term (signature base (queryFamily queries original.declarations)) [] ()) :=
  ⟨⟨[pattern 0 0 0], [], [], [], []⟩, [], rfl⟩
def takeSelection : Selection Nat := ⟨[10], [], []⟩
abbrev middle := ContextualClauseSourceState.target queries privateRows original takePlan takeSelection
abbrev middleLocals := ContextualClauseSourceState.resultLocals queries privateRows original

local instance : DecidableEq (OldPrivateNames ⊕ (Empty ⊕ (Mettapedia.Logic.LP.ScopedVar OldPrivateNames ⊕ original.Names))) := by
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar OldPrivateNames) := inferInstance
  let _ : DecidableEq original.Names := original.equality
  let _ : DecidableEq (Mettapedia.Logic.LP.ScopedVar OldPrivateNames ⊕ original.Names) := inferInstance
  let _ : DecidableEq (Empty ⊕ (Mettapedia.Logic.LP.ScopedVar OldPrivateNames ⊕ original.Names)) := inferInstance
  infer_instance

def remakePlan : ContextualPublication.Plan (Term (signature base (queryFamily queries middle.declarations)) [] ()) :=
  ⟨⟨[], [], [], [], [literal 99]⟩, [true], rfl⟩
def remakeSelection : Selection Nat := ⟨[], [], [10]⟩
abbrev finalWorld := ContextualClauseSourceState.target queries middleLocals middle remakePlan remakeSelection

abbrev plain := ContextualSourceSchedules.Schedule.snoc
  (ContextualSourceSchedules.Schedule.snoc (ContextualSourceSchedules.Schedule.nil original) queries takePlan takeSelection)
  queries remakePlan remakeSelection
abbrev sourceBody := ContextualConditionalTemplateSchedules.Schedule.segment firstPart plain

theorem logical_identifier_reuse_has_valid_resources :
    sourceBody.compile.resources.condition.Holds ContextualSourceSchedules.Schedule.unitLabel
      ContextualConditionalTemplateSourceControls.before.present := by decide +kernel

theorem the_latest_birth_is_selected :
    sourceBody.outputBirth 10 = some (ContextualConditionalTemplateSchedules.Birth.ofOrdinary
      (plain.births.get ⟨0, by decide +kernel⟩)) := by
  rw [ContextualConditionalTemplateSchedules.Schedule.outputBirth,
    ContextualSourceSchedules.Schedule.productionIndex]
  rfl

theorem source_shapes : sourceBody.ShapesHold := by
  apply (ContextualConditionalTemplateSchedules.Schedule.shapes_segment firstPart plain).mpr
  constructor
  · exact (firstPart.admitted_characterization.mp ContextualConditionalTemplateSourceControls.the_mixed_body_is_admitted.1).1
  · apply (ContextualSourceSchedules.Schedule.shapes_snoc _ queries remakePlan remakeSelection).mpr
    constructor
    · apply (ContextualSourceSchedules.Schedule.shapes_snoc _ queries takePlan takeSelection).mpr
      constructor
      · intro shape member
        cases member
      · exact ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩
    · exact ⟨by decide +kernel, by decide +kernel, rfl, rfl, rfl⟩

theorem its_origin_has_the_final_row_meaning {V : Type} (next : V → MetaArity base)
    (candidate : Assignment (ContextualClauseSourceState.target queries middleLocals middle remakePlan remakeSelection).declarations next)
    (value : Term (signature base next) [] ()) :
    (ContextualConditionalTemplateSchedules.Birth.ofOrdinary (plain.births.get ⟨0, by decide +kernel⟩)).origin.Instances candidate value ↔
      Matches (ContextualClauseSourceState.resultLocals queries middleLocals middle)
        (ContextualClauseSourceState.target queries middleLocals middle remakePlan remakeSelection).declarations
        candidate value ((ContextualClauseSourceState.target queries middleLocals middle remakePlan remakeSelection).rows 10) :=
  sourceBody.selected_birth_instances source_shapes 10 _ the_latest_birth_is_selected next candidate value

end Reuse

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalTemplateOriginControls
