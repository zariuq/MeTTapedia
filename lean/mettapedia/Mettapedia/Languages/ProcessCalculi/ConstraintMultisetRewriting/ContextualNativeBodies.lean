import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualScheduleCompilation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualIndependentProblems
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualConditionalRealizations
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.OccurrenceAllocationRenaming
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualCutRepresentation

/-!
# Compiled source bodies: the interface of the native lowering

Every native construction after source compilation reads a compiled body,
not the clause grammar that produced it. A body records the entry-name
frame, the information it adds, its ordered physical selections, its shape
and guard-cut obligations with the exact admission characterization, its
net inputs, and the information blocks its publication contract needs.
Each original guard cut is also represented over entry occurrences and
authored prefix creations, with the same problem, checks and guard meaning.
Each clause grammar supplies these from facts it already proves.

The guard problem is built once here: one block for the current caller,
one per publication block of the clause kind, and one per original guard
cut. Consistency needs terminal information only, never a guard verdict.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open ContextualConjunctiveQueries ContextualConditionalRows ContextualConditionalRealizations
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

variable {S : Signature} {O First Last : Type} [DecidableEq O]
    {first : First → MetaArity S} {last : Last → MetaArity S} {Γ : Ctx S} {sort : S.Srt}

/-- Entry names inside the terminal declarations, as an injective frame. -/
abbrev entryFrame {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}
    (names : before.Names → after.Names) (injective : Function.Injective names)
    (preserve : ∀ name, after.declarations (names name) = before.declarations name) :
    ContextualGuardMatching.Extension before.declarations where
  Names := after.Names
  declarations := after.declarations
  name := names
  injective := injective
  preserves := preserve

/-- The resource commits of authored selections. -/
abbrev commitsOf (selections : List (Selection O)) : List (Commit O Unit) :=
  selections.map fun picked => picked.commit

/-- A native inventory name: the invocation control (`none`) or an allocated occurrence. -/
abbrev GuardPhysical (O : Type) := Option (OccurrenceAllocationRenaming.Name O)

/-- The allocated resource trace of authored selections. -/
abbrev allocation (selections : List (Selection O)) : List (Selection (OccurrenceAllocationRenaming.Name O)) :=
  OccurrenceAllocationRenaming.rename OccurrenceAllocationRenaming.Cursor.initial selections

/-- The single net resource commit of an allocated trace. -/
abbrev netOf (selections : List (Selection O)) : CompiledSchedule (OccurrenceAllocationRenaming.Name O) Unit :=
  CompiledSchedule.compile OccurrenceAllocationRenaming.label (OccurrenceAllocationRenaming.commits (allocation selections))

/-- A compiled source body from `before` to `after`. -/
structure Body (S : Signature) (O : Type) [DecidableEq O] (context : Ctx S) (sort : S.Srt)
    {First Last : Type} {first : First → MetaArity S} {last : Last → MetaArity S}
    (before : ContextualClauseSourceState.World first O context sort)
    (after : ContextualClauseSourceState.World last O context sort) : Type 1 where
  /-- Entry names inside the terminal declarations. -/
  names : before.Names → after.Names
  names_injective : Function.Injective names
  names_preserve : ∀ name, after.declarations (names name) = before.declarations name
  /-- Information added by the body after the transported entry information. -/
  deltas : ContextualResidual.Problem after.declarations
  final_equations : after.equations =
    ContextualResidual.mapProblem (entryFrame names names_injective names_preserve).assignment before.equations ++ deltas
  /-- The authored physical selections, in order. -/
  selections : List (Selection O)
  physical_trace : fireList before.present (commitsOf selections) = after.present
  /-- Port shapes; with the resources, terminal consistency and the original cuts
  they characterize source admission exactly. -/
  ShapesHold : Prop
  cuts : List (ContextualSourceSchedules.Cut after.declarations O context sort)
  Admitted : Prop
  admitted_iff : Admitted ↔ ShapesHold ∧
    Executable ContextualSourceSchedules.Schedule.unitLabel before.present (commitsOf selections) ∧
    ContextualConditionalExecution.Solvable after.equations ∧ ∀ cut ∈ cuts, cut.Holds
  cuts_solvable : ContextualConditionalExecution.Solvable after.equations →
    ∀ cut ∈ cuts, ContextualConditionalExecution.Solvable cut.problem
  /-- The publication blocks of the clause kind and their creation-time conditions. -/
  Extra : Type
  extraIndexEquality : DecidableEq Extra
  extraVariables : Extra → Type
  extraDeclarations : ∀ extra, extraVariables extra → MetaArity S
  extraEquality : ∀ extra, DecidableEq (extraVariables extra)
  extraConditions : ∀ extra, ContextualResidual.Problem (extraDeclarations extra)
  extraIndices : List Extra
  extras_solvable : ContextualConditionalExecution.Solvable after.equations →
    ∀ extra, ContextualConditionalExecution.Solvable (extraConditions extra)
  /-- Entry occurrences used by the net takes and reads, with joint witnesses. -/
  initialInputs : Finset O
  net_input_is_initial :
    Executable ContextualSourceSchedules.Schedule.unitLabel before.present (commitsOf selections) →
      ∀ physical ∈ (netOf selections).effect.taken ∪ (netOf selections).effect.kept,
        ∃ occurrence ∈ before.present, physical = Sum.inl occurrence ∧ occurrence ∈ initialInputs
  initial_inputs_realize_together : ShapesHold → ∀ {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment after.declarations next), ContextualResidual.Models candidate after.equations →
      ∀ (inputs : List O), (∀ occurrence ∈ inputs, occurrence ∈ initialInputs) →
        ∃ extension : ContextualGuardMatching.Extension next,
          ∃ _filler : Assignment first extension.declarations,
            ∀ occurrence ∈ inputs, ∃ pattern : Term (signature S extension.declarations) context sort,
              Realizes first before.declarations
                (Assignment.compose extension.assignment
                  (Assignment.compose candidate (entryFrame names names_injective names_preserve).assignment))
                pattern (before.rows occurrence)
  /-- Every original cut over entry occurrences and authored prefix creations. -/
  entryCuts : List (ContextualSourceSchedules.EntryCut after.declarations O context sort)
  entry_cuts_length : entryCuts.length = cuts.length
  entry_cuts_compare : ShapesHold →
    Executable ContextualSourceSchedules.Schedule.unitLabel before.present (commitsOf selections) →
      List.Forall₂ (fun entry source => entry.view.problem = source.problem ∧ entry.view.checks = source.checks ∧
        (entry.Holds ↔ source.Holds)) entryCuts cuts
  entry_cut_inputs : ∀ cut ∈ entryCuts, ∀ (Future : Type) (future : Future → MetaArity S)
    (candidate : Assignment after.declarations future) (pattern : Term (signature S future) context sort) (occurrence : O),
      Matches cut.view.locals after.declarations candidate pattern (cut.view.rows (.inl occurrence)) ↔
        Matches first before.declarations
          (Assignment.compose candidate (entryFrame names names_injective names_preserve).assignment)
          pattern (before.rows occurrence)
  entry_cut_world : ∀ cut ∈ entryCuts, cut.view.world = (before.present.image Sum.inl \ cut.taken) ∪ cut.made
  entry_cut_created_not_initial : ∀ cut ∈ entryCuts, ∀ occurrence : O, Sum.inl occurrence ∉ cut.made

namespace Body

variable {before : ContextualClauseSourceState.World first O Γ sort}
    {after : ContextualClauseSourceState.World last O Γ sort}

abbrev frame (body : Body S O Γ sort before after) : ContextualGuardMatching.Extension before.declarations :=
  entryFrame body.names body.names_injective body.names_preserve

abbrev commits (body : Body S O Γ sort before after) : List (Commit O Unit) :=
  commitsOf body.selections

abbrev allocated (body : Body S O Γ sort before after) : List (Selection (OccurrenceAllocationRenaming.Name O)) :=
  allocation body.selections

abbrev net (body : Body S O Γ sort before after) : CompiledSchedule (OccurrenceAllocationRenaming.Name O) Unit :=
  netOf body.selections

def currentProblem (body : Body S O Γ sort before after) : ContextualResidual.Problem after.declarations :=
  ContextualResidual.mapProblem body.frame.assignment before.equations ++ body.deltas

theorem current_problem_eq (body : Body S O Γ sort before after) : body.currentProblem = after.equations :=
  body.final_equations.symm

theorem model_at_entry (body : Body S O Γ sort before after) {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment after.declarations next)
    (model : ContextualResidual.Models candidate after.equations) :
    ContextualResidual.Models (Assignment.compose candidate body.frame.assignment) before.equations := by
  rw [body.final_equations] at model
  exact (ContextualResidual.models_mapProblem _ _ _).mp
    ((ContextualResidual.models_append candidate _ _).mp model).1

theorem admitted_final_solvable (body : Body S O Γ sort before after) (admitted : body.Admitted) :
    ContextualConditionalExecution.Solvable after.equations :=
  (body.admitted_iff.mp admitted).2.2.1

theorem allocated_resources_of_executable (body : Body S O Γ sort before after)
    (executable : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits) :
    Executable OccurrenceAllocationRenaming.label (before.present.image Sum.inl)
        (OccurrenceAllocationRenaming.commits body.allocated) ∧
      fireList (before.present.image Sum.inl) (OccurrenceAllocationRenaming.commits body.allocated) =
        after.present.image
          (OccurrenceAllocationRenaming.finish OccurrenceAllocationRenaming.Cursor.initial body.selections).current := by
  have prepared : Executable OccurrenceAllocationRenaming.label before.present
      (OccurrenceAllocationRenaming.commits body.selections) := by
    with_unfolding_all exact executable
  obtain ⟨renamed, same⟩ := OccurrenceAllocationRenaming.lifts body.selections
    OccurrenceAllocationRenaming.Cursor.initial before.present prepared
  refine ⟨renamed, ?_⟩
  have sourceResult : fireList before.present (OccurrenceAllocationRenaming.commits body.selections) = after.present := by
    with_unfolding_all exact body.physical_trace
  rw [sourceResult] at same
  exact same

/-! ## The guard problem: current, publication and cut blocks -/

instance extraDecidableEq (body : Body S O Γ sort before after) : DecidableEq body.Extra := body.extraIndexEquality

abbrev CutIndex (body : Body S O Γ sort before after) := Fin body.cuts.length
abbrev GuardBlockIndex (body : Body S O Γ sort before after) := Sum (Option body.Extra) body.CutIndex

def guardVariables (body : Body S O Γ sort before after) : body.GuardBlockIndex → Type
  | .inl none => after.Names
  | .inl (some extra) => body.extraVariables extra
  | .inr _ => after.Names

def guardDeclarations (body : Body S O Γ sort before after) :
    ∀ index, body.guardVariables index → MetaArity S
  | .inl none => after.declarations
  | .inl (some extra) => body.extraDeclarations extra
  | .inr _ => after.declarations

def guardConditions (body : Body S O Γ sort before after) :
    ∀ index, ContextualResidual.Problem (body.guardDeclarations index)
  | .inl none => body.currentProblem
  | .inl (some extra) => body.extraConditions extra
  | .inr index => (body.cuts.get index).problem

def guardIndices (body : Body S O Γ sort before after) : List body.GuardBlockIndex :=
  (none :: body.extraIndices.map some).map Sum.inl ++ (List.finRange body.cuts.length).map Sum.inr

theorem guard_index_current_listed (body : Body S O Γ sort before after) : Sum.inl none ∈ body.guardIndices :=
  List.mem_append_left _ (List.mem_map.mpr ⟨none, List.mem_cons_self, rfl⟩)

theorem guard_index_extra_listed (body : Body S O Γ sort before after) (extra : body.Extra)
    (listed : extra ∈ body.extraIndices) : Sum.inl (some extra) ∈ body.guardIndices :=
  List.mem_append_left _ (List.mem_map.mpr ⟨some extra, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨extra, listed, rfl⟩), rfl⟩)

theorem guard_index_cut_listed (body : Body S O Γ sort before after) (index : body.CutIndex) :
    Sum.inr index ∈ body.guardIndices :=
  List.mem_append_right _ (List.mem_map.mpr ⟨index, List.mem_finRange index, rfl⟩)

abbrev guardFamily (body : Body S O Γ sort before after) :=
  ContextualIndependentProblems.family body.guardVariables body.guardDeclarations

instance guardEquality (body : Body S O Γ sort before after) :
    DecidableEq (ContextualAnswerFamilies.Names body.guardVariables) := by
  letI : ∀ index, DecidableEq (body.guardVariables index) := fun index =>
    match index with
    | .inl none => after.equality
    | .inl (some extra) => body.extraEquality extra
    | .inr _ => after.equality
  infer_instance

def guardProblem (body : Body S O Γ sort before after) : ContextualResidual.Problem body.guardFamily :=
  ContextualIndependentProblems.problem body.guardVariables body.guardDeclarations body.guardConditions body.guardIndices

/-- Guard truth is not needed for the consistency of any block. -/
theorem guard_blocks_solvable (body : Body S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (index : body.GuardBlockIndex) :
    ContextualConditionalExecution.Solvable (body.guardConditions index) := by
  cases index with
  | inl index =>
      cases index with
      | none =>
          change ContextualConditionalExecution.Solvable body.currentProblem
          rw [body.current_problem_eq]
          exact consistent
      | some extra => exact body.extras_solvable consistent extra
  | inr index => exact body.cuts_solvable consistent _ (List.get_mem _ _)

/-- The extra blocks reject no consistent terminal model, including for a body with a false earlier guard. -/
theorem guard_problem_solvable_iff (body : Body S O Γ sort before after) :
    ContextualConditionalExecution.Solvable body.guardProblem ↔
      ContextualConditionalExecution.Solvable after.equations := by
  constructor
  · rintro ⟨Future, future, candidate, model⟩
    have current := (ContextualIndependentProblems.models_iff body.guardVariables body.guardDeclarations
      body.guardConditions body.guardIndices candidate).mp model (.inl none) body.guard_index_current_listed
    change ContextualResidual.Models _ body.currentProblem at current
    rw [body.current_problem_eq] at current
    exact ⟨Future, future, _, current⟩
  · intro consistent
    exact ContextualIndependentProblems.solvable body.guardVariables body.guardDeclarations body.guardConditions
      (body.guard_blocks_solvable consistent) body.guardIndices

def guardView (body : Body S O Γ sort before after) (index : body.CutIndex) :
    ContextualSourceSchedules.Cut body.guardFamily O Γ sort :=
  let cut := body.cuts.get index
  let embedding := ContextualIndependentProblems.inclusion body.guardVariables body.guardDeclarations (.inr index)
  { cut.map embedding with problem := body.guardProblem }

theorem guard_view_iff (body : Body S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations) (index : body.CutIndex) :
    (body.guardView index).Holds ↔ (body.cuts.get index).Holds := by
  simp only [ContextualSourceSchedules.Cut.Holds, guardView, ContextualSourceSchedules.Cut.map, List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  exact ContextualIndependentProblems.asks_iff body.guardVariables body.guardDeclarations body.guardConditions
    (body.guard_blocks_solvable consistent) body.guardIndices (.inr index) (body.guard_index_cut_listed index)
    (body.cuts.get index).locals (body.cuts.get index).rows (body.cuts.get index).world check

/-- Exact source admission without presupposing any guard verdict in the compilation. -/
theorem guarded_admission_iff (body : Body S O Γ sort before after) :
    (body.ShapesHold ∧ Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits ∧
      ContextualConditionalExecution.Solvable body.guardProblem ∧
      ∀ index : body.CutIndex, (body.guardView index).Holds) ↔ body.Admitted := by
  rw [body.admitted_iff]
  constructor
  · rintro ⟨shapes, resources, consistent, guards⟩
    have terminal := body.guard_problem_solvable_iff.mp consistent
    refine ⟨shapes, resources, terminal, ?_⟩
    intro cut member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact (body.guard_view_iff terminal index).mp (guards index)
  · rintro ⟨shapes, resources, terminal, guards⟩
    refine ⟨shapes, resources, body.guard_problem_solvable_iff.mpr terminal, ?_⟩
    intro index
    exact (body.guard_view_iff terminal index).mpr (guards _ (List.get_mem _ _))

def reducedGuardView (body : Body S O Γ sort before after)
    (update : ContextualFrameUpdate.Update body.guardProblem) (index : body.CutIndex) :
    ContextualSourceSchedules.Cut update.declaration O Γ sort :=
  { (body.guardView index).map update.answer with problem := update.remaining }

/-- Solver reduction keeps all original countermodels, even with a nonempty remaining queue. -/
theorem reduced_guard_view_iff (body : Body S O Γ sort before after)
    (consistent : ContextualConditionalExecution.Solvable after.equations)
    (update : ContextualFrameUpdate.Update body.guardProblem) (index : body.CutIndex) :
    (body.reducedGuardView update index).Holds ↔ (body.cuts.get index).Holds := by
  apply Iff.trans ?_ (body.guard_view_iff consistent index)
  simp only [ContextualSourceSchedules.Cut.Holds, reducedGuardView, ContextualSourceSchedules.Cut.map, List.forall_mem_map]
  apply forall_congr'
  intro check
  apply forall_congr'
  intro _member
  constructor
  · intro asked Future future candidate model
    obtain ⟨residual, residualModel, images⟩ := update.factors future candidate model
    have held := (ContextualConditionalGuards.holds_transport (body.guardView index).locals update.answer residual
      (body.guardView index).rows (body.guardView index).world check).mp
      (asked Future future residual residualModel)
    have same : candidate = Assignment.compose residual update.answer := funext images
    exact same.symm ▸ held
  · intro asked Future future candidate model
    apply (ContextualConditionalGuards.holds_transport (body.guardView index).locals update.answer candidate
      (body.guardView index).rows (body.guardView index).world check).mpr
    exact asked Future future _ (update.valid.sound future candidate model)

/-- An actual bounded worklist return retains the original guard verdicts; it need not finish. -/
theorem actual_guard_update [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    (body : Body S O Γ sort before after) (consistent : ContextualConditionalExecution.Solvable after.equations)
    (fuel : Nat) :
    ∃ update : ContextualFrameUpdate.Update body.guardProblem,
      ContextualFrameWorklist.run fuel body.guardFamily body.guardProblem = .residual update ∧
        ∀ index : body.CutIndex,
          (body.reducedGuardView update index).Holds ↔ (body.cuts.get index).Holds := by
  cases computed : ContextualFrameWorklist.run fuel body.guardFamily body.guardProblem with
  | refuted impossible =>
      obtain ⟨Future, future, candidate, model⟩ := body.guard_problem_solvable_iff.mpr consistent
      exact False.elim (impossible future candidate model)
  | residual update =>
      exact ⟨update, rfl, fun index => body.reduced_guard_view_iff consistent update index⟩

/-! ## Original guard cuts over entry occurrences and authored creations -/

def entryCutAt (body : Body S O Γ sort before after) (index : body.CutIndex) :
    ContextualSourceSchedules.EntryCut after.declarations O Γ sort :=
  body.entryCuts.get ⟨index.val, by rw [body.entry_cuts_length]; exact index.isLt⟩

theorem entry_cut_at_compare (body : Body S O Γ sort before after) (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits)
    (index : body.CutIndex) :
    (body.entryCutAt index).view.problem = (body.cuts.get index).problem ∧
      (body.entryCutAt index).view.checks = (body.cuts.get index).checks ∧
      ((body.entryCutAt index).Holds ↔ (body.cuts.get index).Holds) := by
  have compared := body.entry_cuts_compare shapes resources
  have bound : index.val < body.entryCuts.length := by rw [body.entry_cuts_length]; exact index.isLt
  exact compared.get bound index.isLt

theorem entry_guards_iff (body : Body S O Γ sort before after) (shapes : body.ShapesHold)
    (resources : Executable ContextualSourceSchedules.Schedule.unitLabel before.present body.commits) :
    (∀ cut ∈ body.entryCuts, cut.Holds) ↔ ∀ cut ∈ body.cuts, cut.Holds := by
  constructor
  · intro compiled cut member
    obtain ⟨index, rfl⟩ := List.mem_iff_get.mp member
    exact (body.entry_cut_at_compare shapes resources index).2.2.mp
      (compiled (body.entryCutAt index) (List.get_mem _ _))
  · intro original cut member
    obtain ⟨position, rfl⟩ := List.mem_iff_get.mp member
    let index : body.CutIndex := ⟨position.val, by rw [← body.entry_cuts_length]; exact position.isLt⟩
    exact (body.entry_cut_at_compare shapes resources index).2.2.mpr
      (original _ (List.get_mem _ _))

end Body

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualNativeBodies
