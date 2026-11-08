import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualComputedFreshFrame
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualGuardedStep
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualPatternTermination

/-!
# Completed solver answers realize guarded activations in helper-active frames

The selected rule and row uses are prepared exactly once. Transport maps
those existing terms, both sides of their equations, and the capture parts
of retained rows. Occurrence selection and the occupied-scope ledger keep
their original identities. Guard asks still quantify over every future
declaration family.

Physical occurrence admission and guard evidence do not assume equation
consistency. A completed actual solver update constructs that consistency
in the explicit frame containing its returned helpers.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open ContextualFrameUpdate

universe u
variable {S : Signature} {V Next Local Shared : Type} {O : Type u}
  {source : V → MetaArity S} {next : Next → MetaArity S}

def configurationMap (change : Assignment source next) {Γ : Ctx S} {sort : S.Srt}
    (configuration : Configuration (Term (signature S source) Γ sort) O) :
    Configuration (Term (signature S next) Γ sort) O :=
  ⟨ContextualFrameUnifier.mapProblem change configuration.equations, configuration.present⟩

theorem map_append (change : Assignment source next) {Γ : Ctx S} {sort : S.Srt}
    (first second : EquationStore (Term (signature S source) Γ sort)) :
    ContextualFrameUnifier.mapProblem change (first ++ second) =
      ContextualFrameUnifier.mapProblem change first ++ ContextualFrameUnifier.mapProblem change second :=
  List.map_append

theorem map_useEquations (change : Assignment source next) {Γ : Ctx S} {sort : S.Srt}
    (patterns values : List (Term (signature S source) Γ sort)) :
    ContextualFrameUnifier.mapProblem change (ContextualActivatedStep.useEquations patterns values) =
      ContextualActivatedStep.useEquations (patterns.map (instantiate change)) (values.map (instantiate change)) := by
  induction patterns generalizing values with
  | nil => rfl
  | cons pattern rest earlier =>
      cases values with
      | nil => rfl
      | cons value tail =>
          simpa only [ContextualActivatedStep.useEquations, Selection.equations, ContextualFrameUnifier.mapProblem,
            List.zipWith_cons_cons, List.map_cons, id] using congrArg (List.cons (instantiate change pattern, instantiate change value))
              (earlier tail)

variable (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

def preparedRule (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) : RuleInstance (Term (signature S next) Γ sort) :=
  (ContextualActivatedStep.prepared locals captures occupied selection rule rows).rule.map (instantiate change)

def guardRows (change : Assignment (ContextualActivatedStep.target locals captures) next) {Γ : Ctx S} {sort : S.Srt}
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) : O → ContextualStoredRows.Row locals next Γ sort :=
  fun occurrence => (ContextualGuardedStep.guardRows locals captures rows occurrence).map locals change

def result [DecidableEq O] (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    Configuration (Term (signature S next) Γ sort) O :=
  configurationMap change (ContextualActivatedStep.result locals captures occupied selection rule rows before)

def resultRows [DecidableEq O] (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) : O → ContextualStoredRows.Row locals next Γ sort :=
  fun occurrence => (ContextualActivatedStep.resultRows locals captures selection outputs rows occurrence).map locals change

theorem transported_problem (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    ContextualFrameUnifier.mapProblem change (ContextualActivatedStep.problem locals captures occupied selection rule rows before) =
      (configurationMap change (ContextualActivatedStep.frame locals captures before)).equations ++
        ContextualActivatedStep.useEquations (preparedRule locals captures change occupied selection rule rows).take
          ((List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection rule rows).taken).map (instantiate change)) ++
        ContextualActivatedStep.useEquations (preparedRule locals captures change occupied selection rule rows).read
          ((List.ofFn (ContextualActivatedStep.prepared locals captures occupied selection rule rows).read).map (instantiate change)) ++
        (preparedRule locals captures change occupied selection rule rows).tell := by
  simp only [ContextualActivatedStep.problem, map_append, map_useEquations, preparedRule, RuleInstance.map, configurationMap]
  rfl

structure Valid [DecidableEq O] (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputLabel : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort) : Prop where
  admitted : ContextualGuardedStep.Requirements locals captures occupied selection rule rows before outputLabel
  take_length : (preparedRule locals captures change occupied selection rule rows).take.length = selection.taken.length
  read_length : (preparedRule locals captures change occupied selection rule rows).read.length = selection.read.length
  outputs : selection.made.map (fun occurrence => instantiate change (outputLabel occurrence)) =
    (preparedRule locals captures change occupied selection rule rows).produce
  occurrences : Enabled (fun occurrence => instantiate change (outputLabel occurrence)) before.present
    (selection.commit (T := Term (signature S next) Γ sort))
  consistent : (ContextualFamilies.action next Γ sort).Consistent
    (result locals captures change occupied selection rule rows before).equations
  checks : ∀ check ∈ (preparedRule locals captures change occupied selection rule rows).checks,
    ContextualGuardSemantics.Ask locals (result locals captures change occupied selection rule rows before).equations
      (guardRows locals captures change rows) before.present check

theorem from_update [DecidableEq O] {occupied : Finset Nat} {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort}
    (admitted : ContextualGuardedStep.Requirements locals captures occupied selection rule rows before outputs)
    (update : Update (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before)))
    (empty : update.remaining = []) :
    Valid locals captures (ContextualComputedFreshFrame.includeSource update) occupied selection rule rows before outputs := by
  let change := ContextualComputedFreshFrame.includeSource update
  refine ⟨admitted, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [preparedRule, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
      ContextualFreshening.ruleAt, RuleInstance.map, List.length_map] using admitted.take_length
  · simpa only [preparedRule, ContextualActivatedStep.prepared, ContextualSelectionViews.prepare,
      ContextualFreshening.ruleAt, RuleInstance.map, List.length_map] using admitted.read_length
  · have mapped := congrArg (List.map (instantiate change)) admitted.outputs
    simpa only [List.map_map, preparedRule, RuleInstance.map, Function.comp_def] using mapped
  · refine ⟨admitted.occurrences.taken_subset, admitted.occurrences.kept_subset,
      admitted.occurrences.apart, admitted.occurrences.fresh, ?_⟩
    intro query member
    cases member
  · exact ContextualComputedFreshFrame.consistent _ update empty
  · intro check member
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    exact ContextualGuardSemantics.Ask.transport locals (admitted.checks original present) change

structure FromRun [DecidableEq O] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)] (fuel : Nat) (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)
    (update : Update (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before))) : Prop where
  computed : ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals captures)
    (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before)) = .residual update
  empty : update.remaining = []
  valid : Valid locals captures (ContextualComputedFreshFrame.includeSource update) occupied selection rule rows before outputs

theorem from_run [DecidableEq O] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)] {fuel : Nat} {occupied : Finset Nat} {selection : Selection O}
    {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort}
    (admitted : ContextualGuardedStep.Requirements locals captures occupied selection rule rows before outputs)
    (update : Update (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before)))
    (computed : ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals captures)
      (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before)) = .residual update)
    (empty : update.remaining = []) : FromRun locals captures fuel occupied selection rule rows before outputs update :=
  ⟨computed, empty, from_update locals captures admitted update empty⟩

theorem solve_or_refute [DecidableEq O] [DecidableEq Local] [DecidableEq Shared] [DecidableEq S.Srt]
    [∀ result, DecidableEq (S.Op result)] {occupied : Finset Nat} {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort}
    (admitted : ContextualGuardedStep.Requirements locals captures occupied selection rule rows before outputs)
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before))) :
    ∃ fuel,
      (∃ update, FromRun locals captures fuel occupied selection rule rows before outputs update) ∨
      (∃ proof, ContextualFrameWorklist.run fuel (ContextualActivatedStep.target locals captures)
        (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before)) = .refuted proof) := by
  obtain ⟨fuel, solved | refused⟩ := ContextualPatternTermination.solves_or_refutes _ patterned
  · obtain ⟨update, computed, empty, _, _⟩ := solved
    exact ⟨fuel, .inl ⟨update, from_run locals captures admitted update computed empty⟩⟩
  · exact ⟨fuel, .inr refused⟩

/-- Every completed actual return recovers the original semantic admission.
This direction requires no pattern-fragment or termination hypothesis. -/
theorem FromRun.semantic_admission [DecidableEq O] [DecidableEq Local] [DecidableEq Shared]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {fuel : Nat} {occupied : Finset Nat} {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort}
    {update : Update (ContextualResidual.observeProblem
      (ContextualActivatedStep.problem locals captures occupied selection rule rows before))}
    (returned : FromRun locals captures fuel occupied selection rule rows before outputs update) :
    ContextualGuardedStep.Valid locals captures occupied selection rule rows before outputs :=
  ⟨returned.valid.admitted,
    ContextualFrameUnifier.solvable_of_model
      ((ContextualResidual.models_observeProblem _ _).mp (update.completed returned.empty))⟩

/-- The supported structural-pattern profile realizes exactly semantic
admission. Fresh helper families are obtained from the actual worklist,
and the comparison does not assume a completed run as a premise. -/
theorem semantic_admission_iff_completed_run [DecidableEq O] [DecidableEq Local] [DecidableEq Shared]
    [DecidableEq S.Srt] [∀ result, DecidableEq (S.Op result)]
    {occupied : Finset Nat} {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort}
    (patterned : ContextualPatternFragment.ProblemPattern
      (ContextualResidual.observeProblem (ContextualActivatedStep.problem locals captures occupied selection rule rows before))) :
    ContextualGuardedStep.Valid locals captures occupied selection rule rows before outputs ↔
      ∃ fuel update, FromRun locals captures fuel occupied selection rule rows before outputs update := by
  constructor
  · intro admitted
    obtain ⟨fuel, completed | refuted⟩ := solve_or_refute locals captures admitted.toRequirements patterned
    · obtain ⟨update, returned⟩ := completed
      exact ⟨fuel, update, returned⟩
    · obtain ⟨impossible, _⟩ := refuted
      obtain ⟨Future, future, candidate, model⟩ := admitted.solvable
      exact False.elim (impossible future candidate ((ContextualResidual.models_observeProblem _ _).mpr model))
  · rintro ⟨fuel, update, returned⟩
    exact returned.semantic_admission locals captures

theorem present_is_the_same_fire [DecidableEq O] (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (ContextualActivatedStep.source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    (result locals captures change occupied selection rule rows before).present =
      fire before.present (selection.commit (T := Term (signature S next) Γ sort)) := rfl

theorem produced_row_is_shared [DecidableEq O] (change : Assignment (ContextualActivatedStep.target locals captures) next)
    (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) {occurrence : O} (made : occurrence ∈ selection.made) :
    resultRows locals captures change selection outputs rows occurrence = .shared (instantiate change (outputs occurrence)) := by
  rw [resultRows, ContextualActivatedStep.produced_row_is_shared locals captures selection outputs rows made]
  rfl

theorem retained_row_keeps_private_locals [DecidableEq O]
    (change : Assignment (ContextualActivatedStep.target locals captures) next) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (outputs : O → Term (signature S (ContextualActivatedStep.target locals captures)) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) {occurrence : O}
    (notMade : occurrence ∉ selection.made) :
    resultRows locals captures change selection outputs rows occurrence =
      (rows occurrence).map locals (Assignment.compose change (ContextualSelectionViews.capturedTarget locals captures)) := by
  simp only [resultRows, ContextualActivatedStep.resultRows, if_neg notMade]
  exact ContextualStoredRows.Row.map_compose locals _ _ _

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualTransportedActivation
