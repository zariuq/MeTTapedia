import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualStoredRows
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualFrameUnifier

/-!
# Positive occurrence firings with computed contextual views

A firing opens the rule once and each selected stored-schema use once.
Live values retain their existing identities. Old equations enter the same
extended declaration frame as the computed views, and retained row metadata
transports its captures into that frame. The physical occurrence selection
and its consume/read/produce conditions are the existing ones.

This profile requires the rule's check list to be empty. Local-instantiation
semantics for absence and counts, logical admission of published schemas and
the runtime occupied-ledger invariant are separate obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep

open Mettapedia.OSLF.Binding hiding instantiate instantiateArgs
open Mettapedia.OSLF.Binding.ContextualFamily
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe u
variable {S : Signature} {Local Shared : Type} {O : Type u}
  (locals : Local → MetaArity S) (captures : Shared → MetaArity S)

abbrev source := ContextualSelectionViews.source locals captures
abbrev target := ContextualSelectionViews.target locals captures

def frame {Γ : Ctx S} {sort : S.Srt}
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    Configuration (Term (signature S (target locals captures)) Γ sort) O :=
  ⟨ContextualFrameUnifier.mapProblem (ContextualSelectionViews.capturedTarget locals captures)
      before.equations, before.present⟩

def prepared (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :=
  ContextualSelectionViews.prepare locals captures occupied selection rule
    (fun occurrence => ContextualStoredRows.asTemplate locals captures (rows occurrence))

def useEquations {T : Type} (patterns values : List T) : EquationStore T :=
  Selection.equations id patterns values

def problem (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    EquationStore (Term (signature S (target locals captures)) Γ sort) :=
  let views := prepared locals captures occupied selection rule rows
  (frame locals captures before).equations ++
    useEquations views.rule.take (List.ofFn views.taken) ++
      useEquations views.rule.read (List.ofFn views.read) ++ views.rule.tell

/-- The selected event's equations, without duplicating the incoming
constraint store. Each take/read port keeps its own prepared row view. -/
def addedEquations (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    EquationStore (Term (signature S (target locals captures)) Γ sort) :=
  let views := prepared locals captures occupied selection rule rows
  useEquations views.rule.take (List.ofFn views.taken) ++
    useEquations views.rule.read (List.ofFn views.read) ++ views.rule.tell

theorem problem_eq_frame_append (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    problem locals captures occupied selection rule rows before =
      (frame locals captures before).equations ++ addedEquations locals captures occupied selection rule rows := by
  simp only [problem, addedEquations, List.append_assoc]

/-- Equation preparation inspects exactly the selected take/read rows.
Other rows may still matter to guards, which are not erased by this law. -/
theorem addedEquations_rows_congr (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    {first second : O → ContextualStoredRows.Row locals captures Γ sort}
    (same : ∀ occurrence ∈ selection.taken ++ selection.read, first occurrence = second occurrence) :
    addedEquations locals captures occupied selection rule first =
      addedEquations locals captures occupied selection rule second := by
  have takes : (prepared locals captures occupied selection rule first).taken =
      (prepared locals captures occupied selection rule second).taken := by
    funext port
    exact congrArg (fun row => ContextualSelectionViews.termAtPort locals captures occupied
      (ContextualActivationScopes.takePort selection port) (ContextualStoredRows.asTemplate locals captures row))
      (same _ (List.mem_append_left _ (List.get_mem _ _)))
  have reads : (prepared locals captures occupied selection rule first).read =
      (prepared locals captures occupied selection rule second).read := by
    funext port
    exact congrArg (fun row => ContextualSelectionViews.termAtPort locals captures occupied
      (ContextualActivationScopes.readPort selection port) (ContextualStoredRows.asTemplate locals captures row))
      (same _ (List.mem_append_right _ (List.get_mem _ _)))
  dsimp only [addedEquations]
  rw [takes, reads]
  rfl

def result [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    Configuration (Term (signature S (target locals captures)) Γ sort) O :=
  ⟨problem locals captures occupied selection rule rows before,
    fire before.present (selection.commit (T := Term (signature S (target locals captures)) Γ sort))⟩

def resultRows [DecidableEq O] (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort) :
    O → ContextualStoredRows.Row locals (target locals captures) Γ sort :=
  fun occurrence => if occurrence ∈ selection.made then .shared (outputs occurrence)
    else (rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures)

structure Valid [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputLabel : O → Term (signature S (target locals captures)) Γ sort) : Prop where
  no_checks : rule.checks = []
  take_distinct : selection.taken.Nodup
  output_distinct : selection.made.Nodup
  take_length : rule.take.length = selection.taken.length
  read_length : rule.read.length = selection.read.length
  outputs : selection.made.map outputLabel = (prepared locals captures occupied selection rule rows).rule.produce
  occurrences : Enabled outputLabel before.present
    (selection.commit (T := Term (signature S (target locals captures)) Γ sort))
  solvable : ContextualFrameUnifier.Solvable
    (problem locals captures occupied selection rule rows before)

def Step [DecidableEq O] (occupied : Finset Nat) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (after : Configuration (Term (signature S (target locals captures)) Γ sort) O)
    (afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort)
    (afterOccupied : Finset Nat) : Prop :=
  ∃ selection, Valid locals captures occupied selection rule rows before outputs ∧
    after = result locals captures occupied selection rule rows before ∧
      afterRows = resultRows locals captures selection outputs rows ∧
        afterOccupied = ContextualActivationScopes.after occupied selection

theorem prepared_taken_view (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (position : Fin selection.taken.length) :
    (prepared locals captures occupied selection rule rows).taken position =
      ContextualStoredRows.viewAt locals captures
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.takePort selection position))
        (rows (selection.taken.get position)) :=
  (ContextualStoredRows.viewAt_eq_freshening locals captures _ _).symm

theorem prepared_read_view (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (position : Fin selection.read.length) :
    (prepared locals captures occupied selection rule rows).read position =
      ContextualStoredRows.viewAt locals captures
        (ContextualActivationScopes.scopeAt occupied (ContextualActivationScopes.readPort selection position))
        (rows (selection.read.get position)) :=
  (ContextualStoredRows.viewAt_eq_freshening locals captures _ _).symm

private theorem models_cons_iff {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment (target locals captures) next) {Γ : Ctx S} {sort : S.Srt}
    (equation : Equation (Term (signature S (target locals captures)) Γ sort))
    (rest : EquationStore (Term (signature S (target locals captures)) Γ sort)) :
    ContextualFrameUnifier.Models candidate (equation :: rest) ↔
      instantiate candidate equation.1 = instantiate candidate equation.2 ∧
        ContextualFrameUnifier.Models candidate rest := by
  simp [ContextualFrameUnifier.Models]

theorem models_useEquations_iff {Next : Type} {next : Next → MetaArity S}
    (candidate : Assignment (target locals captures) next) {Γ : Ctx S} {sort : S.Srt}
    (patterns values : List (Term (signature S (target locals captures)) Γ sort))
    (lengths : patterns.length = values.length) :
    ContextualFrameUnifier.Models candidate (useEquations patterns values) ↔
      List.Forall₂ (fun pattern value => instantiate candidate pattern = instantiate candidate value) patterns values := by
  induction patterns generalizing values with
  | nil =>
      have empty : values = [] := List.length_eq_zero_iff.mp lengths.symm
      subst values
      simp [useEquations, Selection.equations, ContextualFrameUnifier.Models]
  | cons pattern rest earlier =>
      cases values with
      | nil => simp at lengths
      | cons value others =>
          have lengths' : rest.length = others.length := Nat.succ.inj lengths
          simpa only [useEquations, Selection.equations, List.zipWith_cons_cons,
            models_cons_iff, List.forall₂_cons, id] using
            and_congr_right (fun _ => earlier others lengths')

theorem Valid.models_inputs [DecidableEq O] {Next : Type} (next : Next → MetaArity S)
    {occupied : Finset Nat} {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    (valid : Valid locals captures occupied selection rule rows before outputs)
    (candidate : Assignment (target locals captures) next)
    (solved : ContextualFrameUnifier.Models candidate
      (problem locals captures occupied selection rule rows before)) :
    let views := prepared locals captures occupied selection rule rows
    ContextualFrameUnifier.Models candidate (frame locals captures before).equations ∧
      List.Forall₂ (fun pattern value => instantiate candidate pattern = instantiate candidate value)
        views.rule.take (List.ofFn views.taken) ∧
      List.Forall₂ (fun pattern value => instantiate candidate pattern = instantiate candidate value)
        views.rule.read (List.ofFn views.read) ∧
      ContextualFrameUnifier.Models candidate views.rule.tell := by
  have parts := solved
  simp only [problem, ContextualFrameUnifier.models_append] at parts
  have takeLength : (prepared locals captures occupied selection rule rows).rule.take.length =
      (List.ofFn (prepared locals captures occupied selection rule rows).taken).length := by
    simpa only [prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, List.length_map, List.length_ofFn] using valid.take_length
  have readLength : (prepared locals captures occupied selection rule rows).rule.read.length =
      (List.ofFn (prepared locals captures occupied selection rule rows).read).length := by
    simpa only [prepared, ContextualSelectionViews.prepare, ContextualFreshening.ruleAt,
      RuleInstance.map, List.length_map, List.length_ofFn] using valid.read_length
  exact ⟨parts.1.1.1, (models_useEquations_iff locals captures candidate _ _ takeLength).mp parts.1.1.2,
    (models_useEquations_iff locals captures candidate _ _ readLength).mp parts.1.2, parts.2⟩

theorem models_refine_old_frame {Next : Type} (next : Next → MetaArity S)
    (occupied : Finset Nat) (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    (candidate : Assignment (target locals captures) next)
    (solved : ContextualFrameUnifier.Models candidate
      (problem locals captures occupied selection rule rows before)) :
    ContextualFrameUnifier.Models
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) before.equations := by
  have old : ContextualFrameUnifier.Models candidate (frame locals captures before).equations := by
    have parts := solved
    simp only [problem, ContextualFrameUnifier.models_append] at parts
    exact parts.1.1.1
  exact (ContextualFrameUnifier.models_mapProblem
    (ContextualSelectionViews.capturedTarget locals captures) candidate before.equations).mp old

theorem result_refines [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O) :
    (ContextualFamilies.action (target locals captures) Γ sort).Refines
      (result locals captures occupied selection rule rows before).equations
      (frame locals captures before).equations := by
  intro candidate solved
  have parts := solved
  simp only [result, problem, SubstitutionAction.models_append] at parts
  exact parts.1.1.1

theorem Valid.kept_survive [DecidableEq O] {occupied : Finset Nat} {selection : Selection O}
    {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    (valid : Valid locals captures occupied selection rule rows before outputs)
    {occurrence : O} (read : occurrence ∈ selection.read) :
    occurrence ∈ (result locals captures occupied selection rule rows before).present :=
  kept_subset_fire valid.occurrences (by simpa [Selection.commit] using read)

theorem Valid.consumed_removed [DecidableEq O] {occupied : Finset Nat} {selection : Selection O}
    {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    (valid : Valid locals captures occupied selection rule rows before outputs)
    {occurrence : O} (taken : occurrence ∈ selection.taken) :
    occurrence ∉ (result locals captures occupied selection rule rows before).present := by
  have old : occurrence ∈ before.present :=
    valid.occurrences.taken_subset (by simpa [Selection.commit] using taken)
  have notMade : occurrence ∉ selection.commit.made := fun made =>
    Finset.disjoint_left.mp valid.occurrences.fresh made old
  simp only [result, fire, Finset.mem_union, Finset.mem_sdiff, not_or]
  exact ⟨fun member => member.2 (by simpa [Selection.commit] using taken), notMade⟩

theorem Valid.retained_row_transports_captures [DecidableEq O]
    {occupied : Finset Nat} {selection : Selection O} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    (valid : Valid locals captures occupied selection rule rows before outputs)
    {occurrence : O} (old : occurrence ∈ before.present) :
    resultRows locals captures selection outputs rows occurrence =
      (rows occurrence).map locals (ContextualSelectionViews.capturedTarget locals captures) := by
  have notMade : occurrence ∉ selection.made := by
    intro made
    exact Finset.disjoint_left.mp valid.occurrences.fresh
      (by simpa [Selection.commit] using made) old
  exact if_neg notMade

theorem produced_row_is_shared [DecidableEq O] (selection : Selection O) {Γ : Ctx S} {sort : S.Srt}
    (outputs : O → Term (signature S (target locals captures)) Γ sort)
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    {occurrence : O} (made : occurrence ∈ selection.made) :
    resultRows locals captures selection outputs rows occurrence = .shared (outputs occurrence) :=
  if_pos made

theorem produced_occurrence_is_present [DecidableEq O] (occupied : Finset Nat) (selection : Selection O)
    {Γ : Ctx S} {sort : S.Srt}
    (rule : RuleInstance (Term (signature S (source locals captures)) Γ sort))
    (rows : O → ContextualStoredRows.Row locals captures Γ sort)
    (before : Configuration (Term (signature S captures) Γ sort) O)
    {occurrence : O} (made : occurrence ∈ selection.made) :
    occurrence ∈ (result locals captures occupied selection rule rows before).present :=
  made_subset_fire (store := before.present)
    (c := selection.commit (T := Term (signature S (target locals captures)) Γ sort))
    (by simpa [Selection.commit] using made)

theorem Step.solvable [DecidableEq O] {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    {after : Configuration (Term (signature S (target locals captures)) Γ sort) O}
    {afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort}
    {afterOccupied : Finset Nat}
    (step : Step locals captures occupied rule rows before outputs after afterRows afterOccupied) :
    ContextualFrameUnifier.Solvable after.equations := by
  obtain ⟨selection, valid, rfl, _, _⟩ := step
  exact valid.solvable

theorem Step.refines_old_frame [DecidableEq O] {Next : Type} (next : Next → MetaArity S)
    {occupied : Finset Nat} {Γ : Ctx S} {sort : S.Srt}
    {rule : RuleInstance (Term (signature S (source locals captures)) Γ sort)}
    {rows : O → ContextualStoredRows.Row locals captures Γ sort}
    {before : Configuration (Term (signature S captures) Γ sort) O}
    {outputs : O → Term (signature S (target locals captures)) Γ sort}
    {after : Configuration (Term (signature S (target locals captures)) Γ sort) O}
    {afterRows : O → ContextualStoredRows.Row locals (target locals captures) Γ sort}
    {afterOccupied : Finset Nat}
    (step : Step locals captures occupied rule rows before outputs after afterRows afterOccupied)
    (candidate : Assignment (target locals captures) next)
    (solved : ContextualFrameUnifier.Models candidate after.equations) :
    ContextualFrameUnifier.Models
      (Assignment.compose candidate (ContextualSelectionViews.capturedTarget locals captures)) before.equations := by
  obtain ⟨selection, _, rfl, _, _⟩ := step
  exact models_refine_old_frame locals captures next occupied selection rule rows before candidate solved

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ContextualActivatedStep
