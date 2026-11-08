import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnPreparation
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedQueryReturn

/-!
# Return obligations through actual local source transitions

The protected source variable stays related to an observation of the reached
equations. Either its output equation has already been earned, or its return
continuation is still pending. The observation may be a constant or the
current read of an open caller slot; those are intentionally different laws.
Prefix code may be arbitrary and argument-return delimiters may skip younger
work. Sequential-let is handled by the existing outer surface owner before
this local component is invoked.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnLocal

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ProtectedSlots RefinementTransport
open ScopedReturnObligation (Pending AtHead)

def Reads (bindings : Equations) (recipe : Atom) (observation : Environment → Atom) : Prop :=
  ∀ environment, Solves environment bindings → read environment recipe = observation environment

theorem Reads.extends {before after : Equations} {recipe : Atom} {observation : Environment → Atom}
    (reads : Reads before recipe observation) (extended : Extends before after) : Reads after recipe observation :=
  fun environment solved => reads environment (extended environment solved)

theorem Reads.refined_destination {before after : Equations} {recipe destination : Atom}
    {observation : Environment → Atom} (reads : Reads before recipe observation)
    (returned : Refinement before recipe destination (some after)) : Reads after destination observation := by
  intro environment solved
  cases returned with
  | accepted witness old same =>
      have equations := (solves_append_equation _ _ _ _).mp solved
      exact equations.2.symm.trans (reads environment equations.1)

def Holds (name : String) (observation : Environment → Atom) (control : Control) : Prop :=
  Reads control.bindings (.var name) observation ∧
    (Reads control.bindings control.destination observation ∨ Pending (.var name) control.destination control.goals)

/-- The local theorem's sequential-let exclusion is earned by the actual
outer dispatch. Both valid and malformed sequences are owned there. -/
theorem local_sequence_exclusion {Context : Type} (source : ScopedCursor Context)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (control : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (scopes : source.2.scopes = scope :: parents)
    (frontier : scope.frontier = (control, context, origins) :: pending)
    (ordinary : ScopedQuerySource.syntaxStep source = none) :
    ∀ pairs body destination older,
      control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older := by
  intro pairs body destination older atSequence
  simp only [ScopedQuerySource.syntaxStep, scopes, frontier, atSequence] at ordinary
  cases parsed : Eval.nestedLets pairs body <;> simp [parsed] at ordinary

theorem silent_destination {Context : Type} {policy : Policy} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (step : Source.Step policy program before (.silent after)) :
    after.control.destination = before.control.destination := by
  cases step with
  | expanded expression destination older next atGoal ordinary prepared => exact prepared.retains_frame.2.1
  | argument value destination younger older action atGoal returned => cases returned <;> rfl
  | restoring | accepted | conditional | printed => rfl

/-- This is the actual local step family, including propagated-error returns.
No source-output list or invariant of a callee is supplied as an oracle. -/
theorem silent_preserves {Context : Type} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (name : String) (observation : Environment → Atom)
    (holds : Holds name observation before.control)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (step : Source.Step .eagerValue program before (.silent after)) : Holds name observation after.control := by
  have extended : Extends before.control.bindings after.control.bindings :=
    local_step_extends step _ (by simp [localRecords])
  refine ⟨holds.1.extends extended, ?_⟩
  rcases holds.2 with realized | pending
  · left
    rw [silent_destination step]
    exact realized.extends extended
  · cases step with
    | restoring boundary older atGoal =>
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · cases head
        · exact .inr tail
    | expanded expression destination older next atGoal ordinary prepared =>
        right
        rw [prepared.retains_frame.2.1]
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · rcases head with ⟨same, returns⟩
          rw [← same]
          apply ScopedReturnPreparation.prepared_variable_return program before.control next name expression
            destination older returns ordinary _ prepared
          intro pairs body identical
          apply noSequence pairs body destination older
          simpa only [identical] using atGoal
        · exact tail.prepared_prefix prepared
    | accepted expression destination older bindings atGoal matched =>
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · rcases head with ⟨same, recipe⟩
          left
          change Reads bindings before.control.destination observation
          rw [← same]
          apply Reads.refined_destination holds.1
          simpa only [recipe] using matched
        · exact .inr tail
    | conditional condition yes no destination older environment atGoal resolved =>
        right
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · rcases head with ⟨same, yesReturn, noReturn⟩
          change Pending (.var name) before.control.destination
            (.evaluate (if read environment condition == Effects.boolean true then yes else no) destination :: older)
          rw [← same]
          apply Pending.evaluation
          split <;> assumption
        · exact tail.prepend_evaluation _ _
    | printed arguments destination older environment printed atGoal resolved readout =>
        rcases pending.head_or_tail _ _ atGoal with head | tail
        · simp [AtHead] at head
        · exact .inr (tail.prepend_equation _ _)
    | argument expression destination younger older action atGoal returned =>
        cases returned with
        | ordinary environment resolved normal =>
            rcases pending.head_or_tail _ _ atGoal with head | tail
            · cases head
            · exact .inr tail
        | propagated environment resolved error bindings matched =>
            exact .inr (pending.return_delimiter expression destination older.length (younger ++ older) older
              atGoal (callerSuffix?_split younger older))

theorem terminal_observation {Context : Type} (name : String) (observation : Environment → Atom) (cursor : Cursor Context)
    (holds : Holds name observation cursor.control) (terminal : cursor.control.goals = [])
    (environment : Environment) (resolved : resolve cursor.control.bindings = some environment) :
    read environment cursor.control.destination = observation environment := by
  rcases holds.2 with realized | pending
  · exact realized environment (resolve_sound resolved)
  · exact False.elim (pending.nonempty terminal)

/-- Equal contexts need not have equal input values or the same fresh clause
names. Each occurrence carries its own reached ground-input witness. -/
def InputHolds (argument : Atom) (control : Control) : Prop :=
  ∃ name value, (encode value).isGround ∧ Fixed control.bindings argument value ∧ Holds name (fun _ => value) control

theorem input_silent_preserves {Context : Type} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (argument : Atom)
    (holds : InputHolds argument before.control)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (step : Source.Step .eagerValue program before (.silent after)) : InputHolds argument after.control := by
  obtain ⟨name, value, ground, inputFixed, returning⟩ := holds
  have extended : Extends before.control.bindings after.control.bindings :=
    local_step_extends step _ (by simp [localRecords])
  exact ⟨name, value, ground, inputFixed.extends extended,
    silent_preserves name (fun _ => value) returning noSequence step⟩

theorem terminal_input_observation {Context : Type} (argument : Atom) (cursor : Cursor Context)
    (holds : InputHolds argument cursor.control) (terminal : cursor.control.goals = [])
    (environment : Environment) (resolved : resolve cursor.control.bindings = some environment) :
    read environment cursor.control.destination = read environment argument ∧
      (encode (read environment cursor.control.destination)).isGround := by
  obtain ⟨name, value, ground, inputFixed, returning⟩ := holds
  have output := terminal_observation name (fun _ => value) cursor returning terminal environment resolved
  rw [output, inputFixed environment (resolve_sound resolved)]
  exact ⟨rfl, ground⟩

/-- This source property is meaningful for open inputs too. It does not say
that an input's type, or even its read value, stayed the same since entry. -/
def AliasHolds (argument : Atom) (control : Control) : Prop :=
  ∃ name, Holds name (fun environment => read environment argument) control

theorem alias_silent_preserves {Context : Type} {program : SpaceSemantics.Program}
    {before after : Cursor Context} (argument : Atom) (holds : AliasHolds argument before.control)
    (noSequence : ∀ pairs body destination older,
      before.control.goals ≠ .evaluate (.expression [.symbol "let*", .expression pairs, body]) destination :: older)
    (step : Source.Step .eagerValue program before (.silent after)) : AliasHolds argument after.control := by
  obtain ⟨name, returning⟩ := holds
  exact ⟨name, silent_preserves name _ returning noSequence step⟩

theorem terminal_alias_observation {Context : Type} (argument : Atom) (cursor : Cursor Context)
    (holds : AliasHolds argument cursor.control) (terminal : cursor.control.goals = [])
    (environment : Environment) (resolved : resolve cursor.control.bindings = some environment) :
    read environment cursor.control.destination = read environment argument := by
  obtain ⟨name, returning⟩ := holds
  exact terminal_observation name _ cursor returning terminal environment resolved

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnLocal
