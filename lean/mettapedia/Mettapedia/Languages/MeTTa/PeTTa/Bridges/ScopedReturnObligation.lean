import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnSyntax
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnDepth

/-!
# Pending return obligations in source continuations

The obligation may be behind arbitrary pending work. Argument-return
delimiters in that work are shifted around the retained suffix, using the
existing continuation operation. Thus this is not a no-delimiter admission
restriction. The value observation is earned when the recipe is delivered;
the all-transition scoped invariant is a separate theorem to be composed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnObligation

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open EagerDFSStreaming.Scoped.ProtectedContinuation
open ScopedReturnSyntax (Returns)

inductive Pending (recipe destination : Atom) : List Goal → Prop where
  | evaluation (expression : Atom) (older : List Goal) (returns : Returns recipe expression) :
      Pending recipe destination (.evaluate expression destination :: older)
  | equation (older : List Goal) : Pending recipe destination (.equate recipe destination :: older)
  | conditional (condition yes no : Atom) (older : List Goal)
      (yesReturn : Returns recipe yes) (noReturn : Returns recipe no) :
      Pending recipe destination (.branch condition yes no destination :: older)
  | query (space pattern body : Atom) (older : List Goal) (returns : Returns recipe body) :
      Pending recipe destination (.query space pattern body destination :: older)
  | readyQuery (space pattern body : Atom) (older : List Goal) (returns : Returns recipe body) :
      Pending recipe destination (.invoke "match" [space, pattern, body] destination :: older)
  | readyCase (key : Atom) (rows : List Atom) (cases : SpaceSemantics.Cases) (older : List Goal)
      (parsed : Eval.readCases rows = some cases) (returns : ∀ row ∈ cases, Returns recipe row.2) :
      Pending recipe destination (.invoke "case" [key, .expression rows] destination :: older)
  | attached (younger suffix : List Goal) (pending : Pending recipe destination suffix) :
      Pending recipe destination (younger.map (shift suffix.length) ++ suffix)

def AtHead (recipe target : Atom) : Goal → Prop
  | .evaluate expression destination => destination = target ∧ Returns recipe expression
  | .equate value destination => destination = target ∧ value = recipe
  | .branch _ yes no destination => destination = target ∧ Returns recipe yes ∧ Returns recipe no
  | .query _ _ body destination => destination = target ∧ Returns recipe body
  | .invoke "match" [_, _, body] destination => destination = target ∧ Returns recipe body
  | .invoke "case" [_, .expression rows] destination =>
      destination = target ∧ ∃ cases, Eval.readCases rows = some cases ∧ ∀ row ∈ cases, Returns recipe row.2
  | _ => False

theorem Pending.head_or_tail {recipe target : Atom} {goals : List Goal}
    (pending : Pending recipe target goals) : ∀ head older, goals = head :: older →
      AtHead recipe target head ∨ Pending recipe target older := by
  induction pending with
  | evaluation expression older returns => intro head rest same; cases same; exact .inl ⟨rfl, returns⟩
  | equation older => intro head rest same; cases same; exact .inl ⟨rfl, rfl⟩
  | conditional condition yes no older yesReturn noReturn =>
      intro head rest same; cases same; exact .inl ⟨rfl, yesReturn, noReturn⟩
  | query space pattern body older returns => intro head rest same; cases same; exact .inl ⟨rfl, returns⟩
  | readyQuery space pattern body older returns => intro head rest same; cases same; exact .inl ⟨rfl, returns⟩
  | readyCase key rows cases older parsed returns => intro head rest same; cases same; exact .inl ⟨rfl, cases, parsed, returns⟩
  | attached younger suffix pending ih =>
      intro head older same
      cases younger with
      | nil => exact ih head older (by simpa using same)
      | cons first rest =>
          simp only [List.map_cons, List.cons_append, List.cons.injEq] at same
          exact .inr (same.2 ▸ Pending.attached rest suffix pending)

theorem Pending.nonempty {recipe destination : Atom} {goals : List Goal}
    (pending : Pending recipe destination goals) : goals ≠ [] := by
  induction pending <;> simp_all

theorem Pending.prepend {recipe destination : Atom} {goals : List Goal}
    (pending : Pending recipe destination goals) (younger : List Goal)
    (unchanged : younger.map (shift goals.length) = younger) :
    Pending recipe destination (younger ++ goals) := by
  rw [← unchanged]
  exact .attached younger goals pending

theorem Pending.prepend_evaluation {recipe destination : Atom} {goals : List Goal}
    (pending : Pending recipe destination goals) (expression output : Atom) :
    Pending recipe destination (.evaluate expression output :: goals) := by
  simpa only [List.singleton_append] using pending.prepend [.evaluate expression output] rfl

theorem Pending.prepend_equation {recipe destination : Atom} {goals : List Goal}
    (pending : Pending recipe destination goals) (value output : Atom) :
    Pending recipe destination (.equate value output :: goals) := by
  simpa only [List.singleton_append] using pending.prepend [.equate value output] rfl

/-- The real finite delimiter retains the same suffix after selecting its
older work. Invalid delimiters remain invalid on both sides. -/
theorem callerSuffix_attached (younger suffix : List Goal) (depth : Nat) :
    callerSuffix? (depth + suffix.length) (younger.map (shift suffix.length) ++ suffix) =
      (callerSuffix? depth younger).map (fun older => older.map (shift suffix.length) ++ suffix) := by
  simp only [callerSuffix?, List.length_append, List.length_map]
  by_cases valid : depth ≤ younger.length
  · have shiftedValid : depth + suffix.length ≤ younger.length + suffix.length := by omega
    simp only [if_pos valid, if_pos shiftedValid, Nat.add_sub_add_right, List.drop_append,
      List.map_drop, Option.map_some, List.length_map]
    rw [Nat.sub_eq_zero_of_le (Nat.sub_le _ _)]
    rfl
  · have shiftedInvalid : ¬ depth + suffix.length ≤ younger.length + suffix.length := by omega
    simp only [if_neg valid, if_neg shiftedInvalid, Option.map_none]

theorem Pending.after_delimiter {recipe destination : Atom} {suffix : List Goal}
    (pending : Pending recipe destination suffix) (younger : List Goal) (depth : Nat) (older : List Goal)
    (selected : callerSuffix? (depth + suffix.length)
      (younger.map (shift suffix.length) ++ suffix) = some older) : Pending recipe destination older := by
  rw [callerSuffix_attached] at selected
  obtain ⟨retained, _actual, rfl⟩ := Option.map_eq_some_iff.mp selected
  exact .attached retained suffix pending

/-- A source argument-return may skip younger work, but not the pending
return retained behind its shifted delimiter. -/
theorem Pending.return_delimiter {recipe target : Atom} {goals : List Goal}
    (pending : Pending recipe target goals) :
    ∀ value destination depth remaining older,
      goals = .argumentReturn value destination depth :: remaining →
      callerSuffix? depth remaining = some older → Pending recipe target older := by
  induction pending with
  | evaluation | equation | conditional | query | readyQuery | readyCase =>
      intro value destination depth remaining older same selected
      cases same
  | attached younger suffix pending ih =>
      intro value destination depth remaining older same selected
      cases younger with
      | nil => exact ih value destination depth remaining older (by simpa using same) selected
      | cons first rest =>
          cases first <;> simp only [List.map_cons, shift, List.cons_append] at same
          all_goals cases same
          exact pending.after_delimiter rest _ older selected

theorem binding_preparation {recipe destination : Atom} {body : Atom} (returns : Returns recipe body)
    (program : SpaceSemantics.Program) (pattern producer joined : Atom) (older : List Goal) :
    Pending recipe destination (letGoals .eagerValue program pattern producer body destination joined ++ older) := by
  exact ((Pending.evaluation body older returns).prepend_equation pattern joined).prepend_evaluation producer joined

theorem conditional_preparation {recipe destination : Atom} {yes no : Atom}
    (yesReturn : Returns recipe yes) (noReturn : Returns recipe no)
    (condition tested : Atom) (older : List Goal) :
    Pending recipe destination (.evaluate condition tested :: .branch tested yes no destination :: older) :=
  (Pending.conditional tested yes no older yesReturn noReturn).prepend_evaluation condition tested

theorem conditional_absent_preparation {recipe destination : Atom} {yes : Atom}
    (yesReturn : Returns recipe yes) (condition tested : Atom) (older : List Goal) :
    Pending recipe destination (.evaluate condition tested ::
      .branch tested yes (.expression [.symbol "empty"]) destination :: older) :=
  conditional_preparation yesReturn .empty condition tested older

/-- Expanding arbitrary prefix code leaves the pending return behind it.
This is earned for every actual syntax-preparation rule, not a premise that
the prefix terminates or produces a prescribed result. -/
theorem Pending.prepared_prefix {recipe target : Atom} {older : List Goal}
    (pending : Pending recipe target older) {policy : Policy} {program : SpaceSemantics.Program}
    {control next : Control} {destination expression : Atom}
    (prepared : Source.Prepared policy program control destination older expression next) :
    Pending recipe target next.goals := by
  cases prepared with
  | variableValue name => exact pending.prepend_equation _ _
  | symbol name => exact pending.prepend_equation _ _
  | grounded value => exact pending.prepend_equation _ _
  | quotation value => exact pending.prepend_equation _ _
  | binding pattern producer body =>
      exact pending.prepend _ (shift_letGoals _ _ _ _ _ _ _ _)
  | cut => exact pending.prepend [.commit, .equate (Effects.boolean true) destination] rfl
  | once child =>
      exact pending.prepend [.openCommit, .evaluate child destination, .commit, .restoreCommit control.cutBoundary] rfl
  | conditional condition yes no =>
      exact pending.prepend [.evaluate condition (.var (freshName control 0)),
        .branch (.var (freshName control 0)) yes no destination] rfl
  | conditionalWithoutElse condition yes =>
      exact pending.prepend [.evaluate condition (.var (freshName control 0)),
        .branch (.var (freshName control 0)) yes (.expression [.symbol "empty"]) destination] rfl
  | application head arguments ordinary declared =>
      let work := callArguments program head arguments (freshSlots control arguments.length)
      have preserve := pending.prepend (work.1 ++ [.invoke head work.2 destination]) (by
        simp only [work, List.map_append, shift_callArguments, List.map_cons, List.map_nil, shift])
      simpa only [replace, work, List.append_assoc, List.singleton_append] using preserve
  | construction head arguments ordinary data =>
      cases policy with
      | relational =>
          exact pending.prepend _ (by simp only [List.map_cons, shift, List.map_map, Function.comp_def])
      | eagerValue =>
          exact pending.prepend _ (by simp only [List.map_append, List.map_cons, List.map_nil, shift,
            List.map_map, Function.comp_def])
  | tuple children noHead =>
      exact pending.prepend _ (shift_dataGoals _ _ _ _ _)

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedReturnObligation
