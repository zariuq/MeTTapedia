import Mettapedia.Languages.ProcessCalculi.MORK.VariantReadout
import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixScopes

/-!
# Readout and inverse transport of actual source answers

A single basis covers printed output and returned answers. Readout leaves the
world and unread input intact and preserves fault/suspension constructors.
Displayed labels are not executable logical identities: inverse transport
recovers the original sharing before continuation in the originating world.
Readout construction is not asserted to be free or part of evaluator fuel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.AnswerReadout

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Unifying
open Mettapedia.Languages.ProcessCalculi.MORK

theorem rename_as_variable_map (scope : Nat) : ∀ term : Atom,
    Unifying.rename scope term = AtomRenaming.rename (freshName scope) term
  | .var _ | .symbol _ | .grounded _ => rfl
  | .expression items => by
      simp only [Unifying.rename,AtomRenaming.rename]
      exact congrArg Atom.expression (list items)
where
  list : ∀ items : List Atom,
      Unifying.rename.renameList scope items = AtomRenaming.rename.list (freshName scope) items
    | [] => rfl
    | first :: rest => by
        simp only [Unifying.rename.renameList,AtomRenaming.rename.list,rename_as_variable_map scope first,list rest]

theorem normalize_rename_apart (scope : Nat) (term : Atom) :
    VariantReadout.normalize (Unifying.rename scope term) = VariantReadout.normalize term := by
  rw [rename_as_variable_map]
  apply VariantReadout.normalize_rename
  intro first _ second _ same
  exact ((ScopedSource.freshName_equal_iff scope scope first second).mp same).2

/-- Copying isolates answers from each other, but preserves each answer's own
variable-sharing pattern. The joint observer can still see that isolation. -/
theorem each_copies (scope : Nat) : ∀ answers : List Answer,
    VariantReadout.each (copies scope answers) = answers.map (fun answer => VariantReadout.normalize (resolve answer.bindings answer.value))
  | [] => rfl
  | answer :: rest => by
      simp only [copies,VariantReadout.each,List.map_cons,normalize_rename_apart]
      exact congrArg (List.cons _) (each_copies (scope + 1) rest)

structure Completion where
  state : Effects.State
  input : List Atom
  outputCount : Nat
  packet : VariantReadout.Packet

def completed (state : Effects.State) (answers input output : List Atom) : Completion :=
  ⟨state,input,output.length,VariantReadout.pack (output ++ answers)⟩

def displayedOutput (view : Completion) : List Atom := view.packet.values.take view.outputCount
def displayedAnswers (view : Completion) : List Atom := view.packet.values.drop view.outputCount

inductive View where
  | complete (value : Completion)
  | exhausted (configuration : Configuration)
  | fault (reason : Effects.Fault) (configuration : Configuration)

def read : Outcome → View
  | .complete state answers input output => .complete (completed state answers input output)
  | .exhausted configuration => .exhausted configuration
  | .fault reason configuration => .fault reason configuration

def restore : View → Outcome
  | .complete view =>
      let values := VariantReadout.restore view.packet
      .complete view.state (values.drop view.outputCount) view.input (values.take view.outputCount)
  | .exhausted configuration => .exhausted configuration
  | .fault reason configuration => .fault reason configuration

theorem restore_read (outcome : Outcome) : restore (read outcome) = outcome := by
  cases outcome <;> simp [read,restore,completed,VariantReadout.restore_pack]

theorem read_injective : Function.Injective read := by
  intro first second same
  simpa only [restore_read] using congrArg restore same

theorem completed_keeps_world (state : Effects.State) (answers input output : List Atom) :
    (completed state answers input output).state = state ∧
      (completed state answers input output).input = input := ⟨rfl,rfl⟩

theorem displayed_output_length (state : Effects.State) (answers input output : List Atom) :
    (displayedOutput (completed state answers input output)).length = output.length := by
  simp [displayedOutput,completed,VariantReadout.pack_length]

theorem displayed_answer_length (state : Effects.State) (answers input output : List Atom) :
    (displayedAnswers (completed state answers input output)).length = answers.length := by
  simp [displayedAnswers,completed,VariantReadout.pack_length]

/-- Branch substitutions remain attached even when their variables do not
occur in the displayed value. An enclosing continuation can still read them. -/
structure BranchPacket where
  bindings : List Subst
  payload : VariantReadout.Packet

def packAnswers (answers : List Answer) : BranchPacket :=
  ⟨answers.map (·.bindings),VariantReadout.pack (answers.map (·.value))⟩

def restoreAnswers (packet : BranchPacket) : List Answer :=
  List.zipWith (fun value bindings => ⟨value,bindings⟩) (VariantReadout.restore packet.payload) packet.bindings

theorem restore_packAnswers (answers : List Answer) : restoreAnswers (packAnswers answers) = answers := by
  simp only [restoreAnswers,packAnswers,VariantReadout.restore_pack]
  induction answers with
  | nil => rfl
  | cons answer rest ih =>
      cases answer
      simpa only [List.map_cons,List.zipWith_cons_cons] using congrArg (List.cons _) ih

/-- Re-entry uses both the inverse basis and each branch's own substitution.
Displayed names alone are not references into the originating world. -/
def resume (source : Configuration) (packet : BranchPacket) : Configuration :=
  {source with control := .returned (restoreAnswers packet)}

theorem resume_pack (source : Configuration) (answers : List Answer) :
    resume source (packAnswers answers) = {source with control := .returned answers} := by
  simp only [resume,restore_packAnswers]

/-- Exact configuration recovery preserves any existing source continuation,
including effects, errors and finite cutoffs. This does not erase readout cost. -/
theorem run_after_transport (registry : SpaceSemantics.Program) (fuel : Nat)
    (source : Configuration) (answers : List Answer) :
    run registry fuel (resume source (packAnswers answers)) =
      run registry fuel {source with control := .returned answers} := by
  rw [resume_pack]

end Mettapedia.Languages.MeTTa.PeTTa.AnswerReadout
