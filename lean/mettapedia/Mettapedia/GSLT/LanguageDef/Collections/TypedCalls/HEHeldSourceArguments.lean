import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEIfSourceSelection

/-!
# Held branch delivery under retained contextual frames

An Atom formal delivers its authored syntax. The conditional's branch packet
therefore keeps both branch programs inert while its Bool condition is run.
These are compositions of the existing source argument rules.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Spec.Eval Spec.Eval.Completed

theorem metatype (value : Entry.Value) : ∃ type, MetaTypeRel value.erase type := by
  cases value with
  | symbol name => exact ⟨_, by simpa only [Entry.Value.erase] using MetaTypeRel.symbol name⟩
  | var name => exact ⟨_, by simpa only [Entry.Value.erase] using MetaTypeRel.variable name⟩
  | grounded value => exact ⟨_, by simpa only [Entry.Value.erase] using MetaTypeRel.grounded value⟩
  | expression status children =>
      exact ⟨_, by simpa only [Entry.Value.erase] using MetaTypeRel.expression (children.map Entry.Value.erase)⟩

theorem held {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (value : Entry.Value) (before : Frame) :
    Stateful.AtomRel environment label world live scope value Atom.atomType before
      [(before.read policy value, before)] world (policy := policy) := by
  apply Stateful.AtomRel.delivered
  by_cases stopped : IsEmptyOrErrorRel (before.read policy value).erase
  · exact .stopped stopped
  · obtain ⟨type, intrinsic⟩ := metatype (before.read policy value)
    exact .pass stopped intrinsic (Or.inl rfl)

/-- Two held arguments are delivered unchanged when their whole annotated
values are fixed by the reached frame. No purity or evaluator-result premise
is involved, and the caller's live syntax is kept in each child boundary. -/
theorem pair {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (yes no : Entry.Value) (before : Frame)
    (yesRead : before.read policy yes = yes) (noRead : before.read policy no = no) :
    Stateful.ArgumentsRel environment label world live scope
      [(yes, Atom.atomType), (no, Atom.atomType)] before
      [(Entry.Value.argumentPacket [yes, no], before)] world (policy := policy) := by
  have yesHeld := held environment policy label world
    (argumentScope [(no, Atom.atomType)] ++ live) scope yes before
  have noHeld := held environment policy label world
    (argumentScope [] ++ yes.erase :: live) scope no before
  rw [yesRead] at yesHeld
  rw [noRead] at noHeld
  have noContinue : ¬ArgumentStopped no (no, before) := by
    simp [ArgumentStopped]
  have yesContinue : ¬ArgumentStopped yes (yes, before) := by
    simp [ArgumentStopped]
  have tail : Stateful.ArgumentsRel environment label world (yes.erase :: live) scope
      [(no, Atom.atomType)] before [(Entry.Value.argumentPacket [no], before)] world (policy := policy) := by
    apply Stateful.ArgumentsRel.cons noHeld
    simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
      (Stateful.ArgumentBranchesRel.continuing (head := (no, before)) noContinue
        (Stateful.ArgumentsRel.nil (frame := before)) Stateful.ArgumentBranchesRel.nil)
  apply Stateful.ArgumentsRel.cons yesHeld
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    (Stateful.ArgumentBranchesRel.continuing (head := (yes, before)) yesContinue tail
      Stateful.ArgumentBranchesRel.nil)

theorem conditional {Context World : Type} (environment : WorldEnvironment Context World)
    (policy : Policy) (label : Context) (world : World) (live : List Atom) (scope : List String)
    (condition yes no : Entry.Value) (before : Frame) (answer : Bool)
    (yesRead : before.read policy yes = yes) (noRead : before.read policy no = no)
    (conditionRun : Stateful.AtomRel environment label world
      (argumentScope [(yes, Atom.atomType), (no, Atom.atomType)] ++ live) scope
      condition (.symbol "Bool") before [(.grounded (.bool answer), before)] world (policy := policy)) :
    Stateful.ArgumentsRel environment label world live scope
      [(condition, .symbol "Bool"), (yes, Atom.atomType), (no, Atom.atomType)] before
      [(Entry.Value.argumentPacket [.grounded (.bool answer), yes, no], before)] world
      (policy := policy) := by
  apply Stateful.ArgumentsRel.cons conditionRun
  have rest := pair environment policy label world ((Entry.Value.grounded (.bool answer)).erase :: live)
    scope yes no before yesRead noRead
  simpa only [List.map_cons, List.map_nil, List.append_nil, argumentPrepend_packet] using
    (Stateful.ArgumentBranchesRel.continuing (head := (Entry.Value.grounded (.bool answer), before))
      (by simp [ArgumentStopped, Entry.Value.erase, IsEmptyOrErrorRel, IsErrorRel, Atom.empty])
      rest Stateful.ArgumentBranchesRel.nil)

theorem ground_read (policy : Policy) (before : Frame) (value : Atom)
    (closed : Spec.Type.Presentation.TypeSubst.typeVars value = []) :
    before.read policy (Entry.Value.ofAtom value) = Entry.Value.ofAtom value := by
  apply Frame.read_variable_free
  intro name occurs
  have member := Spec.Eval.Steps.atomOccurs_mem_typeVars occurs
  simp only [Entry.Value.erase_ofAtom, closed, List.not_mem_nil] at member

namespace Range

open HEIfSourceSelection.Range HEBinaryNumericSource
open HEFreshEquationFrames.Range (number)

/-- The actual range conditional evaluates comparison and retains both
authored branches, under any reached alias-bearing caller frame. -/
theorem arguments (services : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (lower upper : Int) :
    Stateful.ArgumentsRel (primitiveEnvironment services) space () live scope
      [(Entry.Value.ofAtom (condition lower upper), .symbol "Bool"),
       (Entry.Value.ofAtom yes, Atom.atomType), (Entry.Value.ofAtom (no lower upper), Atom.atomType)] before
      [(Entry.Value.argumentPacket [.grounded (.bool (decide (lower ≥ upper))),
        Entry.Value.ofAtom yes, Entry.Value.ofAtom (no lower upper)], before)] () (policy := policy) := by
  apply conditional
  · exact ground_read policy before yes (by rfl)
  · exact ground_read policy before (no lower upper) (by rfl)
  · simpa only [condition, number, Entry.Value.ofAtom, Operation.call, greaterEqual,
      List.map_cons, List.map_nil] using
      comparison_source services policy space
        (argumentScope [(Entry.Value.ofAtom yes, Atom.atomType),
          (Entry.Value.ofAtom (no lower upper), Atom.atomType)] ++ live)
        scope before lower upper rfl

/-- Held recursive syntax is still present even when the comparison takes
the terminating branch. Merely delivering arguments does not run recursion. -/
theorem recursive_branch_retained (services : Minimal.Services) (policy : Policy) (before : Frame)
    (live : List Atom) (scope : List String) (bound : Int) :
    Stateful.ArgumentsRel (primitiveEnvironment services) space () live scope
      [(Entry.Value.ofAtom (condition bound bound), .symbol "Bool"),
       (Entry.Value.ofAtom yes, Atom.atomType), (Entry.Value.ofAtom (no bound bound), Atom.atomType)] before
      [(Entry.Value.argumentPacket [.grounded (.bool true),
        Entry.Value.ofAtom yes, Entry.Value.ofAtom (no bound bound)], before)] () (policy := policy) := by
  simpa only [ge_iff_le, le_refl, decide_true] using arguments services policy before live scope bound bound

end Range

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEHeldSourceArguments
