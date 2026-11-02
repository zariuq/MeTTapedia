import Mettapedia.Languages.MeTTa.PeTTa.Bridges.PureCallExtraction

/-!
# Pure zero-or-one source bodies and inert empty alternatives

The accepted result is itself optional: `some none` is a proved empty source
answer, whereas outer `none` refuses specialization. Alternative bodies are
checked separately and concatenated in source order. Two produced answers
are refused even when their Atom values are identical. Pure empty equations
can therefore be ignored by a singleton/empty observer only after their
actual source execution has been justified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.OptionalCallExtraction

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Eval SpaceSemantics

structure Certified (program : Program) (caller : Subst) (source : Atom) where
  value : Option Atom
  returns : ∀ state, Returns program caller state source state value.toList

def fromPure {program : Program} {caller : Subst} {source : Atom}
    (compiled : PureCallExtraction.Certified program caller source) : Certified program caller source :=
  ⟨some compiled.value, compiled.returns⟩

def empty (program : Program) (caller : Subst) :
    Certified program caller (.expression [.symbol "empty"]) :=
  ⟨none, fun state => empty_returns program caller state⟩

def singleton {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) : Option (PureCallExtraction.Certified program caller source) :=
  match value : compiled.value with
  | none => none
  | some answer => some ⟨answer, fun state => by simpa [value] using compiled.returns state⟩

private theorem path_trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

def branch {program : Program} {caller : Subst} {test yes no : Atom}
    (condition : PureCallExtraction.Certified program caller test) (flag : Bool)
    (boolean : condition.value = Effects.boolean flag)
    (chosen : Certified program caller (if flag then yes else no)) :
    Certified program caller (.expression [.symbol "if", test, yes, no]) where
  value := chosen.value
  returns state := by
    have tested := condition.returns state
    rw [boolean] at tested
    refine .step (step_transition rfl)
      (path_trans (path_with_caller_frames program [.branch caller yes no] tested) ?_)
    refine .step ?_ (single_sequence_answers program state state _ chosen.value.toList (chosen.returns state))
    apply step_transition
    cases flag <;> simp [step, withFrames, finished, Effects.boolean]

structure Alternatives (program : Program) (controls : List Control) where
  values : List Atom
  returns : ∀ state collected, (theory program).MultiStep
    {state, control := .sequence controls collected}
    (finished state (collected ++ values) [] [])

def Alternatives.nil (program : Program) : Alternatives program [] where
  values := []
  returns state collected := by
    simpa using (.step (step_transition rfl) (.refl _) : (theory program).MultiStep
      {state, control := .sequence [] collected} (finished state collected [] []))

def Alternatives.cons {program : Program} {caller : Subst} {source : Atom} {controls : List Control}
    (first : Certified program caller source) (rest : Alternatives program controls) :
    Alternatives program (.evaluate caller source :: controls) where
  values := first.value.toList ++ rest.values
  returns state collected := by
    simpa [List.append_assoc] using sequence_cons_answers program state state state
      (.evaluate caller source) controls collected first.value.toList
      ((collected ++ first.value.toList) ++ rest.values)
      (first.returns state) (rest.returns state (collected ++ first.value.toList))

theorem evaluated_arguments_answers (program : Program) (caller : Subst) (state : Effects.State)
    (head : String) (sources values : List Atom)
    (returns : List.Forall₂ (fun source value => PureReturns program caller state source state value)
      sources values) (prior : List Atom) (index : Nat) (answers : List Atom)
    (demand : ∀ offset < sources.length, argumentIsRaw program head (index + offset) = false)
    (rest : (theory program).MultiStep
      {state, control := .arguments caller (.function head) [] (prior ++ values) (index + sources.length)}
      (finished state answers [] [])) :
    (theory program).MultiStep
      {state, control := .arguments caller (.function head) sources prior index}
      (finished state answers [] []) := by
  induction returns generalizing prior index with
  | nil => simpa using rest
  | @cons source value sources values first later ih =>
      apply evaluated_argument_answers program caller state state state (.function head)
        source value answers sources prior index
        (by simpa using demand 0 (by simp)) first
      apply ih (prior ++ [value]) (index + 1)
      · intro offset bounded
        simpa [Nat.add_assoc, Nat.add_comm 1] using demand (offset + 1) (by simpa using bounded)
      · simpa [List.append_assoc, Nat.add_assoc, Nat.add_comm 1] using rest

def call {program : Program} {caller : Subst} {head : String} {sources : List Atom}
    {controls : List Control} (admitted : PureCallExtraction.Callable program head sources.length)
    (arguments : PureCallExtraction.Arguments program caller sources)
    (selected : application program head arguments.values = .sequence controls [])
    (alternatives : Alternatives program controls) (value : Option Atom)
    (singleton : alternatives.values = value.toList) :
    Certified program caller (.expression (.symbol head :: sources)) where
  value := value
  returns state := by
    apply call_answers program caller state state head sources value.toList
      (by simp [admitted.registered]) _ admitted.ordinary
    apply evaluated_arguments_answers program caller state head sources arguments.values
      (arguments.returns state) [] 0 value.toList (by simpa using admitted.demanded)
    have rest := alternatives.returns state []
    simp only [List.nil_append, singleton] at rest
    refine .step ?_ rest
    apply step_transition
    simp only [step, admitted.notIO, admitted.notNative, Bool.false_eq_true, ↓reduceIte,
      List.nil_append, selected]

def prepare : (fuel : Nat) → (program : Program) → (caller : Subst) →
    (source : Atom) → Option (Certified program caller source)
  | 0, _, _, _ => none
  | fuel + 1, program, caller, source =>
      match PureCallExtraction.prepare (fuel + 1) program caller source with
      | some compiled => some (fromPure compiled)
      | none => match source with
        | .expression [.symbol "empty"] => some (empty program caller)
        | .expression [.symbol "if", test, yes, no] => do
            let optional ← prepare fuel program caller test
            let condition ← singleton optional
            match boolean : condition.value with
            | .grounded (.bool flag) =>
                let chosen ← prepare fuel program caller (if flag then yes else no)
                return branch condition flag boolean chosen
            | _ => none
        | .expression [.symbol head, left, right] => do
            let leftOptional ← prepare fuel program caller left
            let first ← singleton leftOptional
            let rightOptional ← prepare fuel program caller right
            let second ← singleton rightOptional
            match PureCallExtraction.binary head first second with
            | some compiled => some (fromPure compiled)
            | none => authored program caller head [left, right] (prepare fuel program)
        | .expression (.symbol head :: sources) =>
            authored program caller head sources (prepare fuel program)
        | _ => none
where
  authored (program : Program) (caller : Subst) (head : String) (sources : List Atom)
      (compile : (bindings : Subst) → (source : Atom) → Option (Certified program bindings source)) :
      Option (Certified program caller (.expression (.symbol head :: sources))) := do
    let admitted ← PureCallExtraction.callable program head sources.length
    let arguments ← PureCallExtraction.prepare.arguments program caller
      (fun source => (compile caller source).bind singleton) sources
    match selected : application program head arguments.values with
    | .sequence controls [] =>
        let compiled ← alternatives program compile controls
        match shape : compiled.values with
        | [] => return call admitted.down arguments selected compiled none shape
        | [value] => return call admitted.down arguments selected compiled (some value) shape
        | _ => none
    | _ => none

  alternatives (program : Program)
      (compile : (caller : Subst) → (source : Atom) → Option (Certified program caller source)) :
      (controls : List Control) → Option (Alternatives program controls)
    | [] => some (Alternatives.nil program)
    | .evaluate caller source :: rest => do
        let first ← compile caller source
        let later ← alternatives program compile rest
        return Alternatives.cons first later
    | _ => none

theorem completed_iff {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (state after : Effects.State)
    (answers input output : List Atom) :
    (∃ fuel, run program fuel {state, control := .evaluate caller source} =
      .complete after answers input output) ↔
      after = state ∧ answers = compiled.value.toList ∧ input = [] ∧ output = [] :=
  path_completed_iff program _ state compiled.value.toList [] [] (compiled.returns state)
    after answers input output

theorem accepted_empty_is_source_empty {program : Program} {caller : Subst} {source : Atom}
    (compiled : Certified program caller source) (empty : compiled.value = none) (state : Effects.State) :
    ∃ fuel, run program fuel {state, control := .evaluate caller source} = .complete state [] [] [] := by
  apply (completed_iff compiled state state [] [] []).mpr
  simp [empty]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.OptionalCallExtraction
