import Mettapedia.Languages.MeTTa.PeTTa.Eval

/-!
# Completed stream collection and inert dynamic superposition

Literal superposition evaluates each authored branch. Its dynamic primitive
instead unpacks the evaluated tuple as values. `unique` collects the entire
producer, preserves its state and I/O, and returns the first occurrences
without executing their syntax a second time. The eleven-frame-exit steps
are evaluator transitions, not a physical deduplication cost bound.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.StreamSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Eval SpaceSemantics

def unique (body : Atom) : Atom := .expression [.symbol "unique", body]

theorem unique_finish_run (program : Program) (bindings : Subst) (state : Effects.State)
    (answers input output : List Atom) :
    run program 11 {state, control := .returned answers, frames := uniqueFrames bindings, input, output} =
      .complete state answers.eraseDups input output := by
  rfl

theorem unique_finish (program : Program) (bindings : Subst) (state : Effects.State)
    (answers input output : List Atom) :
    (theory program).MultiStep
      {state, control := .returned answers, frames := uniqueFrames bindings, input, output}
      (finished state answers.eraseDups input output) :=
  (completed_run_iff_path program _ state answers.eraseDups input output).mp
    ⟨11, unique_finish_run program bindings state answers input output⟩

private theorem trans {system : Mettapedia.GSLT.GSLT} {a b c : system.Term}
    (first : system.MultiStep a b) (second : system.MultiStep b c) : system.MultiStep a c := by
  induction first with
  | refl _ => exact second
  | step step _ ih => exact .step step (ih second)

theorem unique_path (program : Program) (bindings : Subst) (before after : Effects.State)
    (body : Atom) (answers oldInput oldOutput input output : List Atom)
    (produced : (theory program).MultiStep
      {state := before, control := .evaluate bindings body, input := oldInput, output := oldOutput}
      (finished after answers input output)) :
    (theory program).MultiStep
      {state := before, control := .evaluate bindings (unique body), input := oldInput, output := oldOutput}
      (finished after answers.eraseDups input output) := by
  refine .step (.unique_enter rfl) (trans ?_ (unique_finish program bindings after answers input output))
  simpa only [withFrames, finished, List.nil_append, List.append_nil] using path_with_caller_frames program (uniqueFrames bindings) produced

theorem unique_returns (program : Program) (bindings : Subst) (before after : Effects.State)
    (body : Atom) (answers : List Atom) (produced : Returns program bindings before body after answers) :
    Returns program bindings before (unique body) after answers.eraseDups :=
  unique_path program bindings before after body answers [] [] [] [] produced

theorem dynamic_superpose_returns (program : Program) (bindings : Subst) (state : Effects.State)
    (name : String) (items : List Atom) (captured : Subst.lookup bindings name = some (.expression items)) :
    Returns program bindings state (.expression [.symbol "superpose", .var name]) state items := by
  apply application_answers program bindings state state "superpose" [.var name] items
    (by simp [StdLib.known]) _ rfl
  apply variable_arguments_answers program bindings state state (.function "superpose") [name] [] 0 items
  simpa only [List.nil_append, List.map_cons, List.map_nil, List.length_cons, List.length_nil, Nat.zero_add,
    applySubst, captured, Option.getD_some] using
    native_function_arguments_answers program bindings state state "superpose" [.expression items] 1 items (by decide) (by decide) rfl

theorem dynamic_superpose_keeps_multiplicity (state : Effects.State) (value : Atom) :
    StdLib.apply state "superpose" [.expression [value, value]] = .ok (state, [value, value]) := rfl

theorem unique_keeps_support (answers : List Atom) (value : Atom) : value ∈ answers.eraseDups ↔ value ∈ answers := by simp

theorem unique_empty_iff (answers : List Atom) : answers.eraseDups = [] ↔ answers = [] := by
  constructor
  · intro empty
    cases answers with
    | nil => rfl
    | cons first rest =>
        have present : first ∈ (first :: rest).eraseDups := by simp
        rw [empty] at present
        cases present
  · rintro rfl; rfl

theorem unique_native_collection (state : Effects.State) (answers : List Atom) :
    StdLib.apply state "unique-atom" [.expression answers] = .ok (state, [.expression answers.eraseDups]) := rfl

end Mettapedia.Languages.MeTTa.PeTTa.StreamSource
