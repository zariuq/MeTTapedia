import Mettapedia.Languages.MeTTa.PeTTa.UnifyingPrefixes

/-!
# Executed source controls for runtime heads and private partials

These compute the actual extended source machine, not a value-only application
oracle. The paired source fixtures calibrate the successful calls and runtime
exception boundary independently. Lambda authoring/installation, native partial
arity profiles and streaming operand scheduling remain distinct obligations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying.DynamicCallControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

def num (value : Int) : Atom := .grounded (.int value)
def sym (name : String) : Atom := .symbol name
def var (name : String) : Atom := .var name
def call (head : String) (arguments : List Atom) : Atom := .expression (.symbol head :: arguments)
def held (value : Atom) : Atom := call "quote" [value]
def bind (pattern initializer body : Atom) : Atom := call "let" [pattern, initializer, body]
def invoke (head : Atom) (arguments : List Atom) : Atom := .expression (head :: arguments)
def equation (head : String) (arguments : List Atom) (body : Atom) : Atom :=
  call "=" [call head arguments, body]

def execute (forms requested : List Atom) : Except String (List Shown) := do
  let program ← SpaceSemantics.collect forms
  pure ((requests program 600 (Effects.loaded program) requested).map shown)

def pair : Atom := equation "pair" [var "x", var "y"] (call "pair-value" [var "x", var "y"])
def forbidden : Atom := call "println!" [sym "forbidden"]

def basicRequests : List Atom :=
  [bind (var "f") (held (sym "+")) (invoke (var "f") [num 2, num 3]),
   bind (var "f") (call "pair" [num 10]) (invoke (var "f") [num 20]),
   bind (var "f") (call "pair" [held forbidden]) (invoke (var "f") [num 8]),
   bind (var "f") (call "pair" [var "x"])
     (bind (var "x") (num 7) (invoke (var "f") [num 8])),
   bind (var "f") (held (sym "missing")) (invoke (var "f") [num 7])]

theorem basic_source_results : execute [pair] basicRequests = .ok
    [.printed [] [num 5],
     .printed [] [call "pair-value" [num 10, num 20]],
     .printed [] [call "pair-value" [forbidden, num 8]],
     .printed [] [call "pair-value" [num 7, num 8]],
     .printed [] [call "missing" [num 7]]] := by
  decide +kernel

theorem public_partial_spelling_is_data :
    execute [pair] [bind (var "f") (held (call "partial" [sym "pair", .expression [num 10]]))
      (invoke (var "f") [num 20])] =
      .ok [.printed [] [invoke (call "partial" [sym "pair", .expression [num 10]]) [num 20]]] := by
  decide +kernel

theorem direct_private_partial_is_held :
    execute [pair] [Eval.partialValue "pair" [forbidden]] =
      .ok [.printed [] [Eval.partialValue "pair" [forbidden]]] := by
  decide +kernel

theorem runtime_lookup_sees_new_function :
    execute [] [bind (var "f") (held (sym "new-function"))
      (bind (var "ignored") (call "add-atom" [sym "&self", equation "new-function" [] (num 77)])
        (invoke (var "f") []))] = .ok [.printed [] [num 77]] := by
  decide +kernel

theorem fixed_written_head_keeps_translation_time_policy :
    execute [] [bind (var "ignored") (call "add-atom" [sym "&self", equation "new-function" [] (num 77)])
      (call "new-function" [])] = .ok [.printed [] [call "new-function" []]] := by
  decide +kernel

theorem removed_runtime_function_becomes_data :
    execute [pair] [bind (var "f") (held (sym "pair"))
      (bind (var "ignored") (call "remove-atom" [sym "&self", pair])
        (invoke (var "f") [num 7, num 8]))] =
      .ok [.printed [] [call "pair" [num 7, num 8]]] := by
  decide +kernel

def holdForm : Atom := equation "hold" [var "x"] (var "x")
def holdType : Atom := call ":" [sym "hold", call "->" [sym "Atom", sym "Atom"]]

theorem runtime_arguments_are_already_evaluated :
    execute [holdType, holdForm]
      [call "hold" [call "println!" [num 9]],
       bind (var "f") (held (sym "hold")) (invoke (var "f") [call "println!" [num 9]])] =
      .ok [.printed [] [call "println!" [num 9]], .printed [num 9] [Effects.boolean true]] := by
  decide +kernel

/-- Resolving the callee's name does not license switching to the written
head's raw-argument policy. The two requests have different effects/results. -/
theorem replacing_runtime_head_by_static_changes_observation :
    execute [holdType, holdForm]
      [bind (var "f") (held (sym "hold")) (invoke (var "f") [call "println!" [num 9]])] ≠
    execute [holdType, holdForm] [call "hold" [call "println!" [num 9]]] := by
  decide +kernel

def badForm : Atom := equation "bad" [var "x"] (call "+" [sym "bad-value", var "x"])

theorem runtime_callee_errors_are_caught :
    execute [badForm]
      [bind (var "f") (held (sym "+")) (call "collapse" [invoke (var "f") [sym "bad-value", num 3]]),
       bind (var "f") (held (sym "bad")) (call "collapse" [invoke (var "f") [num 3]])] =
      .ok [.printed [] [.expression []], .printed [] [.expression []]] := by
  decide +kernel

def alternatives : List Atom :=
  [equation "alternatives" [] (sym "first"),
   equation "alternatives" [] (bind (var "ignored") (call "add-atom" [sym "&self", call "mark" []])
     (call "+" [sym "bad-value", num 3]))]

theorem caught_error_keeps_completed_answers_and_effects :
    execute alternatives
      [bind (var "f") (held (sym "alternatives")) (call "collapse" [invoke (var "f") []]),
       call "collapse" [call "match" [sym "&self", call "mark" [], sym "present"]]] =
      .ok [.printed [] [.expression [sym "first"]], .printed [] [.expression [sym "present"]]] := by
  decide +kernel

theorem dynamic_over_application_is_outside_its_callee :
    execute [pair] [bind (var "f") (held (sym "pair")) (invoke (var "f") [num 1, num 2, num 3])] =
      .ok [.fault (.overApplication "pair" [2] 3)] := by
  decide +kernel

def recoveryProgram : SpaceSemantics.Program :=
  { equations :=
      [⟨"alternatives", [], sym "first"⟩,
       ⟨"alternatives", [], bind (var "ignored") (call "add-atom" [sym "&self", call "mark" []])
         (call "+" [sym "bad-value", num 3])⟩]
    declarations := []
    layout := [.equation, .equation] }

theorem collected_recovery_program : SpaceSemantics.collect alternatives = .ok recoveryProgram := by
  rfl

def recoveryRequest : Atom :=
  bind (var "f") (held (sym "alternatives")) (call "collapse" [invoke (var "f") []])

def recoveryStart : Configuration := start (Effects.loaded recoveryProgram) recoveryRequest

def recoveryPause? : Option Configuration :=
  match run recoveryProgram 46 recoveryStart with
  | .exhausted saved => some saved
  | _ => none

theorem recovery_pause_exists : recoveryPause?.isSome = true := by decide +kernel

/-- Extraction requires the proved suspended constructor; no default restart
configuration is substituted when a requested pause is unavailable. -/
def recoverySaved : Configuration := recoveryPause?.get recovery_pause_exists

def invalidArgument? : Control → Option String
  | .fault (.invalidArguments head) => some head
  | _ => none

theorem invalidArgument?_some (control : Control) (head : String) :
    invalidArgument? control = some head ↔ control = .fault (.invalidArguments head) := by
  constructor
  · intro recognized
    unfold invalidArgument? at recognized
    split at recognized
    · cases recognized
      rfl
    · cases recognized
  · rintro rfl
    rfl

theorem recovery_paused : run recoveryProgram 46 recoveryStart = .exhausted recoverySaved := by
  have suspended := recovery_pause_exists
  cases stopped : run recoveryProgram 46 recoveryStart with
  | complete state answers input output => simp [recoveryPause?, stopped] at suspended
  | fault reason saved => simp [recoveryPause?, stopped] at suspended
  | exhausted saved => simp [recoverySaved, recoveryPause?, stopped]

theorem recovery_pause_is_after_effect :
    recoverySaved.control = .fault (.invalidArguments "+") ∧
      recoverySaved.state.core.count (call "mark" []) = 1 := by
  constructor
  · exact (invalidArgument?_some _ _).mp (by decide +kernel)
  · decide +kernel

theorem recovery_retains_first_answer :
    (recoverDynamic [] recoverySaved.frames).map (fun result => result.1.map Answer.value) =
      some [sym "first"] := by
  decide +kernel

def completedMarks : Outcome → Option Nat
  | .complete state _ _ _ => some (state.core.count (call "mark" []))
  | _ => none

theorem actual_resume_law :
    run recoveryProgram (46 + 100) recoveryStart = run recoveryProgram 100 recoverySaved :=
  resume_exhausted recoveryProgram 46 100 recoveryStart recoverySaved recovery_paused

theorem resumed_effect_occurs_once :
    completedMarks (run recoveryProgram 100 recoverySaved) = some 1 := by
  decide +kernel

theorem restarting_repeats_the_effect :
    completedMarks (run recoveryProgram 100 (start recoverySaved.state recoveryRequest)) = some 2 := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PeTTa.Unifying.DynamicCallControls
