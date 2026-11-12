import Mettapedia.Languages.MeTTa.PeTTa.Unifying

/-!
# The rules of PeTTa by two-way unification, and their runs

`Transition registry` states one step of a request translated against
`registry`, rule by rule, from the syntax of the control and the top frame; a
rule never mentions `Unifying.step`. `step_iff_transition` shows that the
machine takes exactly these steps, and `completed_run_iff_derivation` that a
fuelled run completes with an observation exactly when the rules derive it, as
`Eval.completed_run_iff_derivation` does for the matching machine.

A step is not defined for a unification that runs out of fuel or a completed
configuration; an uncaught fault is terminal too. A recoverable runtime-call
fault instead takes its recovery step. Running out of fuel is the machine's
`exhausted` outcome, never a derivation (`no_exhausted_derivation`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Unifying

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open SpaceSemantics (Program Cases)
open Effects (State Fault)
open Eval (Target ioHead argumentIsRaw readCases nestedLets)
open LiveEquations (liveEquations)

/-- Control forms actually handled before ordinary applications by
`Unifying.step`. This source profile does not yet implement the matching
machine's `unique` control form; it follows ordinary call/data dispatch here. -/
def sourceControlForm : Atom → Bool
  | .expression [.symbol "let", _, _, _]
  | .expression [.symbol "let*", .expression _, _]
  | .expression [.symbol "case", _, .expression _]
  | .expression [.symbol "if", _, _, _]
  | .expression [.symbol "collapse", _]
  | .expression [.symbol "superpose", .expression _]
  | .expression [.symbol "empty"]
  | .expression [.symbol "quote", _]
  | .expression [.symbol "match", _, _, _] => true
  | _ => false

/-- The rules of one request translated against `registry`. -/
inductive Transition (registry : Program) : Configuration → Configuration → Prop where
  | fault_caught {source : Configuration} {reason : Fault} {earned : List Answer} {rest : List Frame}
      (control : source.control = .fault reason)
      (recovered : recoverDynamic [] source.frames = some (earned, rest)) :
      Transition registry source { source with control := .returned earned, frames := rest }
  | dynamic_partial {source : Configuration} {bindings : Subst} {callee : Atom}
      {supplied captured : List Atom} {head : String}
      (control : source.control = .dynamic bindings callee supplied)
      (recognized : partial? (resolve bindings callee) = some (head, captured)) :
      Transition registry source { source with
        control := .dynamic bindings (.symbol head) (captured ++ supplied.map (resolve bindings)) }
  | dynamic_native {source : Configuration} {bindings : Subst} {callee : Atom}
      {supplied : List Atom} {head : String}
      (control : source.control = .dynamic bindings callee supplied)
      (resolved : resolve bindings callee = .symbol head)
      (native : (ioHead head || StdLib.known head) = true) :
      Transition registry source { source with
        control := .arguments bindings (.function head) [] (supplied.map (resolve bindings)) 0
        frames := .dynamicCall :: source.frames }
  | dynamic_equations {source : Configuration} {bindings : Subst} {callee : Atom}
      {supplied : List Atom} {head : String} {selected : Control} {used : Nat}
      (control : source.control = .dynamic bindings callee supplied)
      (resolved : resolve bindings callee = .symbol head)
      (notNative : (ioHead head || StdLib.known head) = false)
      (registered : (codeEquations source.state source.privateCode).any (·.head == head) = true)
      (chosen : application (runtimeRegistry registry source.state source.privateCode)
        (codeEquations source.state source.privateCode)
        head (supplied.map (resolve bindings)) bindings source.uses = some (selected, used)) :
      Transition registry source { source with
        control := selected, uses := source.uses + used, frames := invocationFrames selected source.frames }
  | dynamic_data {source : Configuration} {bindings : Subst} {callee : Atom} {supplied : List Atom}
      (control : source.control = .dynamic bindings callee supplied)
      (notPartial : partial? (resolve bindings callee) = none)
      (notCallable : runtimeCallable source.state (resolve bindings callee) source.privateCode = false) :
      Transition registry source { source with
        control := .returned [⟨.expression (resolve bindings callee :: supplied.map (resolve bindings)), bindings⟩] }
  | sequence_done {source : Configuration} {answers : List Answer}
      (control : source.control = .sequence [] answers) :
      Transition registry source { source with control := .returned answers }
  | sequence_enter {source : Configuration} {first : Control} {rest : List Control}
      {answers : List Answer} (control : source.control = .sequence (first :: rest) answers) :
      Transition registry source
        { source with control := first, frames := .sequence rest answers :: source.frames }
  | construct {source : Configuration} {bindings : Subst} {held : List Atom} {index : Nat}
      (control : source.control = .arguments bindings .data [] held index) :
      Transition registry source
        { source with control := .returned [⟨.expression (held.map (resolve bindings)), bindings⟩] }
  | read_end {source : Configuration} {bindings : Subst} {index : Nat}
      (control : source.control = .arguments bindings (.function "readln!") [] [] index)
      (input : source.input = []) :
      Transition registry source
        { source with control := .returned [⟨.symbol "end_of_file", bindings⟩] }
  | read_line {source : Configuration} {bindings : Subst} {index : Nat} {first : Atom}
      {rest : List Atom}
      (control : source.control = .arguments bindings (.function "readln!") [] [] index)
      (input : source.input = first :: rest) :
      Transition registry source
        { source with
          input := rest
          control := .returned [⟨rename source.uses first, bindings⟩]
          uses := source.uses + 1 }
  | print {source : Configuration} {bindings : Subst} {index : Nat} {held : Atom}
      (control : source.control = .arguments bindings (.function "println!") [] [held] index) :
      Transition registry source
        { source with
          output := source.output ++ [resolve bindings held]
          control := .returned [⟨Effects.boolean true, bindings⟩] }
  | evaluate_code {source : Configuration} {bindings : Subst} {index : Nat} {held : Atom}
      (control : source.control = .arguments bindings (.function "eval") [] [held] index) :
      Transition registry source
        { source with control := .evaluate bindings (resolve bindings held) }
  | read_bad {source : Configuration} {bindings : Subst} {index : Nat} {held : List Atom}
      (control : source.control = .arguments bindings (.function "readln!") [] held index)
      (invalid : held ≠ []) :
      Transition registry source { source with control := .fault (.invalidArguments "readln!") }
  | print_bad {source : Configuration} {bindings : Subst} {index : Nat} {held : List Atom}
      (control : source.control = .arguments bindings (.function "println!") [] held index)
      (invalid : ∀ value, held ≠ [value]) :
      Transition registry source { source with control := .fault (.invalidArguments "println!") }
  | eval_bad {source : Configuration} {bindings : Subst} {index : Nat} {held : List Atom}
      (control : source.control = .arguments bindings (.function "eval") [] held index)
      (invalid : ∀ value, held ≠ [value]) :
      Transition registry source { source with control := .fault (.invalidArguments "eval") }
  /-- `remove-atom` removes the rows that unify with its argument. -/
  | remove {source : Configuration} {bindings : Subst} {index : Nat} {location pattern : Atom}
      {after : State} {answers : List Atom} {used : Nat}
      (control : source.control =
        .arguments bindings (.function "remove-atom") [] [location, pattern] index)
      (removed : removeRows source.state (resolve bindings location) (resolve bindings pattern)
        source.uses = some (.ok (after, answers, used))) :
      Transition registry source
        { source with
          state := after
          control := .returned (answers.map fun value => ⟨value, bindings⟩)
          uses := source.uses + used }
  | remove_fault {source : Configuration} {bindings : Subst} {index : Nat}
      {location pattern : Atom} {reason : Fault}
      (control : source.control =
        .arguments bindings (.function "remove-atom") [] [location, pattern] index)
      (removed : removeRows source.state (resolve bindings location) (resolve bindings pattern)
        source.uses = some (.error reason)) :
      Transition registry source { source with control := .fault reason }
  | remove_bad {source : Configuration} {bindings : Subst} {index : Nat} {held : List Atom}
      (control : source.control = .arguments bindings (.function "remove-atom") [] held index)
      (invalid : ∀ first second, held ≠ [first, second]) :
      Transition registry source { source with control := .fault (.invalidArguments "remove-atom") }
  | native_query {source : Configuration} {bindings : Subst} {index : Nat} {held : List Atom}
      {answers : List Answer} {used : Nat}
      (control : source.control = .arguments bindings (.function "match") [] held index)
      (queried : matchCall source.state bindings source.uses (held.map (resolve bindings)) =
        some (.ok (answers,used))) :
      Transition registry source
        {source with control := .returned answers, uses := source.uses + used}
  | native_query_fault {source : Configuration} {bindings : Subst} {index : Nat} {held : List Atom}
      {reason : Fault}
      (control : source.control = .arguments bindings (.function "match") [] held index)
      (queried : matchCall source.state bindings source.uses (held.map (resolve bindings)) =
        some (.error reason)) :
      Transition registry source {source with control := .fault reason}
  | primitive {source : Configuration} {bindings : Subst} {head : String} {index : Nat}
      {held answers : List Atom} {after : State}
      (control : source.control = .arguments bindings (.function head) [] held index)
      (ordinary : ioHead head = false) (notRemove : head ≠ "remove-atom") (notMatch : head ≠ "match")
      (native : StdLib.known head = true)
      (result : StdLib.apply source.state head
        (primitiveInputs head source.uses (held.map (resolve bindings))) = .ok (after, answers)) :
      Transition registry source
        { source with
          state := after
          control := .returned ((primitiveOutputs head source.uses answers).map fun value => ⟨value, bindings⟩)
          uses := source.uses + primitiveUses head answers }
  | primitive_fault {source : Configuration} {bindings : Subst} {head : String} {index : Nat}
      {held : List Atom} {reason : Fault}
      (control : source.control = .arguments bindings (.function head) [] held index)
      (ordinary : ioHead head = false) (notRemove : head ≠ "remove-atom") (notMatch : head ≠ "match")
      (native : StdLib.known head = true)
      (result : StdLib.apply source.state head
        (primitiveInputs head source.uses (held.map (resolve bindings))) = .error reason) :
      Transition registry source { source with control := .fault reason }
  /-- A call of an authored function: classified by the registry, the live
  equations selected by unifying their renamed heads with the arguments. -/
  | equations {source : Configuration} {bindings : Subst} {head : String} {index : Nat}
      {held : List Atom} {selected : Control} {used : Nat}
      (control : source.control = .arguments bindings (.function head) [] held index)
      (ordinary : ioHead head = false) (notRemove : head ≠ "remove-atom")
      (notNative : StdLib.known head = false)
      (chosen : application (codeRegistry registry source.privateCode)
        (codeEquations source.state source.privateCode) head
        (held.map (resolve bindings)) bindings source.uses = some (selected, used)) :
      Transition registry source { source with control := selected, uses := source.uses + used }
  | raw_argument {source : Configuration} {bindings : Subst} {target : Target}
      {first : Atom} {rest values : List Atom} {index : Nat}
      (control : source.control = .arguments bindings target (first :: rest) values index)
      (raw : (match target with
        | .function head => argumentIsRaw registry head index
        | .data => false) = true) :
      Transition registry source
        { source with
          control := .returned [⟨resolve bindings first, bindings⟩]
          frames := .argument target rest values index :: source.frames }
  | evaluated_argument {source : Configuration} {bindings : Subst} {target : Target}
      {first : Atom} {rest values : List Atom} {index : Nat}
      (control : source.control = .arguments bindings target (first :: rest) values index)
      (demanded : (match target with
        | .function head => argumentIsRaw registry head index
        | .data => false) = false) :
      Transition registry source
        { source with
          control := .evaluate bindings first
          frames := .argument target rest values index :: source.frames }
  | value_variable {source : Configuration} {bindings : Subst} {name : String}
      (control : source.control = .evaluate bindings (.var name)) :
      Transition registry source
        { source with control := .returned [⟨resolve bindings (.var name), bindings⟩] }
  | symbol {source : Configuration} {bindings : Subst} {name : String}
      (control : source.control = .evaluate bindings (.symbol name)) :
      Transition registry source { source with control := .returned [⟨.symbol name, bindings⟩] }
  | grounded {source : Configuration} {bindings : Subst} {value : GroundedValue}
      (control : source.control = .evaluate bindings (.grounded value)) :
      Transition registry source { source with control := .returned [⟨.grounded value, bindings⟩] }
  | let_enter {source : Configuration} {bindings : Subst} {pattern value body : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "let", pattern, value, body])) :
      Transition registry source
        { source with
          control := .evaluate bindings value
          frames := .bind pattern body :: source.frames }
  | let_star {source : Configuration} {bindings : Subst} {pairs : List Atom} {body nested : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "let*", .expression pairs, body]))
      (expanded : nestedLets pairs body = some nested) :
      Transition registry source { source with control := .evaluate bindings nested }
  | let_star_bad {source : Configuration} {bindings : Subst} {pairs : List Atom} {body : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "let*", .expression pairs, body]))
      (invalid : nestedLets pairs body = none) :
      Transition registry source { source with control := .fault (.invalidArguments "let*") }
  | case_enter {source : Configuration} {bindings : Subst} {value : Atom}
      {rows : List Atom} {cases : Cases}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "case", value, .expression rows]))
      (parsed : readCases rows = some cases) :
      Transition registry source
        { source with
          control := .evaluate bindings value
          frames := .select cases :: source.frames }
  | case_bad {source : Configuration} {bindings : Subst} {value : Atom} {rows : List Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "case", value, .expression rows]))
      (invalid : readCases rows = none) :
      Transition registry source { source with control := .fault (.invalidArguments "case") }
  | if_enter {source : Configuration} {bindings : Subst} {condition yes no : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "if", condition, yes, no])) :
      Transition registry source
        { source with
          control := .evaluate bindings condition
          frames := .branch yes no :: source.frames }
  | collapse_enter {source : Configuration} {bindings : Subst} {expression : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "collapse", expression])) :
      Transition registry source
        { source with
          control := .evaluate bindings expression
          frames := .collect bindings :: source.frames }
  | superpose_enter {source : Configuration} {bindings : Subst} {alternatives : List Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "superpose", .expression alternatives])) :
      Transition registry source
        { source with control := .sequence (alternatives.map (.evaluate bindings)) [] }
  | empty_enter {source : Configuration} {bindings : Subst}
      (control : source.control = .evaluate bindings (.expression [.symbol "empty"])) :
      Transition registry source { source with control := .returned [] }
  | quote_enter {source : Configuration} {bindings : Subst} {expression : Atom}
      (control : source.control = .evaluate bindings (.expression [.symbol "quote", expression])) :
      Transition registry source
        { source with control := .returned [⟨resolve bindings expression, bindings⟩] }
  | query_enter {source : Configuration} {bindings : Subst} {space pattern body : Atom}
      (control : source.control = .evaluate bindings
        (.expression [.symbol "match", space, pattern, body])) :
      Transition registry source
        { source with
          control := .evaluate bindings space
          frames := .query pattern body :: source.frames }
  | call_enter {source : Configuration} {bindings : Subst} {head : String} {arguments : List Atom}
      (control : source.control = .evaluate bindings (.expression (.symbol head :: arguments)))
      (notControl : sourceControlForm (.expression (.symbol head :: arguments)) = false)
      (callable : (ioHead head || StdLib.known head ||
        (codeRegistry registry source.privateCode).equations.any (·.head == head)) = true) :
      Transition registry source
        { source with control := .arguments bindings (.function head) arguments [] 0 }
  | data_enter {source : Configuration} {bindings : Subst} {head : String} {arguments : List Atom}
      (control : source.control = .evaluate bindings (.expression (.symbol head :: arguments)))
      (notControl : sourceControlForm (.expression (.symbol head :: arguments)) = false)
      (notCallable : (ioHead head || StdLib.known head ||
        (codeRegistry registry source.privateCode).equations.any (·.head == head)) = false) :
      Transition registry source
        { source with control := .arguments bindings .data (.symbol head :: arguments) [] 0 }
  | partial_value {source : Configuration} {bindings : Subst} {head : String} {captured : List Atom}
      (control : source.control = .evaluate bindings (Eval.partialValue head captured)) :
      Transition registry source { source with
        control := .returned [⟨resolve bindings (Eval.partialValue head captured), bindings⟩] }
  | dynamic_enter {source : Configuration} {bindings : Subst} {items : List Atom}
      (control : source.control = .evaluate bindings (.expression items))
      (unheaded : ∀ head arguments, items ≠ .symbol head :: arguments)
      (notPartial : partial? (.expression items) = none)
      (dynamic : dynamicItems items = true) :
      Transition registry source { source with
        control := .arguments bindings .data items [] 0
        frames := .dispatch :: source.frames }
  | expression_enter {source : Configuration} {bindings : Subst} {items : List Atom}
      (control : source.control = .evaluate bindings (.expression items))
      (unheaded : ∀ head arguments, items ≠ .symbol head :: arguments)
      (notPartial : partial? (.expression items) = none)
      (notDynamic : dynamicItems items = false) :
      Transition registry source
        { source with control := .arguments bindings .data items [] 0 }
  | dispatch_return {source : Configuration} {answers : List Answer} {rest : List Frame}
      (control : source.control = .returned answers) (frames : source.frames = .dispatch :: rest) :
      Transition registry source { source with
        control := .sequence (answers.map dispatchAnswer) [], frames := rest }
  | dynamic_return {source : Configuration} {answers : List Answer} {rest : List Frame}
      (control : source.control = .returned answers) (frames : source.frames = .dynamicCall :: rest) :
      Transition registry source { source with control := .returned answers, frames := rest }
  | collapse_return {source : Configuration} {answers : List Answer} {outer : Subst}
      {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .collect outer :: rest) :
      Transition registry source
        { source with
          control := .returned [⟨.expression (copies source.uses answers), outer⟩]
          frames := rest
          uses := source.uses + answers.length }
  | sequence_return {source : Configuration} {answers collected : List Answer}
      {pending : List Control} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .sequence pending collected :: rest) :
      Transition registry source
        { source with control := .sequence pending (collected ++ answers), frames := rest }
  | argument_return {source : Configuration} {answers : List Answer} {values pending : List Atom}
      {target : Target} {index : Nat} {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .argument target pending values index :: rest) :
      Transition registry source
        { source with
          control := .sequence (answers.map fun answer =>
            .arguments answer.bindings target pending (values ++ [answer.value]) (index + 1)) []
          frames := rest }
  | binding_return {source : Configuration} {answers : List Answer} {pattern body : Atom}
      {rest : List Frame} {continued : List Control}
      (control : source.control = .returned answers)
      (frames : source.frames = .bind pattern body :: rest)
      (bound : bindAnswers pattern body answers = some continued) :
      Transition registry source { source with control := .sequence continued [], frames := rest }
  | case_return {source : Configuration} {answers : List Answer} {cases : Cases}
      {rest : List Frame} {continued : List Control}
      (control : source.control = .returned answers)
      (frames : source.frames = .select cases :: rest)
      (selected : selectAnswers cases answers = some continued) :
      Transition registry source { source with control := .sequence continued [], frames := rest }
  | if_return {source : Configuration} {answers : List Answer} {yes no : Atom}
      {rest : List Frame}
      (control : source.control = .returned answers)
      (frames : source.frames = .branch yes no :: rest) :
      Transition registry source
        { source with
          control := .sequence (answers.map fun answer =>
            .evaluate answer.bindings (if answer.value == Effects.boolean true then yes else no)) []
          frames := rest }
  | query_return {source : Configuration} {answers : List Answer} {pattern body : Atom}
      {rest : List Frame} {continued : List Control} {used : Nat}
      (control : source.control = .returned answers)
      (frames : source.frames = .query pattern body :: rest)
      (queried : queries source.state pattern body source.uses answers = some (continued, used)) :
      Transition registry source
        { source with control := .sequence continued [], frames := rest, uses := source.uses + used }

/-! ## The machine takes exactly these steps -/

theorem transition_step {registry : Program} {source target : Configuration}
    (derivation : Transition registry source target) :
    step registry source = some target := by
  cases derivation
  all_goals try solve | simp_all [step, sourceControlForm, ioHead]
  case equations bindings head index held selected used control ordinary notRemove notNative chosen =>
    have notMatch : head ≠ "match" := by intro same; subst head; cases notNative
    simp [step,control,ordinary,notRemove,notMatch,notNative,chosen]
  case raw_argument bindings target first rest values index control raw =>
    cases target <;> simp_all [step]
  case evaluated_argument bindings target first rest values index control demanded =>
    cases target <;> simp_all [step]
  case call_enter bindings head arguments control notControl callable =>
    simp only [step, control]
    split <;> simp_all [sourceControlForm]
    all_goals aesop
  case data_enter bindings head arguments control notControl notCallable =>
    simp only [step, control]
    split <;> simp_all [sourceControlForm]
    all_goals aesop
  case dynamic_native bindings callee supplied head control resolved native =>
    simp [step, control, resolved, partial?, native]
  case dynamic_equations bindings callee supplied head selected used control resolved notNative registered chosen =>
    simp [step, control, resolved, partial?, notNative, registered, chosen]
  case dynamic_data bindings callee supplied control notPartial notCallable =>
    cases resolved : resolve bindings callee <;> simp_all [step, runtimeCallable]
  case partial_value bindings head captured control =>
    simp [step, control, Eval.partialValue, Eval.partialTag, partial?]
  case remove_bad bindings index held control invalid =>
    cases held with
    | nil => simp [step, control, ioHead]
    | cons first rest =>
      cases rest with
      | nil => simp [step, control, ioHead]
      | cons second rest =>
        cases rest with
        | nil => exact absurd rfl (invalid first second)
        | cons third rest => simp [step, control, ioHead]

theorem step_transition {registry : Program} {source target : Configuration}
    (computed : step registry source = some target) :
    Transition registry source target := by
  cases source with
  | mk state control frames input output uses privateCode =>
    cases control with
    | fault reason =>
      cases recovered : recoverDynamic [] frames with
      | none => simp [step, recovered] at computed
      | some pair =>
          rcases pair with ⟨earned, rest⟩
          simp only [step, recovered, Option.some.injEq] at computed
          subst target
          exact .fault_caught rfl recovered
    | dynamic bindings callee supplied =>
      cases recognized : partial? (resolve bindings callee) with
      | some pair =>
          rcases pair with ⟨head, captured⟩
          simp only [step, recognized, Option.some.injEq] at computed
          subst target
          exact .dynamic_partial rfl recognized
      | none =>
          cases resolved : resolve bindings callee with
          | symbol head =>
              by_cases native : (ioHead head || StdLib.known head) = true
              · simp only [step, resolved, partial?, native, ↓reduceIte, Option.some.injEq] at computed
                subst target
                exact .dynamic_native rfl resolved native
              · have notNative : (ioHead head || StdLib.known head) = false := Bool.eq_false_iff.mpr native
                by_cases registered : (codeEquations state privateCode).any (·.head == head) = true
                · cases chosen : application (runtimeRegistry registry state privateCode) (codeEquations state privateCode)
                    head (supplied.map (resolve bindings)) bindings uses with
                  | none => simp [step, resolved, partial?, notNative, registered, chosen] at computed
                  | some pair =>
                      rcases pair with ⟨selected, used⟩
                      simp only [step, resolved, partial?, notNative, registered, Bool.false_eq_true, ↓reduceIte,
                        chosen, Option.some.injEq] at computed
                      subst target
                      exact .dynamic_equations rfl resolved notNative registered chosen
                · have notRegistered := Bool.eq_false_iff.mpr registered
                  simp only [step, resolved, partial?, notNative, notRegistered, Bool.false_eq_true,
                    ↓reduceIte, Option.some.injEq] at computed
                  subst target
                  simpa only [resolved] using
                    (Transition.dynamic_data (registry := registry) (bindings := bindings) (callee := callee)
                      (source := ⟨state, .dynamic bindings callee supplied, frames, input, output, uses, privateCode⟩)
                      rfl recognized (by simp [runtimeCallable, resolved, notNative, notRegistered]))
          | var name =>
              have ready := recognized
              rw [resolved] at ready
              simp only [step, resolved, ready, Option.some.injEq] at computed
              subst target
              simpa only [resolved] using
                (Transition.dynamic_data (registry := registry) (bindings := bindings) (callee := callee)
                  (source := ⟨state, .dynamic bindings callee supplied, frames, input, output, uses, privateCode⟩)
                  rfl recognized (by simp [runtimeCallable, resolved]))
          | grounded value =>
              have ready := recognized
              rw [resolved] at ready
              simp only [step, resolved, ready, Option.some.injEq] at computed
              subst target
              simpa only [resolved] using
                (Transition.dynamic_data (registry := registry) (bindings := bindings) (callee := callee)
                  (source := ⟨state, .dynamic bindings callee supplied, frames, input, output, uses, privateCode⟩)
                  rfl recognized (by simp [runtimeCallable, resolved]))
          | expression items =>
              have ready := recognized
              rw [resolved] at ready
              simp only [step, resolved, ready, Option.some.injEq] at computed
              subst target
              simpa only [resolved] using
                (Transition.dynamic_data (registry := registry) (bindings := bindings) (callee := callee)
                  (source := ⟨state, .dynamic bindings callee supplied, frames, input, output, uses, privateCode⟩)
                  rfl recognized (by simp [runtimeCallable, resolved]))
    | sequence pending answers =>
      cases pending with
      | nil =>
        simp only [step, Option.some.injEq] at computed
        subst target
        exact .sequence_done rfl
      | cons first rest =>
        simp only [step, Option.some.injEq] at computed
        subst target
        exact .sequence_enter rfl
    | arguments bindings destination pending held index =>
      cases pending with
      | nil =>
        cases destination with
        | data =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .construct rfl
        | function head =>
          by_cases io : ioHead head = true
          · simp only [ioHead, List.mem_cons, List.not_mem_nil, or_false, decide_eq_true_eq] at io
            rcases io with read | print | evaluate
            · subst head
              cases held with
              | nil =>
                cases input with
                | nil =>
                  simp [step, ioHead] at computed
                  subst target
                  exact .read_end rfl rfl
                | cons first rest =>
                  simp [step, ioHead] at computed
                  subst target
                  exact .read_line rfl rfl
              | cons first rest =>
                simp [step, ioHead] at computed
                subst target
                exact .read_bad rfl (by simp)
            · subst head
              cases held with
              | nil =>
                simp [step, ioHead] at computed
                subst target
                exact .print_bad rfl (by simp)
              | cons first rest =>
                cases rest with
                | nil =>
                  simp [step, ioHead] at computed
                  subst target
                  exact .print rfl
                | cons second rest =>
                  simp [step, ioHead] at computed
                  subst target
                  exact .print_bad rfl (by simp)
            · subst head
              cases held with
              | nil =>
                simp [step, ioHead] at computed
                subst target
                exact .eval_bad rfl (by simp)
              | cons first rest =>
                cases rest with
                | nil =>
                  simp [step, ioHead] at computed
                  subst target
                  exact .evaluate_code rfl
                | cons second rest =>
                  simp [step, ioHead] at computed
                  subst target
                  exact .eval_bad rfl (by simp)
          · have ordinary : ioHead head = false := by simpa using io
            by_cases remove : head = "remove-atom"
            · subst head
              match held, computed with
              | [location, pattern], computed =>
                  cases removed : removeRows state (resolve bindings location)
                      (resolve bindings pattern) uses with
                  | none => simp [step, ordinary, removed] at computed
                  | some result =>
                      cases result with
                      | ok triple =>
                          obtain ⟨after, answers, used⟩ := triple
                          simp [step, ordinary, removed] at computed
                          subst target
                          exact .remove rfl removed
                      | error reason =>
                          simp [step, ordinary, removed] at computed
                          subst target
                          exact .remove_fault rfl removed
              | [], computed =>
                  simp [step, ordinary] at computed
                  subst target
                  exact .remove_bad rfl (by simp)
              | [_], computed =>
                  simp [step, ordinary] at computed
                  subst target
                  exact .remove_bad rfl (by simp)
              | _ :: _ :: _ :: _, computed =>
                  simp [step, ordinary] at computed
                  subst target
                  exact .remove_bad rfl (by simp)
            · by_cases matched : head = "match"
              · subst head
                cases queried : matchCall state bindings uses (held.map (resolve bindings)) with
                | none => simp [step,ioHead,queried] at computed
                | some result =>
                    cases result with
                    | ok pair =>
                        obtain ⟨answers,used⟩ := pair
                        simp [step,ioHead,queried] at computed
                        subst target
                        exact .native_query rfl queried
                    | error reason =>
                        simp [step,ioHead,queried] at computed
                        subst target
                        exact .native_query_fault rfl queried
              · by_cases native : StdLib.known head = true
                · cases result : StdLib.apply state head (primitiveInputs head uses (held.map (resolve bindings))) with
                  | ok pair =>
                      obtain ⟨after, answers⟩ := pair
                      simp [step, ordinary, remove, matched, native, result] at computed
                      subst target
                      exact .primitive rfl ordinary remove matched native result
                  | error reason =>
                      simp [step, ordinary, remove, matched, native, result] at computed
                      subst target
                      exact .primitive_fault rfl ordinary remove matched native result
                · have notNative : StdLib.known head = false := by simpa using native
                  cases chosen : application (codeRegistry registry privateCode) (codeEquations state privateCode) head
                      (held.map (resolve bindings)) bindings uses with
                  | none => simp [step, ordinary, remove, matched, notNative, chosen] at computed
                  | some pair =>
                      obtain ⟨selected, used⟩ := pair
                      simp [step, ordinary, remove, matched, notNative, chosen] at computed
                      subst target
                      exact .equations rfl ordinary remove notNative chosen
      | cons first rest =>
        cases destination with
        | data =>
          simp only [step, Bool.false_eq_true, ↓reduceIte, Option.some.injEq] at computed
          subst target
          exact .evaluated_argument rfl rfl
        | function head =>
          simp only [step] at computed
          split at computed
          · cases computed
            exact .raw_argument rfl (by assumption)
          · cases computed
            exact .evaluated_argument rfl
              (by simpa using ‹¬ argumentIsRaw registry head index = true›)
    | evaluate bindings expression =>
      cases expression with
      | var name =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .value_variable rfl
      | symbol name =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .symbol rfl
      | grounded value =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .grounded rfl
      | expression items =>
        simp only [step] at computed
        split at computed
        all_goals try contradiction
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .let_enter rfl
        · split at computed
          · cases computed
            simp_all only [Atom.expression.injEq]
            exact .let_star rfl (by assumption)
          · cases computed
            simp_all only [Atom.expression.injEq]
            exact .let_star_bad rfl (by assumption)
        · split at computed
          · cases computed
            simp_all only [Atom.expression.injEq]
            exact .case_enter rfl (by assumption)
          · cases computed
            simp_all only [Atom.expression.injEq]
            exact .case_bad rfl (by assumption)
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .if_enter rfl
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .collapse_enter rfl
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .superpose_enter rfl
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .empty_enter rfl
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .quote_enter rfl
        · cases computed
          simp_all only [Atom.expression.injEq]
          exact .query_enter rfl
        · split at computed
          · cases computed
            simp_all only [Atom.expression.injEq]
            apply Transition.call_enter rfl _ (by assumption)
            simp only [sourceControlForm]
            split <;> (simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at * <;> aesop)
          · rename_i notCallable
            cases computed
            simp_all only [Atom.expression.injEq]
            subst_vars
            apply Transition.data_enter rfl _ (Bool.eq_false_iff.mpr notCallable)
            simp only [sourceControlForm]
            split <;> (simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at * <;> aesop)
        · rename_i scannedExpression scannedItems notLet notLetStar notCase notIf
            notCollapse notSuperpose notEmpty notQuote notMatch unheaded same
          have sameItems : items = scannedItems := Atom.expression.inj same
          subst scannedItems
          cases recognized : partial? (.expression items) with
            | some pair =>
                rcases pair with ⟨head, captured⟩
                have shape := (partial?_some (.expression items) head captured).mp recognized
                simp only [recognized, Option.some.injEq] at computed
                subst target
                rw [shape]
                exact .partial_value rfl
            | none =>
                simp only [recognized] at computed
                split at computed
                · cases computed
                  exact .dynamic_enter rfl (by aesop) recognized (by assumption)
                · cases computed
                  exact .expression_enter rfl (by aesop) recognized
                    (Bool.eq_false_iff.mpr (by assumption))
    | returned answers =>
      cases frames with
      | nil => simp [step] at computed
      | cons frame rest =>
        cases frame with
        | dynamicCall =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .dynamic_return rfl rfl
        | dispatch =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .dispatch_return rfl rfl
        | collect outer =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .collapse_return rfl rfl
        | sequence pending collected =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .sequence_return rfl rfl
        | argument destination pending values index =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .argument_return rfl rfl
        | bind pattern body =>
          cases bound : bindAnswers pattern body answers with
          | none => simp [step, bound] at computed
          | some continued =>
              simp [step, bound] at computed
              subst target
              exact .binding_return rfl rfl bound
        | select cases =>
          cases selected : selectAnswers cases answers with
          | none => simp [step, selected] at computed
          | some continued =>
              simp [step, selected] at computed
              subst target
              exact .case_return rfl rfl selected
        | branch yes no =>
          simp only [step, Option.some.injEq] at computed
          subst target
          exact .if_return rfl rfl
        | query pattern body =>
          cases queried : queries state pattern body uses answers with
          | none => simp [step, queried] at computed
          | some pair =>
              obtain ⟨continued, used⟩ := pair
              simp [step, queried] at computed
              subst target
              exact .query_return rfl rfl queried

theorem step_iff_transition (registry : Program) (source target : Configuration) :
    step registry source = some target ↔ Transition registry source target :=
  ⟨step_transition, transition_step⟩

/-! ## Runs -/

/-- The whole-request judgment. -/
inductive Runs (registry : Program) : Configuration → Outcome → Prop where
  | completed {source : Configuration} {answers : List Answer}
      (control : source.control = .returned answers) (frames : source.frames = []) :
      Runs registry source (.complete source.state
        (answers.map fun answer => resolve answer.bindings answer.value) source.input source.output)
  | fault {source : Configuration} {reason : Fault}
      (control : source.control = .fault reason) (uncaught : recoverDynamic [] source.frames = none) :
      Runs registry source (.fault reason source)
  | next {source target : Configuration} {result : Outcome}
      (transition : Transition registry source target) (rest : Runs registry target result) :
      Runs registry source result

/-- Running out of fuel is never a derivation. -/
theorem no_exhausted_derivation (registry : Program) (source unfinished : Configuration) :
    ¬ Runs registry source (.exhausted unfinished) := by
  intro derivation
  generalize resultEq : Outcome.exhausted unfinished = result at derivation
  induction derivation with
  | completed => cases resultEq
  | fault => cases resultEq
  | next _ _ ih => exact ih resultEq

theorem run_succ_of_step (registry : Program) (fuel : Nat)
    (source target : Configuration) (transition : step registry source = some target) :
    run registry (fuel + 1) source = run registry fuel target := by
  cases source with
  | mk state control frames input output uses privateCode =>
      cases control with
      | fault reason =>
          cases recovered : recoverDynamic [] frames with
          | none => simp [step, recovered] at transition
          | some pair => simp only [run, recovered, transition]
      | returned answers =>
          cases frames
          · simp [step] at transition
          · simp only [run, transition]
      | _ => simp only [run, transition]

theorem derivation_has_run {registry : Program} {source : Configuration} {result : Outcome}
    (derivation : Runs registry source result) :
    ∃ fuel, run registry fuel source = result := by
  induction derivation with
  | completed control frames =>
    refine ⟨0, ?_⟩
    rename_i source answers
    cases source
    simp_all [run]
  | fault control uncaught =>
    refine ⟨0, ?_⟩
    rename_i source reason
    cases source
    simp_all [run]
  | next transition _ ih =>
    obtain ⟨fuel, computed⟩ := ih
    exact ⟨fuel + 1, (run_succ_of_step _ _ _ _ (transition_step transition)).trans computed⟩

theorem run_has_derivation (registry : Program) (fuel : Nat) (source : Configuration)
    (result : Outcome) (notExhausted : ∀ unfinished, result ≠ .exhausted unfinished)
    (computed : run registry fuel source = result) :
    Runs registry source result := by
  induction fuel generalizing source with
  | zero =>
    cases source with
    | mk state control frames input output uses privateCode =>
      cases control with
      | fault reason =>
          cases recovered : recoverDynamic [] frames with
          | none =>
              simp only [run, recovered] at computed
              subst result
              exact .fault rfl recovered
          | some pair =>
              simp only [run, recovered] at computed
              exact False.elim (notExhausted _ computed.symm)
      | _ =>
          cases frames <;> simp only [run] at computed
          all_goals first
            | exact False.elim (notExhausted _ computed.symm)
            | (subst result; exact .completed rfl rfl)
  | succ fuel ih =>
    have advance (current : Configuration)
        (computed : run registry (fuel + 1) current = result)
        (unfolded : run registry (fuel + 1) current =
          match step registry current with
          | some next => run registry fuel next
          | none => .exhausted current) :
        Runs registry current result := by
      rw [unfolded] at computed
      cases transition : step registry current with
      | none =>
        simp only [transition] at computed
        exact False.elim (notExhausted _ computed.symm)
      | some next =>
        exact .next (step_transition transition) (ih next (by simpa [transition] using computed))
    cases source with
    | mk state control frames input output uses privateCode =>
      cases control with
      | fault reason =>
          cases recovered : recoverDynamic [] frames with
          | none =>
              simp only [run, recovered] at computed
              subst result
              exact .fault rfl recovered
          | some pair =>
              exact advance _ computed (by simp only [run, recovered]; rfl)
      | _ =>
          cases frames
          all_goals try solve
            | simp only [run] at computed
              subst result
              exact .completed rfl rfl
          all_goals exact advance _ computed rfl

/-- **The fuelled machine and the rules agree** on every completed observation:
the store, the answers, the remaining input and the output. -/
theorem completed_run_iff_derivation (registry : Program) (source : Configuration)
    (state : State) (answers input output : List Atom) :
    (∃ fuel, run registry fuel source = .complete state answers input output) ↔
      Runs registry source (.complete state answers input output) := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact run_has_derivation registry fuel source _ (by simp) computed
  · exact derivation_has_run

theorem fault_run_iff_derivation (registry : Program) (source : Configuration)
    (reason : Fault) (faulted : Configuration) :
    (∃ fuel, run registry fuel source = .fault reason faulted) ↔
      Runs registry source (.fault reason faulted) := by
  constructor
  · rintro ⟨fuel, computed⟩
    exact run_has_derivation registry fuel source _ (by simp) computed
  · exact derivation_has_run

end Mettapedia.Languages.MeTTa.PeTTa.Unifying
