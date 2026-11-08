import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEDispatchDeopt

/-!
# HE's error protocol at `let`, `switch`, `case` and the cast walker

HE's standard library declares `(: let (-> Atom %Undefined% Atom %Undefined%))`
and `(: switch (-> %Undefined% Expression %Undefined%))`; `case` evaluates
its key with `metta` at `%Undefined%` and collects the answers, errors among
them, as data. In HE's interpreter (`Languages.MeTTa.HE.evalAtom`):

* **An argument fault is the call's answer.** The value of `let` and the key
  of `switch` are arguments at `%Undefined%`: each answer of their
  evaluation that is an error other than the expression itself is the
  call's reply as it is, with nothing bound and the equation not run, and
  the delivery passes it through (`let_replies`, `switch_replies`,
  `fault_delivered`). At the evaluator, `let`'s answers are, for each
  applicability record and each answer of the value, that error, or the
  equation run on the call with the value (`let_answers`); `switch` likewise
  (`switch_answers`). This is the shared machine's argument-return goal
  after the bound value or the key.
* **A key's answers stream.** An expression key evaluated at `%Undefined%`
  answers HE's selection of its interpretation: its successes, or its errors
  when it has none. Publishing successes as they arrive and holding the
  errors to the key's last answer is that selection
  (`key_streams`, through `HEDispatchDeopt.stream_eq_keep`), and the
  successes of any prefix are final (`HEDispatchDeopt.keepBy_prefix`).
* **`Empty` is neutral in the cast walker's join.** An `Empty` body is
  answered as it is at every expected type, so it agrees with every reading
  of the walker, cast, left or neutral (`empty_agrees`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEErrorProtocol

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.HE.CompletedDelivery
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open HEReturns HEDispatchDeopt

/-- An argument answer that the argument stage passes through: an `Empty` or
`Error` other than the argument expression itself. -/
def Fault (arg : Atom) (answer : Atom × Bindings) : Bool :=
  answer.1 != arg && isEmptyOrError answer.1

/-- **An error reply is the call's answer**: the ordinary delivery passes an
error through, with its bindings. -/
theorem fault_delivered {space : Space} {dispatch : GroundedDispatch} {head : String}
    {e range : Atom} (error : isErrorAtom e = true) (b : Bindings) (fuel : Nat) (live : List Atom) :
    invoke space dispatch (.ordinary range) (delivered head e) b (fuel + 1) live = [(e, b)] := by
  have failed : isEmptyOrError e = true := by simp [isEmptyOrError, error]
  rw [delivered_failed head failed, invoke]
  simp [InvocationMode.errorPassthrough, error]

/-- **`let`'s argument stage**: the pattern and the template are held at
`Atom`; the value is evaluated at `%Undefined%`, and each fault is the reply as
it is, nothing bound and the template not reached. -/
theorem let_replies {space : Space} {dispatch : GroundedDispatch} (pattern value template : Atom)
    (b : Bindings) (fuel : Nat) (live : List Atom) :
    interpretArgs space dispatch [pattern, value, template]
        [Atom.atomType, Atom.undefinedType, Atom.atomType] b (fuel + 4) live =
      (evalAtom space dispatch value Atom.undefinedType b (fuel + 2)
          ([template] ++ [Atom.atomType] ++ (pattern :: live))).map fun answer =>
        if Fault value answer then answer
        else (argumentPacket [pattern, answer.1, template], answer.2) := by
  rw [interpretArgs]
  simp only [List.cons_append, List.nil_append]
  rw [evalAtom_held]
  have held : (pattern != pattern && isEmptyOrError pattern) = false := by simp
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, held, Bool.false_eq_true, if_false]
  rw [interpretArgs]
  rw [List.map_flatMap]
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro answer _
  by_cases fault : Fault value answer = true
  · have hf : (answer.1 != value && isEmptyOrError answer.1) = true := fault
    have hfa : (argumentsSucceeded answer.1) = false := by
      simp only [Bool.and_eq_true] at hf
      exact argumentsSucceeded_of_emptyOrError hf.2
    simp [hf, fault, hfa]
  · have hf : (answer.1 != value && isEmptyOrError answer.1) = false := by
      simpa [Fault] using fault
    simp only [hf, Bool.false_eq_true, if_false, fault]
    rw [interpretArgs, evalAtom_held]
    simp [interpretArgs, argumentsSucceeded, unpackArguments, argumentPacket, argumentValues]

/-- **`switch`'s argument stage**: the key is evaluated at `%Undefined%`, each
fault is the reply as it is, and the cases are held at `Expression`. -/
theorem switch_replies {space : Space} {dispatch : GroundedDispatch} (key : Atom) (cases : List Atom)
    (b : Bindings) (fuel : Nat) (live : List Atom) :
    interpretArgs space dispatch [key, .expression cases] [Atom.undefinedType, Atom.expressionType] b
        (fuel + 3) live =
      (evalAtom space dispatch key Atom.undefinedType b (fuel + 2)
          ([.expression cases] ++ [Atom.expressionType] ++ live)).map fun answer =>
        if Fault key answer then answer
        else (argumentPacket [answer.1, .expression cases], answer.2) := by
  rw [interpretArgs]
  rw [List.map_eq_flatMap]
  apply List.flatMap_congr
  intro answer _
  by_cases fault : Fault key answer = true
  · have hf : (answer.1 != key && isEmptyOrError answer.1) = true := fault
    simp [hf, fault]
  · have hf : (answer.1 != key && isEmptyOrError answer.1) = false := by
      simpa [Fault] using fault
    simp only [hf, Bool.false_eq_true, if_false, fault]
    have expr : evalAtom space dispatch (.expression cases) Atom.expressionType answer.2 (fuel + 1)
        (answer.1 :: live) = [(.expression cases, answer.2)] := by
      rw [evalAtom]
      by_cases failed : isEmptyOrError (.expression cases) = true
      · simp [failed]
      · simp [failed, getMetaType, Atom.expressionType]
    rw [interpretArgs]
    simp only [List.nil_append] at expr ⊢
    rw [expr]
    simp [interpretArgs, argumentsSucceeded, unpackArguments, argumentPacket, argumentValues]

/-! ## The calls at the evaluator -/

/-- `let`'s declaration. -/
def letType : Atom := arrowType [Atom.atomType, Atom.undefinedType, Atom.atomType] Atom.undefinedType

/-- `switch`'s declaration. -/
def switchType : Atom := arrowType [Atom.undefinedType, Atom.expressionType] Atom.undefinedType

theorem letType_ground : atomVariables letType = [] := by decide

theorem switchType_ground : atomVariables switchType = [] := by decide

/-- **`let`'s answers**: for each applicability record and each answer of the
value at `%Undefined%`, an error fault is the answer as it is; any other
reply is delivered and run. -/
theorem let_answers {space : Space} {dispatch : GroundedDispatch} {pattern value template expected : Atom}
    (declared : getAtomTypes space (.symbol "let") = [letType])
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression [.symbol "let", pattern, value, template])
      letType expected space bindings (fuel + 5) = .inr bs)
    (enough : matchFuel letType ≤ fuel + 3) (live : List Atom) :
    evalAtom space dispatch (.expression [.symbol "let", pattern, value, template]) expected bindings
        (fuel + 7) live =
      keep (bs.flatMap fun b =>
        (evalAtom space dispatch value Atom.undefinedType b (fuel + 2)
            ([template] ++ [Atom.atomType] ++
              (pattern :: .symbol "let" :: callReturnType Atom.undefinedType :: live))).flatMap
          fun answer =>
            if Fault value answer ∧ isErrorAtom answer.1 = true then [answer]
            else invoke space dispatch (.ordinary (callReturnType Atom.undefinedType))
              (delivered "let" (if Fault value answer then answer.1
                else argumentPacket [pattern, answer.1, template]))
              answer.2 (fuel + 5) live) := by
  rw [strict_call (head := "let") (params := [Atom.atomType, Atom.undefinedType, Atom.atomType])
    declared letType_ground (by decide) (by decide) notAtom notExpression applicable enough]
  congr 1
  apply List.flatMap_congr
  intro b _
  rw [show fuel + 3 + 1 = fuel + 4 from rfl, let_replies, List.flatMap_map]
  apply List.flatMap_congr
  intro answer _
  by_cases fault : Fault value answer = true
  · by_cases err : isErrorAtom answer.1 = true
    · simp only [fault, err, and_self, if_true]
      exact fault_delivered err answer.2 (fuel + 4) live
    · simp [fault, err]
  · simp [fault]

/-- **`switch`'s answers**: for each applicability record and each answer of
the key at `%Undefined%`, an error fault is the answer as it is; any other
reply is delivered and run. -/
theorem switch_answers {space : Space} {dispatch : GroundedDispatch} {key expected : Atom}
    {cases : List Atom}
    (declared : getAtomTypes space (.symbol "switch") = [switchType])
    (notAtom : expected ≠ Atom.atomType) (notExpression : expected ≠ Atom.expressionType)
    {bindings : Bindings} {bs : List Bindings} {fuel : Nat}
    (applicable : checkIfFunctionTypeIsApplicable (.expression [.symbol "switch", key, .expression cases])
      switchType expected space bindings (fuel + 4) = .inr bs)
    (enough : matchFuel switchType ≤ fuel + 2) (live : List Atom) :
    evalAtom space dispatch (.expression [.symbol "switch", key, .expression cases]) expected bindings
        (fuel + 6) live =
      keep (bs.flatMap fun b =>
        (evalAtom space dispatch key Atom.undefinedType b (fuel + 2)
            ([.expression cases] ++ [Atom.expressionType] ++
              (.symbol "switch" :: callReturnType Atom.undefinedType :: live))).flatMap
          fun answer =>
            if Fault key answer ∧ isErrorAtom answer.1 = true then [answer]
            else invoke space dispatch (.ordinary (callReturnType Atom.undefinedType))
              (delivered "switch" (if Fault key answer then answer.1
                else argumentPacket [answer.1, .expression cases]))
              answer.2 (fuel + 4) live) := by
  rw [strict_call (head := "switch") (params := [Atom.undefinedType, Atom.expressionType])
    declared switchType_ground (by decide) (by decide) notAtom notExpression applicable enough]
  congr 1
  apply List.flatMap_congr
  intro b _
  rw [show fuel + 2 + 1 = fuel + 3 from rfl, switch_replies, List.flatMap_map]
  apply List.flatMap_congr
  intro answer _
  by_cases fault : Fault key answer = true
  · by_cases err : isErrorAtom answer.1 = true
    · simp only [fault, err, and_self, if_true]
      exact fault_delivered err answer.2 (fuel + 3) live
    · simp [fault, err]
  · simp [fault]

/-! ## A key's answers stream -/

/-- **A key's answers stream**: an expression key evaluated at `%Undefined%`
answers the streaming procedure over its interpretation, successes published
as they arrive and errors held to the last answer, released only when none
succeeded. -/
theorem key_streams {space : Space} {dispatch : GroundedDispatch} {head : String} (rest : List Atom)
    (notError : head ≠ "Error") (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch (.expression (.symbol head :: rest)) Atom.undefinedType bindings (fuel + 1)
        live =
      stream (fun a => !isErrorAtom a)
        (interpretExpression space dispatch (.expression (.symbol head :: rest)) Atom.undefinedType
          bindings fuel live) := by
  rw [evalAtom_expression (isEmptyOrError_call notError rest) (by decide) (by decide), stream_eq_keep]

/-! ## `Empty` in the cast walker -/

/-- **`Empty` is neutral in the cast walker's join**: an `Empty` body answers
itself at every expected type, which every reading of the walker agrees
with. -/
theorem empty_agrees {space : Space} {dispatch : GroundedDispatch} (expected : Atom) (reading : Cast)
    (bindings : Bindings) (fuel : Nat) (live : List Atom) :
    evalAtom space dispatch Atom.empty expected bindings (fuel + 1) live =
      treat expected reading (evalAtom space dispatch Atom.empty Atom.undefinedType bindings (fuel + 1) live) := by
  have failed : isEmptyOrError Atom.empty = true := by decide
  have here : ∀ t, evalAtom space dispatch Atom.empty t bindings (fuel + 1) live = [(Atom.empty, bindings)] := by
    intro t
    rw [evalAtom]
    simp [failed]
  rw [here, here]
  cases reading with
  | atExpected => simp [treat, castAt, Atom.empty, keep, isErrorAtom]
  | none => rfl
  | neutral => rfl

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.HEErrorProtocol
