import Mettapedia.GSLT.LanguageDef.NativeOpsCBodyAgreement
import Lean

/-!
# Original C characters to a common operational body

Admission lexes the original character stream, parses one complete function,
normalizes that C syntax, and compares it with the independently lowered
source function. Success includes an actual common body; trailing tokens,
lexical failures and failed translations cannot establish agreement.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

/-- Check a closed certificate before assigning it to the elaborator's goal.
The certificate is submitted with asynchronous elaboration and skipped kernel
checking both disabled. No logical axiom is introduced. -/
private def dischargeClosedCertificate (goal : Lean.MVarId) (target proof : Lean.Expr) :
    Lean.Elab.Tactic.TacticM Unit := do
  let environment ← Lean.getEnv
  if target.hasMVar || target.hasFVar || proof.hasMVar || proof.hasFVar ||
      target.hasSorry || proof.hasSorry || environment.hasUnsafe target ||
      environment.hasUnsafe proof then
    throwError "The certificate requires a closed safe proof"
  let checked ← Lean.withOptions
    (fun options => Lean.debug.skipKernelTC.set (Lean.Elab.async.set options false) false)
    (Lean.Meta.mkAuxLemma [] target proof (cache := false))
  goal.assign (Lean.mkConst checked)
  Lean.Elab.Tactic.replaceMainGoal []

/-- Submit parser reflexivity without repeating elaborator conversion. The
kernel checks the expected equality before the goal is discharged. -/
elab "native_c_parser_reflexivity" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  let some (_, left, _) := target.eq? | throwError "Expected a closed equality"
  dischargeClosedCertificate goal target (← Lean.Meta.mkEqRefl left)

/-- Check the literal character-list certificate without asking elaborator
unification to traverse the entire source stream. -/
elab "native_c_character_reflexivity" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  let some (_, _, characters) := target.eq? | throwError "Expected a character-view equality"
  dischargeClosedCertificate goal target (Lean.mkApp (Lean.mkConst ``String.toList_ofList) characters)

/-- Expand a literal's character view without evaluating its UTF-8 decoder.
The result is an ordinary character-list term. `String.toList_ofList`
supplies its checked certificate; this elaborator adds no logical axiom. -/
elab "native_c_characters% " text:term : term => do
  let expression ← Lean.Elab.Term.elabTermEnsuringType text (Lean.mkConst ``String)
  let some value := Lean.Meta.getStringValue? (← Lean.Meta.whnf expression) |
    throwError "Expected a literal C text"
  return Lean.toExpr value.toList

def completeFunction? (names : TypeNames) (tokens : List Token) : Option CFunction :=
  match function? (2 * tokens.length + 4) names tokens with
  | some (function, []) => some function
  | _ => none

theorem completeFunction_iff (names : TypeNames) (tokens : List Token) (function : CFunction) :
    completeFunction? names tokens = some function ↔
      function? (2 * tokens.length + 4) names tokens = some (function, []) := by
  unfold completeFunction?
  cases parsed : function? (2 * tokens.length + 4) names tokens with
  | none => simp only [reduceCtorEq]
  | some pair =>
    rcases pair with ⟨candidate, rest⟩
    cases rest <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq, and_true, and_false]

def functionText? (names : TypeNames) (characters : List Char) : Option CFunction := do
  let tokens ← (lex characters).toOption
  completeFunction? names tokens

theorem functionText_iff (names : TypeNames) (characters : List Char) (function : CFunction) :
    functionText? names characters = some function ↔
      ∃ tokens, lex characters = .ok tokens ∧
        function? (2 * tokens.length + 4) names tokens = some (function, []) := by
  cases scanned : lex characters with
  | error failure => simp only [functionText?, scanned, Except.toOption, bind, Option.bind,
      reduceCtorEq, false_and, exists_false]
  | ok tokens =>
      simp only [functionText?, scanned, Except.toOption, bind, Option.bind, Except.ok.injEq]
      rw [completeFunction_iff]
      constructor
      · intro parsed
        exact ⟨tokens, rfl, parsed⟩
      · rintro ⟨other, rfl, parsed⟩
        exact parsed

def textBodyAgreement (names : TypeNames) (representation : Representation)
    (characters : List Char) (source : NativeOps.Function) : Bool :=
  match functionText? names characters with
  | some function => bodyAgreement representation function source
  | none => false

theorem textBodyAgreement_iff (names : TypeNames) (representation : Representation)
    (characters : List Char) (source : NativeOps.Function) :
    textBodyAgreement names representation characters source = true ↔
      ∃ tokens native function, lex characters = .ok tokens ∧
        function? (2 * tokens.length + 4) names tokens = some (native, []) ∧
        normalizeFunction? representation native = some function ∧
        NativeLowering.function? representation.interface source = some function := by
  have split : textBodyAgreement names representation characters source = true ↔
      ∃ native, functionText? names characters = some native ∧
        bodyAgreement representation native source = true := by
    cases parsed : functionText? names characters with
    | none => simp only [textBodyAgreement, parsed, reduceCtorEq, false_and, exists_false]
    | some native =>
        simp only [textBodyAgreement, parsed, Option.some.injEq]
        constructor
        · intro checked
          exact ⟨native, rfl, checked⟩
        · rintro ⟨other, rfl, checked⟩
          exact checked
  rw [split]
  constructor
  · rintro ⟨native, parsed, checked⟩
    obtain ⟨tokens, scanned, consumed⟩ := (functionText_iff _ _ _).mp parsed
    obtain ⟨function, normalized, lowered⟩ := (bodyAgreement_iff _ _ _).mp checked
    exact ⟨tokens, native, function, scanned, consumed, normalized, lowered⟩
  · rintro ⟨tokens, native, function, scanned, consumed, normalized, lowered⟩
    exact ⟨native, (functionText_iff _ _ _).mpr ⟨tokens, scanned, consumed⟩,
      (bodyAgreement_iff _ _ _).mpr ⟨function, normalized, lowered⟩⟩

/-- Complete consumption accepts an ordinary unit-returning function. -/
theorem complete_unit_function :
    ∃ function, functionText? ["void".toList] "void f(void) { return; }".toList =
      some function := by
  apply Option.isSome_iff_exists.mp
  decide +kernel

theorem trailing_function_token_refused :
    functionText? ["void".toList] "void f(void) { return; } extra".toList = none := by
  decide +kernel

theorem malformed_function_token_refused (names : TypeNames) (representation : Representation)
    (source : NativeOps.Function) : textBodyAgreement names representation ['@'] source = false := by
  rfl

/-- Multibyte scalars and a final newline survive literal admission. -/
theorem literal_character_view_preserves_unicode :
    "λ🙂\n".toList = native_c_characters% "λ🙂\n" := by
  native_c_character_reflexivity

theorem literal_character_view_distinguishes_trailing_newline :
    "λ🙂\n".toList ≠ "λ🙂".toList := by
  have shorter : "λ🙂".toList = native_c_characters% "λ🙂" := String.toList_ofList
  rw [literal_character_view_preserves_unicode, shorter]
  intro equal
  have lengths := congrArg List.length equal
  cases lengths

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
