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

/-- Submit a closed reflexivity certificate without repeating elaborator
conversion. The expected equality itself is checked by the kernel, with
kernel checking explicitly enabled, before the goal is discharged. -/
elab "native_c_parser_reflexivity" : tactic => do
  let goal ← Lean.Elab.Tactic.getMainGoal
  let target ← Lean.instantiateMVars (← goal.getType)
  let some (_, left, _) := target.eq? | throwError "Expected a closed equality"
  let proof ← Lean.Meta.mkEqRefl left
  let environment ← Lean.getEnv
  if target.hasMVar || target.hasFVar || proof.hasMVar || proof.hasFVar ||
      target.hasSorry || proof.hasSorry || environment.hasUnsafe target ||
      environment.hasUnsafe proof then
    throwError "Parser reflexivity requires a closed safe proof"
  let checked ← Lean.withOptions
    (fun options => Lean.debug.skipKernelTC.set (Lean.Elab.async.set options false) false)
    (Lean.Meta.mkAuxLemma [] target proof (cache := false))
  goal.assign (Lean.mkConst checked)
  Lean.Elab.Tactic.replaceMainGoal []

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

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
