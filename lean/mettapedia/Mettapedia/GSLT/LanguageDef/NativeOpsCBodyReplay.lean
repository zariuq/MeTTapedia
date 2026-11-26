import Mettapedia.GSLT.LanguageDef.NativeOpsCBodyTextAgreement

/-!
# Checked replay of generated native C bodies

A generated row supplies the independently proposed tokens and function, the
source characters, the parser's type names, and the lowering representation
and source body. A row may cite a separate lexical proof over the same inputs.
The declared conclusions retain the ordered input and complete parser readout.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeOps.NativeC

open Lean Elab Command

private def bodyField (native : Ident) (suffix : String) : Ident :=
  mkIdentFrom native (native.getId.appendAfter suffix)

/-- Compare the normalized target body with the independently lowered source. -/
syntax (name := nativeCBodyCheck) "native_c_body_check " ident "(" term ")" "(" term ")" : command

elab_rules : command
  | `(command| native_c_body_check $native:ident ($representation:term) ($source:term)) => do
    let bodyChecked := bodyField native "_body_checked"
    let bodyAgrees := bodyField native "_body_agrees"
    elabCommand (← `(theorem $bodyChecked :
      bodyAgreement $representation $native $source = true := by decide +kernel))
    elabCommand (← `(theorem $bodyAgrees :
      ∃ function, normalizeFunction? $representation $native = some function ∧
        NativeLowering.function? ($representation).interface $source = some function :=
      (bodyAgreement_iff _ _ _).mp $bodyChecked))

/-- Relate the checked body to a complete source read. The arguments after
the function are type names, representation, characters, tokens, and source
function. A segmented read provides its lexical proof and composition lemma. -/
syntax (name := nativeCBodyReplay) "native_c_body_replay " ident
  "(" term ")" "(" term ")" "(" term ")" "(" term ")" "(" term ")"
  ("using " ident " with " ident)? : command

elab_rules : command
  | `(command| native_c_body_replay $native:ident ($names:term) ($representation:term)
        ($characters:term) ($tokens:term) ($source:term) $[using $lexed:ident with $compose:ident]?) => do
    let field := bodyField native
    let bodyChecked := field "_body_checked"
    let bodyAgrees := field "_body_agrees"
    let scanned := lexed.getD (field "_characters_lexed")
    let parsed := field "_tokens_parsed"
    let textChecked := field "_text_checked"
    let textAgrees := field "_text_agrees"
    if lexed.isNone then
      elabCommand (← `(theorem $scanned : lex $characters = .ok $tokens := by decide +kernel))
    elabCommand (← `(theorem $parsed :
      function? (2 * ($tokens).length + 4) $names $tokens = some ($native, []) := by
      native_c_parser_reflexivity))
    let agreement ← match compose with
      | some combine => `(term| $combine
          (show lex $characters = .ok $tokens from $scanned) $parsed $bodyChecked)
      | none => `(term| by
          apply (textBodyAgreement_iff _ _ _ _).mpr
          obtain ⟨function, normalized, lowered⟩ := $bodyAgrees
          exact ⟨$tokens, $native, function, $scanned, $parsed, normalized, lowered⟩)
    elabCommand (← `(theorem $textChecked :
      textBodyAgreement $names $representation $characters $source = true := $agreement))
    elabCommand (← `(theorem $textAgrees :
      ∃ tokens native function, lex $characters = .ok tokens ∧
        function? (2 * tokens.length + 4) $names tokens = some (native, []) ∧
        normalizeFunction? $representation native = some function ∧
        NativeLowering.function? ($representation).interface $source = some function :=
      (textBodyAgreement_iff _ _ _ _).mp $textChecked))

end Mettapedia.GSLT.LanguageDef.NativeOps.NativeC
