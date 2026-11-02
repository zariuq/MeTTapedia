import Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceLexicalAdequacy

/-! # Executable named-binding controls

Repeated spelling is lexical shadowing unless the inner pattern explicitly
crosses to the outer cell. The controls use the independent executable scope
semantics, not a metadata classification of the source forms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceLexicalAdequacy.Controls

open Mettapedia.GSLT.LanguageDef.TemplateScope

abbrev Source := Src Nat Nat
abbrev Value := Tm Nat (BId Nat)

def shadow (crossing : Option (List Nat)) : Source :=
  .letS (.sv 0) (.sym 1)
    (.app (.app (.sym 9) (.sv 0))
      (.letS (.sv 0) (.sym 2) (.sv 0) crossing)) none

def lexicalAnswers (query : Source) : Option (List Value) :=
  answersDir .patternOnly .static (progLF 99 99 (fun _ => none)) 60
    (elabLFFormAt [] query)

def refiningAnswers (query : Source) : Option (List Value) :=
  answersDir .patternOnly .static (progM 99 99 (fun _ => none)) 60
    (elabMFormAt [] query)

def pair : Value := .app (.app (.sym 9) (.sym 1)) (.sym 2)

theorem lexical_shadow_has_two_distinct_cells : lexicalAnswers (shadow none) = some [pair] := by
  decide +kernel

theorem explicit_crossing_exposes_the_conflict :
    lexicalAnswers (shadow (some [0])) = some [] := by
  decide +kernel

theorem explicit_freshness_retains_shadowing :
    lexicalAnswers (shadow (some [])) = some [pair] := by
  decide +kernel

theorem silently_erasing_a_crossing_changes_execution :
    lexicalAnswers (shadow (some [0])) ≠ lexicalAnswers (shadow none) := by
  decide +kernel

theorem refinement_is_not_lexical_shadowing : refiningAnswers (shadow none) = some [] := by
  decide +kernel

theorem translated_refinement_keeps_the_conflict :
    lexicalAnswers (toLexical (shadow none)) = some [] := by
  decide +kernel

/-- Lambda application captures the outer lexical cell and binds its own
parameter without capturing the same numeral used for the store spelling. -/
def capturedApplication : Source :=
  .letS (.sv 0) (.sym 1)
    (.app (.lam 0 none (.app (.app (.sym 9) (.sv 0)) (.par 0))) (.sym 2)) none

theorem lambda_parameter_and_store_name_are_distinct :
    lexicalAnswers capturedApplication = some [pair] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeCandidates.Native.SourceLexicalAdequacy.Controls
