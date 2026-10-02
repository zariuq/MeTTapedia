import Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
import Mettapedia.GSLT.LanguageDef.Interaction.Strength

/-!
# All base rules at the contact, and a rule that is not a cut

The contact signature with the contact rule and one contextual rule: a
wrapped term reduces when the term inside reduces.  The only base rule is
headed by the contact, so the theory has the second strength for the family
consisting of the contact.  The contextual rule's left side is a wrapper, not
a cut, and with no equation it is not equal to one: the theory does not have
the third strength, literally or up to the equations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep

/-- A wrapped term reduces when the term inside reduces. -/
def wrapCongRule : RewriteRule where
  name := "WrapCong"
  typeContext := []
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := wrap (.fvar "S")
  right := wrap (.fvar "T")

/-- The contact signature with the contact rule and reduction under the
wrapper. -/
def contactWithWrapCong : LanguageDef :=
  { name := "Contact"
    types := ["Proc"]
    terms := terms
    equations := []
    rewrites := [syncRule, wrapCongRule] }

theorem wrapCongRule_validates :
    LanguageDef.validateRewrite contactWithWrapCong wrapCongRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [wrapCongRule, contactWithWrapCong, terms, wrap]

/-- The theory passes the declaration gate. -/
theorem contactWithWrapCong_validate_eq_nil : contactWithWrapCong.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    have cases : rewrite = syncRule ∨ rewrite = wrapCongRule := by
      have listed : rewrite ∈ [syncRule, wrapCongRule] := membership
      simpa using listed
    rcases cases with rfl | rfl
    · rw [LanguageDef.validateRewrite_congr_signature (first := contactWithWrapCong)
        (second := contactWith []) rfl rfl]
      exact syncRule_validates []
    · exact wrapCongRule_validates

/-- The presentation: processes, the contact, and the contact rule. -/
def wrapCongPresentation : InteractivePresentation where
  presentation := ⟨contactWithWrapCong, contactWithWrapCong_validate_eq_nil⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨terms[7], List.getElem_mem (by decide)⟩
  interactionRewrite := ⟨syncRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- First strength: the selected rule is a base rule headed by the contact. -/
theorem wrapCong_baseInteraction : wrapCongPresentation.BaseInteraction :=
  isBaseRewrite_of_premises_eq_nil rfl

/-- Second strength: its only base rule is headed by the contact. -/
theorem wrapCong_baseRewritesHeaded :
    BaseRewritesHeadedBy contactWithWrapCong [wrapCongPresentation.contactHead] := by
  intro rewrite membership base
  have cases : rewrite = syncRule ∨ rewrite = wrapCongRule := by
    have listed : rewrite ∈ [syncRule, wrapCongRule] := membership
    simpa using listed
  rcases cases with rfl | rfl
  · exact ⟨_, List.mem_singleton.mpr rfl, rfl⟩
  · exact absurd base (not_isBaseRewrite_of_congruence (source := .fvar "S")
      (target := .fvar "T") (List.Mem.head _))

/-- Not the third strength: the contextual rule's left side is not a cut. -/
theorem wrapCong_not_everyRuleIsCut : ¬ wrapCongPresentation.EveryRuleIsCut :=
  wrapCongPresentation.not_everyRuleIsCut_of_rule (rewrite := wrapCongRule)
    (List.Mem.tail _ (List.Mem.head _)) (fun cut => cut)

/-- Nor up to the equations: there are none, so the wrapper is equal only to
itself. -/
theorem wrapCong_not_everyRuleIsCutUpToEquations :
    ¬ wrapCongPresentation.EveryRuleIsCutUpToEquations base := by
  intro all
  obtain ⟨cut, equivalent, isCut⟩ := all wrapCongRule (List.Mem.tail _ (List.Mem.head _))
  have same : wrapCongRule.left = cut :=
    (equationEquiv_iff_eq_of_no_generators (base := base)
      (language := contactWithWrapCong) (by decide) _ _).mp equivalent
  rw [← same] at isCut
  exact isCut

end Mettapedia.GSLT.LanguageDef.Interaction.Controls.EquationalContact
