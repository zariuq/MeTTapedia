import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.OSLF.MeTTaIL.GeneratedRuleValidation

/-!
# A contact with no base rule

A language with one sort, a binary constructor on it, and a single rule that
reduces the left operand of that constructor when the operand itself reduces.
The rule is headed by a same-sort contact, so the language admits an
interactive presentation.  It is not interactive: its only rule asks for a
reduction of a subterm, nothing is ever supplied, and the theory has no
reduction at all.

This is what the words "base rewrite" add to the definition of an interactive
theory.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Interaction.Controls

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open StructuralMorphism

/-- The constructors: an inert process and a binary contact. -/
def contextualOnlyTerms : List GrammarRule := [
    { label := "Stop", category := "Proc", params := [], syntaxPattern := [] },
    { label := "Join", category := "Proc",
      params := [.simple "left" (.base "Proc"), .simple "right" (.base "Proc")],
      syntaxPattern := [.nonTerminal "left", .nonTerminal "right"] }
  ]

/-- The left operand of a contact reduces when it reduces on its own. -/
def joinLeftRule : RewriteRule where
  name := "JoinLeft"
  typeContext := [("Q", .base "Proc")]
  premises := [.congruence (.fvar "S") (.fvar "T")]
  left := .apply "Join" [.fvar "S", .fvar "Q"]
  right := .apply "Join" [.fvar "T", .fvar "Q"]

/-- A contact whose only rule is contextual. -/
def contextualOnly : LanguageDef :=
  { name := "ContextualOnly"
    types := ["Proc"]
    terms := contextualOnlyTerms
    equations := []
    rewrites := [joinLeftRule] }

theorem joinLeftRule_validates :
    LanguageDef.validateRewrite contextualOnly joinLeftRule = [] := by
  apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := "S")
    (target := "T") <;>
    first
      | rfl
      | decide
      | rule_patterns [joinLeftRule, contextualOnly, contextualOnlyTerms]

/-- The language passes the declaration gate. -/
theorem contextualOnly_validate_eq_nil : contextualOnly.validate = [] := by
  apply LanguageDef.validate_eq_nil_of_constructorAndRewrites
  · rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide +kernel
  · intro rewrite membership
    obtain rfl : rewrite = joinLeftRule := by simpa [contextualOnly] using membership
    exact joinLeftRule_validates

/-- The presentation selecting the contact and the contextual rule. -/
def contextualOnlyPresentation : InteractivePresentation where
  presentation := ⟨contextualOnly, contextualOnly_validate_eq_nil⟩
  interactingSort := ⟨TypeDecl.plain "Proc", List.Mem.head _⟩
  contactConstructor := ⟨contextualOnlyTerms[1], List.Mem.tail _ (List.Mem.head _)⟩
  interactionRewrite := ⟨joinLeftRule, List.Mem.head _⟩
  contactRepresentation := .binary
  representsContact := by rfl
  interactionHeaded := by rfl

/-- The language admits an interactive presentation. -/
theorem contextualOnly_admits : AdmitsInteractivePresentation contextualOnly :=
  contextualOnlyPresentation.admits

/-- Its selected rule is not a base rule. -/
theorem contextualOnly_not_baseInteraction :
    ¬ contextualOnlyPresentation.BaseInteraction := by
  decide

/-- No presentation of it selects a base rule: the language is not
interactive. -/
theorem contextualOnly_not_interactive : ¬ IsInteractive contextualOnly := by
  apply not_isInteractive_of_no_baseRewrite
  intro rewrite membership
  obtain rfl : rewrite = joinLeftRule := by simpa [contextualOnly] using membership
  decide

/-- A conditional contact site is not an object of the semantic iGSLT category. -/
theorem contextualOnly_not_IGSLT :
    ¬ ∃ theory : IGSLT, theory.presentation.presentation.language = contextualOnly := by
  rintro ⟨theory, sameLanguage⟩
  have interactive := theory.isInteractive
  rw [sameLanguage] at interactive
  exact contextualOnly_not_interactive interactive

/-- The theory has no reduction: from no term, to no term, with any premise
evaluator. -/
theorem contextualOnly_no_step (base : BasePremiseEvaluator) (source target : Pattern) :
    ¬ Step base contextualOnly source target := by
  apply not_step_of_rewrites_ask_reduction
  intro rule membership
  obtain rfl : rule = joinLeftRule := by simpa [contextualOnly] using membership
  exact ⟨_, List.Mem.head _, rfl⟩

end Mettapedia.GSLT.LanguageDef.Interaction.Controls
