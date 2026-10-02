import Mettapedia.OSLF.Framework.ObserverExtension
import Mettapedia.GSLT.LanguageDef.Interaction.Strength

/-!
# How interactive the observer extension is

The observer extension adjoins, for each opened constructor, an opening rule,
a build rule and projection rules.  This module says what the extension keeps
of the interactive structure of the theory it extends, distinguishing base
rule heads from literal left-hand-side cut shape.

* **First strength: kept.**  The extension has the same sort, the same
  contact and the same selected base rule; it is interactive with the same
  cut whenever it passes the declaration gate.
* **Second strength: kept for an enlarged family.**  Its base rules are
  headed by the family of the theory, by the cut, or by one of the adjoined
  formers.
* **Literal cut shape: lost.** The opening rule's left side is a cut, a request
  beside the term to open.  The build and projection rules apply a former to
  the bundle of arguments; their left sides are not cuts.  As soon as one
  declared constructor is opened, not every rule's left side is a cut.

The last assertion concerns literal syntax. It does not establish failure
of a cut decomposition modulo equations or a property of quotient-level
proper transitions.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.Framework.ObserverExtension

/-- The opening rule is headed by the cut. -/
theorem patternHead?_openingRule (cut : CollType) (constructor : String) (arity : Nat) :
    patternHead? (openingRule cut constructor arity).left = some (.collection cut) :=
  rfl

/-- The build rule is headed by the build former. -/
theorem patternHead?_buildRule (constructor : String) (arity : Nat) :
    patternHead? (buildRule constructor arity).left =
      some (.constructor (buildLabel constructor)) :=
  rfl

/-- A projection rule is headed by its projection former. -/
theorem patternHead?_projectionRule (constructor : String) (arity index : Nat) :
    patternHead? (projectionRule constructor arity index).left =
      some (.constructor (getLabel constructor index)) :=
  rfl

/-! ## First strength: the same cut -/

namespace InteractivePresentation

/-- The same sort, contact and rule, selected in the observer extension. -/
def observed (presentation : InteractivePresentation) (cut : CollType)
    (opened : List String)
    (valid : (observerExtension presentation.presentation.language cut opened).validate = []) :
    InteractivePresentation where
  presentation := ⟨observerExtension presentation.presentation.language cut opened, valid⟩
  interactingSort := ⟨presentation.interactingSort.1,
    List.mem_append_left _ presentation.interactingSort.2⟩
  contactConstructor := ⟨presentation.contactConstructor.1,
    mem_terms_of_mem _ cut opened presentation.contactConstructor.2⟩
  interactionRewrite := ⟨presentation.interactionRewrite.1,
    mem_rewrites_of_mem _ cut opened presentation.interactionRewrite.2⟩
  contactRepresentation := presentation.contactRepresentation
  representsContact := presentation.representsContact
  interactionHeaded := presentation.interactionHeaded

/-- **The extension is interactive with the same cut.**  If the selected rule
of the theory is a base rule, the extension is interactive, with that rule
and that contact. -/
theorem observed_isInteractive (presentation : InteractivePresentation) (cut : CollType)
    (opened : List String)
    (valid : (observerExtension presentation.presentation.language cut opened).validate = [])
    (base : presentation.BaseInteraction) :
    IsInteractive (observerExtension presentation.presentation.language cut opened) ∧
      (presentation.observed cut opened valid).contactHead = presentation.contactHead ∧
      (presentation.observed cut opened valid).interactionRewrite.1 =
        presentation.interactionRewrite.1 :=
  ⟨(presentation.observed cut opened valid).isInteractive base, rfl, rfl⟩

end InteractivePresentation

/-! ## Second strength: an enlarged family -/

/-- The heads the extension adds: the cut and the adjoined formers. -/
def observerHeads (lang : LanguageDef) (cut : CollType) (opened : List String) :
    List PatternHead :=
  .collection cut :: (adjoinedLabels lang opened).map PatternHead.constructor

/-- **The base rules of the extension are headed by the theory's family, the
cut, or an adjoined former.** -/
theorem observerExtension_baseRewritesHeaded {lang : LanguageDef} {family : List PatternHead}
    (headed : BaseRewritesHeadedBy lang family) (cut : CollType) (opened : List String) :
    BaseRewritesHeadedBy (observerExtension lang cut opened)
      (family ++ observerHeads lang cut opened) := by
  intro rewrite membership base
  simp only [observerExtension, List.mem_append, List.mem_flatMap] at membership
  rcases membership with authored | ⟨declaration, declarationMember, ruleMember⟩
  · obtain ⟨head, inFamily, same⟩ := headed rewrite authored base
    exact ⟨head, List.mem_append_left _ inFamily, same⟩
  · have labels : ∀ label ∈ instrumentLabels declaration,
        PatternHead.constructor label ∈ observerHeads lang cut opened := by
      intro label labelMember
      exact List.mem_cons_of_mem _ (List.mem_map.mpr
        ⟨label, List.mem_flatMap.mpr ⟨declaration, declarationMember, labelMember⟩, rfl⟩)
    rcases instrumentRules_cases cut ruleMember with rfl | rfl | ⟨position, positionMember, rfl⟩
    · exact ⟨.collection cut, List.mem_append_right _ (List.mem_cons_self ..), rfl⟩
    · exact ⟨_, List.mem_append_right _ (labels _ (by simp [instrumentLabels])), rfl⟩
    · refine ⟨_, List.mem_append_right _ (labels _ ?_), rfl⟩
      simp only [instrumentLabels, List.mem_cons, List.mem_map]
      exact Or.inr (Or.inr (Or.inr ⟨position, positionMember, rfl⟩))

/-! ## Literal cut shape: lost -/

/-- Not every rule of the extension is a literal cut. Whatever presentation
of the extension is chosen, the build rule of an opened constructor has a
left side that is a former applied to one argument. This assertion does not
quantify over equation-equivalent representatives of that left side. -/
theorem observerExtension_not_everyRuleIsCut (presentation : InteractivePresentation)
    {lang : LanguageDef} {cut : CollType} {opened : List String}
    (extension : presentation.presentation.language = observerExtension lang cut opened)
    {declaration : GrammarRule} (isOpened : declaration ∈ openedRules lang opened) :
    ¬ presentation.EveryRuleIsCut := by
  apply presentation.not_everyRuleIsCut_of_rule
    (rewrite := buildRule declaration.label declaration.params.length)
  · rw [extension]
    exact buildRule_mem lang cut opened isOpened
  · intro isCut
    exact isCut

end Mettapedia.GSLT.LanguageDef
