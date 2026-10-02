import Mettapedia.GSLT.LanguageDef.Interaction.Presentability
import Mettapedia.GSLT.LanguageDef.Interaction.HeterogeneousCut
import Mettapedia.GSLT.LanguageDef.InteractionCut

/-!
# Three strengths of "interactive"

The word is used at three strengths.

1. **Some base rule is headed by the contact.**  This is the definition: a
   sort, a same-sort contact on it, and a base rule headed by that contact.
2. **Every base rule is headed by a member of a distinguished family.**  This
   is what locating the events of a theory uses: a cut of a term is live only
   if its subterm is headed by the family.
3. **Every rule's left side is a cut.**  This is what an extension that puts a
   probe in interaction position uses: every rule, contextual rules included,
   has a left side that is the contact applied to two operands.

The third implies the second for the family consisting of the contact alone,
and neither implies the other otherwise: the second with a family of the
theory's choosing says nothing about same-sort contact, and the first says
nothing about the other rules.

The third is also read "up to the equations".  When the contact is a bag with
a unit, every sorted term is equal to a cut of itself with the unit, so that
reading holds of every rule and distinguishes nothing.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open EquationSemantics
open WellSorted

/-- What heads a pattern: a constructor label, or the kind of a bare
collection. -/
inductive PatternHead where
  | constructor (label : String)
  | collection (kind : CollType)
deriving DecidableEq, Repr

/-- The head of a pattern, when it has one. -/
def patternHead? : Pattern → Option PatternHead
  | .apply label _ => some (.constructor label)
  | .collection kind _ _ => some (.collection kind)
  | _ => none

/-- **Second strength.**  Every base rewrite of the language is headed by a
member of the family. -/
def BaseRewritesHeadedBy (language : LanguageDef) (family : List PatternHead) : Prop :=
  ∀ rewrite ∈ language.rewrites, IsBaseRewrite rewrite →
    ∃ head ∈ family, patternHead? rewrite.left = some head

namespace InteractivePresentation

/-- The head of the selected contact. -/
def contactHead (presentation : InteractivePresentation) : PatternHead :=
  match presentation.contactRepresentation with
  | .binary => .constructor presentation.contactConstructor.1.label
  | .collection kind => .collection kind

/-- A pattern that is literally a cut: the binary contact applied to two
operands, or a contact collection of at least two components, a named rest
counting as one. -/
def IsCutPattern (presentation : InteractivePresentation) : Pattern → Prop
  | .apply label [_, _] =>
      presentation.contactRepresentation = .binary ∧
        label = presentation.contactConstructor.1.label
  | .collection kind elements rest =>
      presentation.contactRepresentation = .collection kind ∧
        2 ≤ elements.length + rest.toList.length
  | _ => False

/-- **Third strength.**  Every rule's left side is literally a cut. -/
def EveryRuleIsCut (presentation : InteractivePresentation) : Prop :=
  ∀ rewrite ∈ presentation.presentation.language.rewrites,
    presentation.IsCutPattern rewrite.left

/-- The third strength, read up to the static equations. -/
def EveryRuleIsCutUpToEquations (base : BasePremiseEvaluator)
    (presentation : InteractivePresentation) : Prop :=
  ∀ rewrite ∈ presentation.presentation.language.rewrites,
    ∃ cut, EquationEquiv base presentation.presentation.language rewrite.left cut ∧
      presentation.IsCutPattern cut

/-- A cut is headed by the contact. -/
theorem patternHead?_of_isCutPattern (presentation : InteractivePresentation)
    {pattern : Pattern} (cut : presentation.IsCutPattern pattern) :
    patternHead? pattern = some presentation.contactHead := by
  match pattern, cut with
  | .apply label [_, _], ⟨binary, sameLabel⟩ =>
      simp [patternHead?, contactHead, binary, sameLabel]
  | .collection kind elements rest, ⟨collection, _⟩ =>
      simp [patternHead?, contactHead, collection]

/-- The selected interaction rewrite of a presentation at the third strength
is a cut; so is every other rule. -/
theorem interaction_isCut (presentation : InteractivePresentation)
    (everyRule : presentation.EveryRuleIsCut) :
    presentation.IsCutPattern presentation.interactionRewrite.1.left :=
  everyRule _ presentation.interactionRewrite.2

/-- **Third implies second**, for the family consisting of the contact. -/
theorem baseRewritesHeadedBy_of_everyRuleIsCut (presentation : InteractivePresentation)
    (everyRule : presentation.EveryRuleIsCut) :
    BaseRewritesHeadedBy presentation.presentation.language [presentation.contactHead] := by
  intro rewrite membership _
  exact ⟨presentation.contactHead, List.mem_singleton.mpr rfl,
    presentation.patternHead?_of_isCutPattern (everyRule rewrite membership)⟩

/-- The literal reading implies the reading up to the equations. -/
theorem everyRuleIsCutUpToEquations_of_everyRuleIsCut (base : BasePremiseEvaluator)
    (presentation : InteractivePresentation) (everyRule : presentation.EveryRuleIsCut) :
    presentation.EveryRuleIsCutUpToEquations base :=
  fun rewrite membership => ⟨rewrite.left, Relation.EqvGen.refl _, everyRule rewrite membership⟩

/-- A language at the second strength whose family is the contact alone has
only contact-headed base rewrites: a base rewrite headed by anything else
refutes it. -/
theorem not_baseRewritesHeadedBy_of_other_head (presentation : InteractivePresentation)
    {rewrite : RewriteRule}
    (membership : rewrite ∈ presentation.presentation.language.rewrites)
    (base : IsBaseRewrite rewrite) {head : PatternHead}
    (headed : patternHead? rewrite.left = some head)
    (other : head ≠ presentation.contactHead) :
    ¬ BaseRewritesHeadedBy presentation.presentation.language [presentation.contactHead] := by
  intro all
  obtain ⟨found, inFamily, same⟩ := all rewrite membership base
  obtain rfl := List.mem_singleton.mp inFamily
  rw [headed] at same
  exact other (Option.some.inj same)

/-- A rule whose left side is not a cut refutes the third strength. -/
theorem not_everyRuleIsCut_of_rule (presentation : InteractivePresentation)
    {rewrite : RewriteRule}
    (membership : rewrite ∈ presentation.presentation.language.rewrites)
    (notCut : ¬ presentation.IsCutPattern rewrite.left) :
    ¬ presentation.EveryRuleIsCut :=
  fun all => notCut (all rewrite membership)

/-- **A language with a rule read across a heterogeneous constructor has the
third strength under no interactive presentation.**  The rule read is a rule
of the language, and its left side is headed by a constructor that is not
the contact. -/
theorem not_everyRuleIsCut_of_heterogeneousReading (presentation : InteractivePresentation)
    (reading : HeterogeneousCutReading presentation.presentation.language) :
    ¬ presentation.EveryRuleIsCut := by
  apply presentation.not_everyRuleIsCut_of_rule reading.ruleMember
  rw [reading.source]
  rintro ⟨-, sameLabel⟩
  exact reading.contact_label_ne presentation sameLabel

end InteractivePresentation

/-! ## A unit for the contact makes every sorted term a cut -/

/-- **With a unit, the reading up to equations is empty.**  When a bag
constructor declares the flattening algebra with a unit, every pattern sorted
at its sort is equal to the two-component bag of itself and the unit. -/
theorem equationEquiv_cut_with_unit {base : BasePremiseEvaluator} {language : LanguageDef}
    {rule : GrammarRule} {kind : CollType} {algebra : CollectionAlgebra} {unit : String}
    (algebraRule : AlgebraRule language rule kind algebra)
    (flatten : algebra.flatten = true) (declaredUnit : algebra.unit = some unit)
    {pattern : Pattern} {free : FreeTypeContext} {bound : List TypeExpr}
    (typed : HasSort language free bound pattern rule.category) :
    EquationEquiv base language pattern
      (.collection kind [pattern, .apply unit []] none) := by
  obtain ⟨parameterName, parameters⟩ := algebraRule.selfSorted
  obtain ⟨unitRule, unitMember, unitLabel, unitCategory, unitParameters⟩ :=
    algebraRule.unitAuthored unit declaredUnit
  have unitTyped : HasType language free bound (.apply unit []) (.base rule.category) := by
    have typedUnit := HasType.constructor (language := language) (free := free)
      (bound := bound) (rule := unitRule) (arguments := []) unitMember
      (by
        rintro ⟨name, collectionType, elementType, shape⟩
        rw [unitParameters] at shape
        cases shape)
      (by rw [unitParameters]; exact .nil)
    rw [unitLabel, unitCategory] at typedUnit
    exact typedUnit
  have singletonSorted : SortedAt language (.collection kind [pattern] none) rule.category :=
    ⟨free, bound, HasType.collectionConstructor algebraRule.authored parameters
      (.cons typed (.nil _ _))⟩
  have pairSorted : SortedAt language
      (.collection kind ([pattern] ++ (.apply unit []) :: []) none) rule.category :=
    ⟨free, bound, HasType.collectionConstructor algebraRule.authored parameters
      (.cons typed (.cons unitTyped (.nil _ _)))⟩
  have toSingleton : EquationEquiv base language (.collection kind [pattern] none) pattern :=
    derivedInstance_equivalent
      (DerivedInstance.singleton algebraRule flatten singletonSorted)
  have dropUnit : EquationEquiv base language
      (.collection kind ([pattern] ++ (.apply unit []) :: []) none)
      (.collection kind ([pattern] ++ []) none) :=
    derivedInstance_equivalent
      (DerivedInstance.unitElim algebraRule declaredUnit pairSorted)
  have dropUnit' : EquationEquiv base language
      (.collection kind [pattern, .apply unit []] none) (.collection kind [pattern] none) := by
    simpa using dropUnit
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ toSingleton)
    (Relation.EqvGen.symm _ _ dropUnit')

end Mettapedia.GSLT.LanguageDef
