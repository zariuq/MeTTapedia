import Mettapedia.GSLT.LanguageDef.ContinuedCategory

/-!
# What an interaction cut forces on the selected rule

An interaction cut is read off the selected rule, so its existence constrains
the shape of that rule.  This module extracts three such constraints.

* When the left side is a binary application whose two operands contain
  nothing that could itself be an ordered contact, the cut's core is the left
  side and its two operands are those of the left side.
* An operand that is a constructor application is an introduction by the
  constructor with that label, and one of its arguments is the continuation,
  which is a schema variable.
* A contractum that is a constructor application is headed by the residual
  constructor; in a continued theory the residual constructor is neither of
  the two introductions.

Each is a necessary condition, used to show that a given iGSLT is not the
underlying theory of any continued one.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism
open WellSorted

mutual
  /-- Some subterm, the pattern included, is a binary application or a
  collection of at least two listed elements: the shapes an ordered contact
  core can take. -/
  def containsContactShape : Pattern → Bool
    | .bvar _ => false
    | .fvar _ => false
    | .apply _ arguments =>
        arguments.length == 2 || containsContactShapeList arguments
    | .lambda _ body => containsContactShape body
    | .multiLambda _ _ body => containsContactShape body
    | .subst body replacement =>
        containsContactShape body || containsContactShape replacement
    | .collection _ elements _ =>
        decide (2 ≤ elements.length) || containsContactShapeList elements

  /-- The list form. -/
  def containsContactShapeList : List Pattern → Bool
    | [] => false
    | pattern :: patterns =>
        containsContactShape pattern || containsContactShapeList patterns
end

/-- A member of a list with no contact shape has none. -/
theorem containsContactShape_of_mem {patterns : List Pattern}
    (none : containsContactShapeList patterns = false) {pattern : Pattern}
    (membership : pattern ∈ patterns) : containsContactShape pattern = false := by
  induction patterns with
  | nil => cases membership
  | cons head tail recurse =>
      simp only [containsContactShapeList, Bool.or_eq_false_iff] at none
      rcases List.mem_cons.mp membership with rfl | inTail
      · exact none.1
      · exact recurse none.2 inTail

/-- An ordered contact core has a contact shape. -/
theorem containsContactShape_of_cutSourceShape {presentation : ValidatedLanguageDef}
    {contact : CoreContactPresentation presentation} {program environment core : Pattern}
    (shape : CutSourceShape contact program environment core) :
    containsContactShape core = true := by
  cases shape with
  | binary _ => simp [containsContactShape]
  | collection context rest _ => simp [containsContactShape]

/-- A pattern containing a filled contact shape contains a contact shape. -/
theorem containsContactShape_fill :
    ∀ (context : OneHoleContext) {core : Pattern},
      containsContactShape core = true → containsContactShape (context.fill core) = true
  | .hole, _, shaped => shaped
  | .apply label before inner after, core, shaped => by
      have innerShaped := containsContactShape_fill inner shaped
      have listed : containsContactShapeList (before ++ inner.fill core :: after) = true := by
        induction before with
        | nil => simp [containsContactShapeList, innerShaped]
        | cons head tail recurse => simp [containsContactShapeList, recurse]
      simp [OneHoleContext.fill, containsContactShape, listed]
  | .lambda _ inner, _, shaped => by
      simpa [OneHoleContext.fill, containsContactShape] using
        containsContactShape_fill inner shaped
  | .multiLambda _ _ inner, _, shaped => by
      simpa [OneHoleContext.fill, containsContactShape] using
        containsContactShape_fill inner shaped
  | .substBody inner _, _, shaped => by
      simp [OneHoleContext.fill, containsContactShape,
        containsContactShape_fill inner shaped]
  | .substReplacement _ inner, _, shaped => by
      simp [OneHoleContext.fill, containsContactShape,
        containsContactShape_fill inner shaped]
  | .collection collectionType before inner after rest, core, shaped => by
      have innerShaped := containsContactShape_fill inner shaped
      have listed : containsContactShapeList (before ++ inner.fill core :: after) = true := by
        induction before with
        | nil => simp [containsContactShapeList, innerShaped]
        | cons head tail recurse => simp [containsContactShapeList, recurse]
      simp [OneHoleContext.fill, containsContactShape, listed]

/-- Renaming symbols does not change whether a list contains a contact
shape, when it does not for each member. -/
theorem containsContactShapeList_map {function : Pattern → Pattern} :
    ∀ (patterns : List Pattern),
      (∀ pattern ∈ patterns,
        containsContactShape (function pattern) = containsContactShape pattern) →
      containsContactShapeList (patterns.map function) = containsContactShapeList patterns
  | [], _ => rfl
  | head :: tail, pointwise => by
      simp only [List.map_cons, containsContactShapeList,
        pointwise head (List.mem_cons_self ..),
        containsContactShapeList_map tail (fun pattern membership =>
          pointwise pattern (List.mem_cons_of_mem _ membership))]

/-- The contact shape of a pattern is a matter of its form: renaming symbols
does not change it. -/
theorem containsContactShape_mapPattern (symbols : LanguageDefSymbolMap) (pattern : Pattern) :
    containsContactShape (mapPattern symbols pattern) = containsContactShape pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => rfl
  | hfvar name => rfl
  | happly label arguments recurse =>
      simp [mapPattern, containsContactShape, containsContactShapeList_map arguments recurse]
  | hlambda binder body recurse => simpa [mapPattern, containsContactShape] using recurse
  | hmultiLambda arity binders body recurse =>
      simpa [mapPattern, containsContactShape] using recurse
  | hsubst body replacement recurseBody recurseReplacement =>
      simp [mapPattern, containsContactShape, recurseBody, recurseReplacement]
  | hcollection collectionType elements rest recurse =>
      simp [mapPattern, containsContactShape, containsContactShapeList_map elements recurse]

namespace InteractionCutPresentation

variable {theory : IGSLT}

/-- **The operands of a binary rule.**  When the selected rule's left side is
a binary application whose operands contain no contact shape, the cut has no
envelope and its two operands are those of the left side. -/
theorem operands_of_binary_left (cut : InteractionCutPresentation theory)
    {label : String} {first second : Pattern}
    (left : theory.presentation.interactionRewrite.1.left = .apply label [first, second])
    (firstPlain : containsContactShape first = false)
    (secondPlain : containsContactShape second = false) :
    cut.program.schemaTerm = first ∧ cut.environment.schemaTerm = second := by
  have fills : cut.sourceShape.envelope.fill cut.sourceShape.core =
      .apply label [first, second] := cut.sourceShape.fillsSource.trans left
  have coreShaped := containsContactShape_of_cutSourceShape cut.sourceShape.coreShape
  generalize cut.sourceShape.envelope = envelope at fills
  generalize coreValue : cut.sourceShape.core = core at fills coreShaped
  have shape := cut.sourceShape.coreShape
  rw [coreValue] at shape
  cases envelope with
  | hole =>
      simp only [OneHoleContext.fill] at fills
      subst fills
      generalize cut.coreContact = contact at shape
      generalize cut.program.schemaTerm = program at shape
      generalize cut.environment.schemaTerm = environment at shape
      generalize source : Pattern.apply label [first, second] = pattern at shape
      cases shape with
      | binary _ =>
          simp only [Pattern.apply.injEq, List.cons.injEq, and_true] at source
          exact ⟨source.2.1.symm, source.2.2.symm⟩
      | collection _ _ _ => cases source
  | apply constructor before inner after =>
      simp only [OneHoleContext.fill, Pattern.apply.injEq] at fills
      obtain ⟨-, arguments⟩ := fills
      have innerShaped := containsContactShape_fill inner coreShaped
      have member : inner.fill core ∈ [first, second] := by
        rw [← arguments]
        simp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with same | same
      · rw [same, firstPlain] at innerShaped
        cases innerShaped
      · rw [same, secondPlain] at innerShaped
        cases innerShaped
  | lambda _ _ => simp [OneHoleContext.fill] at fills
  | multiLambda _ _ _ => simp [OneHoleContext.fill] at fills
  | substBody _ _ => simp [OneHoleContext.fill] at fills
  | substReplacement _ _ => simp [OneHoleContext.fill] at fills
  | collection _ _ _ _ _ => simp [OneHoleContext.fill] at fills

end InteractionCutPresentation

namespace InteractionOperandProfile

variable {presentation : InteractivePresentation}

/-- **An operand that is a constructor application is an introduction.**  Its
constructor has that label, and its continuation, a schema variable, is one
of its arguments. -/
theorem of_apply (operand : InteractionOperandProfile presentation)
    {label : String} {arguments : List Pattern}
    (shape : operand.schemaTerm = .apply label arguments) :
    operand.constructor.1.label = label ∧
      arguments[operand.continuation.index]? = some operand.continuationPattern := by
  obtain ⟨constructor, schemaTerm, continuation, continuationPattern, continuationVariable,
    subject, form⟩ := operand
  simp only at shape
  subst shape
  cases form with
  | introduced represented continuationSelected =>
      exact ⟨represented.2.1.symm, continuationSelected⟩
  | direct same =>
      exfalso
      rw [← same] at continuationVariable
      cases continuationVariable

/-- The continuation of an operand is a schema variable or a schema variable
under a binder: never a constructor application. -/
theorem continuationPattern_ne_apply (operand : InteractionOperandProfile presentation)
    (label : String) (arguments : List Pattern) :
    operand.continuationPattern ≠ .apply label arguments := by
  intro same
  have continuationVariable := operand.continuationVariable
  rw [same] at continuationVariable
  cases continuationVariable

end InteractionOperandProfile

namespace ContinuationRetypingPlan

/-- **A covered contractum is not headed by an introduction.**  When the
contractum is a constructor application, its head is the residual
constructor, and a continuation signature contains neither introduction of
the cut. -/
theorem contractum_head_ne_introductions {theory : IGSLT}
    {cut : InteractionCutPresentation theory} (plan : ContinuationRetypingPlan cut)
    {label : String} {arguments : List Pattern}
    (right : theory.presentation.interactionRewrite.1.right = .apply label arguments) :
    cut.program.constructor.1.label ≠ label ∧
      cut.environment.constructor.1.label ≠ label := by
  have covered := plan.residualCovered
  generalize cut.residual = residual at covered
  generalize contractum : theory.presentation.interactionRewrite.1.right = pattern
    at residual right
  cases residual with
  | constructor residualConstructor represented =>
      subst right
      have membership : residualConstructor ∈ continuationConstructors cut := covered
      have distinct := (ContinuationRetypingPlan.mem_continuationConstructors_iff
        cut residualConstructor).mp membership
      have residualLabel : label = residualConstructor.1.label := represented.2.1
      constructor
      · intro same
        apply distinct.1
        exact ContinuationRetypingPlan.authoredConstructorLabel_injective _
          (residualLabel.symm.trans same.symm)
      · intro same
        apply distinct.2
        exact ContinuationRetypingPlan.authoredConstructorLabel_injective _
          (residualLabel.symm.trans same.symm)
  | substitution body replacement => cases right

end ContinuationRetypingPlan

namespace CIGSLT

/-- The contractum of a continued theory is not headed by an introduction. -/
theorem contractum_head_ne_introductions (theory : CIGSLT)
    {label : String} {arguments : List Pattern}
    (right : theory.theory.presentation.interactionRewrite.1.right =
      .apply label arguments) :
    theory.cut.program.constructor.1.label ≠ label ∧
      theory.cut.environment.constructor.1.label ≠ label :=
  theory.continuationRetyping.contractum_head_ne_introductions right

end CIGSLT

end Mettapedia.GSLT.LanguageDef
