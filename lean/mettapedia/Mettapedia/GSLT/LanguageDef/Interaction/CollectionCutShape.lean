import Mettapedia.GSLT.LanguageDef.InteractionCut

/-!
# The operands of a rule headed by a collection contact

When the selected rule's left side is a collection of two listed elements and
the core contact of a cut is not an ordered binary constructor, the cut has
no envelope and its two operands are the two elements, in the order the rule
lists them.  The two elements must themselves contain no collection of two or
more listed elements, so that the core cannot sit inside one of them.

A core contact is an ordered binary constructor only when its constructor has
two plain parameters, so in a signature without such a constructor every core
is a collection.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open StructuralMorphism

mutual
  /-- Some subterm, the pattern included, is a collection of at least two
  listed elements. -/
  def containsWideCollection : Pattern → Bool
    | .bvar _ => false
    | .fvar _ => false
    | .apply _ arguments => containsWideCollectionList arguments
    | .lambda _ body => containsWideCollection body
    | .multiLambda _ _ body => containsWideCollection body
    | .subst body replacement =>
        containsWideCollection body || containsWideCollection replacement
    | .collection _ elements _ =>
        decide (2 ≤ elements.length) || containsWideCollectionList elements

  /-- The list form. -/
  def containsWideCollectionList : List Pattern → Bool
    | [] => false
    | pattern :: patterns =>
        containsWideCollection pattern || containsWideCollectionList patterns
end

/-- A list with a wide collection inside one of its members contains one. -/
theorem containsWideCollectionList_of_mem (before after : List Pattern) {pattern : Pattern}
    (shaped : containsWideCollection pattern = true) :
    containsWideCollectionList (before ++ pattern :: after) = true := by
  induction before with
  | nil => simp [containsWideCollectionList, shaped]
  | cons head tail recurse => simp [containsWideCollectionList, recurse]

/-- A pattern containing a filled wide collection contains a wide
collection. -/
theorem containsWideCollection_fill :
    ∀ (context : OneHoleContext) {core : Pattern},
      containsWideCollection core = true → containsWideCollection (context.fill core) = true
  | .hole, _, shaped => shaped
  | .apply _ before inner after, _, shaped => by
      simp [OneHoleContext.fill, containsWideCollection,
        containsWideCollectionList_of_mem before after
          (containsWideCollection_fill inner shaped)]
  | .lambda _ inner, _, shaped => by
      simpa [OneHoleContext.fill, containsWideCollection] using
        containsWideCollection_fill inner shaped
  | .multiLambda _ _ inner, _, shaped => by
      simpa [OneHoleContext.fill, containsWideCollection] using
        containsWideCollection_fill inner shaped
  | .substBody inner _, _, shaped => by
      simp [OneHoleContext.fill, containsWideCollection,
        containsWideCollection_fill inner shaped]
  | .substReplacement _ inner, _, shaped => by
      simp [OneHoleContext.fill, containsWideCollection,
        containsWideCollection_fill inner shaped]
  | .collection _ before inner after _, _, shaped => by
      simp [OneHoleContext.fill, containsWideCollection,
        containsWideCollectionList_of_mem before after
          (containsWideCollection_fill inner shaped)]

/-- A constructor is an ordered binary core contact only when it has two
plain parameters. -/
theorem params_of_coreContactRepresentation?_binary {sort : TypeDecl}
    {constructor : GrammarRule}
    (binary : coreContactRepresentation? sort constructor = some .binary) :
    ∃ first firstType second secondType,
      constructor.params = [.simple first firstType, .simple second secondType] := by
  unfold coreContactRepresentation? at binary
  split at binary
  · split at binary
    · exact ⟨_, _, _, _, by assumption⟩
    · cases binary
    · cases binary
  · cases binary

namespace InteractionCutPresentation

variable {theory : IGSLT}

/-- **The operands of a collection rule.**  When the selected rule's left
side lists two elements neither of which contains a wide collection, and the
core contact is not an ordered binary constructor, the cut has no envelope
and its two operands are the two elements in order. -/
theorem operands_of_collection_left (cut : InteractionCutPresentation theory)
    (collectionCore : cut.coreContact.representation ≠ .binary)
    {collectionType : CollType} {first second : Pattern} {rest : Option String}
    (left : theory.presentation.interactionRewrite.1.left =
      .collection collectionType [first, second] rest)
    (firstPlain : containsWideCollection first = false)
    (secondPlain : containsWideCollection second = false) :
    cut.program.schemaTerm = first ∧ cut.environment.schemaTerm = second := by
  have fills : cut.sourceShape.envelope.fill cut.sourceShape.core =
      .collection collectionType [first, second] rest :=
    cut.sourceShape.fillsSource.trans left
  have shape := cut.sourceShape.coreShape
  generalize cut.sourceShape.envelope = envelope at fills
  generalize cut.sourceShape.core = core at fills shape
  generalize cut.coreContact = contact at shape collectionCore
  generalize cut.program.schemaTerm = program at shape
  generalize cut.environment.schemaTerm = environment at shape
  cases shape with
  | binary binaryContact => exact absurd binaryContact collectionCore
  | @collection coreType context coreRest _ =>
      have coreShaped : containsWideCollection
          (.collection coreType (program :: environment :: context) coreRest) = true := by
        simp [containsWideCollection]
      cases envelope with
      | hole =>
          simp only [OneHoleContext.fill, Pattern.collection.injEq, List.cons.injEq] at fills
          exact ⟨fills.2.1.1, fills.2.1.2.1⟩
      | collection frameType before inner after frameRest =>
          simp only [OneHoleContext.fill, Pattern.collection.injEq] at fills
          have innerShaped := containsWideCollection_fill inner coreShaped
          have member : inner.fill
              (.collection coreType (program :: environment :: context) coreRest) ∈
                [first, second] := by
            rw [← fills.2.1]
            simp
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with same | same
          · rw [same, firstPlain] at innerShaped
            cases innerShaped
          · rw [same, secondPlain] at innerShaped
            cases innerShaped
      | apply _ _ _ _ => simp [OneHoleContext.fill] at fills
      | lambda _ _ => simp [OneHoleContext.fill] at fills
      | multiLambda _ _ _ => simp [OneHoleContext.fill] at fills
      | substBody _ _ => simp [OneHoleContext.fill] at fills
      | substReplacement _ _ => simp [OneHoleContext.fill] at fills

end InteractionCutPresentation

end Mettapedia.GSLT.LanguageDef
