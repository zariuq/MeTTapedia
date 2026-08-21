/-
# Authored semantic atom keys

The authored (colour-erased) companion of `CostStaticAtomKey`: the
proof-free identity of one normalized authored frame parameter, with
realizations at either colour by constructor re-tagging.

This is the value level at which the rebased cross-colour formulation of
the hereditary Cost₁ obligation is stated: coloured realizations form a
split fibration over authored syntax, with erasure the bundle projection
and each colour's symbol action a section.  Realization is literal here:
`reifyAt` re-tags the authored normal's constructors by the colour symbol
action.
-/

import Mettapedia.GSLT.LanguageDef.CostStaticTyping
import Mettapedia.GSLT.LanguageDef.CostCanonicalSection
import Mettapedia.GSLT.LanguageDef.CostSemanticAtom

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.PatternCode

/-- Proof-free identity of one normalized authored-frame parameter.

Mirrors `CostStaticAtomKey` with the normalized value kept in the authored
constructor namespace: `reifyAt` maps it to either colour's realization.
Source and target fibers are both retained; encoded source or boundary
names are deliberately absent. -/
structure CostAuthoredAtomKey where
  sourceType : TypeExpr
  sourceSupport : List TypeExpr
  targetType : TypeExpr
  targetSupport : List TypeExpr
  authoredNormal : Pattern
deriving Repr, DecidableEq

namespace CostAuthoredAtomKey

/-- Realize an authored key at a chosen colour: the colour symbol action
re-tags each constructor of the authored normal while leaving binder
structure, indices, order, multiplicity, and rest variables untouched. -/
def reifyAt (source : CIGSLT) (color : CostStaticColor)
    (key : CostAuthoredAtomKey) : Pattern :=
  mapPattern (color.symbols source) key.authoredNormal

/-- The complete raw semantic key realized in one selected colour.  Types,
supports, and the authored normal move through the same symbol action, so a
typed realization can state one equality of complete keys rather than five
unrelated component equations. -/
def realizedKey (source : CIGSLT) (color : CostStaticColor)
    (key : CostAuthoredAtomKey) : CostStaticAtomKey where
  sourceType := mapTypeExpr (color.symbols source) key.sourceType
  sourceSupport := key.sourceSupport.map
    (mapTypeExpr (color.symbols source))
  targetType := mapTypeExpr (color.symbols source) key.targetType
  targetSupport := key.targetSupport.map
    (mapTypeExpr (color.symbols source))
  normal := key.reifyAt source color

@[simp]
theorem realizedKey_normal (source : CIGSLT) (color : CostStaticColor)
    (key : CostAuthoredAtomKey) :
    (key.realizedKey source color).normal = key.reifyAt source color := rfl

/-! Erase a colour from every constructor label of a pattern: successful
decodes recover the authored spelling; constructors not in the selected
colour's image are preserved unchanged (fail-open).  Free names, binders,
indices, order, multiplicity, collections, and rest variables are untouched. -/
mutual
  def eraseColor (color : CostStaticColor) : Pattern → Pattern
    | .bvar index => .bvar index
    | .fvar name => .fvar name
    | .apply constructor arguments =>
        .apply
          ((decodeCostStaticConstructor color constructor).getD constructor)
          (eraseColorList color arguments)
    | .lambda binder body => .lambda binder (eraseColor color body)
    | .multiLambda arity binders body =>
        .multiLambda arity binders (eraseColor color body)
    | .subst body replacement =>
        .subst (eraseColor color body) (eraseColor color replacement)
    | .collection collectionType elements rest =>
        .collection collectionType (eraseColorList color elements) rest

  /-- List companion of `eraseColor`; elementwise, order-preserving. -/
  def eraseColorList (color : CostStaticColor) : List Pattern → List Pattern
    | [] => []
    | pattern :: patterns =>
        eraseColor color pattern :: eraseColorList color patterns
end

/-- The list companion is elementwise erasure. -/
theorem eraseColorList_eq_map (color : CostStaticColor) (patterns : List Pattern) :
    eraseColorList color patterns = patterns.map (eraseColor color) := by
  induction patterns with
  | nil => rfl
  | cons member members ih =>
      simp only [eraseColorList, List.map_cons, ih]

/-- Elementwise realization-then-erasure on a list is the identity, given the
pointwise fact from `Pattern.inductionOn`'s elementwise hypothesis. -/
theorem map_eraseColor_mapPattern (source : CIGSLT) (color : CostStaticColor)
    (patterns : List Pattern)
    (ih : ∀ member, member ∈ patterns →
      eraseColor color (mapPattern (color.symbols source) member) = member) :
    (patterns.map (mapPattern (color.symbols source))).map (eraseColor color) =
      patterns := by
  induction patterns with
  | nil => rfl
  | cons member members ihTail =>
      rw [List.map_cons, List.map_cons,
        ih member List.mem_cons_self,
        ihTail (fun tailMember tailMembership =>
          ih tailMember (List.mem_cons_of_mem member tailMembership))]

/-- **Section law at the pattern carrier**: realization followed by same-colour
erasure is the identity on every authored pattern.  At the fibration level
this is `U ∘ C_c = Id` for the colour section `C_c = reifyAt color`. -/
theorem eraseColor_reifyAt (source : CIGSLT) (color : CostStaticColor)
    (pattern : Pattern) :
    eraseColor color (mapPattern (color.symbols source) pattern) = pattern := by
  induction pattern using Pattern.inductionOn with
  | hbvar index => simp only [mapPattern, eraseColor]
  | hfvar name => simp only [mapPattern, eraseColor]
  | happly constructor arguments ih =>
      simp only [mapPattern, eraseColor, mapPatternList_eq_map,
        eraseColorList_eq_map, CostStaticColor.symbols_constructor,
        decodeCostStaticConstructor_append, Option.getD_some]
      exact congrArg (Pattern.apply constructor)
        (map_eraseColor_mapPattern source color arguments ih)
  | hlambda binder body ih =>
      simp only [mapPattern, eraseColor, Pattern.lambda.injEq, true_and]
      exact ih
  | hmultiLambda arity binders body ih =>
      simp only [mapPattern, eraseColor, Pattern.multiLambda.injEq,
        true_and]
      exact ih
  | hsubst body replacement ihBody ihRepl =>
      simp only [mapPattern, eraseColor, Pattern.subst.injEq]
      exact ⟨ihBody, ihRepl⟩
  | hcollection collectionType elements rest ih =>
      simp only [mapPattern, eraseColor, mapPatternList_eq_map,
        eraseColorList_eq_map, Pattern.collection.injEq, true_and, and_true]
      exact map_eraseColor_mapPattern source color elements ih

/-- The authored normal is the unique same-colour erasure of its realization. -/
theorem reifyAt_eraseColor (source : CIGSLT) (color : CostStaticColor)
    (key : CostAuthoredAtomKey) :
    eraseColor color (key.reifyAt source color) = key.authoredNormal :=
  eraseColor_reifyAt source color key.authoredNormal

/-- Equality of complete authored keys is componentwise. -/
theorem ext_components {left right : CostAuthoredAtomKey}
    (sourceType : left.sourceType = right.sourceType)
    (sourceSupport : left.sourceSupport = right.sourceSupport)
    (targetType : left.targetType = right.targetType)
    (targetSupport : left.targetSupport = right.targetSupport)
    (authoredNormal : left.authoredNormal = right.authoredNormal) :
    left = right := by
  cases left
  cases right
  simp_all

end CostAuthoredAtomKey

/-- A proof-relevant realization leg from one authored semantic atom into a
selected Cost colour.  The endpoint remains an ordinary typed static atom;
`key_eq` certifies that all four fibres and its normal are exactly the
colour realization of the common authored key. -/
structure CostAuthoredAtomRealization (source : CIGSLT)
    (color : CostStaticColor) (targetFree : WellSorted.FreeTypeContext)
    (authored : CostAuthoredAtomKey) where
  atom : TypedCostStaticAtom source color targetFree
  key_eq : atom.key = authored.realizedKey source color

namespace CostAuthoredAtomRealization

/-- Two realization legs at the same colour select the same typed semantic
atom.  This is the exact same-colour specialization of the authored fibre,
not a definitional or carrier-level identification. -/
theorem atom_eq {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {authored : CostAuthoredAtomKey}
    (left right : CostAuthoredAtomRealization source color targetFree
      authored) :
    left.atom = right.atom :=
  TypedCostStaticAtom.ext (left.key_eq.trans right.key_eq.symm)

/-- Proof irrelevance leaves the typed endpoint atom as the complete identity
of a realization leg. -/
@[ext]
theorem ext {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    {authored : CostAuthoredAtomKey}
    {left right : CostAuthoredAtomRealization source color targetFree
      authored}
    (atomEquality : left.atom = right.atom) : left = right := by
  cases left
  cases right
  cases atomEquality
  rfl

end CostAuthoredAtomRealization

/-- A heterogeneous authored apex with two proof-relevant colour-realization
legs.  Unlike `CostStaticAtomKeyCospan`, the two raw endpoint keys need not be
equal when the colours differ; their common coordinate is `apex`. -/
structure CostAuthoredAtomCospan (source : CIGSLT)
    (leftColor rightColor : CostStaticColor)
    (targetFree : WellSorted.FreeTypeContext) where
  apex : CostAuthoredAtomKey
  left : CostAuthoredAtomRealization source leftColor targetFree apex
  right : CostAuthoredAtomRealization source rightColor targetFree apex

namespace CostAuthoredAtomCospan

/-- Reversing a heterogeneous cospan preserves the authored apex and swaps
its typed realization legs. -/
def symm {source : CIGSLT} {leftColor rightColor : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (cospan : CostAuthoredAtomCospan source leftColor rightColor targetFree) :
    CostAuthoredAtomCospan source rightColor leftColor targetFree where
  apex := cospan.apex
  left := cospan.right
  right := cospan.left

/-- At one colour, a heterogeneous cospan specializes to exact equality of
the existing typed raw atoms. -/
theorem sameColor_atoms_eq {source : CIGSLT} {color : CostStaticColor}
    {targetFree : WellSorted.FreeTypeContext}
    (cospan : CostAuthoredAtomCospan source color color targetFree) :
    cospan.left.atom = cospan.right.atom :=
  cospan.left.atom_eq cospan.right

end CostAuthoredAtomCospan

end Mettapedia.GSLT.LanguageDef
