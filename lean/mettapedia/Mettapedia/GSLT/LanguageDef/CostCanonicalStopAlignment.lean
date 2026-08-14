import Mettapedia.GSLT.LanguageDef.CostFvarAlignedCanonicalization
import Mettapedia.OSLF.MeTTaIL.ReflectiveCanonicalStopAlignment

/-!
# Keyed canonicalization over collapsing-stop alignment

Rigid constructors commute with two-depth keyed canonicalization.  Quote
applications and bare parallel collections are the only exceptional roots;
`CanonicalStopAligned` stops there and delegates their full canonical output
to a client callback.

This is deliberately weaker than unrestricted semantic-leaf congruence.
Traversing a Quote or bare parallel would be unsound because absorption and
sorting may observe endpoint-local differences.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.OSLF.MeTTaIL.ReflectiveSubstitution

mutual
  /-- Keyed canonicalization preserves stopped structural alignment.  The
  client supplies semantic evidence for exact rigid free variables and for
  the explicitly stopped collapsing pairs. -/
  def canonicalStopAligned_canonicalizeByDepths
      {Key : Type} [LinearOrder Key]
      {stop relation : Pattern → Pattern → Prop}
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name))
      (callback : ∀ availableDepth scopeDepth {left right},
        stop left right →
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
            left)
          (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
            right)) :
      ∀ {left right}, CanonicalStopAligned declaration stop left right →
        ∀ availableDepth scopeDepth,
          PatternLeafAligned relation
            (canonicalizeByDepths leftKey declaration availableDepth
              scopeDepth left)
            (canonicalizeByDepths rightKey declaration availableDepth
              scopeDepth right)
    | _, _, .leaf given, availableDepth, scopeDepth =>
        callback availableDepth scopeDepth given
    | _, _, .bvar index, _, _ => .bvar index
    | _, _, .fvar name, _, _ => .leaf (fvarReflexive name)
    | _, _, @CanonicalStopAligned.apply _ _ constructor ne _ _ arguments,
        availableDepth, scopeDepth => by
        have normalizedArguments :=
          canonicalStopAlignedList_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback arguments availableDepth scopeDepth
        have notQuoteBeq :
            (constructor == declaration.quoteConstructor) = false :=
          beq_eq_false_iff_ne.mpr ne
        simp only [canonicalizeByDepths, finishNormalizeReflectiveApply,
          notQuoteBeq, Bool.false_eq_true, if_false]
        exact .apply constructor normalizedArguments
    | _, _, .lambda binder body, availableDepth, scopeDepth =>
        .lambda binder
          (canonicalStopAligned_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback body (availableDepth + 1)
              (scopeDepth + 1))
    | _, _, .multiLambda arity binders body, availableDepth, scopeDepth =>
        .multiLambda arity binders
          (canonicalStopAligned_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback body (availableDepth + arity)
              (scopeDepth + arity))
    | _, _, .subst body replacement, availableDepth, scopeDepth =>
        .subst
          (canonicalStopAligned_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback body (availableDepth + 1)
              (scopeDepth + 1))
          (canonicalStopAligned_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback replacement availableDepth scopeDepth)
    | _, _, @CanonicalStopAligned.collection _ _ collectionType ne _ _
        elements, availableDepth, scopeDepth => by
        have normalizedElements :=
          canonicalStopAlignedList_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback elements availableDepth scopeDepth
        have notParallelBeq :
            (collectionType == declaration.parallelCollection) =
              false :=
          beq_eq_false_iff_ne.mpr ne
        simpa [canonicalizeByDepths, notParallelBeq] using
          (PatternLeafAligned.collection collectionType none
            normalizedElements)
    | _, _, .collectionRest collectionType rest elements, availableDepth,
        scopeDepth => by
        have normalizedElements :=
          canonicalStopAlignedList_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback elements availableDepth scopeDepth
        simpa [canonicalizeByDepths] using
          (PatternLeafAligned.collection collectionType (some rest)
            normalizedElements)

  /-- Listwise companion of
  `canonicalStopAligned_canonicalizeByDepths`. -/
  def canonicalStopAlignedList_canonicalizeByDepths
      {Key : Type} [LinearOrder Key]
      {stop relation : Pattern → Pattern → Prop}
      (leftKey rightKey : Nat → Nat → Pattern → Key)
      (declaration : ReflectivePresentationDecl)
      (fvarReflexive : ∀ name, relation (.fvar name) (.fvar name))
      (callback : ∀ availableDepth scopeDepth {left right},
        stop left right →
        PatternLeafAligned relation
          (canonicalizeByDepths leftKey declaration availableDepth scopeDepth
            left)
          (canonicalizeByDepths rightKey declaration availableDepth scopeDepth
            right)) :
      ∀ {left right}, CanonicalStopAlignedList declaration stop left right →
        ∀ availableDepth scopeDepth,
          PatternLeafAlignedList relation
            (canonicalizeListByDepths leftKey declaration availableDepth
              scopeDepth left)
            (canonicalizeListByDepths rightKey declaration availableDepth
              scopeDepth right)
    | _, _, .nil, _, _ => .nil
    | _, _, .cons head tail, availableDepth, scopeDepth =>
        .cons
          (canonicalStopAligned_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback head availableDepth scopeDepth)
          (canonicalStopAlignedList_canonicalizeByDepths
            leftKey rightKey declaration
            fvarReflexive callback tail availableDepth scopeDepth)
end

/-! ## Canary properties -/

/-- The rigid free-variable arm genuinely needs the supplied semantic
reflexivity fact: syntax alone cannot manufacture an arbitrary relation. -/
theorem patternLeafAligned_fvar_fvar_iff
    {relation : Pattern → Pattern → Prop} {name : String} :
    PatternLeafAligned relation (.fvar name) (.fvar name) ↔
      relation (.fvar name) (.fvar name) := by
  constructor
  · intro aligned
    cases aligned with
    | leaf related => exact related
  · exact PatternLeafAligned.leaf

/-- The eliminator preserves an ordinary rigid free variable without
invoking the collapsing callback. -/
example {Key : Type} [LinearOrder Key]
    (key : Nat → Nat → Pattern → Key)
    (declaration : ReflectivePresentationDecl) (name : String)
    (availableDepth scopeDepth : Nat) :
    PatternLeafAligned (· = ·)
      (canonicalizeByDepths key declaration availableDepth scopeDepth
        (.fvar name))
      (canonicalizeByDepths key declaration availableDepth scopeDepth
        (.fvar name)) :=
  canonicalStopAligned_canonicalizeByDepths key key declaration
    (fun _ => rfl)
    (fun _ _ {_ _} impossible => False.elim impossible)
    (.fvar name) availableDepth scopeDepth

/-- In particular, a relation that rejects every semantic leaf cannot align
even identical free variables. -/
example (name : String) :
    ¬ PatternLeafAligned (fun _ _ => False) (.fvar name) (.fvar name) := by
  intro aligned
  exact patternLeafAligned_fvar_fvar_iff.mp aligned

end Mettapedia.GSLT.LanguageDef
