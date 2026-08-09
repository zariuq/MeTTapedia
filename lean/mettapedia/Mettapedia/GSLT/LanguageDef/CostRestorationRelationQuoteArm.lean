import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Aligned apex arm for language-level quote heads

`CommonRestorationApex.of_canonicalRootAligned` requires every aligned
application head to be an ordinary constructor of the generated language.
That excludes a real typed configuration: both endpoints headed by a quote
constructor of the *other* static colour.  Such a head is not this
declaration's own quote — so the aligned inversion applies and keyed
canonicalization does not reset its child depth — yet it is a language-level
quote, so the apex relation compares its children at visible depth zero.

This arm closes exactly that configuration.  The keyed children remain at
the ambient endpoint depths; only the relation's depth index drops to zero,
which the recursive callback supports directly.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical

namespace CostStaticAtomKeyCospan

namespace CommonRestorationApex

/-- Aligned application congruence at a language-level quote head that is
not the declaration's own quote constructor.  Children are compared at
visible depth zero on both sides, while their keyed forms remain at the
ambient endpoint depths. -/
theorem of_canonicalRootAligned_languageQuoteHead
    {source : CIGSLT} {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (close : ∀ leftChildDepth rightChildDepth childRootDepth
      {leftChild rightChild : Pattern},
      canonicalize declaration leftChild = canonicalize declaration rightChild →
        CommonRestorationApex source cospan declaration childRootDepth
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration leftChildDepth leftChild)
          (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
            declaration rightChildDepth rightChild))
    {leftDepth rightDepth rootDepth : Nat} {constructor : String}
    {leftArguments rightArguments : List Pattern}
    (ne : constructor ≠ declaration.quoteConstructor)
    (quoteHead : ReflectiveContextSupport.isQuoteConstructor
      source.costWholeReflectionProfile constructor = true)
    (children : List.Forall₂
      (fun leftChild rightChild =>
        canonicalize declaration leftChild =
          canonicalize declaration rightChild)
      leftArguments rightArguments) :
    CommonRestorationApex source cospan declaration rootDepth
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration leftDepth (.apply constructor leftArguments))
      (canonicalizeByAt (cospan.commonSemanticPatternKeyAt source)
        declaration rightDepth (.apply constructor rightArguments)) := by
  let key := cospan.commonSemanticPatternKeyAt source
  have closeList : ∀ leftChildDepth rightChildDepth childRootDepth
      {leftChildren rightChildren : List Pattern},
      List.Forall₂
          (fun leftChild rightChild =>
            canonicalize declaration leftChild =
              canonicalize declaration rightChild)
          leftChildren rightChildren →
        CommonRestorationApexList source cospan declaration childRootDepth
          (canonicalizeListByAt key declaration leftChildDepth leftChildren)
          (canonicalizeListByAt key declaration rightChildDepth
            rightChildren) := by
    intro leftChildDepth rightChildDepth childRootDepth leftChildren
      rightChildren related
    rw [canonicalizeListByAt_eq_map, canonicalizeListByAt_eq_map]
    induction related with
    | nil => exact .nil childRootDepth
    | cons headRelated _ inductionHypothesis =>
        exact .cons
          (close leftChildDepth rightChildDepth childRootDepth headRelated)
          inductionHypothesis
  have arguments : CommonRestorationApexList source cospan declaration
      (if ReflectiveContextSupport.isQuoteConstructor
          source.costWholeReflectionProfile constructor then 0 else rootDepth)
      (canonicalizeListByAt key declaration leftDepth leftArguments)
      (canonicalizeListByAt key declaration rightDepth rightArguments) := by
    simpa [quoteHead] using
      closeList leftDepth rightDepth 0 children
  simpa [canonicalizeByAt, ne] using
    (CommonRestorationApex.apply constructor arguments)

end CommonRestorationApex

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
