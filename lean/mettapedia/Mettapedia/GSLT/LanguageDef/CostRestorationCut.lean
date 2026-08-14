import Mettapedia.GSLT.LanguageDef.CostRestorationRelation

/-!
# Context-indexed cuts through common restoration

A common-restoration apex relates two complete terms in one semantic-key
namespace.  Recursive clients sometimes need to retain how an inner apex is
used beneath a pair of aligned one-hole contexts before eliminating it.
`CommonRestorationCut` is that proof-relevant, Kripke-indexed carrier.

The source language, semantic cospan, and reflective declaration remain fixed
throughout a cut.  Contextual descent records the actual paired context
evidence; it cannot change the semantic namespace or manufacture an enclosing
normal-form equality.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

namespace CostStaticAtomKeyCospan

/-- A context-indexed derivation through common-restoration roots.

A terminal retains a complete restoration apex.  An `under` step retains the
aligned contexts and an inner cut at their common hole depth. -/
inductive CommonRestorationCut
    (source : CIGSLT)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl) :
    Nat → Pattern → Pattern → Type where
  | terminal
      {depth : Nat} {left right : Pattern}
      (apex : CommonRestorationApex source cospan declaration depth
        left right) :
      CommonRestorationCut source cospan declaration depth left right
  | under
      {depth holeDepth : Nat}
      {leftContext rightContext : OneHoleContext}
      {leftInner rightInner : Pattern}
      (contexts : CommonRestorationApex.Context
        (source := source) cospan declaration depth holeDepth
          leftContext rightContext)
      (inner : CommonRestorationCut source cospan declaration holeDepth
        leftInner rightInner) :
      CommonRestorationCut source cospan declaration depth
        (leftContext.fill leftInner) (rightContext.fill rightInner)

namespace CommonRestorationCut

/-- Introduce one contextual layer around a terminal restoration apex. -/
def congr
    {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth holeDepth : Nat}
    {leftContext rightContext : OneHoleContext}
    {leftInner rightInner : Pattern}
    (contexts : CommonRestorationApex.Context
      (source := source) cospan declaration depth holeDepth
        leftContext rightContext)
    (inner : CommonRestorationApex source cospan declaration holeDepth
      leftInner rightInner) :
    CommonRestorationCut source cospan declaration depth
      (leftContext.fill leftInner) (rightContext.fill rightInner) :=
  .under contexts (.terminal inner)

/-- Descend through aligned contexts without changing the semantic cospan or
declaration. -/
def descend
    {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth holeDepth : Nat}
    {leftContext rightContext : OneHoleContext}
    {leftInner rightInner : Pattern}
    (contexts : CommonRestorationApex.Context
      (source := source) cospan declaration depth holeDepth
        leftContext rightContext)
    (inner : CommonRestorationCut source cospan declaration holeDepth
      leftInner rightInner) :
    CommonRestorationCut source cospan declaration depth
      (leftContext.fill leftInner) (rightContext.fill rightInner) :=
  .under contexts inner

/-- Compose every retained contextual layer to the enclosing apex. -/
def toApex
    {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right : Pattern}
    (cut : CommonRestorationCut source cospan declaration depth left right) :
    CommonRestorationApex source cospan declaration depth left right :=
  match cut with
  | .terminal apex => apex
  | .under contexts inner => contexts.fill (toApex inner)

/-- Endpoint reindexing changes only the presentation of the indices. -/
def reindex
    {source : CIGSLT}
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    {cospan : CostStaticAtomKeyCospan leftKey rightKey}
    {declaration : ReflectivePresentationDecl}
    {depth : Nat} {left right left' right' : Pattern}
    (leftEq : left = left') (rightEq : right = right')
    (cut : CommonRestorationCut source cospan declaration depth left right) :
    CommonRestorationCut source cospan declaration depth left' right' := by
  cases leftEq
  cases rightEq
  exact cut

/-- Identity cut in the selected semantic namespace. -/
def refl
    (source : CIGSLT)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (pattern : Pattern) :
    CommonRestorationCut source cospan declaration depth pattern pattern :=
  .terminal (CommonRestorationApex.refl cospan declaration depth pattern)

/-- Functorial action of one rigid context on a cut.  Binder increments and
reflective quote resets are computed by `restorationDepthThroughContext`. -/
def throughSameContext
    (source : CIGSLT)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (context : OneHoleContext)
    {left right : Pattern}
    (inner : CommonRestorationCut source cospan declaration
      (restorationDepthThroughContext source depth context) left right) :
    CommonRestorationCut source cospan declaration depth
      (context.fill left) (context.fill right) :=
  .under (CommonRestorationApex.Context.refl cospan declaration depth context)
    inner

/-- Positive canary: any rigid context carries a reflexive cut. -/
def reflexiveThroughContext
    (source : CIGSLT)
    {leftCount rightCount : Nat}
    {leftKey : Fin leftCount → CostStaticAtomKey}
    {rightKey : Fin rightCount → CostStaticAtomKey}
    (cospan : CostStaticAtomKeyCospan leftKey rightKey)
    (declaration : ReflectivePresentationDecl)
    (depth : Nat) (context : OneHoleContext) (pattern : Pattern) :
    CommonRestorationCut source cospan declaration depth
      (context.fill pattern) (context.fill pattern) :=
  throughSameContext source cospan declaration depth context
    (refl source cospan declaration
      (restorationDepthThroughContext source depth context) pattern)

end CommonRestorationCut

end CostStaticAtomKeyCospan

end Mettapedia.GSLT.LanguageDef
