import Mettapedia.Languages.ProcessCalculi.MORK.AuthoredContextBridge

/-!
# Collection-shaped MORK zipper contexts

Collections receive no special reduction semantics in this module.  The only
result proved here is representational: when an authored one-hole context has
collection shape, its translation is an exact MORK lens update.  Reduction
authority remains in the language's authored contextual rules.
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts

private abbrev ILPattern := Mettapedia.OSLF.MeTTaIL.Syntax.Pattern

/-- Replacing the hole of a collection-shaped context is represented exactly
by a MORK zipper lens.  This theorem grants no reduction authority. -/
theorem collectionContext_lensRel
    (collectionType : CollType) (before after : List ILPattern)
    (rest : Option String) (source target : ILPattern) :
    LensRel
      (morkPatternToAtom
        ((OneHoleContext.collection collectionType before .hole after rest).fill source))
      (morkPatternToAtom source)
      (morkPatternToAtom target)
      (morkPatternToAtom
        ((OneHoleContext.collection collectionType before .hole after rest).fill target)) :=
  oneHoleContext_lensRel _ source target

/-- If the collection-shaped frame is authored by a language rule, the bridge
retains both the authorizing rule witness and the exact zipper realization. -/
theorem authoredCollectionContext_lensRel
    {lang : LanguageDef} {sourceSort targetSort : String}
    {collectionType : CollType} {before after : List ILPattern}
    {rest : Option String}
    (authored : AuthoredContextFrame lang sourceSort targetSort
      (.collection collectionType before .hole after rest))
    (source target : ILPattern) :
    ∃ rule ∈ lang.rewrites,
      RuleAuthorizesContext rule
        (.collection collectionType before .hole after rest) ∧
      LensRel
        (morkPatternToAtom
          ((OneHoleContext.collection collectionType before .hole after rest).fill source))
        (morkPatternToAtom source)
        (morkPatternToAtom target)
        (morkPatternToAtom
          ((OneHoleContext.collection collectionType before .hole after rest).fill target)) :=
  authoredContextFrame_lensRel authored source target

/-! ## Boundary examples -/

/-- Positive: a bag-element occurrence has an exact zipper update. -/
example :
    LensRel
      (morkPatternToAtom (.collection .hashBag [.fvar "before", .fvar "x"] none))
      (morkPatternToAtom (.fvar "x"))
      (morkPatternToAtom (.fvar "y"))
      (morkPatternToAtom (.collection .hashBag [.fvar "before", .fvar "y"] none)) := by
  simpa [OneHoleContext.fill] using
    collectionContext_lensRel .hashBag [.fvar "before"] [] none
      (.fvar "x") (.fvar "y")

private def noContextLanguage : LanguageDef where
  name := "no-context-rules"
  types := []
  terms := []
  equations := []
  rewrites := []

/-- Negative: collection shape alone emits no executable contextual rule. -/
example (base : Mettapedia.OSLF.MeTTaIL.ContextualStep.BasePremiseEvaluator)
    (source : ILPattern) (fuel : Nat) :
    compiledContextRules base noContextLanguage fuel source = [] := by
  cases fuel <;> rfl

end Mettapedia.Languages.ProcessCalculi.MORK
