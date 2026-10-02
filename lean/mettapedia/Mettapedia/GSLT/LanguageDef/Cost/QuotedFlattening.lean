import Mettapedia.GSLT.LanguageDef.ContinuedCategory

/-!
# Structural obstruction to merging nested quotation wrappers

Continued morphisms act by constructor-symbol maps. Such a map preserves the
argument tree, even before its separate quote-faithfulness law is imposed.
Consequently a nested binary wrapper over a nullary program cannot be sent to
a single wrapper over that program. This is stronger than a collision argument
for this structural arrow class, and requires no choice of signature algebra.
-/

namespace Mettapedia.GSLT.LanguageDef.Cost.QuotedFlattening

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- No constructor-symbol map can implement even this closed instance of
wrapper multiplication. The target signature is arbitrary. -/
theorem mapPattern_nestedWrapper_ne_singleWrapper
    (symbols : LanguageDefSymbolMap)
    (outer inner body targetWrapper targetBody : String)
    (innerSignature outerSignature targetSignature : Pattern) :
    mapPattern symbols
        (.apply outer [.apply inner [.apply body [], innerSignature],
          outerSignature]) ≠
      .apply targetWrapper [.apply targetBody [], targetSignature] := by
  simp [mapPattern, mapPatternList]

/-- Naturality makes the same obstruction visible on actual canonical keys:
target normalization cannot secretly perform a nonstructural flattening. -/
theorem canonicalKeyMap_nestedWrapper_ne_singleWrapper
    {source target : CIGSLT} (morphism : CIGSLT.Morphism source target)
    (key : source.CanonicalKey)
    (outer inner body targetWrapper targetBody : String)
    (innerSignature outerSignature targetSignature : Pattern)
    (shape : key.1.1 =
      .apply outer [.apply inner [.apply body [], innerSignature],
        outerSignature]) :
    (morphism.canonicalKeyMap key).1.1 ≠
      .apply targetWrapper [.apply targetBody [], targetSignature] := by
  rw [CIGSLT.Morphism.canonicalKeyMap_pattern, shape]
  exact mapPattern_nestedWrapper_ne_singleWrapper _ _ _ _ _ _ _ _ _

end Mettapedia.GSLT.LanguageDef.Cost.QuotedFlattening
