import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryProviderBuilt

open Mettapedia.GSLT.LanguageDef
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus

def zb : Pattern := .apply (costBaseConstructorName "PZero") []
def zw : Pattern := .apply (costWrappedConstructorName "PZero") []
def qb : Pattern := .apply (costBaseConstructorName "NQuote") [zb]
def qw : Pattern := .apply (costWrappedConstructorName "NQuote") [zw]

/-- **The canonical sort key is colour-sensitive.** -/
theorem patternCode_colour_sensitive :
    Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode zb ≠
      Mettapedia.OSLF.MeTTaIL.PatternCode.patternCode zw := by decide

/-- **Two colourings of one authored two-element bag sort into different
orders.**  Sorting is therefore NOT natural in colour erasure. -/
theorem sortPatterns_not_natural_in_colour :
    Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns [zb, qw] ≠
      Mettapedia.OSLF.MeTTaIL.PatternCode.sortPatterns [zw, qb] := by decide

end Mettapedia.Languages.ProcessCalculi.RhoCalculus
