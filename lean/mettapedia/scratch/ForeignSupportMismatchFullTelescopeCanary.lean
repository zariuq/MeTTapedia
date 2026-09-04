import Mettapedia.Languages.ProcessCalculi.RhoCalculus.CostHereditaryParallelFrontier
import «scratch».ForeignSupportMismatchCanary

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus
namespace ForeignSupportMismatchFullTelescopeCanary

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ReflectiveCanonical
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.LanguageDefContinuedInteraction
open ForeignSupportMismatchCanary

noncomputable def leftView : leftTree.StaticRootView .base := by
  have packed := leftViewPair
  have color := leftViewPair_color
  cases color
  exact packed.2

noncomputable def rightView : rightTree.StaticRootView .base := by
  have packed := rightViewPair
  have color := rightViewPair_color
  cases color
  exact packed.2

theorem rootsAligned : CanonicalRootAligned declaration leftPattern
    rightPattern := by
  apply CanonicalRootAligned.apply (by decide)
  exact .cons canonical_eq .nil

theorem color_is_foreign : (.base : CostStaticColor) ≠ .wrapped := by decide

end ForeignSupportMismatchFullTelescopeCanary
end Mettapedia.Languages.ProcessCalculi.RhoCalculus
