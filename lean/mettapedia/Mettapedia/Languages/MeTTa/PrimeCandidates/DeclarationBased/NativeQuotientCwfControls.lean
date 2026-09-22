import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveQuotientCwf
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveContextualQuotient
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedQuotientControls
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConversionFibres
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeFormedFibreControls
import Mettapedia.GSLT.Core.ContextualLadderTerminal

/-! # Concrete controls for comprehension over formed conversion classes -/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased
set_option autoImplicit false

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveContextual.QuotientCwf
open _root_.CategoryTheory FormationSensitive
namespace Controls

abbrev context : (cwf HOLNativeRelatorCompatibility.rules).Ctx :=
  (quotientProjection HOLNativeRelatorCompatibility.rules).obj Common.context

def wireType : (cwf HOLNativeRelatorCompatibility.rules).Ty context := QType.mk Common.wireType

def projected (wire : NativeWireData.Wire) :
    (cwf HOLNativeRelatorCompatibility.rules).Tm context wireType :=
  TermFibre.mk (Common.projected wire)

def result (wire : NativeWireData.Wire) :
    (cwf HOLNativeRelatorCompatibility.rules).Tm context wireType :=
  TermFibre.mk (Common.result wire)

/-- A real computation is identified in the constructed CwF's term fibre. -/
theorem projected_is_result (wire : NativeWireData.Wire) : projected wire = result wire :=
  (TermFibre.mk_eq_iff _ _).mpr (Common.projected_converts_result wire)

/-- Distinct actual data remain distinct in the very same constructed fibre. -/
theorem natural_result_equal_iff (first second : Nat) :
    result (.natural first) = result (.natural second) ↔ first = second :=
  (TermFibre.mk_eq_iff _ _).trans (QuotientControls.natural_conversion_iff first second)

theorem seven_is_not_eight : result (.natural 7) ≠ result (.natural 8) := by
  intro same
  have impossible := (natural_result_equal_iff 7 8).mp same
  cases impossible

end Controls

#print axioms Controls.projected_is_result
#print axioms Controls.seven_is_not_eight

end FormationSensitiveContextual.QuotientCwf
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
