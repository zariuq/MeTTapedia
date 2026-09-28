import Mettapedia.Languages.Agda.Structural.AdministrativeSpineLinearization
import Mettapedia.Languages.Agda.Structural.AdministrativeBinderPreservationControls

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.Structural.AdministrativeStatics.CanonizationPreparation

open Mettapedia.OSLF.Binding
open Statics (RawTm RawTy RawContext TypeParameter TypeBody)

namespace Controls

noncomputable def nonemptyTail : CoreDerivation (Statics.termEqual SpineStatics.Controls.functionContext
    (eliminate (.var .zero) SpineStatics.Controls.twoArguments)
    (eliminate (eliminate (.var .zero) SpineStatics.Controls.firstSpine) SpineStatics.Controls.secondSpine)
    SpineStatics.Controls.domain.code) :=
  consToNested (A := SpineStatics.Controls.domain) (B := .noBind SpineStatics.Controls.arrow)
    (includePrior SpineStatics.Controls.functionTyped) (includePrior SpineStatics.Controls.firstArgumentTyped)
    (includePrior SpineStatics.Controls.secondAction)

noncomputable def convertedTail : Action SpineStatics.Controls.functionContext SpineStatics.Controls.arrow.code
    SpineStatics.Controls.secondSpine PreservationControls.expandedUniverse :=
  Derivation.outputConversion (includePrior SpineStatics.Controls.secondAction)
    (PreservationControls.universeConversion (includeCanonical SpineStatics.Controls.functionContextFormed)).typeSymmetry

noncomputable def convertedNonemptyTail : CoreDerivation (Statics.termEqual SpineStatics.Controls.functionContext
    (eliminate (.var .zero) SpineStatics.Controls.twoArguments)
    (eliminate (eliminate (.var .zero) SpineStatics.Controls.firstSpine) SpineStatics.Controls.secondSpine)
    PreservationControls.expandedUniverse) :=
  consToNested (A := SpineStatics.Controls.domain) (B := .noBind SpineStatics.Controls.arrow)
    (includePrior SpineStatics.Controls.functionTyped) (includePrior SpineStatics.Controls.firstArgumentTyped) convertedTail

theorem linearization_changes_raw_syntax :
    eliminate (.var .zero) SpineStatics.Controls.twoArguments ≠
      eliminate (eliminate (.var .zero) SpineStatics.Controls.firstSpine) SpineStatics.Controls.secondSpine := by
  intro same
  cases same

end Controls
end Mettapedia.Languages.Agda.Structural.AdministrativeStatics.CanonizationPreparation
