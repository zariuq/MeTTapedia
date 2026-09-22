import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRegularity
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode

/-!
# Checked conversion of formed dependent judgments

A finite conversion certificate changes the displayed type only after its
target formation has been checked. The construction is independent of any
concrete root decoder, universe profile or language adapter.
-/

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitive

variable {Head : Type} [DecidableEq Head] {R : Rules Head}
    [DecidableRel R.headEq] {n : Nat}

/-- Checked conversion retains source admission and target formation. -/
theorem Judgment.convertChecked
    (decoder : StructuralConversionCode.RootDecoder R.computation)
    {context : Ctx Head n} {term sourceType targetType : Tm Head n} {sortHead : Head}
    (source : Judgment R context term sourceType)
    (targetFormed : Typing R context targetType (.head sortHead))
    (isUniverse : R.isUniverse sortHead)
    {code : StructuralConversionCode.Code Head decoder.Code n}
    (checked : code.check R.headEq decoder.decode sourceType targetType = true) :
    Judgment R context term targetType :=
  ⟨source.context, .conv source.typing targetFormed isUniverse
    (StructuralConversionCode.Code.check_sound decoder checked)⟩

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.FormationSensitive
