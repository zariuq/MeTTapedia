import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ComputationProgramAnswers

/-!
# The shared fixed descriptor program for the vectors package

The value depends on the package's fourteen-row presentation, not on a call.
Consumers add their own examples without making the basic program depend on
the source-definition compiler or its example corpus.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.Controls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open TypedEquality TypedEquality.Normalization
open NativeTypesOnTheStep.Computing

abbrev setting := ComputationProfile.Controls.setting
abbrev qualified := ComputationProfile.Controls.qualified

def program : Program setting.R :=
  ⟨Vectors.vectorEquations, ComputationProfile.Controls.presentation, fun _ _ => Iff.rfl⟩

theorem fixed_table : program.table.length = 14 := rfl

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.ComputationProgram.Controls
