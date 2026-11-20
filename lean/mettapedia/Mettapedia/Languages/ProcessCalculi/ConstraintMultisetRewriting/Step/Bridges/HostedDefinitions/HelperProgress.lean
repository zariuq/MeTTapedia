import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.HelperPending
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Bridges.HostedDefinitions.ContextProgress

/-! # A finite helper episode composes with its actual return continuation -/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.HelperProgress

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
open SourceLanguage.Elaboration
open NativeTypesOnTheStep.Computing
open ContextProgress (Terminates)

theorem pending {dev : Definitions.Development} (built : Compiled dev) {n : Nat}
    (result : Tower.Tm n) (continuation : MClosed)
    (boundary : Terminates built (resumeC (encodeTm result) continuation))
    {current : MClosed} (represented : HelperPending.Pending result continuation current) :
    Terminates built current := by
  have helperAcc := HelperPending.normalizing represented
  induction helperAcc with
  | intro current _ ih =>
      refine .intro current ?_
      intro next edge
      have helperStep := HelperIsolation.assembled_step_is_helper built represented.1 edge
      rcases HelperPending.advance built represented edge with inside | returned
      · exact ih next helperStep inside
      · exact returned.symm ▸ boundary

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.Bridges.HostedDefinitions.HelperProgress
