import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderExecution

/-!
# Concrete header selections enter the authored rho theory

An input/output occurrence selection generates an actual authored COMM.
The generated theory then permits independently supplied sorted equation
representatives at both ends. This bridge preserves the selected literal
contractum; it does not replace a supplied execution by a chosen schedule.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryTargetSteps

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryActive RhoUnaryReadback
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open HeaderInversion

/-- A rendered frontier inhabits the independently sorted target carrier. -/
noncomputable def frontierProcess {Γ : Ctx sig} (world : World Γ 0)
    (activities : List (Activity Γ)) : TargetProcess :=
  HeaderExecution.headerProcess (headers world activities)
    (headers_typed world activities) (headers_safe world activities)

/-- Formation of the actual selected contractum follows from COMM typing
and quotation-scope preservation. -/
noncomputable def contractumProcess {Γ : Ctx sig} (world : World Γ 0)
    (activities : List (Activity Γ)) (selected : Selection (headers world activities)) :
    TargetProcess :=
  HeaderExecution.contractumProcess (headers world activities)
    (headers_typed world activities) (headers_safe world activities) selected

/-- This step is constructed from the authored rule's matcher/application
proof, before any source simulation or readback theorem is used. -/
theorem selection_step {Γ : Ctx sig} (world : World Γ 0)
    (activities : List (Activity Γ)) (selected : Selection (headers world activities)) :
    Target.Step (frontierProcess world activities)
      (contractumProcess world activities selected) :=
  HeaderExecution.selection_step (headers world activities)
    (headers_typed world activities) (headers_safe world activities) selected

/-- The same occurrence receipt retains any supplied sorted endpoint in
its actual equation class. -/
theorem supplied_selection_step {Γ : Ctx sig} (world : World Γ 0)
    (activities : List (Activity Γ)) (selected : Selection (headers world activities))
    (before after : TargetProcess)
    (sourceEquation : StructuralCongruence before.1 (actual world activities))
    (targetEquation : StructuralCongruence selected.contractum after.1) :
    Target.Step before after :=
  HeaderExecution.supplied_selection_step (headers world activities)
    (headers_typed world activities) (headers_safe world activities) selected
    before after sourceEquation targetEquation

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryTargetSteps
