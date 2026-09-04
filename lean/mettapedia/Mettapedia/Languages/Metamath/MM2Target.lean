import Mettapedia.Languages.ProcessCalculi.MORK.AuthoredContextBridge
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveExecution
import Mettapedia.Languages.ProcessCalculi.MORK.ReflectiveGSLTNativeTypes
import Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-!
# Supplied MM2 target presentation

The Metamath transformations consume an operational MM2 presentation through
this behavioral capability.  The target is not selected by a name, digest,
or equality with one privileged object.  OSLF is applied to the actual
supplied target GSLT before its native transition types are used.
-/

namespace Mettapedia.Languages.Metamath.MM2Transformation

open Mettapedia.GSLT.ProofRelevant
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK
open Mettapedia.Languages.ProcessCalculi.MORK.MM2Surface

/-- An operational MM2 target supplied to a transformation.  The embedding
and two-sided step law are the target capability boundary. -/
structure MM2Target where
  operational : ProofRelevantGSLT
  embedSpace : Space → operational.theory.Term
  embedSpace_injective : Function.Injective embedSpace
  step_iff : ∀ source target,
    operational.theory.Step (embedSpace source) (embedSpace target) ↔
      (reflectiveSourceExecGSLT .leaveInert).Step source target
  render : List Atom → Option String
  render_eq_canonical : ∀ program, render program = renderProgram? program

noncomputable def ordinaryMM2Target : MM2Target where
  operational := reflectivePresented
  embedSpace := id
  embedSpace_injective := Function.injective_id
  step_iff := fun _ _ => Iff.rfl
  render := renderProgram?
  render_eq_canonical := fun _ => rfl

/-- A supplied operational embedding cannot smuggle an unrelated syntax
artifact through a constant or otherwise lawless renderer.  Text parsing and
MORK execution adequacy are deliberately separate obligations. -/
@[simp] theorem MM2Target.render_eq_renderProgram (target : MM2Target)
    (program : List Atom) :
    target.render program = renderProgram? program :=
  target.render_eq_canonical program

/-- Negative control: no admitted MM2 target can use the constant empty
renderer that the former lawless field permitted. -/
theorem MM2Target.renderer_not_constant_empty (target : MM2Target) :
    target.render [.symbol "ok"] ≠ some "" := by
  rw [target.render_eq_renderProgram]
  decide +kernel

/-- OSLF is run over the actual target GSLT supplied to the compiler.  On the
embedded MM2 image, its exact-target native type is equivalent to one ordinary
reflective-MM2 work-queue step. -/
theorem MM2Target.native_type_iff_step (target : MM2Target)
    (source result : Space) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      target.operational.theory).satisfies (target.embedSpace source)
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          target.operational.theory (target.embedSpace result)).pred ↔
      (reflectiveSourceExecGSLT .leaveInert).Step source result := by
  exact
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.satisfies_exactTargetNativeType_iff_step
        target.operational.theory
        (target.embedSpace source) (target.embedSpace result)).trans
      (target.step_iff source result)

/-- A supplied target capability cannot license an OSLF-native target event
that ordinary MM2 itself does not have. -/
theorem MM2Target.no_invented_native_step (target : MM2Target)
    {source result : Space}
    (absent : ¬ (reflectiveSourceExecGSLT .leaveInert).Step source result) :
    ¬ (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      target.operational.theory).satisfies (target.embedSpace source)
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          target.operational.theory (target.embedSpace result)).pred := by
  rw [target.native_type_iff_step]
  exact absent

/-- The ordinary MORK target is the identity embedding instance. -/
theorem ordinaryMM2Target_native_type_iff_step
    (source target : Space) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF
      ordinaryMM2Target.operational.theory).satisfies
        (ordinaryMM2Target.embedSpace source)
        (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.exactTargetNativeType
          ordinaryMM2Target.operational.theory
          (ordinaryMM2Target.embedSpace target)).pred ↔
      (reflectiveSourceExecGSLT .leaveInert).Step source target :=
  ordinaryMM2Target.native_type_iff_step source target

#print axioms MM2Target.native_type_iff_step
#print axioms MM2Target.no_invented_native_step
#print axioms MM2Target.render_eq_renderProgram
#print axioms MM2Target.renderer_not_constant_empty
#print axioms ordinaryMM2Target_native_type_iff_step

end Mettapedia.Languages.Metamath.MM2Transformation
