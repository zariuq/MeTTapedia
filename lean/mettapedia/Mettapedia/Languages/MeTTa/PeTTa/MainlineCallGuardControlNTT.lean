import Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl
import Mettapedia.OSLF.Framework.GSLTTypeSynthesis

/-!
# OSLF native types for authentic PeTTa call-guard control

This module applies the shared abstract-GSLT OSLF construction to the cold
compiler, completed-call executor, and their composed source theory.  The
generated behavioral native types therefore classify actual compiler and
guard transitions, rather than replaying a precomputed action receipt.

These are the semantic OSLF native types of the three operational GSLTs.  A
separate shared proof-calculus construction may later give them a syntactic
presentation; no language-specific substitute is introduced here.
-/

namespace Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControlNTT

open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan
open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl

set_option autoImplicit false

def compileOSLF := gsltOSLF compileGSLT

def executeOSLF := gsltOSLF executeGSLT

def callGuardOSLF := gsltOSLF callGuardGSLT

theorem compile_galois :
    GaloisConnection (gsltDiamond compileGSLT) (gsltBox compileGSLT) :=
  gsltGalois compileGSLT

theorem execute_galois :
    GaloisConnection (gsltDiamond executeGSLT) (gsltBox executeGSLT) :=
  gsltGalois executeGSLT

theorem callGuard_galois :
    GaloisConnection (gsltDiamond callGuardGSLT) (gsltBox callGuardGSLT) :=
  gsltGalois callGuardGSLT

theorem compile_exactTarget_iff_step
    (source target : CompileControl) :
    compileOSLF.satisfies source
        (exactTargetNativeType compileGSLT target).pred ↔
      compileGSLT.Step source target :=
  satisfies_exactTargetNativeType_iff_step compileGSLT source target

theorem execute_exactTarget_iff_step
    (source target : ExecuteControl) :
    executeOSLF.satisfies source
        (exactTargetNativeType executeGSLT target).pred ↔
      executeGSLT.Step source target :=
  satisfies_exactTargetNativeType_iff_step executeGSLT source target

theorem callGuard_exactTarget_iff_step
    (source target : CallGuardControl) :
    callGuardOSLF.satisfies source
        (exactTargetNativeType callGuardGSLT target).pred ↔
      callGuardGSLT.Step source target :=
  satisfies_exactTargetNativeType_iff_step callGuardGSLT source target

/-- OSLF-generated cold native evidence preserves the independently stated
compiler result. -/
theorem compile_native_step_preserves_denotation
    {source target : CompileControl}
    (inhabited : compileOSLF.satisfies source
      (exactTargetNativeType compileGSLT target).pred) :
    source.denote = target.denote := by
  exact compileStep_denote_preserved
    ((compile_exactTarget_iff_step source target).1 inhabited)

/-- OSLF-generated hot native evidence preserves the complete ordered guard
observation. -/
theorem execute_native_step_preserves_denotation
    {source target : ExecuteControl}
    (inhabited : executeOSLF.satisfies source
      (exactTargetNativeType executeGSLT target).pred) :
    source.denote = target.denote := by
  exact executeStep_denote_preserved
    ((execute_exactTarget_iff_step source target).1 inhabited)

/-- OSLF-generated composed native evidence preserves the independent
compiler/executor observation across both cold and hot phases. -/
theorem callGuard_native_step_preserves_denotation
    {source target : CallGuardControl}
    (inhabited : callGuardOSLF.satisfies source
      (exactTargetNativeType callGuardGSLT target).pred) :
    source.denote = target.denote := by
  exact callGuardStep_denote_preserved
    ((callGuard_exactTarget_iff_step source target).1 inhabited)

namespace Canary

open Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardPlan.Canary

theorem outside_fragment_step_inhabits_execute_native_type :
    executeOSLF.satisfies
        (.request (owned exactTypeSnapshot) wrongOrdinaryInputCall
          .outsideFragment)
        (exactTargetNativeType executeGSLT
          (.halted ⟨.fallback .outsideFragment,
            [.fallback .outsideFragment]⟩)).pred := by
  apply (execute_exactTarget_iff_step _ _).2
  exact Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControl.OperationalCanary.outside_fragment_is_explicit_fallback_step

theorem compile_to_execute_boundary_inhabits_native_type
    (owned : MainlineCallGuardProjection.OwnedSnapshot)
    (call : CallGuardNativeKernel.Call) (result : CompilationResult) :
    callGuardOSLF.satisfies
        (.compiling owned call (.halted result))
        (exactTargetNativeType callGuardGSLT
          (.executing (.request owned call result))).pred := by
  apply (callGuard_exactTarget_iff_step _ _).2
  rfl

theorem halted_execute_has_no_native_successor
    (observation : ControlObservation) (target : ExecuteControl) :
    ¬ executeOSLF.satisfies (.halted observation)
        (exactTargetNativeType executeGSLT target).pred := by
  intro inhabited
  exact executeGSLT_halted_normal observation
    ⟨target, (execute_exactTarget_iff_step _ _).1 inhabited⟩

theorem halted_callGuard_has_no_native_successor
    (observation : ControlObservation) (target : CallGuardControl) :
    ¬ callGuardOSLF.satisfies (.executing (.halted observation))
        (exactTargetNativeType callGuardGSLT target).pred := by
  intro inhabited
  exact callGuardGSLT_halted_normal observation
    ⟨target, (callGuard_exactTarget_iff_step _ _).1 inhabited⟩

end Canary

/-- The OSLF-indexed source has the same exact terminal path boundary already
proved for the authentic operational GSLT. -/
theorem terminal_path_iff_reference
    (owned : MainlineCallGuardProjection.OwnedSnapshot)
    (call : CallGuardNativeKernel.Call) (observation : ControlObservation) :
    callGuardGSLT.MultiStep (callGuardStart owned call)
        (.executing (.halted observation)) ↔
      observation = executeControl owned call
        (compileGuards owned call.function call.sourceArguments.length) :=
  callGuardGSLT_terminal_iff owned call observation

#print axioms compile_galois
#print axioms execute_galois
#print axioms callGuard_galois
#print axioms compile_exactTarget_iff_step
#print axioms execute_exactTarget_iff_step
#print axioms callGuard_exactTarget_iff_step
#print axioms compile_native_step_preserves_denotation
#print axioms execute_native_step_preserves_denotation
#print axioms callGuard_native_step_preserves_denotation
#print axioms Canary.outside_fragment_step_inhabits_execute_native_type
#print axioms Canary.compile_to_execute_boundary_inhabits_native_type
#print axioms Canary.halted_execute_has_no_native_successor
#print axioms Canary.halted_callGuard_has_no_native_successor
#print axioms terminal_path_iff_reference

end Mettapedia.Languages.MeTTa.PeTTa.MainlineCallGuardControlNTT
