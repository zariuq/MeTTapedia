import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafety
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRhoControls

/-!
# Controls for admitted scopes and actual whole-program initialization

A guarded server may allocate a used private name in its released body.
An autonomous replicated allocator lies outside the current scope-opening
class. Unused restrictions introduced by actual static equations remain
admitted. A retained lambda definition and call enter the authored rho
runtime with a fresh result channel and initialize in exactly sixteen
communications.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafetyControls

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryReadback RhoUnarySourceSafety

abbrev context : Ctx sig := [Srt.nm]
abbrev publicName : Var context Srt.nm := .zero

def privateBody : Proc (Srt.nm :: Srt.nm :: context) :=
  out1 (.var .zero) (.var (.succ .zero))

def guardedAllocator : Proc context := rep (inp1 (.var publicName) (nu privateBody))

theorem guarded_allocator_admitted : ScopedOpening.Safe guardedAllocator :=
  guarded_safe (.server _ (.nu (.out1 _ _)))

def autonomousAllocator : Proc context :=
  rep (nu (out1 (.var .zero) (.var (.succ publicName))))

/-- Copying a used restriction before any input is a different scope
discipline from copying a guarded input whose continuation allocates. -/
theorem autonomous_allocator_not_admitted : ¬ ScopedOpening.Safe autonomousAllocator := by
  simp [autonomousAllocator, rep, nu, out1, ScopedOpening.Safe, ScopedOpening.Vacuous,
    countVar, countVarArgs, weakenVar, sameVar_self, sameVar]

theorem unused_scope_inside_server :
    ScopedOpening.Safe (rep (nu (weaken (inp1 (.var publicName) (nu privateBody))))) := by
  have equal : StructuralEq guardedAllocator
      (rep (nu (weaken (inp1 (.var publicName) (nu privateBody))))) :=
    .rep (.symm (.nuUnused _))
  exact (ScopedOpening.safe_structural equal).mp guarded_allocator_admitted

abbrev identityContext : Ctx sig := Srt.nm :: NamePassingRhoControls.publicScope
def identityWorld : RhoUnaryWorld.SeedWorld identityContext := RhoUnaryWorld.initial identityContext

/-- The compiler's return channel is physically distinct from every
source reference in this actual runtime entry. -/
theorem identity_return_is_fresh (name : Var NamePassingRhoControls.publicScope Srt.nm) :
    (Var.zero : Var identityContext Srt.nm) ≠ .succ name := by
  intro impossible
  cases impossible

/-- All initialization steps are ordinary authored core-rho firings. The
stored identity and its pending call have not been replaced by a return. -/
theorem retained_identity_initializes_in_sixteen :
    ∃ code : RhoUnaryCode.Code 0,
      NamePassingRho.compile NamePassingRhoControls.retainedIdentity (fun _ name => .succ name)
        .zero identityWorld.world = some code ∧
      ∃ final : TargetProcess, ∃ path : ExecutionPath Target
        (runtimeProcess code identityWorld.available) final,
      ∃ witness : Witness identityWorld
        (MonadicProtocol.lower (NamePassingLambda.compile NamePassingRhoControls.retainedIdentity
          (fun _ name => .succ name) .zero)) final,
        witness.credit = 0 ∧ path.length = 16 := by
  obtain ⟨code, supplied⟩ := NamePassingRho.compile_total NamePassingRhoControls.retainedIdentity
    (fun _ name => .succ name) .zero identityWorld.world
  refine ⟨code, supplied, ?_⟩
  simpa only [NamePassingRhoReadback.initializationSites, NamePassingRhoControls.retainedIdentity] using
    NamePassingRhoReadback.initialized_runtime NamePassingRhoControls.retainedIdentity
      (fun _ name => .succ name) .zero identityWorld code supplied

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafetyControls
