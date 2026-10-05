import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBetaEnvelope
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpeningExecution
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafety

/-!
# Every supplied binary compiler firing reads back to a source beta event

Static equations may expose a call beneath private scopes, move its frame or
change its guarded continuation. Source call ownership first reconstructs the
independently authored beta site. Opening the existing scope preserves the
actual selected communication arity and the supplied endpoint. The physical
call boundary then identifies that endpoint with the compiled source successor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryReadback

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingActiveOrigins NamePassingBinaryOwnership NamePassingBetaEnvelope
open ScopedCommunicationInversion ActiveMarking ActiveHeaderInvariant

/-- The selected source site and its genuine beta step refer to the original
source. The equation concerns the supplied target, not a replacement outcome
chosen from another possible execution. -/
theorem traced_binary_readback {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (actual : Exposure (compile source environment result) target)
    (traced : TracedExposure (mark source []) actual)
    (binary : inputHeader actual.selected = .input2) :
    ∃ site : BetaSite source [] traced.continuation.inputOrigin traced.continuation.outputOrigin,
      Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.StepModulo .beta source site.successor ∧
      StructuralEq target (compile site.successor environment result) := by
  obtain ⟨site⟩ := traced_binary_site source environment result actual traced binary
  let boundary := betaEnvelope site environment result
  have safe : ScopedOpening.Safe (boundary.scope.close
      (par (par (out2 (.var boundary.channel) (.var boundary.first) (.var boundary.second))
        (inp2 (.var boundary.channel) boundary.guard)) boundary.frame)) :=
    (ScopedOpening.safe_structural boundary.before).mp
      (RhoUnarySourceSafety.lambda_polyadic_safe source environment result)
  obtain ⟨returned, opened, arity, endpoint⟩ := ScopedOpening.open_scope_exposure
    boundary.scope _ (actual.changeSource (.symm boundary.before)) safe
  have sameArity : inputHeader opened.selected = .input2 := arity.trans binary
  have returnedEq := boundary.opened_readback
    (opened.changeSource (.symm (.parAssoc _ _ _))) sameArity
  exact ⟨site, site.sound, endpoint.trans returnedEq⟩

/-- An arbitrary actual modulo firing retains a proof-relevant original
source site and reaches exactly its compiled successor up to the equations. -/
theorem binary_readback {Γ Δ : Ctx sig} (source : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (actual : Exposure (compile source environment result) target)
    (binary : inputHeader actual.selected = .input2) :
    ∃ successor : Expr Γ,
      Mettapedia.Languages.LambdaCalculus.NamePassing.Environment.StepModulo .beta source successor ∧
      StructuralEq target (compile successor environment result) := by
  obtain ⟨traced⟩ := tracedExposure_exists
    (Origin.mk .privateCall []) (mark_fits source [] environment result) actual
  obtain ⟨site, sourceStep, endpoint⟩ := traced_binary_readback source environment result
    actual traced binary
  exact ⟨site.successor, sourceStep, endpoint⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryReadback
