import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActivePrefixResidual
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins

/-!
# Exact untouched frames of compiled binary lambda calls

Source constructor addresses distinguish linear lambda listeners and
application senders. All persistent declarations use unary guards, so the
binary actors satisfy the static residual invariant. Every supplied binary
firing therefore retains exactly the compiled source's other actors,
including their multiplicity, modulo its actual private scope telescope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryResidual

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus.NamePassing
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveHeaderInvariant
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActiveMarking
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ActivePrefixResidual
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingActiveOrigins
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedCommunicationInversion

theorem binary_repFree {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (header : Header)
    (binary : header = .input2 ∨ header = .output2) :
    repFree header (compile source environment result) = true := by
  induction source generalizing Δ with
  | var => simp only [compile, out1, repFree]
  | lam => simp only [compile, inp2, repFree]
  | app function argument ih =>
      simp only [compile, nu, par, out2, repFree, ih, Bool.true_and]
  | defn value body valueIH bodyIH =>
      simp only [compile, nu, par, rep, inp1, repFree, visible, bodyIH, Bool.true_and]
      rcases binary with h | h <;> subst header <;> rfl
  | carrier name value body valueIH bodyIH =>
      simp only [compile, par, inp1, repFree, bodyIH, Bool.and_true]

theorem lambda_count {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (origin : Origin) : count .input2 origin (mark source address) ≤ 1 := by
  induction source generalizing address with
  | var => simp [mark, count]
  | lam => simp only [mark, count]; split <;> omega
  | app function argument ih =>
      simpa [mark, count] using ih (.function :: address)
  | defn value body valueIH bodyIH =>
      simpa only [mark, count, Nat.add_zero] using bodyIH (.definitionBody :: address)
  | carrier name value body valueIH bodyIH =>
      simpa [mark, count] using bodyIH (.carrierBody :: address)

private theorem origin_ne_of_deeper (origin : Origin) (address : List Edge)
    (deeper : origin.address.length < address.length) (kind : Kind) :
    origin ≠ Origin.mk kind address := by
  intro equal
  have lengths := congrArg (fun value : Origin => value.address.length) equal
  simp only at lengths
  omega

/-- A constructor deeper than an origin's recorded address cannot carry
that origin, including through declaration and application contexts. -/
theorem count_deeper {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (origin : Origin) (header : Header) (deeper : origin.address.length < address.length) :
    count header origin (mark source address) = 0 := by
  induction source generalizing address with
  | var => simp only [mark, count]; simp [origin_ne_of_deeper origin address deeper]
  | lam => simp only [mark, count]; simp [origin_ne_of_deeper origin address deeper]
  | app function argument ih =>
      simp only [mark, count]
      rw [ih (.function :: address) (by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper)]
      simp [origin_ne_of_deeper origin address deeper]
  | defn value body valueIH bodyIH =>
      simpa only [mark, count, Nat.add_zero] using
        bodyIH (.definitionBody :: address) (by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper)
  | carrier name value body valueIH bodyIH =>
      simp only [mark, count]
      rw [bodyIH (.carrierBody :: address) (by simpa only [List.length_cons] using Nat.lt_succ_of_lt deeper)]
      simp [origin_ne_of_deeper origin address deeper]

theorem application_count {Γ : Ctx sig} (source : Expr Srt.nm Γ) (address : List Edge)
    (origin : Origin) : count .output2 origin (mark source address) ≤ 1 := by
  induction source generalizing address with
  | var => simp [mark, count]
  | lam => simp [mark, count]
  | app function argument ih =>
      by_cases same : origin = Origin.mk .application address
      · simp only [mark, count]
        rw [count_deeper function (.function :: address) origin .output2 (by
          simpa only [same, List.length_cons] using Nat.lt_succ_self address.length)]
        simp [same]
      · simpa only [mark, count, same, and_false, ite_false, Nat.add_zero] using ih (.function :: address)
  | defn value body valueIH bodyIH =>
      simpa only [mark, count, Nat.add_zero] using bodyIH (.definitionBody :: address)
  | carrier name value body valueIH bodyIH =>
      simpa [mark, count] using bodyIH (.carrierBody :: address)

/-- The arbitrary selected binary exposure has exactly the original
compiled frame after its two selected source actors are removed. -/
theorem actual_binary_frame {Γ Δ : Ctx sig} (source : Expr Srt.nm Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {target : Proc Δ}
    (exposure : Exposure (compile source environment result) target)
    (traced : TracedExposure (mark source []) exposure)
    (binary : inputHeader exposure.selected = .input2) :
    StructuralEq
      (remove .output2 traced.continuation.outputOrigin
        (cutTree .input2 traced.continuation.inputOrigin (mark source []))
        (remove .input2 traced.continuation.inputOrigin (mark source [])
          (compile source environment result)))
      (exposure.scope.close exposure.frame) :=
  binary_frame_residual (mark_fits source [] environment result) exposure traced binary
    (binary_repFree source environment result .input2 (Or.inl rfl))
    (binary_repFree source environment result .output2 (Or.inr rfl))
    (lambda_count source [] _) (application_count source [] _)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingBinaryResidual
