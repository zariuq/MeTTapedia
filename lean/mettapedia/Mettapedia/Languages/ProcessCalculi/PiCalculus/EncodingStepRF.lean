import Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
import Mettapedia.Languages.ProcessCalculi.PiCalculus.EncodingEquivariance

/-!
# One step for one step, without restriction and replication

Within the fragment of the pi calculus without restriction and replication,
and for communications that respect the variable convention, a step of a
process is followed by exactly one step of its encoding, and that step
reaches the encoding of the reduct itself: the rho reduction is closed under
structural congruence, so the congruence between the contractum and the
encoding of the reduct is absorbed into the step.

The existing forward simulation states the same correspondence for zero or
more steps and up to structural congruence; it follows from this one.  Read
along contexts, transitions are preserved one for one in this fragment.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PiCalculus

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Substitution
open Mettapedia.Languages.ProcessCalculi.RhoCalculus hiding StructuralCongruence NameEquiv
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence
  (refl symm trans par_singleton par_comm par_cong)

local notation:50 p " ≡ᵨ " q =>
  Mettapedia.Languages.ProcessCalculi.RhoCalculus.StructuralCongruence p q

open private semanticSubstProc_dropPayload_SC_openBVar closeFVar_encode_rf_rhoProcCoreShape
  closeFVar_encode_rf_noBoundUnderQuote rhoPar_to_two from
  Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation

/-- **An exchange is followed by one step to the encoding of its reduct.** -/
theorem exchange_step_rf {body : Process} (free : RestrictionFree body)
    (channel bound datum : Name) (n v : String) (distinct : bound ≠ datum)
    (convention : BarendregtFor bound datum body) :
    Nonempty (Reduction.Reduces
      (encode (.par (.input channel bound body) (.output channel datum)) n v)
      (encode (body.substitute bound datum) n v)) := by
  have contracted :
      semanticCommSubst (closeFVar 0 bound (encode body (n ++ "_L") v))
          (.apply "PDrop" [.fvar datum]) ≡ᵨ
        openBVar 0 (.fvar datum) (closeFVar 0 bound (encode body (n ++ "_L") v)) := by
    have shaped : rhoProcCoreShape (closeFVar 0 bound (encode body (n ++ "_L") v)) = true :=
      closeFVar_encode_rf_rhoProcCoreShape free 0 bound (n ++ "_L") v
    have opaqueQuote :
        noBoundUnderQuote 0 (closeFVar 0 bound (encode body (n ++ "_L") v)) = true :=
      closeFVar_encode_rf_noBoundUnderQuote free 0 bound (n ++ "_L") v 0
    simpa [semanticCommSubst, semanticNormalizeProc, semanticNormalizeName] using
      semanticSubstProc_dropPayload_SC_openBVar 0 datum shaped opaqueQuote
  have reduct : openBVar 0 (.fvar datum) (closeFVar 0 bound (encode body (n ++ "_L") v)) =
      encode (body.substitute bound datum) n v :=
    (encode_rf_open_close_subst free bound datum (n ++ "_L") v distinct convention).trans
      (encode_rf_ns_independent (rf_substitute free bound datum) (n ++ "_L") n v)
  rw [reduct] at contracted
  refine ⟨Reduction.Reduces.equiv (par_comm _ _) (Reduction.Reduces.comm (rest := [])) ?_⟩
  exact trans _ (.collection .hashBag [encode (body.substitute bound datum) n v] none) _
    (par_cong _ _ (by simp) fun index first second => by
      have zero : index = 0 := by
        have bounded : index < 1 := first
        omega
      subst zero
      exact contracted)
    (par_singleton _)

/-- **One step for one step.**  A step of a process free of restriction and
replication, all of whose communications respect the variable convention, is
followed by one step of its encoding, to the encoding of the reduct. -/
theorem step_preserved_rf {source target : Process} (step : ReducesRF source target) :
    RestrictionFree source → CommSafe step → ∀ n v : String,
      Nonempty (Reduction.Reduces (encode source n v) (encode target n v)) := by
  induction step with
  | comm channel bound datum body =>
      intro free safe n v
      exact exchange_step_rf (body := body) free.1 channel bound datum n v safe.1 safe.2
  | par_left left left' right inner recurse =>
      intro free safe n v
      obtain ⟨moved⟩ := recurse free.1 safe (n ++ "_L") v
      exact ⟨Reduction.Reduces.equiv (rhoPar_to_two _ _)
        (Reduction.Reduces.par (rest := [encode right (n ++ "_R") v]) moved)
        (symm _ _ (rhoPar_to_two _ _))⟩
  | par_right left right right' inner recurse =>
      intro free safe n v
      obtain ⟨moved⟩ := recurse free.2 safe (n ++ "_R") v
      exact ⟨Reduction.Reduces.equiv (rhoPar_to_two _ _)
        (Reduction.Reduces.par_any (before := [encode left (n ++ "_L") v]) (after := []) moved)
        (symm _ _ (rhoPar_to_two _ _))⟩
  | struct source source' target target' sourceRelated inner targetRelated recurse =>
      intro free safe n v
      have free' := (rfsc_preserves_rf sourceRelated).mp free
      obtain ⟨moved⟩ := recurse free' safe n v
      exact ⟨Reduction.Reduces.equiv (encode_preserves_rfsc sourceRelated free n v) moved
        (encode_preserves_rfsc targetRelated (reducesRF_preserves_rf inner free') n v)⟩

/-- **Transitions are preserved along contexts, one for one, in this
fragment.**  A step of a plugged context is followed by one step of the image
of the context applied to the encoding of what is plugged, to the encoding of
the reduct. -/
theorem contextStep_preserved_rf (context : ProcessContext) (process result : Process)
    (step : ReducesRF (context.fill process) result)
    (free : RestrictionFree (context.fill process)) (safe : CommSafe step) (n v : String) :
    Nonempty (Reduction.Reduces
      (context.encode n v (encode process (context.parameter n) v)) (encode result n v)) := by
  rw [← ProcessContext.encode_fill]
  exact step_preserved_rf step free safe n v

end Mettapedia.Languages.ProcessCalculi.PiCalculus
