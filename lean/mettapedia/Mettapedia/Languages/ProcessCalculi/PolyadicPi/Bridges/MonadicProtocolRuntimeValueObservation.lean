import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeObservations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolRuntimeDrain
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingValueNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLoweredValueNative

/-!
# Returned functions in every witnessed tuple phase

The compiler's fresh result channel cannot be an original unary reference
listener. A public unary listener in any actual tuple-runtime representative
therefore comes from the original binary function listener. Conversely the
runtime's outstanding private debt completes to the actual lowered source;
that finite completion realizes each returned function without executing its
body or choosing a new source communication partner.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeValueObservation

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda ActiveObservation ActiveMarkedNames RuntimeWitness

universe u

theorem compiled_unary_header_absent {Key : Type u} (fresh subject : Key)
    (different : fresh ≠ subject) {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (keys : Environment Key Δ)
    (references : ∀ name, keys (environment .nm name) ≠ subject) :
    ¬ HasHeader .input1 subject fresh keys (compile term environment result) := by
  induction term generalizing Δ with
  | var name => simp only [compile, hasHeader_out1, reduceCtorEq, false_and, not_false_eq_true]
  | lam body => simp only [compile, hasHeader_inp2, reduceCtorEq, false_and, not_false_eq_true]
  | app function argument ih =>
      simp only [compile, hasHeader_nu, hasHeader_par, hasHeader_out2,
        reduceCtorEq, false_and, or_false]
      exact ih (push environment) .zero (extend fresh keys) (fun name => references name)
  | defn value body _ bodyIH =>
      simp only [compile, hasHeader_nu, hasHeader_par, hasHeader_rep, hasHeader_inp1,
        true_and, nameKey, ActiveMarkedNames.extend]
      have safe : ∀ name, extend fresh keys (liftRen environment [.nm] .nm name) ≠ subject := by
        intro name
        cases name with
        | zero => exact different
        | succ old => exact references old
      exact not_or.mpr ⟨bodyIH (liftRen environment [.nm]) (.succ result) (extend fresh keys) safe,
        Ne.symm different⟩
  | carrier name value body _ bodyIH =>
      simp only [compile, hasHeader_par, hasHeader_inp1, true_and, nameKey]
      exact not_or.mpr ⟨bodyIH environment result keys references, Ne.symm (references name)⟩

theorem compiled_unary_result_absent {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (fresh : ∀ name, environment .nm name ≠ result) :
    ¬ PublicHeader .input1 result (compile term environment result) := by
  apply compiled_unary_header_absent (Var.zero : Var (.nm :: Δ) .nm) (Var.succ result)
    (by intro impossible; cases impossible) term environment result (fun name => Var.succ name)
  intro name equal
  exact fresh name (Var.succ.inj equal)

/-- The observed target is supplied independently. Every original source
and target structural representative is included in the comparison. -/
theorem current_return_reflected {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (fresh : ∀ name, environment .nm name ≠ result) {source target : Proc Δ}
    (witness : Witness source target)
    (represented : StructuralEq source (compile term environment result))
    (observed : PublicHeader .input1 result target) :
    Nonempty (NamePassing.Environment.ReturningLambda term) := by
  rcases RuntimeObservations.public_input_reflected witness result observed with unary | binary
  · exact False.elim (compiled_unary_result_absent term environment result fresh
      (((predicate .input1 result).2 represented).mp unary))
  · exact (NamePassingValueNative.represented_value_iff term environment result represented).mp binary

/-- Completing precisely the retained private debt realizes a returned
function on its original result channel. The source endpoint stays fixed. -/
theorem current_return_realized {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (fresh : ∀ name, environment .nm name ≠ result) {source target : Proc Δ}
    (witness : Witness source target)
    (represented : StructuralEq source (compile term environment result))
    (returned : Nonempty (NamePassing.Environment.ReturningLambda term)) :
    ∃ endpoint, ∃ path : ExecutionPath (NativeTypes.operationalTheory Δ) target endpoint,
      PublicHeader .input1 result endpoint ∧ path.length = witness.debt := by
  let block := RuntimeDrain.drain witness
  have current : PublicHeader .input1 result (lower (compile term environment result)) :=
    (NamePassingLoweredValueNative.compiled_value_iff term environment result fresh).mp
      ((NamePassing.ValueObservation.returning_iff term).mpr returned)
  have actual := ((predicate .input1 result).2
    (block.equal.trans (lower_structural represented))).mpr current
  exact ⟨block.endpoint, block.path, actual, block.counted⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.RuntimeValueObservation
