import Mettapedia.Languages.LambdaCalculus.NamePassingValueObservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.ActiveObservation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquationsNative
import Mettapedia.GSLT.Core.OperationalReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalCorrespondence

/-!
# Returned functions inhabit their generated native type

The independent source returned-function observation is exactly an active
binary listener on the compiler's supplied result channel. Private function
call channels are excluded by the actual additional context position. Stored
values remain guarded: a retained definition is not itself a returned value.
The comparison is invariant under both source and target static equations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingValueNative

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda ActiveObservation ActiveMarkedNames

universe u

/-- This is a comparison of independently defined observations. The private
marker need only be distinct from the one result subject being observed. -/
theorem compiled_value_header {Key : Type u} (fresh subject : Key)
    (different : fresh ≠ subject) {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (keys : Environment Key Δ) :
    HasHeader .input2 subject fresh keys (compile term environment result) ↔
      NamePassing.ValueObservation.returning term = true ∧ keys result = subject := by
  induction term generalizing Δ with
  | var name =>
      simp [compile, hasHeader_out1, NamePassing.ValueObservation.returning]
  | lam body =>
      simp [compile, hasHeader_inp2, NamePassing.ValueObservation.returning, nameKey, eq_comm]
  | app function argument ih =>
      simp only [compile, hasHeader_nu, hasHeader_par, hasHeader_out2]
      rw [ih (push environment) .zero (extend fresh keys)]
      simp [ActiveMarkedNames.extend, nameKey, different, NamePassing.ValueObservation.returning]
  | defn value body _ bodyIH =>
      simp only [compile, hasHeader_nu, hasHeader_par, hasHeader_rep, hasHeader_inp1]
      rw [bodyIH (liftRen environment [.nm]) (.succ result) (extend fresh keys)]
      simp [ActiveMarkedNames.extend, nameKey, NamePassing.ValueObservation.returning]
  | carrier name value body _ bodyIH =>
      simp only [compile, hasHeader_par, hasHeader_inp1]
      rw [bodyIH environment result keys]
      simp [NamePassing.ValueObservation.returning]

def sourcePredicate (Γ : Ctx sig) :
    EquationPredicate (NamePassingEnvironmentEquationsNative.sourceTheory Γ) :=
  ⟨fun term => NamePassing.ValueObservation.returning term = true,
    fun _ _ equal =>
      (congrArg (fun flag : Bool => flag = true)
        (NamePassing.ValueObservation.returning_structural equal)).to_iff⟩

def targetPredicate {Δ : Ctx sig} (result : Var Δ .nm) :
    EquationPredicate (NativeTypes.operationalTheory Δ) := predicate .input2 result

/-- The actual compiler maps the source value observation to the target's
generated native predicate in both directions, on every expression. -/
theorem compiled_value_iff {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    (sourcePredicate Γ).1 term ↔ (targetPredicate result).1 (compile term environment result) := by
  have fresh : (Var.zero : Var (.nm :: Δ) .nm) ≠ Var.succ result := by
    intro impossible
    cases impossible
  have compared := compiled_value_header (Var.zero : Var (.nm :: Δ) .nm)
    (Var.succ result) fresh term environment result (fun name => Var.succ name)
  simpa only [sourcePredicate, targetPredicate, predicate, PublicHeader, and_true] using compared.symm

theorem returned_function_native {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    Nonempty (NamePassing.Environment.ReturningLambda term) ↔
      (targetPredicate result).1 (compile term environment result) :=
  (NamePassing.ValueObservation.returning_iff term).symm.trans (compiled_value_iff term environment result)

/-- Any supplied static target representative has the same value type. -/
theorem represented_value_iff {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) {represented : Proc Δ}
    (equal : StructuralEq represented (compile term environment result)) :
    (targetPredicate result).1 represented ↔ Nonempty (NamePassing.Environment.ReturningLambda term) :=
  ((targetPredicate result).2 equal).trans (returned_function_native term environment result).symm

/-- A finite source execution returning a function produces a real target
execution reaching the generated function-readiness predicate. -/
theorem native_may_return_preserved {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (possible : (semanticDiamond (NamePassingEnvironmentEquationsNative.sourceTheory Γ).closure
      (sourcePredicate Γ)).1 term) :
    (semanticDiamond (NativeTypes.operationalTheory Δ).closure
      (targetPredicate result)).1 (compile term environment result) := by
  obtain ⟨returned, sourcePath, value⟩ :=
    (closure_nativeDiamond_iff (NamePassingEnvironmentEquationsNative.sourceTheory Γ)
      (sourcePredicate Γ) term).mp possible
  exact (closure_nativeDiamond_iff (NativeTypes.operationalTheory Δ)
    (targetPredicate result) (compile term environment result)).mpr
      ⟨compile returned environment result,
        (NamePassingEnvironmentEquationsNative.realization environment result).mapMultiStep sourcePath,
        (compiled_value_iff returned environment result).mp value⟩

/-- Every actual target execution that reaches a returned function reflects
to a source execution with the same observation. Static representatives and
intermediate communications are covered by the operational correspondence. -/
theorem native_may_return_iff {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (faithful : Function.Injective (environment .nm))
    (result : Var Δ .nm) :
    (semanticDiamond (NamePassingEnvironmentEquationsNative.sourceTheory Γ).closure
      (sourcePredicate Γ)).1 term ↔
    (semanticDiamond (NativeTypes.operationalTheory Δ).closure
      (targetPredicate result)).1 (compile term environment result) := by
  apply (NamePassingOperationalCorrespondence.correspondence environment faithful result).nativeDiamond_iff
    (sourcePredicate Γ) (targetPredicate result) ?_
    (NamePassingOperationalCorrespondence.compiled_related environment faithful result term)
  intro origin current related
  exact (compiled_value_iff origin environment result).trans
    ((targetPredicate result).2 related).symm

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingValueNative
