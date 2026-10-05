import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingValueNative
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRho
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryInputObservation

/-!
# Returned-function types at the actual unary and rho interfaces

Lowering represents a binary function receiver by a unary public handshake.
Ordinary environment servers also have unary receivers. A fresh result
channel separates these roles. Under that independently checked condition,
source returned functions are exactly the lowered program's public inputs.
The actual rho implementation reflects these observations and realizes them
after its finite administrative initialization.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLoweredValueNative

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda ActiveObservation ActiveMarkedNames
open RhoUnaryReadback

universe u

private theorem sender_input {Key : Type u} {Γ : Ctx sig} (subject fresh : Key)
    (environment : Environment Key Γ) (channel first second : Name Γ) :
    HasHeader .input1 subject fresh environment (MonadicProtocol.sendPair channel first second) ↔
      subject = fresh := by
  simp [MonadicProtocol.sendPair, MonadicProtocol.sendFields, hasHeader_nu, hasHeader_par, hasHeader_out1, hasHeader_inp1,
    nameKey, ActiveMarkedNames.extend]

private theorem receiver_input {Key : Type u} {Γ : Ctx sig} (subject fresh : Key)
    (environment : Environment Key Γ) (channel : Name Γ) (body : Proc (.nm :: .nm :: Γ)) :
    HasHeader .input1 subject fresh environment (MonadicProtocol.receivePair channel body) ↔
      subject = nameKey environment channel := by
  simp [MonadicProtocol.receivePair, hasHeader_inp1]

theorem lowered_value_header {Key : Type u} (fresh subject : Key) (different : fresh ≠ subject)
    {Γ Δ : Ctx sig} (term : Expr Γ) (environment : Ren sig Γ Δ) (result : Var Δ .nm)
    (keys : Environment Key Δ) (references : ∀ name, keys (environment .nm name) ≠ subject) :
    HasHeader .input1 subject fresh keys (MonadicProtocol.lower (compile term environment result)) ↔
      Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation.returning term = true ∧
        keys result = subject := by
  induction term generalizing Δ with
  | var name =>
      simp [compile, MonadicProtocol.lower_out1, hasHeader_out1,
        Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation.returning]
  | lam body =>
      simp [compile, MonadicProtocol.lower_inp2, receiver_input, nameKey, eq_comm,
        Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation.returning]
  | app function argument ih =>
      simp only [compile, MonadicProtocol.lower_nu, MonadicProtocol.lower_par,
        MonadicProtocol.lower_out2, hasHeader_nu, hasHeader_par, sender_input]
      have safe : ∀ name, ActiveMarkedNames.extend fresh keys ((push environment) .nm name) ≠ subject :=
        fun name => references name
      rw [ih (push environment) .zero (ActiveMarkedNames.extend fresh keys) safe]
      simp [ActiveMarkedNames.extend, different, Ne.symm different,
        Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation.returning]
  | defn value body _ bodyIH =>
      simp only [compile, MonadicProtocol.lower_nu, MonadicProtocol.lower_par,
        MonadicProtocol.lower_rep, MonadicProtocol.lower_inp1, hasHeader_nu, hasHeader_par,
        hasHeader_rep, hasHeader_inp1]
      have safe : ∀ name, ActiveMarkedNames.extend fresh keys
          (liftRen environment [.nm] .nm name) ≠ subject := by
        intro name
        cases name with
        | zero => exact different
        | succ name => exact references name
      rw [bodyIH (liftRen environment [.nm]) (.succ result) (ActiveMarkedNames.extend fresh keys) safe]
      simp [ActiveMarkedNames.extend, nameKey, Ne.symm different,
        Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation.returning]
  | carrier name value body _ bodyIH =>
      simp only [compile, MonadicProtocol.lower_par, MonadicProtocol.lower_inp1,
        hasHeader_par, hasHeader_inp1]
      rw [bodyIH environment result keys references]
      simp [nameKey, (references name).symm,
        Mettapedia.Languages.LambdaCalculus.NamePassing.ValueObservation.returning]

def targetPredicate {Δ : Ctx sig} (result : Var Δ .nm) :
    EquationPredicate (NativeTypes.operationalTheory Δ) := predicate .input1 result

/-- This fresh-result condition is a role-separation obligation, rather
than injectivity of all source references. -/
theorem compiled_value_iff {Γ Δ : Ctx sig} (term : Expr Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (fresh : ∀ name, environment .nm name ≠ result) :
    (NamePassingValueNative.sourcePredicate Γ).1 term ↔
      (targetPredicate result).1 (MonadicProtocol.lower (compile term environment result)) := by
  have distinct : (Var.zero : Var (.nm :: Δ) .nm) ≠ Var.succ result := by
    intro impossible
    cases impossible
  have references : ∀ name, Var.succ (environment .nm name) ≠ (Var.succ result : Var (.nm :: Δ) .nm) := by
    intro name equal
    exact fresh name (Var.succ.inj equal)
  have compared := lowered_value_header (Var.zero : Var (.nm :: Δ) .nm)
    (Var.succ result) distinct term environment result (fun name => Var.succ name) references
  simpa only [NamePassingValueNative.sourcePredicate, targetPredicate, predicate, PublicHeader, and_true] using compared.symm

theorem rho_current_input_reflected {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (fresh : ∀ name, environment .nm name ≠ result)
    (world : RhoUnaryWorld.SeedWorld Δ) (code : RhoUnaryCode.Code 0)
    (supplied : NamePassingRho.compile term environment result world.world = some code)
    (observed : Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation.HasInput
      (world.world result).term (runtimeProcess code world.available).1) :
    (NamePassingValueNative.sourcePredicate Γ).1 term := by
  have related := initial_related (NamePassingRho.guarded_compiler_image term environment result)
    world code supplied
  exact (compiled_value_iff term environment result fresh).mpr
    (RhoUnaryInputObservation.related_input_reflected world result related observed)

/-- An actual source returned function is realized as native public input
readiness by the complete emitted rho program, including its allocator. -/
theorem rho_native_current_return_preserved {Γ Δ : Ctx sig} (term : Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) (fresh : ∀ name, environment .nm name ≠ result)
    (world : RhoUnaryWorld.SeedWorld Δ) (code : RhoUnaryCode.Code 0)
    (supplied : NamePassingRho.compile term environment result world.world = some code)
    (returned : (NamePassingValueNative.sourcePredicate Γ).1 term) :
    (semanticDiamond Target.closure (RhoUnaryInputObservation.targetPredicate world result)).1
      (runtimeProcess code world.available) :=
  RhoUnaryInputObservation.native_current_input_preserved world result
    (initial_related (NamePassingRho.guarded_compiler_image term environment result) world code supplied)
    ((compiled_value_iff term environment result fresh).mp returned)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLoweredValueNative
