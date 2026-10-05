import Mettapedia.Languages.LambdaCalculus.NamePassingEnvironmentEquations
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

/-!
# Compiling the independently authored Blue application scope laws

Application carries its private call channel past carrier declarations and
fresh definition scopes. Target scope extrusion and binder exchange implement
the two source equations at the supplied endpoints. The ordinary source
communications then compile modulo these equations; administrative source
equalities do not add communications to the account.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingLambda
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironment

private theorem frame_exchange {Γ : Ctx sig} (body declaration call : Proc Γ) :
    StructuralEq (par (par body declaration) call) (par (par body call) declaration) :=
  .trans (.parAssoc _ _ _)
    (.trans (.par (.refl _) (.parComm _ _)) (.symm (.parAssoc _ _ _)))

/-- The call stays with the active body; the carrier's suspended value is
neither called nor substituted during this structural rearrangement. -/
theorem compile_appCarrier {Γ Δ : Ctx sig} (name : Var Γ .nm)
    (value body : Expr Γ) (argument : Var Γ .nm)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    StructuralEq (compile (.app (.carrier name value body) argument) environment result)
      (compile (.carrier name value (.app body argument)) environment result) := by
  change StructuralEq
    (nu (par (par (compile body (push environment) .zero)
      (listener value (push environment) (.succ (environment _ name))))
      (out2 (.var .zero) (.var (.succ (environment _ argument))) (.var (.succ result)))))
    (par (nu (par (compile body (push environment) .zero)
      (out2 (.var .zero) (.var (.succ (environment _ argument))) (.var (.succ result)))))
      (listener value environment (environment _ name)))
  rw [← listener_weaken]
  exact .trans (.nu (frame_exchange _ _ _)) (.symm (.nuPar _ _))

private theorem swap_definition_body {Γ Δ : Ctx sig}
    (body : Expr (.nm :: Γ)) (environment : Ren sig Γ Δ) :
    rename swapRen (compile body (liftRen (push environment) [.nm]) (.succ .zero)) =
      compile body (push (liftRen environment [.nm])) .zero := by
  rw [compile_target_rename]
  have names : (fun s x => swapRen s (liftRen (push environment) [.nm] s x)) =
      push (liftRen environment [.nm]) := by
    funext s x
    cases x <;> rfl
  exact congrArg (fun assigned => compile body assigned .zero) names

private theorem swap_definition_server {Γ Δ : Ctx sig}
    (value : Expr Γ) (environment : Ren sig Γ Δ) :
    rename swapRen (server value (push (push environment)) .zero) =
      weaken (server value (push environment) .zero) := by
  rw [server_target_rename, server_weaken]
  rfl

/-- Definition and application allocate their private names in opposite
orders on the two sides. Binder exchange preserves their distinct uses. -/
theorem compile_appDefinition {Γ Δ : Ctx sig} (value : Expr Γ)
    (body : Expr (.nm :: Γ)) (argument : Var Γ .nm)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    StructuralEq (compile (.app (.defn value body) argument) environment result)
      (compile (.defn value (.app body (.succ argument))) environment result) := by
  let inside : Proc (.nm :: .nm :: Δ) :=
    par (compile body (liftRen (push environment) [.nm]) (.succ .zero))
      (server value (push (push environment)) .zero)
  let call : Proc (.nm :: Δ) :=
    out2 (.var .zero) (.var (.succ (environment _ argument))) (.var (.succ result))
  let received : Proc (.nm :: .nm :: Δ) :=
    compile body (push (liftRen environment [.nm])) .zero
  let continuation : Proc (.nm :: .nm :: Δ) :=
    out2 (.var .zero) (.var (.succ (.succ (environment _ argument))))
      (.var (.succ (.succ result)))
  let retained : Proc (.nm :: Δ) := server value (push environment) .zero
  have aligned : rename swapRen (par inside (weaken call)) =
      par (par received (weaken retained)) continuation := by
    dsimp only [inside, received, retained, continuation]
    rw [rename_par, rename_par, swap_definition_body, swap_definition_server]
    congr 1
  change StructuralEq (nu (par (nu inside) call))
    (nu (par (nu (par received continuation)) retained))
  apply StructuralEq.trans (.nu (.nuPar inside call))
  apply StructuralEq.trans (.nuSwap (par inside (weaken call)))
  rw [aligned]
  exact .trans (.nu (.nu (frame_exchange _ _ _))) (.nu (.symm (.nuPar _ _)))

/-- Every independently authored static source derivation is implemented
by the actual target equations, including equality under suspended values. -/
theorem compile_structural {Γ Δ : Ctx sig} {source target : Expr Γ}
    (equal : NamePassing.Environment.StructuralEq source target)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    StructuralEq (compile source environment result) (compile target environment result) := by
  induction equal generalizing Δ with
  | refl => exact .refl _
  | symm _ ih => exact .symm (ih environment result)
  | trans _ _ firstIH secondIH =>
      exact .trans (firstIH environment result) (secondIH environment result)
  | appDefinition value body argument =>
      exact compile_appDefinition value body argument environment result
  | appCarrier name value body argument =>
      exact compile_appCarrier name value body argument environment result
  | lam _ ih => exact .inp2 _ (ih (callEnv environment) (.succ .zero))
  | app argument _ ih =>
      exact .nu (.par (ih (push environment) .zero) (.refl _))
  | defn _ _ valueIH bodyIH =>
      exact .nu (.par (bodyIH (liftRen environment [.nm]) (.succ result))
        (.rep (.inp1 _ (valueIH (push (push environment)) .zero))))
  | carrier name _ _ valueIH bodyIH =>
      exact .par (bodyIH environment result) (.inp1 _ (valueIH (push environment) .zero))

/-- One genuine source communication, with published static administration,
still gives one target communication at the supplied translated endpoint. -/
theorem modulo_step_preserved {Γ Δ : Ctx sig} {action : NamePassing.Environment.Action}
    {source target : Expr Γ} (step : NamePassing.Environment.StepModulo action source target)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    StepModulo (compile source environment result) (compile target environment result) := by
  obtain ⟨activeSource, activeTarget, before, firing, after⟩ := step
  exact modulo_congr (compile_structural before environment result)
    (step_preserved firing environment result) (compile_structural after environment result)

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquations
