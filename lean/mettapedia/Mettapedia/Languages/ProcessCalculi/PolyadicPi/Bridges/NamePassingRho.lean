import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingMonadic
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryCompiler

/-!
# The composed name-passing lambda compiler into core rho syntax

All five lambda constructors, including persistent definitions and active
carriers, compile through the existing polyadic translation and private
unary protocol. Their complete images inhabit the guarded unary domain of
the core-rho compiler. Thus the actual composed syntax compiler succeeds
for every source expression, name environment and result channel.

This is image coverage and independently checked emitted-code formation.
NamePassingSpine separately proves execution correspondence using the
initial world's checked channel separation and the source-derived tuple
roles. Syntax totality alone does not establish those execution laws.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRho

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler

theorem guarded_sendPair {Γ : Ctx sig} (channel first second : Name Γ) :
    GuardedUnary (MonadicProtocol.sendPair channel first second) :=
  .nu (.par (.out1 _ _) (.inp1 _ (.par (.out1 _ _) (.out1 _ _))))

theorem guarded_receivePair {Γ : Ctx sig} (channel : Name Γ)
    {body : Proc (.nm :: .nm :: Γ)} (guarded : GuardedUnary body) :
    GuardedUnary (MonadicProtocol.receivePair channel body) :=
  .inp1 _ (.nu (.par (.out1 _ _)
    (.inp1 _ (.inp1 _ (GuardedUnary.rename guarded MonadicProtocol.receiveBodyRen)))))

/-- Coverage concerns the actual compiler's entire source language,
rather than only a collection of accepted examples. -/
theorem guarded_compiler_image {Γ Δ : Ctx sig}
    (term : NamePassingLambda.Expr Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) :
    GuardedUnary (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) := by
  induction term generalizing Δ with
  | var name =>
      simp only [NamePassingLambda.compile, MonadicProtocol.lower_out1]
      exact .out1 _ _
  | lam body ih =>
      simp only [NamePassingLambda.compile, MonadicProtocol.lower_inp2]
      exact guarded_receivePair _ (ih (NamePassingLambda.callEnv environment) (.succ .zero))
  | app function argument ih =>
      simp only [NamePassingLambda.compile, MonadicProtocol.lower_nu,
        MonadicProtocol.lower_par, MonadicProtocol.lower_out2]
      exact .nu (.par (ih (NamePassingLambda.push environment) .zero)
        (guarded_sendPair _ _ _))
  | defn value body valueIH bodyIH =>
      simp only [NamePassingLambda.compile, MonadicProtocol.lower_nu,
        MonadicProtocol.lower_par, MonadicProtocol.lower_rep, MonadicProtocol.lower_inp1]
      exact .nu (.par (bodyIH (liftRen environment [.nm]) (.succ result))
        (.server _ (valueIH (NamePassingLambda.push (NamePassingLambda.push environment)) .zero)))
  | carrier name value body valueIH bodyIH =>
      simp only [NamePassingLambda.compile, MonadicProtocol.lower_par, MonadicProtocol.lower_inp1]
      exact .par (bodyIH environment result)
        (.inp1 _ (valueIH (NamePassingLambda.push environment) .zero))

/-- The actual syntax compiler uses the authored polyadic program, its
private-session lowering, and the guarded unary core-rho implementation. -/
def compile {Γ Δ : Ctx sig} {depth : Nat}
    (term : NamePassingLambda.Expr Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (world : RhoUnaryCompiler.World Δ depth) :
    Option (RhoUnaryCode.Code depth) :=
  RhoUnaryCompiler.compile world
    (MonadicProtocol.lower (NamePassingLambda.compile term environment result))

theorem compile_total {Γ Δ : Ctx sig} {depth : Nat}
    (term : NamePassingLambda.Expr Γ) (environment : Ren sig Γ Δ)
    (result : Var Δ .nm) (world : RhoUnaryCompiler.World Δ depth) :
    ∃ code, compile term environment result world = some code :=
  compile_guarded (guarded_compiler_image term environment result) world

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRho
