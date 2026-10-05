import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.ScopedOpening
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnaryReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingRho

/-!
# Scope-opening safety of the actual compiler and runtime image

The scoped-opening condition excludes used private restrictions inside an
autonomous replicated body. The actual compiler replicates input guards,
whose continuations may allocate arbitrarily many private names. Thus every
guarded-unary program, every retained runtime source and the entire lowered
name-passing lambda compiler satisfy this condition. Static-equation and
name-reindexing invariance are supplied by the shared scoped-opening theory.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafety

open Mettapedia.OSLF.Binding
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open RhoUnaryCompiler RhoUnaryActive RhoUnaryReadback ScopedActiveFrontier

/-- Replication in the compiler domain is an actual guarded server.
Restrictions in a suspended continuation do not run before its input. -/
theorem guarded_safe {Γ : Ctx sig} {process : Proc Γ} (guarded : GuardedUnary process) :
    ScopedOpening.Safe process := by
  induction guarded with
  | nil => simp only [nil, ScopedOpening.Safe]
  | par _ _ firstIH secondIH => simpa only [par, ScopedOpening.Safe] using And.intro firstIH secondIH
  | inp1 => simp only [inp1, ScopedOpening.Safe]
  | out1 => simp only [out1, ScopedOpening.Safe]
  | nu _ ih => simpa only [nu, ScopedOpening.Safe] using ih
  | server => simp only [rep, inp1, ScopedOpening.Safe, ScopedOpening.Vacuous]

/-- Closing private source names adds active scopes, without moving a
restriction beneath an autonomous replicated body. -/
theorem safe_scope {Γ Δ : Ctx sig} (scope : Scope Γ Δ) (body : Proc Δ) :
    ScopedOpening.Safe (scope.close body) ↔ ScopedOpening.Safe body := by
  induction scope with
  | nil => rfl
  | bind rest ih => simpa only [Scope.close, nu, ScopedOpening.Safe] using ih body

theorem safe_parallel {Γ : Ctx sig} (processes : List (Proc Γ))
    (safe : ∀ process ∈ processes, ScopedOpening.Safe process) :
    ScopedOpening.Safe (parallel processes) := by
  induction processes with
  | nil => simp only [parallel, nil, ScopedOpening.Safe]
  | cons first rest ih =>
      simp only [parallel, par, ScopedOpening.Safe]
      exact ⟨safe first List.mem_cons_self, ih (fun process member =>
        safe process (List.mem_cons_of_mem _ member))⟩

/-- This property follows from the stored source constructors, independently
of the current inventory's matching and freshness fields. -/
theorem activities_safe {Γ : Ctx sig} (activities : List (Activity Γ)) :
    ScopedOpening.Safe (source activities) := by
  apply safe_parallel
  intro process member
  obtain ⟨activity, _, rfl⟩ := List.mem_map.mp member
  exact guarded_safe activity.source_guarded

/-- Every supplied representative of the retained source image remains
within the admitted scope-opening class, including administrative phases. -/
theorem witness_safe {Γ : Ctx sig} {initialWorld : RhoUnaryWorld.SeedWorld Γ}
    {origin : Proc Γ} {current : TargetProcess} (witness : Witness initialWorld origin current) :
    ScopedOpening.Safe origin :=
  (ScopedOpening.safe_structural witness.source).mpr
    ((safe_scope witness.scope _).mpr (activities_safe witness.activities))

/-- All five lambda source constructors enter the same admitted unary
scope-opening class after the real private-session compiler. -/
theorem lambda_protocol_safe {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    ScopedOpening.Safe (MonadicProtocol.lower (NamePassingLambda.compile term environment result)) :=
  guarded_safe (NamePassingRho.guarded_compiler_image term environment result)

/-- The polyadic source compiler itself meets the same scope condition;
binary call guards do not require a different private-name theory. -/
theorem lambda_polyadic_safe {Γ Δ : Ctx sig} (term : NamePassingLambda.Expr Γ)
    (environment : Ren sig Γ Δ) (result : Var Δ .nm) :
    ScopedOpening.Safe (NamePassingLambda.compile term environment result) := by
  induction term generalizing Δ with
  | var => simp only [NamePassingLambda.compile, out1, ScopedOpening.Safe]
  | lam => simp only [NamePassingLambda.compile, inp2, ScopedOpening.Safe]
  | app function argument ih =>
      simp only [NamePassingLambda.compile, nu, par, out2, ScopedOpening.Safe, and_true]
      exact ih _ _
  | defn value body _ bodyIH =>
      simp only [NamePassingLambda.compile, nu, par, rep, inp1, ScopedOpening.Safe,
        ScopedOpening.Vacuous, and_true]
      exact bodyIH _ _
  | carrier name value body _ bodyIH =>
      simp only [NamePassingLambda.compile, par, inp1, ScopedOpening.Safe, and_true]
      exact bodyIH _ _

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.RhoUnarySourceSafety
