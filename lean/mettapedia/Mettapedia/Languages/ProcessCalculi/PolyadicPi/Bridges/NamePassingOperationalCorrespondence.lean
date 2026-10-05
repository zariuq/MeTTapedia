import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingCompilerReadback
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingEnvironmentEquationsNative
import Mettapedia.GSLT.Core.OperationalReadbackAccounts

/-!
# Operational correspondence on the entire name-passing compiler image

The related target states are all actual representatives of the emitted
structural class. Every supplied target communication reads back to one
source beta or fetch, and each source step remains implementable from every
related representative. The existing source and target GSLTs supply the path
carriers and transition account; no separate operational authority is added.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalCorrespondence

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.Ultrainfinite
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Effects
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative

/-- The relation includes every structural representative, without restricting
which actual communication or target endpoint may be supplied. -/
def readback {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm) :
    OperationalReadback (sourceTheory Γ) (operationalTheory Δ) where
  related source current := StructuralEq current (compile source environment result)
  readStep := by
    intro source current target related firing
    obtain ⟨action, successor, step, endpoint⟩ :=
      NamePassingCompilerReadback.class_step_readback source environment faithful result related firing
    exact .inr ⟨successor, ⟨action, step⟩, endpoint⟩

/-- Forward execution consumes the previously checked compiler, while
backward execution consumes the independent image-inversion theorem. -/
def correspondence {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm) :
    OperationalCorrespondence (sourceTheory Γ) (operationalTheory Δ) where
  toOperationalReadback := readback environment faithful result
  forward := by
    intro source after current related firing
    have emitted := (compiler environment result).mapStep firing
    have actual := NamePassingEnvironment.modulo_congr related emitted (.refl _)
    exact ⟨compile after environment result, ⟨.cons ⟨actual⟩ (.refl _)⟩, .refl _⟩

theorem compiled_related {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm) (source : Expr Γ) :
    (readback environment faithful result).related source (compile source environment result) :=
  .refl _

/-- Static administration has no primitive transition charge. A real target
communication is charged against its real source event, one for one. -/
def account {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm) :
    (readback environment faithful result).Account where
  sourceAccount := transitionAccount (sourceTheory Γ)
  potential := fun _ _ => 0
  readStep := by
    intro source current target related firing
    obtain ⟨action, successor, step, endpoint⟩ :=
      NamePassingCompilerReadback.class_step_readback source environment faithful result related firing
    exact .inr ⟨successor, ⟨action, step⟩, endpoint, Nat.le_refl 1⟩

/-- Each independently supplied execution prefix has a retained source
prefix of exactly the same communication length and the same related endpoint. -/
theorem prefix_readback {Γ Δ : Ctx sig} (environment : Ren sig Γ Δ)
    (faithful : Function.Injective (environment .nm)) (result : Var Δ .nm)
    {source : Expr Γ} {current final : Proc Δ}
    (related : (readback environment faithful result).related source current)
    (path : ExecutionPath (operationalTheory Δ) current final) :
    ∃ after, ∃ reflected : ExecutionPath (sourceTheory Γ) source after,
      (readback environment faithful result).related after final ∧ reflected.length = path.length := by
  obtain ⟨after, reflected, finalRelated, shorter, bounded⟩ :=
    (account environment faithful result).reflectPath_length_bound related path
  have opposite : path.length ≤ reflected.length := by
    simpa only [account, transitionAccount, Nat.zero_add, toAdd_ofAdd] using bounded
  exact ⟨after, reflected, finalRelated, Nat.le_antisymm shorter opposite⟩

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingOperationalCorrespondence
