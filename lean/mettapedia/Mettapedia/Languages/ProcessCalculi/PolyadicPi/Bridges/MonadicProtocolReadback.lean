import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocolCompletionReflection
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes
import Mettapedia.GSLT.Core.OperationalReadbackAccounts

/-!
# Reading actual private completions into the shared operational interface

Finite assemblies of the identity function's private final phases instantiate
the generic readback against the existing polyadic operational theory. The
target relation is the actual directed active reduction on all scoped
processes. The source relation is the independently defined reduction modulo
structural equations. Every supplied target prefix has a retained source
prefix with the same communication count, and aligned native endpoint
observations reflect through the generated OSLF diamond.

The relation covers private final phases. It does not claim to cover every
state of the four-instruction protocol, nor arbitrary structural target
representatives, nor to lift all alternative source choices after a private
session has already been selected.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Completion

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.OSLF.Framework.GSLTTypeSynthesis
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.NativeTypes

def completionReadback (Γ : Ctx sig) :
    OperationalReadback (operationalTheory Γ) (rawOperationalTheory Γ) where
  related origin current := ∃ requests : List (Request Γ),
    origin = readbackAssembly requests ∧ current = assembly requests
  readStep := by
    rintro origin current next ⟨requests, rfl, rfl⟩ step
    obtain ⟨remaining, endpoint, sourceStep, _, _⟩ := assembly_step_reflection requests step
    exact .inr ⟨readbackAssembly remaining, sourceStep.toModulo, remaining, rfl, endpoint⟩

theorem assembly_related {Γ : Ctx sig} (requests : List (Request Γ)) :
    (completionReadback Γ).related (readbackAssembly requests) (assembly requests) :=
  ⟨requests, rfl, rfl⟩

/-- Every completion communication exposes one real source communication;
no extra instruction potential is required in this final-phase profile. -/
def completionAccount (Γ : Ctx sig) : (completionReadback Γ).Account where
  sourceAccount := transitionAccount (operationalTheory Γ)
  potential := fun _ _ => 0
  readStep := by
    rintro origin current next ⟨requests, rfl, rfl⟩ step
    obtain ⟨remaining, endpoint, sourceStep, _, _⟩ := assembly_step_reflection requests step
    exact .inr ⟨readbackAssembly remaining, sourceStep.toModulo,
      ⟨remaining, rfl, endpoint⟩, Nat.le_refl 1⟩

/-- The shared account theorem consumes an independently given actual
target path and preserves its endpoint. -/
theorem completion_prefix_readback {Γ : Ctx sig} (requests : List (Request Γ))
    {endpoint : Proc Γ}
    (path : ExecutionPath (rawOperationalTheory Γ) (assembly requests) endpoint) :
    ∃ after, ∃ sourcePath : ExecutionPath (operationalTheory Γ)
        (readbackAssembly requests) after,
      (completionReadback Γ).related after endpoint ∧ sourcePath.length = path.length := by
  obtain ⟨after, sourcePath, related, shorter, bounded⟩ :=
    (completionAccount Γ).reflectPath_length_bound (assembly_related requests) path
  have opposite : path.length ≤ sourcePath.length := by
    simpa only [completionAccount, transitionAccount, Nat.zero_add,
      toAdd_ofAdd] using bounded
  exact ⟨after, sourcePath, related, Nat.le_antisymm shorter opposite⟩

/-- Actual native reachability observations cannot acquire a successful
source endpoint that was absent from every source execution. -/
theorem completion_nativeDiamond_reflected {Γ : Ctx sig}
    (sourcePredicate : EquationPredicate (operationalTheory Γ).closure)
    (targetPredicate : EquationPredicate (rawOperationalTheory Γ).closure)
    (observations : ∀ requests : List (Request Γ),
      targetPredicate.1 (assembly requests) → sourcePredicate.1 (readbackAssembly requests))
    (requests : List (Request Γ))
    (possible : (semanticDiamond (rawOperationalTheory Γ).closure targetPredicate).1
      (assembly requests)) :
    (semanticDiamond (operationalTheory Γ).closure sourcePredicate).1
      (readbackAssembly requests) := by
  apply (completionReadback Γ).nativeDiamond_reflected sourcePredicate targetPredicate
    (related := assembly_related requests) (possible := possible)
  rintro origin current ⟨remaining, rfl, rfl⟩ holds
  exact observations remaining holds

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.MonadicProtocol.Completion
