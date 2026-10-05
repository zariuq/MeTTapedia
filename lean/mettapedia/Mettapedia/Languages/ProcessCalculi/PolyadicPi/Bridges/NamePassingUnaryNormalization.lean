import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryOperational
import Mettapedia.GSLT.Core.OperationalNormalization

/-!
# No infinite tuple administration between lambda events

A supplied unary step either performs a real source event or decreases the
finite occurrence debt. Source accessibility and induction on that debt
therefore cover every actual target schedule. Independently positive forward
blocks provide the reverse implication and the infinite-execution comparison.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryNormalization

open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.Languages.ProcessCalculi.PolyadicPi
open Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges
open NamePassingLambda NamePassingEnvironmentEquationsNative NamePassingUnaryForward NamePassingUnaryOperational
open MonadicProtocol.RuntimeWitness

theorem strongly_normalizing {Γ : Ctx sig} {source : Expr Γ} {current : Proc (.nm :: Γ)}
    (normalizing : Acc (fun after before => (sourceTheory Γ).Step before after) source)
    (before : Witness (polyadic source) current) :
    Acc (fun after state => (NativeTypes.operationalTheory (.nm :: Γ)).Step state after) current := by
  induction normalizing generalizing current with
  | intro source _ sourceIH =>
      have solve : ∀ amount : Nat, ∀ (state : Proc (.nm :: Γ))
          (witness : Witness (polyadic source) state), witness.debt = amount →
          Acc (fun after state => (NativeTypes.operationalTheory (.nm :: Γ)).Step state after) state := by
        intro amount
        induction amount using Nat.strong_induction_on with
        | h amount debtIH =>
            intro state witness debt
            apply Acc.intro state
            intro next actual
            rcases readStep witness actual with unchanged | advanced
            · obtain ⟨nextWitness, balance⟩ := unchanged
              exact debtIH nextWitness.debt (by omega) next nextWitness rfl
            · obtain ⟨after, step, nextWitness, _⟩ := advanced
              exact sourceIH after step nextWitness
      exact solve before.debt current before rfl

theorem accessibility_iff {Γ : Ctx sig} {source : Expr Γ} {current : Proc (.nm :: Γ)}
    (related : Related source current) :
    Acc (fun after before => (sourceTheory Γ).Step before after) source ↔
      Acc (fun after state => (NativeTypes.operationalTheory (.nm :: Γ)).Step state after) current := by
  constructor
  · intro normalizing
    obtain ⟨before⟩ := related
    exact strongly_normalizing normalizing before
  · exact fun normalizing => (correspondence Γ).normalization_reflected
      (fun comparison step => positive_forward comparison step) related normalizing

theorem infinite_execution_iff {Γ : Ctx sig} {source : Expr Γ} {current : Proc (.nm :: Γ)}
    (related : Related source current) :
    (∃ execution : Nat → Expr Γ, execution 0 = source ∧
      ∀ index, (sourceTheory Γ).Step (execution index) (execution (index + 1))) ↔
    (∃ runtime : Nat → Proc (.nm :: Γ), runtime 0 = current ∧
      ∀ index, (NativeTypes.operationalTheory (.nm :: Γ)).Step (runtime index) (runtime (index + 1))) := by
  constructor
  · intro execution
    have divergent : ¬ Acc (fun after before => (sourceTheory Γ).Step before after) source :=
      not_acc_iff_exists_descending_chain.mpr execution
    exact not_acc_iff_exists_descending_chain.mp
      (fun normalizing => divergent ((accessibility_iff related).mpr normalizing))
  · intro execution
    have divergent : ¬ Acc
        (fun after state => (NativeTypes.operationalTheory (.nm :: Γ)).Step state after) current :=
      not_acc_iff_exists_descending_chain.mpr execution
    exact not_acc_iff_exists_descending_chain.mp
      (fun normalizing => divergent ((accessibility_iff related).mp normalizing))

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingUnaryNormalization
