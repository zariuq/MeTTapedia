import Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport
import Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-!
# An authored binder premise under an occurrence-preserving oracle extension

Duplicating the real beta answers gives two individual oracle occurrences at
the lambda body's open redex. The old beta answer embeds as the second copy.
The generic ordered-rule transport carries that selected occurrence through
LamCong without closing over its bound variable or merging the two histories.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Examples.ScopedLamCongOracleTransport

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.RuleBinding
open Mettapedia.OSLF.MeTTaIL.ScopedPremiseExecution
open Mettapedia.OSLF.MeTTaIL.OracleOccurrenceEmbedding
open Mettapedia.OSLF.MeTTaIL.OraclePremiseTransport
open Mettapedia.GSLT.Examples.ScopedLamCongExecution

/-- Retain each actual beta result twice, with distinct oracle ordinals. -/
def duplicatedBetaOracle : StepOracle Unit := fun depth source =>
  betaOracle depth source ++ betaOracle depth source

/-- The old beta result is the second copy in the extended oracle list.
This embedding is defined for every context and source, not only the example
redex, so it can interpret all ordered premise calls. -/
def betaOccurrenceEmbedding (depth : Nat) (source : Pattern) :
    Embedding
      (fun oldValue newValue =>
        oldValue.2 = newValue.2 ∧ oldValue.1 = newValue.1)
      (betaOracle depth source)
      (duplicatedBetaOracle depth source) where
  position :=
    (Embedding.afterPrefix (betaOracle depth source)
      (betaOracle depth source)).position
  relates := by
    intro i
    have same :=
      (Embedding.afterPrefix (betaOracle depth source)
        (betaOracle depth source)).relates i
    exact ⟨congrArg Prod.snd same, congrArg Prod.fst same⟩

theorem beta_occurrence_reindexed :
    ((betaOccurrenceEmbedding 1 openRedex).position
      ⟨0, by simp [inner_beta_open]⟩).val = 1 := by
  exact (Embedding.afterPrefix_position
    (betaOracle 1 openRedex) (betaOracle 1 openRedex)
    ⟨0, by simp [inner_beta_open]⟩).trans (by simp [inner_beta_open])

/-- A full firing of the actual authored LamCong rule transports through the
generic rule theorem. It preserves the open result and captures, and its
history certificate includes the exact oracle position of its beta child. -/
theorem authored_lamCong_firing_transports :
    ∃ spec oldFiring newFiring,
      lamCongRule.bindings = some spec ∧
      oldFiring ∈ applyRuleWithOracle betaOracle RelationEnv.empty
        language 0 lamCongRule wrappedRedex ∧
      newFiring ∈ applyRuleWithOracle duplicatedBetaOracle
        RelationEnv.empty language 0 lamCongRule wrappedRedex ∧
      oldFiring.target = wrappedTarget ∧
      newFiring.target = wrappedTarget ∧
      newFiring.captured = oldFiring.captured ∧
      newFiring.completed = oldFiring.completed ∧
      RunTransport Eq betaOracle duplicatedBetaOracle
        betaOccurrenceEmbedding RelationEnv.empty language language
        lamCongRule spec 0 0
        lamCongRule.premises oldFiring.captured oldFiring.completed
        oldFiring.history newFiring.history := by
  obtain ⟨oldFiring, oldSelected, targetEq, _⟩ := lamCong_executes_open
  obtain ⟨spec, newFiring, binding, newSelected,
    capturedEq, completedEq, targetTransport, historyTransport⟩ :=
      applyRuleWithOracle_transport Eq betaOracle duplicatedBetaOracle
        betaOccurrenceEmbedding RelationEnv.empty language language 0
        lamCongRule wrappedRedex oldFiring oldSelected
  exact ⟨spec, oldFiring, newFiring, binding, oldSelected,
    newSelected, targetEq, targetTransport.trans targetEq,
    capturedEq, completedEq, historyTransport⟩

/-- At the actual open redex, duplicating beta's answer makes two equal
answers at different positions; the old selected one is position one. -/
theorem duplicated_beta_answers :
    duplicatedBetaOracle 1 openRedex =
      [((), .bvar 0), ((), .bvar 0)] := by
  simp [duplicatedBetaOracle, inner_beta_open]

/-- Both LamCong firings have the same result, yet retain distinct premise
histories. In particular, a literal history comparison would not express
which duplicate is selected by the embedding. -/
theorem duplicated_lamCong_histories :
    (applyRuleWithOracle duplicatedBetaOracle RelationEnv.empty language
      0 lamCongRule wrappedRedex).map
        (fun firing => (firing.history, firing.target)) =
      [([.step 0 0 ()], wrappedTarget),
       ([.step 0 1 ()], wrappedTarget)] := by
  decide +kernel

theorem old_lamCong_has_no_second_occurrence :
    ¬ ∃ firing ∈ applyRuleWithOracle betaOracle RelationEnv.empty
        language 0 lamCongRule wrappedRedex,
      firing.history = [.step 0 1 ()] := by
  decide +kernel

#print axioms beta_occurrence_reindexed
#print axioms authored_lamCong_firing_transports
#print axioms duplicated_beta_answers
#print axioms duplicated_lamCong_histories
#print axioms old_lamCong_has_no_second_occurrence

end Mettapedia.GSLT.Examples.ScopedLamCongOracleTransport
