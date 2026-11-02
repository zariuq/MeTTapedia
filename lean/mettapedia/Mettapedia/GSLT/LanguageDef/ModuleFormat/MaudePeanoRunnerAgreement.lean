import Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudePeanoModelAgreement
import Mettapedia.OSLF.MeTTaIL.Complete.Normalized
import Mettapedia.OSLF.MeTTaIL.Complete.Explore

/-! The normalized shared class runner preserves source Peano paths at
every budget. A completed run has exactly the source normalizer's result;
each source firing remains discoverable by the shared search. -/

set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoRunner

open Mettapedia.Languages
open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.Machines.ResumableSearchRunner (Machine)
open PeanoProducer PeanoModel

theorem canon_encode (source : Maude.Term) : CanonicalBags.canon (encode source) = encode source := by
  refine Maude.Term.rec
    (motive_1 := fun term => CanonicalBags.canon (encode term) = encode term)
    (motive_2 := fun terms => (terms.map encode).map CanonicalBags.canon = terms.map encode)
    ?_ ?_ ?_ ?_ source
  · intro name
    rw [encode, CanonicalBags.canon]
  · intro id arguments ih
    rw [encode, CanonicalBags.canon_apply, ih]
  · rfl
  · intro first rest firstIH restIH
    simp only [List.map_cons, firstIH, restIH]

theorem commit_encode (context : Maude.VariableContext) (source : Maude.Term) :
    Complete.Normalized.commit (compiledPlan context) .canonical (encode source) = encode source := by
  have laws : Complete.Normalized.laws (compiledPlan context) = [] := by cbv
  have extrusions : Complete.Normalized.extrusions (compiledPlan context) = [] := by cbv
  rw [Complete.Normalized.commit, Complete.Normalized.standard, laws, extrusions,
    CollectionLaws.standardForm_nil, canon_encode]

theorem normalized_readback {context : Maude.VariableContext} {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (step : Complete.Normalized.NormalizedStep (compiledPlan context) [] (.base "Nat") .canonical (encode source) target) :
    ∃ result, target = encode result ∧ Maude.EquationReduction Maude.Examples.peano context "Nat" source result := by
  obtain ⟨reached, step, committed⟩ := step
  obtain ⟨result, decoded, reduced⟩ := step_readback typed step
  refine ⟨result, ?_, reduced⟩
  rw [decoded, commit_encode] at committed
  exact committed.symm

theorem normalized_path_readback {context : Maude.VariableContext} {source : Maude.Term} {target : Pattern}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (path : Relation.ReflTransGen
      (Complete.Normalized.NormalizedStep (compiledPlan context) [] (.base "Nat") .canonical) (encode source) target) :
    ∃ result, target = encode result ∧ Maude.EquationPath Maude.Examples.peano context "Nat" source result := by
  induction path with
  | refl => exact ⟨source, rfl, .refl⟩
  | tail _ step ih =>
      obtain ⟨middle, middleEq, sourcePath⟩ := ih
      rw [middleEq] at step
      obtain ⟨result, resultEq, reduced⟩ := normalized_readback (sourcePath.equivalent typed).sorted.2 step
      exact ⟨result, resultEq, sourcePath.tail reduced⟩

def run (context : Maude.VariableContext) (source : Maude.Term) (ticks quantum : Nat) : Complete.Classes.Machine (compiledPlan context) :=
  Machine.advance (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical) ticks quantum
    (Machine.begin (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical)
      (Complete.Normalized.commit (compiledPlan context) .canonical (encode source)))

theorem run_source_path (context : Maude.VariableContext) (source : Maude.Term) (ticks quantum : Nat)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") :
    ∃ result, (run context source ticks quantum).state = encode result ∧
      Maude.EquationPath Maude.Examples.peano context "Nat" source result := by
  have path := Mettapedia.Machines.ResumableSearchRunner.advance_reaches
    (Complete.Normalized.search_lawful (compiledPlan context) [] (.base "Nat") .canonical)
    (Reduces := Complete.Normalized.NormalizedStep (compiledPlan context) [] (.base "Nat") .canonical)
    (fun valid => ⟨_, GeneralOccurrenceSemantics.Receipt.semantic_step (compiledPlan context) [] (.base "Nat") valid, rfl⟩)
    quantum ticks
    (Mettapedia.Machines.ResumableSearchRunner.begin_reached
      (Complete.Normalized.commit (compiledPlan context) .canonical (encode source)))
  change Relation.ReflTransGen
    (Complete.Normalized.NormalizedStep (compiledPlan context) [] (.base "Nat") .canonical)
    (Complete.Normalized.commit (compiledPlan context) .canonical (encode source))
    (run context source ticks quantum).state at path
  rw [commit_encode] at path
  exact normalized_path_readback typed path

theorem equations_checked (context : Maude.VariableContext) :
    Complete.Predecessors.equationsChecked (compiledPlan context) = true := by cbv

theorem descent_checked (context : Maude.VariableContext) :
    StructuralDescent.checkEnvironment (environment context) = true := by cbv

theorem search_settles (context : Maude.VariableContext) (source : Pattern) :
    ∃ work, Complete.Classes.complete (compiledPlan context)
      (Complete.Classes.runAt (compiledPlan context) [] (.base "Nat") source work) = true :=
  Complete.Classes.equationFree_eventually_complete (compiledPlan context) [] (.base "Nat") source
    (equations_empty context) (descent_checked context)

theorem source_step_discovered {context : Maude.VariableContext} {source target : Maude.Term}
    (step : Maude.EquationReduction Maude.Examples.peano context "Nat" source target) :
    ∃ work receipt, receipt ∈ (Complete.Classes.runAt (compiledPlan context) [] (.base "Nat") (encode source) work).log ∧
      receipt.target = encode target := by
  obtain ⟨work, receipt, member, after⟩ := Complete.Classes.complete_in_limit (compiledPlan context) [] (.base "Nat")
    (encode source) (equations_checked context) ((step_iff_source step.sorted.1).mpr step)
  exact ⟨work, receipt, member, Complete.Classes.equivalent_eq_of_no_equations (compiledPlan context) [] (.base "Nat")
    (equations_empty context) after⟩

theorem source_path_explored {context : Maude.VariableContext} {source target : Maude.Term}
    (path : Maude.EquationPath Maude.Examples.peano context "Nat" source target) :
    Complete.Explore.Explored
      (S := Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical)
      (encode source) (encode target) := by
  induction path with
  | refl => exact Complete.Explore.explored_source _
  | @tail middle target _ step ih =>
      obtain ⟨work, receipt, member, endpoint⟩ := source_step_discovered step
      have published : receipt ∈
          (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical).publication
            ((Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical).run (encode middle) work) := by
        exact member
      have found := Complete.Explore.explored_target
        (Complete.Normalized.search_lawful (compiledPlan context) [] (.base "Nat") .canonical) ih published
      change Complete.Explore.Explored
        (S := Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical)
        (encode source) (Complete.Normalized.commit (compiledPlan context) .canonical receipt.target) at found
      rw [endpoint, commit_encode] at found
      exact found

theorem history_source_path {context : Maude.VariableContext} {source : Maude.Term}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    {states : List Pattern} {receipts : List GeneralOccurrenceSemantics.Receipt}
    (history : Mettapedia.Machines.ResumableSearchRunner.History
      (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical) states receipts)
    (origin : states.getLast? = some (encode source)) :
    ∃ result, states.head? = some (encode result) ∧ Maude.EquationPath Maude.Examples.peano context "Nat" source result := by
  revert origin
  induction history with
  | start initial =>
      intro origin
      have same : initial = encode source := by simpa using origin
      exact ⟨source, by rw [same]; rfl, .refl⟩
  | @commit state states receipts receipt previous valid ih =>
      intro origin
      have previousOrigin : (state :: states).getLast? = some (encode source) := by
        simpa only [List.getLast?_cons_cons] using origin
      obtain ⟨middle, head, path⟩ := ih previousOrigin
      have stateEq : state = encode middle := Option.some.inj head
      have normalized : Complete.Normalized.NormalizedStep (compiledPlan context) [] (.base "Nat") .canonical state
          ((Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical).target receipt) :=
        ⟨receipt.target, GeneralOccurrenceSemantics.Receipt.semantic_step (compiledPlan context) [] (.base "Nat") valid, rfl⟩
      rw [stateEq] at normalized
      obtain ⟨result, decoded, reduced⟩ := normalized_readback (path.equivalent typed).sorted.2 normalized
      exact ⟨result, congrArg some decoded, path.tail reduced⟩

theorem explored_node_source {context : Maude.VariableContext} {source : Maude.Term}
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat") (work : Nat)
    {node : Complete.Explore.Node Pattern (Complete.Classes.State (compiledPlan context)) GeneralOccurrenceSemantics.Receipt}
    (member : node ∈ (Complete.Explore.explore
      (Complete.Normalized.search (compiledPlan context) [] (.base "Nat") .canonical) (encode source) work).nodes) :
    ∃ result, node.state = encode result ∧ Maude.EquationPath Maude.Examples.peano context "Nat" source result := by
  obtain ⟨history, current, origin⟩ := Complete.Explore.node_chain
    (Complete.Normalized.search_lawful (compiledPlan context) [] (.base "Nat") .canonical) (encode source) work node member
  obtain ⟨result, head, path⟩ := history_source_path typed history origin
  exact ⟨result, Option.some.inj (current.symm.trans head), path⟩

theorem done_value (context : Maude.VariableContext) (source : Maude.Term) (ticks quantum : Nat)
    (typed : Maude.HasSort Maude.Examples.peano.signature context source "Nat")
    (done : (run context source ticks quantum).phase = .done) :
    (run context source ticks quantum).state = encode (Maude.PeanoNormalization.reduce source) := by
  obtain ⟨result, decoded, reduced⟩ := run_source_path context source ticks quantum typed
  have reached := Mettapedia.Machines.ResumableSearchRunner.run_reached
    (Complete.Normalized.search_lawful (compiledPlan context) [] (.base "Nat") .canonical)
    (Complete.Normalized.commit (compiledPlan context) .canonical (encode source)) ticks quantum
  have noStep := Complete.Normalized.done_no_step (compiledPlan context) [] (.base "Nat")
    (equations_checked context) reached done
  have noSourceStep : ∀ next, ¬ Maude.EquationReduction Maude.Examples.peano context "Nat" result next := by
    intro next step
    apply noStep (encode next)
    change (GeneralOccurrenceSemantics.gslt (compiledPlan context) [] (.base "Nat")).Step
      (run context source ticks quantum).state (encode next)
    rw [decoded]
    exact (step_iff_source (reduced.equivalent typed).sorted.2).mpr step
  exact decoded.trans (congrArg encode (Maude.PeanoNormalization.normal_result_unique typed reduced noSourceStep))

end Mettapedia.GSLT.LanguageDef.ModuleFormat.MaudeCompilation.NormalizationStage.PeanoRunner
