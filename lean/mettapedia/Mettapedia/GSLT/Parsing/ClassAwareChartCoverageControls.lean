import Mettapedia.GSLT.Parsing.ClassAwareChartCoverage

/-! Coverage retains duplicate physical production occurrences, admits extra
irrelevant families, rejects missing live families, and distinguishes pending
construction from completed absence. -/

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Mettapedia.GSLT.Parsing.ClassAwareChartCoverage.Controls

open ClassAwarePackedForest ClassAwareChartClosure ClassAwareParserPackCorrespondence ParserProfileSemantics

def profile : ParserProfileLayer := ⟨"Coverage", "Word", [], []⟩
def row : CompiledLexicalProduction := ⟨"same", "Word", .char 97, [0]⟩
def plan : CompiledParserPackPlan := {
  lexical := ⟨"Coverage", "Word", [], [row, row]⟩
  structural := [] }
def family (position : Nat) : Family := ⟨⟨"Word", 0, 1⟩, .lexical position, [.terminal (.char 97) 0 1]⟩
def full : Forest := ⟨[⟨"Word", 0, 1⟩], [family 0, family 1]⟩

open ClassAwareChartDemand

def initial : State := ⟨[], []⟩
def requested : State := ⟨[("Word", 0)], []⟩
def ready : State := ⟨[("Word", 0)], full.families⟩

theorem initial_step : ClassAwareChartDemand.step profile plan [97] initial = requested := by
  simp only [ClassAwareChartDemand.step, Mettapedia.Util.LinearHash.eraseDupsFast_eq,
    indexedRequests_exact, indexedStructural_exact]
  decide_cbv

theorem requested_step : ClassAwareChartDemand.step profile plan [97] requested = ready := by
  simp only [ClassAwareChartDemand.step, Mettapedia.Util.LinearHash.eraseDupsFast_eq,
    indexedRequests_exact, indexedStructural_exact]
  decide_cbv

theorem ready_step : ClassAwareChartDemand.step profile plan [97] ready = ready := by
  simp only [ClassAwareChartDemand.step, Mettapedia.Util.LinearHash.eraseDupsFast_eq,
    indexedRequests_exact, indexedStructural_exact]
  decide_cbv

theorem roots_ready : ClassAwareChartClosure.recognizedForest plan [97] ready.families = full := by decide_cbv

theorem expand_roots : ClassAwareChartPruning.expand full full.roots = full.roots := by
  rw [ClassAwareChartPruning.expand_exact]
  decide_cbv

theorem prune_full : ClassAwareChartPruning.prune? full = some full := by
  unfold ClassAwareChartPruning.prune?
  change (ClassAwareChartPruning.finish? full 4 full.roots).map _ = _
  rw [ClassAwareChartPruning.finish?, expand_roots]
  simp only [beq_self_eq_true, ↓reduceIte, Option.map_some, Std.HashSet.contains_ofList]
  decide_cbv

theorem reference_ready : ClassAwareChartDemand.reference? profile plan [97] 3 = some full := by
  unfold ClassAwareChartDemand.reference?
  change ClassAwareChartDemand.finish? profile plan [97] 3 initial = _
  rw [ClassAwareChartDemand.finish?, initial_step]
  have different : (requested == initial) = false := by decide_cbv
  rw [different]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ClassAwareChartDemand.finish?, requested_step]
  have different2 : (ready == requested) = false := by decide_cbv
  rw [different2]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ClassAwareChartDemand.finish?, ready_step]
  simp only [beq_self_eq_true, ↓reduceIte, roots_ready, prune_full]

theorem both_occurrences_covered : coverage? profile plan [97] full 3 = some true := by
  rw [coverage?, reference_ready]
  decide_cbv

theorem omitted_occurrence_rejected :
    coverage? profile plan [97] {full with families := [family 0]} 3 = some false := by
  rw [coverage?, reference_ready]
  decide_cbv

theorem missing_root_rejected :
    coverage? profile plan [97] {full with roots := []} 3 = some false := by
  rw [coverage?, reference_ready]
  decide_cbv

theorem extra_irrelevant_family_allowed :
    coverage? profile plan [97] {full with families := full.families ++ [⟨⟨"Other", 0, 1⟩, .lexical 0, []⟩]} 3 =
      some true := by
  rw [coverage?, reference_ready]
  decide_cbv

theorem zero_budget_pending : coverage? profile plan [97] full 0 = none := rfl

theorem no_word_complete : coverage? profile plan [98] ⟨[], []⟩ 3 = some true := by
  have first : ClassAwareChartDemand.step profile plan [98] initial = requested := by
    simp only [ClassAwareChartDemand.step, Mettapedia.Util.LinearHash.eraseDupsFast_eq,
      indexedRequests_exact, indexedStructural_exact]
    decide_cbv
  have last : ClassAwareChartDemand.step profile plan [98] requested = requested := by
    simp only [ClassAwareChartDemand.step, Mettapedia.Util.LinearHash.eraseDupsFast_eq,
      indexedRequests_exact, indexedStructural_exact]
    decide_cbv
  have recognized : ClassAwareChartClosure.recognizedForest plan [98] requested.families = ⟨[], []⟩ := by decide_cbv
  have pruned : ClassAwareChartPruning.prune? ⟨[], []⟩ = some ⟨[], []⟩ := by
    simp only [ClassAwareChartPruning.prune?, ClassAwareChartPruning.budget,
      ClassAwareChartPruning.finish?, ClassAwareChartPruning.expand_exact, Std.HashSet.contains_ofList]
    decide_cbv
  unfold coverage? ClassAwareChartDemand.reference?
  change (ClassAwareChartDemand.finish? profile plan [98] 3 initial).map _ = _
  rw [ClassAwareChartDemand.finish?, first]
  have different : (requested == initial) = false := by decide_cbv
  rw [different]
  simp only [Bool.false_eq_true, ↓reduceIte]
  rw [ClassAwareChartDemand.finish?, last]
  simp only [beq_self_eq_true, ↓reduceIte, recognized, pruned, Option.map_some]
  decide_cbv

theorem covered_fibre_complete : ClassAwareNativeForestQualification.RootParserComplete full profile plan [97] :=
  coverage?_complete both_occurrences_covered

end Mettapedia.GSLT.Parsing.ClassAwareChartCoverage.Controls
