import Mettapedia.Machines.ResumablePrefixClock
import Mettapedia.Machines.HierarchicalPrefixSearch
import Mettapedia.Machines.HierarchicalPrefixLaws
import Mettapedia.Machines.HierarchicalPrefixCost
import Mettapedia.Computability.KolmogorovComplexity.FeatureHierarchicalSearch
import Mettapedia.Examples.Compression.FeatureDyadicSearchControls
import Mettapedia.Logic.KernelFoundationManifest

/-!
# Competing nested searches, retained budgets and real machine controls

A shorter divergent branch competes with two successful siblings. Each
sibling opens another competing search. Controls inspect real retained
states, incomplete budgets, wrong answers and nonadmitted words. A compiled
four-stack worker is also run through the live hierarchy.
-/

set_option autoImplicit false
set_option maxRecDepth 8192

namespace Mettapedia.Examples.Compression.FeatureHierarchicalSearchControls

open KolmogorovComplexity KolmogorovComplexity.FeatureTheory
open Mettapedia.Machines
open HierarchicalPrefixSearch

abbrev controlCode := FeatureDyadicSearchControls.controlCode

def laterOne : BinString := [true, false]
def laterTwo : BinString := [true, true]

def counter (input : Nat) : PrefixPortfolio.Worker Nat Nat where
  initial _word := 0
  step word state := if word = [false] ∨ state < input then some (state + 1) else none
  read word state := if word ≠ [false] ∧ input ≤ state then some (input - 1) else none
  stopped word state answer found := by
    split at found
    · rename_i terminal
      simp [terminal.1, Nat.not_lt.mpr terminal.2]
    · cases found

def childInput (_input answer : Nat) : Nat := answer

def controlRun (budget : Nat) :=
  ResumablePrefixClock.run (tick counter controlCode childInput 2) budget (initial counter 2 2)

theorem nested_answer_survives_a_shorter_divergent_sibling :
    observes 2 [(laterOne, 1), (laterOne, 0)] (controlRun 132) = true := by decide

theorem both_root_siblings_and_both_child_siblings_are_retained :
    observes 2 [(laterOne, 1), (laterTwo, 0)] (controlRun 132) = true ∧
    observes 2 [(laterTwo, 1), (laterOne, 0)] (controlRun 132) = true ∧
    observes 2 [(laterTwo, 1), (laterTwo, 0)] (controlRun 132) = true := by decide

theorem the_divergent_sibling_keeps_running :
    (match (controlRun 132).2.values [false] with
      | .running count => some count
      | _ => none) = some 63 := by decide

theorem earlier_budget_does_not_claim_the_nested_answer :
    observes 2 [(laterOne, 1), (laterOne, 0)] (controlRun 67) = false := by decide

theorem zero_budget_has_no_child : observes 2 [(laterOne, 1)] (controlRun 0) = false := by decide

theorem wrong_answer_is_not_an_observation :
    observes 2 [(laterOne, 2)] (controlRun 132) = false := by decide

theorem a_depth_limit_is_not_a_completed_deeper_search :
    observes 1 [(laterOne, 1), (laterOne, 0)]
      (ResumablePrefixClock.run (tick counter controlCode childInput 1) 132 (initial counter 1 2)) = false := by
  decide

theorem completed_local_work_on_an_unadmitted_word_is_not_serviced :
    (counter 0).read [true] 0 = some 0 ∧
    observes 1 [([true], 0)]
      (ResumablePrefixClock.run (tick counter controlCode childInput 1) 132 (initial counter 1 0)) = false := by
  decide

theorem sliced_execution_retains_the_whole_hierarchy :
    controlRun (67 + 65) = ResumablePrefixClock.run (tick counter controlCode childInput 2) 65 (controlRun 67) :=
  ResumablePrefixClock.run_add _ 67 65 _

theorem sliced_debits_do_not_double_charge :
    runDebit counter controlCode childInput 2 (67 + 65) (initial counter 2 2) =
      (runDebit counter controlCode childInput 2 67 (initial counter 2 2)).add
        (runDebit counter controlCode childInput 2 65 (controlRun 67)) :=
  runDebit_add counter controlCode childInput 2 67 65 _

def timedControl : List (TimedEntry Nat) := [((laterOne, 1), 2), ((laterOne, 0), 1)]

theorem timed_control_is_actual_worker_execution : TimedPath counter childInput 2 timedControl :=
  .cons (by decide) (.cons (by decide) (.nil 0))

theorem nested_bound_pays_cumulative_weights :
    nestedBound timedControl = 2144 ∧ weightedTerms 0 timedControl = [96, 2048] := by decide

theorem timed_control_is_admitted : ∀ entry ∈ timedControl, controlCode entry.1.1 = true := by
  simp only [timedControl, List.forall_mem_cons]
  constructor <;> decide

theorem the_general_bound_reaches_the_executed_control :
    Follows 2 [(laterOne, 1), (laterOne, 0)] (controlRun 2144) := by
  have reached := path_by_bound counter controlCode FeatureDyadicSearchControls.controlCode_prefixFree
    childInput timed_control_is_actual_worker_execution timed_control_is_admitted 2 (by decide)
  rw [nested_bound_pays_cumulative_weights.1] at reached
  exact reached

def realWorkers (_input : Nat) := FeatureDyadicSearchControls.successorWorker

def realRun (budget : Nat) :=
  ResumablePrefixClock.run (tick realWorkers controlCode childInput 1) budget (initial realWorkers 1 0)

theorem initial_machine_tapes_are_not_published : observes 1 [(laterOne, 1)] (realRun 0) = false := by decide

theorem insufficient_real_machine_allocation_is_not_success :
    observes 1 [(laterOne, 1)] (realRun 17) = false := by decide

theorem actual_four_stack_completion_opens_a_child :
    observes 1 [(laterOne, 1)] (realRun 132) = true := by decide

theorem completed_machine_workers_are_not_restarted :
    (runDebit realWorkers controlCode childInput 1 132 (initial realWorkers 1 0)).localTransitions = 27 := by
  decide

def twoTrue : BinString := [true, true]

def twoStepLookup (input : BinString × BinString) : Option BinString :=
  if input = ([false], []) then some twoTrue
  else if input = ([false], twoTrue) then some fourTrue
  else if input = ([true], fourTrue) then some twoTrue
  else if input = ([true], twoTrue) then some []
  else none

def twoStepAlgorithm (program condition : BinString) : Part BinString :=
  Part.ofOption (twoStepLookup (program, condition))

theorem twoStep_effective : Partrec₂ twoStepAlgorithm := by
  have lookup : Primrec twoStepLookup :=
    Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const ([false], []))) (Primrec.const _)
      (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const ([false], twoTrue))) (Primrec.const _)
        (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const ([true], fourTrue))) (Primrec.const _)
          (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const ([true], twoTrue)))
            (Primrec.const _) (Primrec.const _))))
  exact lookup.to_comp.ofOption

theorem twoStep_chain : BChain twoStepAlgorithm 2 fourTrue [[false], [false]] [] := by
  refine .cons (descriptive := [true]) (residual := twoTrue) ?_ ?_ ?_ ?_
    (.cons (descriptive := [true]) (residual := []) ?_ ?_ ?_ ?_ (.nil [])) <;>
    norm_num [twoStepAlgorithm, twoStepLookup, twoTrue, fourTrue]

theorem an_earlier_autoencoder_really_diverges :
    DyadicSearch.autoencoder twoStepAlgorithm (DyadicSearch.pairCode [] []) fourTrue = Part.none := by
  simp [DyadicSearch.autoencoder, DyadicSearch.parsePair_pairCode, DyadicSearch.executePair,
    twoStepAlgorithm, twoStepLookup, fourTrue]

theorem two_actual_compression_steps_have_a_compiled_hierarchical_search :
    ∃ code : Turing.ToPartrec.Code, ∃ entries : List HierarchicalSearch.Entry,
      entries.length = 2 ∧
      Follows fourTrue.length (entries.map Prod.fst)
        (HierarchicalSearch.search code fourTrue (nestedBound entries)) ∧
      HierarchicalSearch.followFrame (.root fourTrue) (entries.map Prod.fst) = ⟨[], [[false], [false]]⟩ ∧
      nestedBound entries = (weightedTerms 0 entries).sum := by
  obtain ⟨code, _codeSpec, complete⟩ := HierarchicalSearch.exists_bounded_hierarchical_search twoStep_effective
  obtain ⟨entries, count, seen, final, bound⟩ := complete 2 fourTrue [] [[false], [false]] twoStep_chain
  exact ⟨code, entries, count, seen, final, bound⟩

end Mettapedia.Examples.Compression.FeatureHierarchicalSearchControls

open Lean Elab Command

run_cmd do
  let env ← getEnv
  let modules := #[`Mettapedia.Machines.ResumablePrefixClock,
    `Mettapedia.Machines.HierarchicalPrefixSearch, `Mettapedia.Machines.HierarchicalPrefixLaws,
    `Mettapedia.Machines.HierarchicalPrefixCost,
    `Mettapedia.Computability.KolmogorovComplexity.FeatureHierarchicalSearch]
  let allowed := #[``propext, ``Quot.sound, ``Classical.choice]
  let mut names : Array Name := #[]
  let mut regular : NameSet := {}
  let mut seen : NameSet := {}
  for moduleName in modules do
    let some index := env.header.moduleNames.toList.idxOf? moduleName | throwError "missing hierarchical-search module {moduleName}"
    let data := env.header.moduleData[index]!
    names := names ++ data.constNames ++ data.extraConstNames
    for name in data.constNames do regular := regular.insert name
  for (name, _) in env.constants.toList do
    if (`Mettapedia.Examples.Compression.FeatureHierarchicalSearchControls).isPrefixOf name then
      names := names.push name
      regular := regular.insert name
  let mut safe := 0
  let mut theorems := 0
  let mut audited : Array Json := #[]
  let mut compilerImplementations : Array Json := #[]
  for name in names do
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.checked.get.find? name | do
      if regular.contains name then throwError "missing hierarchical-search declaration {name}"
      continue
    if info.isUnsafe || info.isPartial then
      let some owner := Mettapedia.Logic.KernelFoundationManifest.runtimeCounterpart? env name
        | throwError "unmatched hierarchical-search compiler declaration {name}"
      let some ownerInfo := env.checked.get.find? owner | throwError "missing logical owner of {name}"
      unless ownerInfo matches .defnInfo _ do throwError "nondefinition owner of {name}"
      if ownerInfo.isUnsafe || ownerInfo.isPartial then throwError "nonlogical owner of {name}"
      let dependencies ← liftCoreM <| collectAxioms owner
      for dependency in dependencies do
        unless allowed.contains dependency do throwError "unpermitted owner dependency {owner}: {dependency}"
      compilerImplementations := compilerImplementations.push
        (Json.mkObj [("name", toJson name.toString), ("logicalOwner", toJson owner.toString),
          ("matchingTypeLevelsAndOwner", toJson true)])
      continue
    if info matches .axiomInfo _ then throwError "new hierarchical-search axiom {name}"
    let mut references := info.type.getUsedConstants
    if let some body := info.value? (allowOpaque := true) then
      references := references ++ body.getUsedConstants
    for reference in references do
      if let some referencedInfo := env.checked.get.find? reference then
        if referencedInfo.isUnsafe || referencedInfo.isPartial then
          throwError "nonlogical reference in {name}: {reference}"
    let dependencies ← liftCoreM <| collectAxioms name
    for dependency in dependencies do
      unless allowed.contains dependency do throwError "unpermitted hierarchical-search dependency {name}: {dependency}"
    safe := safe + 1
    if info matches .thmInfo _ then
      theorems := theorems + 1
      audited := audited.push (Json.mkObj [("name", toJson name.toString),
        ("axioms", toJson (dependencies.map Name.toString))])
  liftIO <| IO.println (Json.mkObj [("hierarchicalSearchDeclarations", toJson safe),
    ("theorems", toJson theorems), ("auditedTheorems", toJson audited),
    ("separateCompilerImplementations", toJson compilerImplementations.size),
    ("compilerImplementations", toJson compilerImplementations)]).compress
