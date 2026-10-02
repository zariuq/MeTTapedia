import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeRetainedEventPersistence
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeResourceWaveControls

/-!
# Independent execution and contested authority

The first candidate from the real two-location runtime configuration leaves
the second event's original endpoint and purse resources in the unselected
frame. The generic persistence law therefore constructs the next catalogue
candidate and an actual two-firing path. In the competing configuration, the
single purse is consumed and neither the retained frame nor the actual
successor can authorize another firing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeRetainedEventControls

open RuntimeExamples
open RuntimeResourceWaveControls

def singleFunding (location : CostName String) (authority : String) :
    FundingSelection String location {authority} where
  chosen := {⟨{authority}, .empty, by simp [CostSig.RuntimeValid]⟩}
  demand_eq := by simp

def eventAt (location : RawCostName) (authority : String) : CostedEvent String :=
  .wholeRecvSend (decodeCostName location) (decodeCostTerm done) (decodeCostTerm payload)
    {authority} (by simp [CostSig.RuntimeValid]) (singleFunding _ authority)

def firstIndependent : RawRuntimeStep :=
  (runtimeCostCandidatesFromConfig twoConfig)[0]'(by decide +kernel)

theorem firstIndependent_enabled : firstIndependent ∈ runtimeCostCandidatesFromConfig twoConfig :=
  List.getElem_mem _

theorem second_resources_retained :
    (eventAt wrong "bob").consumed ≤
      decodeRawConfig (eraseIndices
        ((initialTraceComponents twoIndependentLocations).map RawTraceComponent.term)
        (firstIndependent.participantIndices ++
          firstIndependent.selectedPurses.map RawIndexedPurse.index)) := by
  decide +kernel

/-- The persistence theorem's resource hypothesis is met by actual data;
the second enabled candidate is constructed without evaluating the run. -/
theorem independent_two_firing_path :
    ∃ second,
      second ∈ runtimeCostCandidatesFromConfig
        ((applyTracedStep (initialTraceComponents twoIndependentLocations)
          firstIndependent 0).map RawTraceComponent.term) ∧
      decodeCostName second.location = decodeCostName wrong ∧
      decodeCostSig second.spend = {"bob"} ∧
      second.FrameExactFor ((applyTracedStep (initialTraceComponents twoIndependentLocations)
        firstIndependent 0).map RawTraceComponent.term) ∧
      ∃ path : CostPath 0 (initialTraceComponents twoIndependentLocations) 2
          (applyTracedStep (applyTracedStep (initialTraceComponents twoIndependentLocations)
            firstIndependent 0) second 1),
        path.depth = 2 ∧ path.steps = [firstIndependent, second] := by
  have sourceValid : twoIndependentLocations.wellFormed = true := by decide +kernel
  exact CostedEvent.two_firing_path_after_retained_frame
    (initialTraceComponents_canonical twoIndependentLocations)
    (initialTraceComponents_wellFormed sourceValid)
    (initialTraceComponents_before twoIndependentLocations)
    (by simpa [initialTraceComponents, Function.comp_def, twoConfig] using firstIndependent_enabled)
    (eventAt wrong "bob") second_resources_retained

def contestedSource : RawCostTerm := parList [whole alice, whole alice, purse pay [alice]]

def firstContested : RawRuntimeStep :=
  (runtimeCostCandidatesFromConfig contestedConfig)[0]'(by decide +kernel)

theorem firstContested_enabled : firstContested ∈ runtimeCostCandidatesFromConfig contestedConfig :=
  List.getElem_mem _

/-- The remaining endpoint cannot supply the purse occurrence removed by
the first firing. The independence premise genuinely excludes this case. -/
theorem contested_resources_not_retained :
    ¬ (eventAt pay "alice").consumed ≤
      decodeRawConfig (eraseIndices
        ((initialTraceComponents contestedSource).map RawTraceComponent.term)
        (firstContested.participantIndices ++
          firstContested.selectedPurses.map RawIndexedPurse.index)) := by
  decide +kernel

theorem contested_successor_has_no_candidate :
    runtimeCostCandidatesFromConfig
      ((applyTracedStep (initialTraceComponents contestedSource) firstContested 0).map
        RawTraceComponent.term) = [] := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RuntimeRetainedEventControls
