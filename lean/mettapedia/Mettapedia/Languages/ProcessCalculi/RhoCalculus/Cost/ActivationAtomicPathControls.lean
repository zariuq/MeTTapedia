import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPaths
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.UnitPolicyControls

/-!
# Discriminating finite runtime controls for atomic cells

Two independently signed communications use distinct literal keys at one
nonempty nominal channel. Both receivers transfer a sealed payload.
The existing occurrence catalogue supplies two successive firings. This raw
runtime control checks the general preserved admission law; the separate
parser-image theorem supplies that admission for actual generated syntax.
A real multi-atom single-cell path shows why the admission is necessary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPathControls

def fireTwice {term : RawCostTerm} (valid : term.wellFormed = true)
    (first : RawRuntimeStep)
    (firstEnabled : first ∈ runtimeCostCandidatesFromConfig
      ((initialTraceComponents term).map RawTraceComponent.term))
    (second : RawRuntimeStep)
    (secondEnabled : second ∈ runtimeCostCandidatesFromConfig
      ((applyTracedStep (initialTraceComponents term) first 0).map RawTraceComponent.term)) :
    CostPath 0 (initialTraceComponents term) 2
      (applyTracedStep (applyTracedStep (initialTraceComponents term) first 0) second 1) := by
  have supported := initialTraceComponents_wellFormed valid
  have bounded := initialTraceComponents_before term
  exact .fire supported bounded first firstEnabled
    (.fire (applyTracedStep_wellFormed supported firstEnabled 0)
      (applyTracedStep_before bounded first) second secondEnabled
      (.done (applyTracedStep_wellFormed
        (applyTracedStep_wellFormed supported firstEnabled 0) secondEnabled 1)
        (applyTracedStep_before (applyTracedStep_before bounded first) second)))

def payload : RawCostTerm := .signed .nil ["p"]
def channel : RawCostName := .signature ["c"]

def contact (authority : String) : RawCostTerm :=
  .par (.signed (.par (.recv channel (.drop (.bvar 0))) (.send channel payload)) [authority])
    (.purse channel [[authority]])

def source : RawCostTerm := .par (contact "a") (contact "b")
def initial : List RawTraceComponent := initialTraceComponents source

def firstStep : RawRuntimeStep :=
  (runtimeCostCandidatesFromConfig (initial.map RawTraceComponent.term))[0]'(by decide +kernel)

theorem first_enabled : firstStep ∈ runtimeCostCandidatesFromConfig (initial.map RawTraceComponent.term) :=
  List.getElem_mem _

def afterFirst : List RawTraceComponent := applyTracedStep initial firstStep 0

def secondStep : RawRuntimeStep :=
  (runtimeCostCandidatesFromConfig (afterFirst.map RawTraceComponent.term))[0]'(by decide +kernel)

theorem second_enabled : secondStep ∈ runtimeCostCandidatesFromConfig (afterFirst.map RawTraceComponent.term) :=
  List.getElem_mem _

def final : List RawTraceComponent := applyTracedStep afterFirst secondStep 1

theorem source_wellFormed : source.wellFormed = true := by decide +kernel

theorem first_occurrence : firstStep ∈ runtimeCostCandidatesFromConfig
    ((initialTraceComponents source).map RawTraceComponent.term) := by
  simpa only [initial] using first_enabled

theorem second_occurrence : secondStep ∈ runtimeCostCandidatesFromConfig
    ((applyTracedStep (initialTraceComponents source) firstStep 0).map RawTraceComponent.term) := by
  simpa only [initial, afterFirst] using second_enabled

def path := fireTwice source_wellFormed firstStep first_occurrence secondStep second_occurrence

theorem two_actual_firings : path.depth = 2 := rfl

theorem two_firing_cell_atom_balance :
    path.consumedPurseCells = path.spends.sum.card ∧
      (decodeRawConfig (initial.map RawTraceComponent.term)).physicalPurseCells =
        (decodeRawConfig (final.map RawTraceComponent.term)).physicalPurseCells + path.spends.sum.card ∧
      (decodeRawConfig (final.map RawTraceComponent.term)).physicalPurseMeasure CostStack.nonSingletonCells = 0 := by
  have canonical := initialTraceComponents_canonical source
  have sourceSeparated : (decodeCostTerm source).components.ResourceSeparated := by
    simp [source, contact, payload, channel, decodeCostTerm, decodeCostProc, decodeCostName,
      CostTerm.components, CostConfig.ResourceSeparated, CostTerm.ResourceSeparated,
      CostTerm.PurseFree, CostTerm.purseInventory, CostName.purseInventory, CostProc.purseInventory]
  have separated : (decodeRawConfig (initial.map RawTraceComponent.term)).ResourceSeparated :=
    initialTraceComponents_resourceSeparated source sourceSeparated
  have atomic : (decodeRawConfig (initial.map RawTraceComponent.term)).physicalPurseMeasure
      CostStack.nonSingletonCells = 0 := by decide +kernel
  obtain ⟨finalAtomic, count⟩ := path.executable_atomic_cells canonical separated atomic
  exact ⟨count, by rw [← count]; exact path.executable_physical_cells_balance canonical separated, finalAtomic⟩

/-- The two firings consume both actual heads and preserve the signed payload copies. -/
theorem concrete_two_firing_inventory :
    path.consumedPurseCells = 2 ∧ path.spends.sum.card = 2 ∧
      (decodeRawConfig (initial.map RawTraceComponent.term)).physicalPurseCells = 2 ∧
      (decodeRawConfig (final.map RawTraceComponent.term)).physicalPurseCells = 0 ∧
      (decodeRawConfig (final.map RawTraceComponent.term)).physicalPurseOccurrences = 2 := by
  decide +kernel

/-- The broader runtime admits one physical cell with two signing atoms.
It is a genuine path, but contradicts a domain-free cell/atom equality. -/
theorem multi_atom_single_cell_counterexample :
    UnitPolicyControls.combinedHeadPath.consumedPurseCells = 1 ∧
      UnitPolicyControls.combinedHeadPath.spends.sum.card = 2 ∧
      UnitPolicyControls.combinedHeadPath.consumedPurseCells ≠
        UnitPolicyControls.combinedHeadPath.spends.sum.card := by
  decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPathControls
