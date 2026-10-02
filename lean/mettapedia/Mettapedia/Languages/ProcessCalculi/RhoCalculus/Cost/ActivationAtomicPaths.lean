import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAtomicPurseImage
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationExecutablePath

/-!
# Atomic generated funding throughout actual finite execution

A concrete count of non-singleton cells vanishes on the existing generated
parser image. The executable occurrence partition preserves that condition:
communicated code introduces no purses, selected heads are removed, and their
ordered tails remain. Thus every firing in an actual finite path from an
admitted generated source consumes one physical cell per exact authority atom.
This does not identify firing count with atom count, or split signature syntax
into authority atoms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- Number of cells whose literal signature bag is not a singleton. -/
def CostStack.nonSingletonCells {Ground : Type u} : CostStack Ground → Nat
  | .empty => 0
  | .cons head tail => (if head.card = 1 then 0 else 1) + tail.nonSingletonCells

theorem CostStack.SingletonHeads.nonSingletonCells_zero {Ground : Type u}
    {stack : CostStack Ground} (atomic : stack.SingletonHeads) : stack.nonSingletonCells = 0 := by
  induction atomic with
  | empty => rfl
  | cons head rest ih => simp only [CostStack.nonSingletonCells, head, if_true, zero_add, ih]

theorem CostStack.nonSingletonCells_cons_zero {Ground : Type u}
    {head : CostSig Ground} {tail : CostStack Ground}
    (zero : (CostStack.cons head tail).nonSingletonCells = 0) :
    head.card = 1 ∧ tail.nonSingletonCells = 0 := by
  unfold CostStack.nonSingletonCells at zero
  by_cases atomic : head.card = 1
  · exact ⟨atomic, by simpa only [atomic, if_true, zero_add] using zero⟩
  · simp only [atomic, if_false] at zero
    omega

theorem CostTerm.components_measure_zero_of_inventory {Ground : Type u}
    (weight : CostStack Ground → Nat) (term : CostTerm Ground)
    (zero : ∀ stack ∈ term.purseInventory, weight stack = 0) :
    term.components.physicalPurseMeasure weight = 0 := by
  cases term with
  | nil => simp [CostTerm.components, CostConfig.physicalPurseMeasure]
  | par left right =>
      rw [CostTerm.components, CostConfig.physicalPurseMeasure_add]
      rw [CostTerm.components_measure_zero_of_inventory weight left
        (fun stack member => zero stack (Multiset.mem_add.mpr (Or.inl member))),
        CostTerm.components_measure_zero_of_inventory weight right
        (fun stack member => zero stack (Multiset.mem_add.mpr (Or.inr member)))]
  | signed process signature => simp [CostTerm.components, CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure]
  | drop name => simp [CostTerm.components, CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure]
  | purse location stack =>
      have head := zero stack (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self stack)))
      simpa [CostTerm.components, CostConfig.physicalPurseMeasure, CostTerm.physicalPurseMeasure] using head

private theorem selected_zero_defects {selected : List RawSelectedPurse}
    (zero : (selected.map fun purse =>
      (CostStack.cons (decodeCostSig purse.head) (decodeCostStack purse.tail)).nonSingletonCells).sum = 0) :
    selected.Forall (fun purse => purse.head.length = 1) ∧
      (selected.map fun purse => (decodeCostStack purse.tail).nonSingletonCells).sum = 0 := by
  induction selected with
  | nil => exact ⟨by simp, rfl⟩
  | cons purse rest ih =>
      simp only [List.map_cons, List.sum_cons] at zero
      have headZero : (CostStack.cons (decodeCostSig purse.head)
          (decodeCostStack purse.tail)).nonSingletonCells = 0 := by omega
      have restZero : (rest.map fun purse =>
          (CostStack.cons (decodeCostSig purse.head) (decodeCostStack purse.tail)).nonSingletonCells).sum = 0 := by omega
      obtain ⟨atomic, tailZero⟩ := CostStack.nonSingletonCells_cons_zero headZero
      obtain ⟨restAtomic, restTails⟩ := ih restZero
      constructor
      · exact (List.forall_cons (fun purse : RawSelectedPurse => purse.head.length = 1) purse rest).mpr
          ⟨atomic, restAtomic⟩
      · simp only [List.map_cons, List.sum_cons, tailZero, restTails, zero_add]

/-- Existing executable forcing preserves atomic cells and equates its two
physical debit observations on this admission domain. -/
theorem applyTracedStep_atomic_cells
    {components : List RawTraceComponent} {step : RawRuntimeStep}
    (canonical : TraceComponentsCanonical components)
    (separated : (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated)
    (atomic : (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseMeasure
      CostStack.nonSingletonCells = 0)
    (enabled : step ∈ runtimeCostCandidatesFromConfig (components.map RawTraceComponent.term))
    (eventId : Nat) :
    (decodeRawConfig ((applyTracedStep components step eventId).map RawTraceComponent.term)).physicalPurseMeasure
      CostStack.nonSingletonCells = 0 ∧
      step.selectedPurses.length = (decodeCostSig step.spend).card := by
  obtain ⟨free, sourceMeasure⟩ := runtime_candidate_code_and_source_measure
    CostStack.nonSingletonCells canonical.rawConfig separated enabled
  have targetMeasure := applyTracedStep_physical_measure CostStack.nonSingletonCells components step eventId free
  rw [atomic] at sourceMeasure
  have retainedZero : (decodeRawConfig (eraseIndices (components.map RawTraceComponent.term)
      (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index))).physicalPurseMeasure
        CostStack.nonSingletonCells = 0 := by omega
  have selectedZero : (step.selectedPurses.map fun purse =>
      (CostStack.cons (decodeCostSig purse.head) (decodeCostStack purse.tail)).nonSingletonCells).sum = 0 := by omega
  obtain ⟨selectedAtomic, tailsZero⟩ := selected_zero_defects selectedZero
  constructor
  · rw [targetMeasure, retainedZero, tailsZero, zero_add]
  · have spend := congrArg Multiset.card
      (runtimeCostCandidatesFromConfig_funding_valid enabled).exact_spend
    rw [rawSelectedSpend_card_eq_length selectedAtomic] at spend
    exact spend

namespace CostPath

/-- Atomic-cell admission is preserved through every existing finite path;
its actual consumed-cell count equals the card of its exact spend bag. -/
theorem executable_atomic_cells :
    ∀ {nextId components finalId finalComponents}
      (path : CostPath nextId components finalId finalComponents),
      TraceComponentsCanonical components →
      (decodeRawConfig (components.map RawTraceComponent.term)).ResourceSeparated →
      (decodeRawConfig (components.map RawTraceComponent.term)).physicalPurseMeasure CostStack.nonSingletonCells = 0 →
      (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseMeasure CostStack.nonSingletonCells = 0 ∧
        path.consumedPurseCells = path.spends.sum.card := by
  intro nextId components finalId finalComponents path
  induction path with
  | done supported bounded =>
      intro _canonical _separated atomic
      exact ⟨atomic, rfl⟩
  | @fire nextId components finalId finalComponents supported bounded step enabled rest ih =>
      intro canonical separated atomic
      obtain ⟨targetAtomic, count⟩ := applyTracedStep_atomic_cells canonical separated atomic enabled nextId
      obtain ⟨finalAtomic, restCount⟩ := ih (applyTracedStep_canonical canonical enabled nextId)
        (applyTracedStep_resourceSeparated canonical separated enabled nextId) targetAtomic
      refine ⟨finalAtomic, ?_⟩
      simp only [consumedPurseCells, steps, spends, List.map_cons, List.sum_cons, Multiset.card_add]
      change step.selectedPurses.length + rest.consumedPurseCells = (decodeCostSig step.spend).card + rest.spends.sum.card
      rw [count, restCount]

end CostPath

namespace ActivationGenerated

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem ConfigImage.initial_atomic_cells {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term) :
    (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term)).physicalPurseMeasure
      CostStack.nonSingletonCells = 0 := by
  rw [initialTraceComponents_physical_measure]
  exact CostTerm.components_measure_zero_of_inventory CostStack.nonSingletonCells _
    (fun stack member => (image.literal_inventory_singleton channelImage member).nonSingletonCells_zero)

/-- Every actual finite execution from this generated parser image has exact
cell/atom balance, independently of how same-location funding is selected. -/
theorem ConfigImage.finite_path_atomic_balance {channelSource source : Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {finalId : Nat} {finalComponents : List RawTraceComponent}
    (path : CostPath 0 (initialTraceComponents (literalEncodeTerm term)) finalId finalComponents) :
    path.consumedPurseCells = path.spends.sum.card ∧
      (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term)).physicalPurseCells =
        (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseCells + path.spends.sum.card ∧
      (decodeRawConfig (finalComponents.map RawTraceComponent.term)).physicalPurseMeasure CostStack.nonSingletonCells = 0 := by
  have canonical := initialTraceComponents_canonical (literalEncodeTerm term)
  have separated := initialTraceComponents_resourceSeparated (literalEncodeTerm term)
    (image.literal_components_resourceSeparated channelImage)
  obtain ⟨finalAtomic, count⟩ := path.executable_atomic_cells canonical separated (image.initial_atomic_cells channelImage)
  exact ⟨count, by rw [← count]; exact path.executable_physical_cells_balance canonical separated, finalAtomic⟩

end ActivationGenerated
end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
