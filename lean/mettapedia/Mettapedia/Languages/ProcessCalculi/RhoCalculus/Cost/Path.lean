import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawWrapping
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Receipt
import Mathlib.Tactic

/-!
# Occurrence-bearing executable cost paths

A path records the exact raw runtime candidate chosen at each firing.  Its
state indices retain producer provenance, so causal arcs are read from actual
resource consumption rather than reconstructed from equal syntax.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

/-- Every producer attached to a component was emitted before `nextId`. -/
def RawTraceComponent.ProducerBefore (nextId : Nat)
    (component : RawTraceComponent) : Prop :=
  ∀ producer, component.producer = some producer → producer < nextId

/-- All component provenance is bounded by the next fresh event ID. -/
def TraceComponentsBefore (nextId : Nat)
    (components : List RawTraceComponent) : Prop :=
  components.Forall (RawTraceComponent.ProducerBefore nextId)

/-- Every traced component belongs to the accepted raw cost-rho grammar. -/
def TraceComponentsWellFormed (components : List RawTraceComponent) : Prop :=
  components.Forall fun component => component.term.wellFormed = true

theorem TraceComponentsWellFormed.toConfig
    {components : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components) :
    (components.map RawTraceComponent.term).Forall
      (fun term => term.wellFormed = true) := by
  rw [List.forall_iff_forall_mem]
  intro term member
  obtain ⟨component, component_member, rfl⟩ := List.mem_map.mp member
  exact List.forall_iff_forall_mem.mp supported component component_member

private theorem retainedTrace_forall {Predicate : RawTraceComponent → Prop}
    {components : List RawTraceComponent} (supported : components.Forall Predicate)
    (indices : List Nat) :
    ((components.zipIdx.filter fun entry => decide (entry.2 ∉ indices)).map
      Prod.fst).Forall Predicate := by
  rw [List.forall_iff_forall_mem]
  intro component member
  obtain ⟨entry, entry_member, rfl⟩ := List.mem_map.mp member
  have zipped := (List.mem_filter.mp entry_member).1
  exact List.forall_iff_forall_mem.mp supported entry.1
    (List.fst_mem_of_mem_zipIdx zipped)

/-- A traced successor preserves the producer bound and assigns the current
event ID exactly to newly produced contractum and purse-tail occurrences. -/
theorem applyTracedStep_before
    {eventId : Nat} {components : List RawTraceComponent}
    (bounded : TraceComponentsBefore eventId components)
    (step : RawRuntimeStep) :
    TraceComponentsBefore (eventId + 1)
      (applyTracedStep components step eventId) := by
  unfold applyTracedStep TraceComponentsBefore
  apply stableSortBy_forall
  simp only [List.forall_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · have retained := retainedTrace_forall bounded
      (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index)
    apply retained.imp
    intro component before producer equality
    exact Nat.lt_succ_of_lt (before producer equality)
  · rw [List.forall_iff_forall_mem]
    intro component member
    obtain ⟨term, _term_member, rfl⟩ := List.mem_map.mp member
    intro producer equality
    injection equality with equality
    omega
  · rw [List.forall_iff_forall_mem]
    intro component member
    obtain ⟨purse, _purse_member, rfl⟩ := List.mem_map.mp member
    intro producer equality
    injection equality with equality
    omega

/-- Raw wrapped syntax remains supported along the provenance-preserving
successor construction. -/
theorem applyTracedStep_wellFormed
    {components : List RawTraceComponent}
    (supported : TraceComponentsWellFormed components)
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig
      (components.map RawTraceComponent.term)) (eventId : Nat) :
    TraceComponentsWellFormed (applyTracedStep components step eventId) := by
  let config := components.map RawTraceComponent.term
  have config_ok : config.Forall (fun term => term.wellFormed = true) :=
    supported.toConfig
  have wrapped := runtimeCostCandidatesFromConfig_wellWrapped config_ok enabled
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have retained_ok := retainedTrace_forall supported
    (step.participantIndices ++ step.selectedPurses.map RawIndexedPurse.index)
  have contractum_ok := RawCostTerm.components_forall_wellFormed
    step.contractum.normalize
    (RawCostTerm.wellFormed_normalize step.contractum wrapped.2.1)
  have tails_ok := selected_tails_forall_wellFormed config_ok
    funding.selected_from_config
  unfold applyTracedStep TraceComponentsWellFormed
  apply stableSortBy_forall
  simp only [List.forall_append]
  refine ⟨⟨retained_ok, ?_⟩, ?_⟩
  · rw [List.forall_iff_forall_mem]
    intro component member
    obtain ⟨term, term_member, rfl⟩ := List.mem_map.mp member
    exact List.forall_iff_forall_mem.mp contractum_ok term term_member
  · rw [List.forall_iff_forall_mem]
    intro component member
    obtain ⟨purse, purse_member, rfl⟩ := List.mem_map.mp member
    exact List.forall_iff_forall_mem.mp tails_ok
      (RawCostTerm.purse purse.surface purse.tail)
      (List.mem_map.mpr ⟨purse, purse_member, rfl⟩)

/-- A finite sequence of actual occurrence-sensitive runtime firings. -/
inductive CostPath :
    (nextId : Nat) → (components : List RawTraceComponent) →
    (finalId : Nat) → (finalComponents : List RawTraceComponent) → Type where
  | done
      {nextId components}
      (supported : TraceComponentsWellFormed components)
      (bounded : TraceComponentsBefore nextId components) :
      CostPath nextId components nextId components
  | fire
      {nextId components finalId finalComponents}
      (supported : TraceComponentsWellFormed components)
      (bounded : TraceComponentsBefore nextId components)
      (step : RawRuntimeStep)
      (enabled : step ∈ runtimeCostCandidatesFromConfig
        (components.map RawTraceComponent.term))
      (rest : CostPath (nextId + 1)
        (applyTracedStep components step nextId) finalId finalComponents) :
      CostPath nextId components finalId finalComponents

namespace CostPath

def depth {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : Nat :=
  match path with
  | .done _ _ => 0
  | .fire _ _ _ _ rest => rest.depth + 1

/-- Ordered raw event emission generated by the exact firing occurrences. -/
def rawEmission {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : RawReceipt :=
  match path with
  | .done _ _ => []
  | .fire _ _ step _ rest =>
      eventFor components step nextId :: rest.rawEmission

/-- The selected executable candidates, in firing order. -/
def steps {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    List RawRuntimeStep :=
  match path with
  | .done _ _ => []
  | .fire _ _ step _ rest => step :: rest.steps

/-- Total number of consumed purse heads, retaining multi-purse firings. -/
def consumedPurseCells {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : Nat :=
  (path.steps.map fun step => step.selectedPurses.length).sum

/-- Total number of emitted funding contributions. -/
def fundingContributionCount {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) : Nat :=
  (path.rawEmission.map fun event => event.funding.length).sum

@[simp]
theorem steps_length_eq_depth {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.steps.length = path.depth := by
  induction path with
  | done => rfl
  | fire _ _ _ _ rest ih => simp [steps, depth, ih, Nat.add_comm]

@[simp]
theorem rawEmission_length_eq_depth {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.rawEmission.length = path.depth := by
  induction path with
  | done => rfl
  | fire _ _ _ _ rest ih => simp [rawEmission, depth, ih, Nat.add_comm]

/-- Each selected purse head emits exactly one funding contribution. -/
theorem fundingContributionCount_eq_consumedPurseCells
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.fundingContributionCount = path.consumedPurseCells := by
  induction path with
  | done => rfl
  | fire _ _ step _ rest ih =>
      simpa [fundingContributionCount, consumedPurseCells, rawEmission, steps,
        eventFor] using
        congrArg (fun count => step.selectedPurses.length + count) ih

/-- The monotone counter advances once per forced COMM. -/
theorem finalId_eq_start_add_depth
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    finalId = nextId + path.depth := by
  induction path with
  | done => simp [depth]
  | @fire start _ finish _ _ _ _ _ rest ih =>
      change finish = start + (rest.depth + 1)
      omega

/-- Every firing consumes at least one purse head, hence event count is bounded
by consumed purse-cell count.  Equality need not hold for split funding. -/
theorem depth_le_consumedPurseCells
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.depth ≤ path.consumedPurseCells := by
  induction path with
  | done => simp [depth, consumedPurseCells, steps]
  | fire supported _ step enabled rest ih =>
      have config_ok := supported.toConfig
      have wrapped := runtimeCostCandidatesFromConfig_wellWrapped config_ok enabled
      have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
      have nonempty := funding.no_ambient_funding wrapped.1
      have one_le : 1 ≤ step.selectedPurses.length :=
        (List.length_pos_iff.mpr nonempty)
      change rest.depth + 1 ≤ step.selectedPurses.length + rest.consumedPurseCells
      omega

/-- Exactly the single-head-funded paths have one consumed purse cell per
event. -/
theorem consumedPurseCells_eq_depth_iff
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.consumedPurseCells = path.depth ↔
      path.steps.Forall (fun step => step.selectedPurses.length = 1) := by
  induction path with
  | done => simp [consumedPurseCells, depth, steps]
  | fire supported _ step enabled rest ih =>
      have config_ok := supported.toConfig
      have wrapped := runtimeCostCandidatesFromConfig_wellWrapped config_ok enabled
      have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
      have nonempty := funding.no_ambient_funding wrapped.1
      have one_le : 1 ≤ step.selectedPurses.length :=
        (List.length_pos_iff.mpr nonempty)
      have rest_bound := rest.depth_le_consumedPurseCells
      simp only [consumedPurseCells, steps, List.map_cons, List.sum_cons, depth,
        List.forall_cons]
      change rest.depth ≤
        (rest.steps.map fun tailStep => tailStep.selectedPurses.length).sum at rest_bound
      change
        (rest.steps.map fun tailStep => tailStep.selectedPurses.length).sum = rest.depth ↔
          rest.steps.Forall
            (fun tailStep => tailStep.selectedPurses.length = 1) at ih
      constructor
      · intro total
        have head_one : step.selectedPurses.length = 1 := by omega
        have tail_total :
            (rest.steps.map fun tailStep => tailStep.selectedPurses.length).sum =
              rest.depth := by omega
        exact ⟨head_one, ih.mp tail_total⟩
      · rintro ⟨head_one, tail_single⟩
        rw [head_one, ih.mpr tail_single]
        omega

/-- The ordered list of raw spends has one entry per forced COMM. -/
def spends {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    List (Multiset String) :=
  path.steps.map fun step => step.spend.toMultiset

@[simp]
theorem spent_depth_eq_steps
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.spends.length = path.depth := by
  simp [spends]

end CostPath

/-- Initial traced configurations contain no invented provenance. -/
def initialTraceComponents (term : RawCostTerm) : List RawTraceComponent :=
  term.normalizeConfig.map fun component => ⟨component, none⟩

theorem initialTraceComponents_before (term : RawCostTerm) :
    TraceComponentsBefore 0 (initialTraceComponents term) := by
  rw [TraceComponentsBefore, List.forall_iff_forall_mem]
  intro component member producer equality
  obtain ⟨term, _term_member, rfl⟩ := List.mem_map.mp member
  simp at equality

theorem initialTraceComponents_wellFormed {term : RawCostTerm}
    (supported : term.wellFormed = true) :
    TraceComponentsWellFormed (initialTraceComponents term) := by
  rw [TraceComponentsWellFormed, List.forall_iff_forall_mem]
  intro component member
  obtain ⟨source, source_member, rfl⟩ := List.mem_map.mp member
  exact List.forall_iff_forall_mem.mp
    (RawCostTerm.normalizeConfig_forall_wellFormed supported) source source_member

/-! ## Proof-carrying conversion to the canonical causal receipt -/

theorem RawRuntimeStep.selectedPurse_wellFormed
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config)
    {purse : RawSelectedPurse} (member : purse ∈ step.selectedPurses) :
    purse.WellFormed := by
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have all_purses := config.purses_forall_wellFormed config_ok
  exact List.forall_iff_forall_mem.mp all_purses purse
    (funding.selected_from_config.mem member)

/-- Convert one selected purse occurrence into its typed funding record. -/
def RawRuntimeStep.selectedFundingContribution
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (step : RawRuntimeStep)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config)
    (purse : { purse // purse ∈ step.selectedPurses }) :
    FundingContribution String RawCostName :=
  let purse_ok := step.selectedPurse_wellFormed config_ok enabled purse.property
  { surface := purse.val.surface
    spend := purse.val.head.toMultiset
    spend_valid :=
      (RawCostSig.valid_iff_toMultiset_ne_zero purse.val.head).mp purse_ok.head }

/-- The occurrence-preserving funding list of an executable candidate is a
nonempty canonical event label. -/
def RawRuntimeStep.toSpendEvent
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (step : RawRuntimeStep)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    SpendEvent String RawCostName := by
  let fundingList := step.selectedPurses.attach.map
    (step.selectedFundingContribution config_ok enabled)
  have wrapped := runtimeCostCandidatesFromConfig_wellWrapped config_ok enabled
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have selected_nonempty := funding.no_ambient_funding wrapped.1
  have funding_nonempty : fundingList ≠ [] := by
    intro empty
    have attached_empty : step.selectedPurses.attach = [] :=
      List.map_eq_nil_iff.mp empty
    exact selected_nonempty (List.attach_eq_nil_iff.mp attached_empty)
  exact
    { funding := fundingList
      funding_nonempty := by simpa using funding_nonempty }

/-- The canonical event label measures exactly the executable candidate's
normalized demanded spend. -/
theorem RawRuntimeStep.toSpendEvent_rawSpend
    {config : RawCostConfig}
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    (step : RawRuntimeStep)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    (step.toSpendEvent config_ok enabled).rawSpend = step.spend.toMultiset := by
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  rw [← funding.exact_spend]
  simp [RawRuntimeStep.toSpendEvent,
    RawRuntimeStep.selectedFundingContribution, SpendEvent.rawSpend,
    rawSelectedSpend]

namespace CostPath

/-- Canonical proof-carrying emission.  IDs and cause pointers are copied from
the executable event; funding validity is derived from the source grammar and
the exact-cover search. -/
def emission {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    ReceiptEmission Nat String RawCostName :=
  match path with
  | .done _ _ => []
  | .fire supported _ step enabled rest =>
      { id := nextId
        causes := (eventFor components step nextId).causes
        label := step.toSpendEvent supported.toConfig enabled } :: rest.emission

@[simp]
theorem emission_length_eq_depth {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.emission.length = path.depth := by
  induction path with
  | done => rfl
  | fire _ _ _ _ rest ih => simp [emission, depth, ih, Nat.add_comm]

/-- Counter IDs are consecutive and occurrence preserving. -/
theorem emission_ids {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.emission.map EmittedEvent.id = List.range' nextId path.depth := by
  induction path with
  | done => rfl
  | @fire start _ _ _ _ _ _ _ rest ih =>
      simp only [emission, List.map_cons, depth]
      rw [List.range'_succ]
      simpa using ih

/-- Each emitted cause is numerically earlier than its effect. -/
theorem eventFor_causes_before
    {eventId : Nat} {components : List RawTraceComponent}
    (bounded : TraceComponentsBefore eventId components)
    (step : RawRuntimeStep) :
    (eventFor components step eventId).causes.Forall (· < eventId) := by
  rw [List.forall_iff_forall_mem]
  intro producer member
  obtain ⟨index, _index_member, found⟩ := List.mem_filterMap.mp member
  unfold producerAt? at found
  cases lookup : components[index]? with
  | none => simp [lookup] at found
  | some component =>
      have producer_eq : component.producer = some producer := by
        simpa [lookup] using found
      obtain ⟨in_bounds, at_index⟩ := List.getElem?_eq_some_iff.mp lookup
      have component_member : component ∈ components :=
        List.mem_iff_getElem.mpr ⟨index, in_bounds, at_index⟩
      exact List.forall_iff_forall_mem.mp bounded component component_member
        producer producer_eq

theorem emission_causes_before_id
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.emission.Forall fun event => event.causes.Forall (· < event.id) := by
  induction path with
  | done => trivial
  | fire _ bounded step _ rest ih =>
      apply (List.forall_cons _ _ _).mpr
      exact ⟨eventFor_causes_before bounded step, ih⟩

/-- The event stored at emission position `i` has counter ID `start + i`. -/
theorem emission_get_id
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents)
    (index : Fin path.emission.length) :
    (path.emission.get index).id = nextId + index.1 := by
  induction path with
  | done => exact Fin.elim0 index
  | @fire start source finish target supported bounded step enabled rest ih =>
      change
        (({ id := start
            causes := (eventFor source step start).causes
            label := step.toSpendEvent supported.toConfig enabled } ::
          rest.emission).get index).id = start + index.1
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · simp
      · change (rest.emission.get tailIndex).id = start + tailIndex.1.succ
        have tail_id := ih tailIndex
        omega

/-- Executions starting from fresh ID zero emit a valid append-only causal
presentation: IDs are unique and every cause names an earlier occurrence. -/
theorem emitted_receipt_valid
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents) :
    path.emission.Valid := by
  constructor
  · rw [path.emission_ids]
    exact List.nodup_range'
  · intro effect
    rw [List.forall_iff_forall_mem]
    intro causeId cause_member
    have effect_property := List.forall_iff_forall_mem.mp
      path.emission_causes_before_id (path.emission.get effect)
      (List.get_mem path.emission effect)
    have cause_before_id := List.forall_iff_forall_mem.mp effect_property
      causeId cause_member
    have effect_id := path.emission_get_id effect
    have cause_before_effect : causeId < effect.1 := by omega
    let cause : Fin path.emission.length :=
      ⟨causeId, Nat.lt_trans cause_before_effect effect.2⟩
    refine ⟨cause, ?_, ?_⟩
    · exact cause_before_effect
    · simpa [cause] using path.emission_get_id cause

/-- The operational log order linearizes consumption causality. -/
theorem emission_linearizes
    {components finalId finalComponents}
    (path : CostPath 0 components finalId finalComponents)
    {earlier later : Fin path.emission.length}
    (causal : (path.emission.toReceipt path.emitted_receipt_valid).CausalLE
      earlier later) :
    earlier ≤ later :=
  ReceiptEmission.emission_linearizes_causal_order path.emission
    path.emitted_receipt_valid causal

/-- Event labels and executable candidates carry exactly the same ordered raw
spend sequence. -/
theorem emission_rawSpends_eq_steps
    {nextId components finalId finalComponents}
    (path : CostPath nextId components finalId finalComponents) :
    path.emission.map (fun event => event.label.rawSpend) = path.spends := by
  induction path with
  | done => rfl
  | fire supported _ step enabled rest ih =>
      change
        (step.toSpendEvent supported.toConfig enabled).rawSpend ::
            (rest.emission.map fun event => event.label.rawSpend) =
          step.spend.toMultiset :: rest.spends
      rw [step.toSpendEvent_rawSpend supported.toConfig enabled, ih]

end CostPath

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
