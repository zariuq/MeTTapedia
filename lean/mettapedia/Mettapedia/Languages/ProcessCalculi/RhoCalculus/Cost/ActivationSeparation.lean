import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage

/-!
# Resource separation for the existing funded rho relation

Code components contain no purse constructors, including quoted or suspended
ones.  Located purses remain separate top-level components, and their locations
likewise contain no embedded purses.  This predicate restricts the existing
`CostStep`; it introduces no new execution relation.

The cell and purse readouts of a funded step are those of the funded resource
system: exactly the selected heads leave, and no purse is added or removed
apart from those a contractum releases. On separated configurations a
contractum releases none.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

/-- Whole code is purse-free; a resource is a top-level purse with a code-only
location.  No authority-bearing code payload is admitted. -/
def CostTerm.ResourceSeparated {Ground : Type u} : CostTerm Ground → Prop
  | .purse location _ => location.purseInventory = 0
  | term => term.PurseFree

/-- Every occurrence of a configuration is separate code or a located purse. -/
def CostConfig.ResourceSeparated {Ground : Type u} (config : CostConfig Ground) : Prop :=
  ∀ term ∈ config, term.ResourceSeparated

private theorem inventory_add_zero {α : Type u} (left right : Multiset α)
    (zero : left + right = 0) : left = 0 ∧ right = 0 := by
  have cards := congrArg Multiset.card zero
  simp only [Multiset.card_add, Multiset.card_zero] at cards
  exact ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩

/-- Purse-free whole code has purse-free flattened code components. -/
theorem CostTerm.PurseFree.component {Ground : Type u}
    {term component : CostTerm Ground} (free : term.PurseFree)
    (member : component ∈ term.components) : component.PurseFree := by
  cases term with
  | nil => simp [CostTerm.components] at member
  | par left right =>
      have both := inventory_add_zero left.purseInventory right.purseInventory free
      rcases Multiset.mem_add.mp member with member | member
      · exact CostTerm.PurseFree.component both.1 member
      · exact CostTerm.PurseFree.component both.2 member
  | signed process signature =>
      have same : component = .signed process signature := by simpa [CostTerm.components] using member
      exact same ▸ free
  | drop name =>
      have same : component = .drop name := by simpa [CostTerm.components] using member
      exact same ▸ free
  | purse location stack =>
      have same : component = .purse location stack := by simpa [CostTerm.components] using member
      exact same ▸ free

/-- Code-only whole terms induce separate configurations after flattening. -/
theorem CostTerm.PurseFree.components_resourceSeparated {Ground : Type u}
    {term : CostTerm Ground} (free : term.PurseFree) : term.components.ResourceSeparated := by
  intro component member
  have componentFree := free.component member
  cases component with
  | purse location stack =>
      have cards := congrArg Multiset.card componentFree
      simp only [CostTerm.purseInventory, Multiset.card_add,
        Multiset.card_singleton, Multiset.card_zero] at cards
      omega
  | nil => exact componentFree
  | signed process signature => exact componentFree
  | par left right => exact componentFree
  | drop name => exact componentFree

@[simp]
theorem CostConfig.resourceSeparated_add_iff {Ground : Type u}
    (left right : CostConfig Ground) :
    (left + right).ResourceSeparated ↔ left.ResourceSeparated ∧ right.ResourceSeparated := by
  constructor
  · intro separated
    exact ⟨fun term member => separated term (Multiset.mem_add.mpr (Or.inl member)),
      fun term member => separated term (Multiset.mem_add.mpr (Or.inr member))⟩
  · rintro ⟨leftSafe, rightSafe⟩ term member
    rcases Multiset.mem_add.mp member with member | member
    · exact leftSafe term member
    · exact rightSafe term member

@[simp]
theorem CostConfig.resourceSeparated_singleton_iff {Ground : Type u}
    (term : CostTerm Ground) :
    CostConfig.ResourceSeparated (term ::ₘ (0 : CostConfig Ground)) ↔ term.ResourceSeparated := by
  simp [CostConfig.ResourceSeparated]

@[simp]
theorem LocatedPurse.configComponents_resourceSeparated_iff {Ground : Type u}
    (purses : Multiset (LocatedPurse Ground)) :
    (LocatedPurse.configComponents purses).ResourceSeparated ↔
      ∀ purse ∈ purses, purse.location.purseInventory = 0 := by
  constructor
  · intro separated purse member
    exact separated purse.toTerm (Multiset.mem_map.mpr ⟨purse, member, rfl⟩)
  · intro locations term member
    change term ∈ purses.map LocatedPurse.toTerm at member
    have mapped : ∃ purse ∈ purses, purse.toTerm = term := Multiset.mem_map.mp member
    obtain ⟨purse, purseMember, equation⟩ := mapped
    subst term
    exact locations purse purseMember

/-- Funding exposes tails at the same purse-free locations and retains every
unselected occurrence at its original location. -/
theorem LocatedTokenCover.preserves_purseFree_locations {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual)
    (locations : ∀ purse ∈ available, purse.location.purseInventory = 0) :
    ∀ purse ∈ residual, purse.location.purseInventory = 0 := by
  intro purse member
  rw [cover.residual_eq] at member
  rcases Multiset.mem_add.mp member with selected | untouched
  · obtain ⟨choice, chosen, rfl⟩ := Multiset.mem_map.mp selected
    apply locations ⟨location, .cons choice.head choice.tail⟩
    rw [cover.available_eq]
    exact Multiset.mem_add.mpr (Or.inl (Multiset.mem_map.mpr ⟨choice, chosen, rfl⟩))
  · exact locations purse (Multiset.mem_of_le cover.untouched_le_available untouched)

theorem CostTerm.PurseFree.wholeRecvSend_payloads {Ground : Type u}
    {channel : CostName Ground} {body payload : CostTerm Ground} {signature : CostSig Ground}
    (free : (CostTerm.signed (.par (.recv channel body) (.send channel payload))
      signature).PurseFree) : body.PurseFree ∧ payload.PurseFree := by
  have cards := congrArg Multiset.card free
  simp only [CostTerm.purseInventory, CostProc.purseInventory, Multiset.card_add,
    Multiset.card_zero] at cards
  exact ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩

theorem CostTerm.PurseFree.wholeSendRecv_payloads {Ground : Type u}
    {channel : CostName Ground} {body payload : CostTerm Ground} {signature : CostSig Ground}
    (free : (CostTerm.signed (.par (.send channel payload) (.recv channel body))
      signature).PurseFree) : body.PurseFree ∧ payload.PurseFree := by
  have cards := congrArg Multiset.card free
  simp only [CostTerm.purseInventory, CostProc.purseInventory, Multiset.card_add,
    Multiset.card_zero] at cards
  exact ⟨Multiset.card_eq_zero.mp (by omega), Multiset.card_eq_zero.mp (by omega)⟩

theorem CostTerm.PurseFree.recv_body {Ground : Type u}
    {channel : CostName Ground} {body : CostTerm Ground} {signature : CostSig Ground}
    (free : (CostTerm.signed (.recv channel body) signature).PurseFree) : body.PurseFree := by
  exact (inventory_add_zero channel.purseInventory body.purseInventory free).2

theorem CostTerm.PurseFree.send_payload {Ground : Type u}
    {channel : CostName Ground} {payload : CostTerm Ground} {signature : CostSig Ground}
    (free : (CostTerm.signed (.send channel payload) signature).PurseFree) : payload.PurseFree := by
  exact (inventory_add_zero channel.purseInventory payload.purseInventory free).2

/-- All three original Cost firing rules preserve resource separation.
Substitution may duplicate code; only the external located purse cover changes
the authority components. -/
theorem CostStep.preserves_resourceSeparated {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    target.ResourceSeparated := by
  cases step with
  | wholeRecvSend valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated ⊢
      have free := CostTerm.PurseFree.wholeRecvSend_payloads separated.1.2
      exact ⟨⟨separated.1.1, (free.1.substitute free.2 0).components_resourceSeparated⟩,
        (LocatedPurse.configComponents_resourceSeparated_iff _).mpr
          (cover.preserves_purseFree_locations
            ((LocatedPurse.configComponents_resourceSeparated_iff _).mp separated.2))⟩

  | wholeSendRecv valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated ⊢
      have free := CostTerm.PurseFree.wholeSendRecv_payloads separated.1.2
      exact ⟨⟨separated.1.1, (free.1.substitute free.2 0).components_resourceSeparated⟩,
        (LocatedPurse.configComponents_resourceSeparated_iff _).mpr
          (cover.preserves_purseFree_locations
            ((LocatedPurse.configComponents_resourceSeparated_iff _).mp separated.2))⟩
  | split recvValid sendValid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated ⊢
      have bodyFree := CostTerm.PurseFree.recv_body separated.1.1.2
      have payloadFree := CostTerm.PurseFree.send_payload separated.1.2
      exact ⟨⟨separated.1.1.1,
        (bodyFree.substitute payloadFree 0).components_resourceSeparated⟩,
        (LocatedPurse.configComponents_resourceSeparated_iff _).mpr
          (cover.preserves_purseFree_locations
            ((LocatedPurse.configComponents_resourceSeparated_iff _).mp separated.2))⟩


/-- Number of literal cells in one temporal purse, including its entire tail. -/
def CostStack.cellCount {Ground : Type u} : CostStack Ground → Nat
  | .empty => 0
  | .cons _ tail => tail.cellCount + 1

/-- A configurable readout of the actual top-level purse occurrences.  Latent
syntax inside code contributes no executable resource to this readout. -/
def CostTerm.physicalPurseMeasure {Ground : Type u}
    {Measure : Type v} [AddCommMonoid Measure]
    (weight : CostStack Ground → Measure) : CostTerm Ground → Measure
  | .purse _ stack => weight stack
  | _ => 0

/-- Sum the readout over the actual multiset of configuration components. -/
def CostConfig.physicalPurseMeasure {Ground : Type u}
    {Measure : Type v} [AddCommMonoid Measure]
    (weight : CostStack Ground → Measure) (config : CostConfig Ground) : Measure :=
  (config.map (CostTerm.physicalPurseMeasure weight)).sum

/-- Number of actual stored temporal cells, before any account observation. -/
abbrev CostConfig.physicalPurseCells {Ground : Type u} (config : CostConfig Ground) : Nat :=
  config.physicalPurseMeasure CostStack.cellCount

/-- Actual purse occurrence count; a depleted purse is still one occurrence. -/
abbrev CostConfig.physicalPurseOccurrences {Ground : Type u}
    (config : CostConfig Ground) : Nat :=
  config.physicalPurseMeasure (fun _ => 1)

@[simp]
theorem CostConfig.physicalPurseMeasure_add {Ground : Type u}
    {Measure : Type v} [AddCommMonoid Measure]
    (weight : CostStack Ground → Measure) (left right : CostConfig Ground) :
    (left + right).physicalPurseMeasure weight =
      left.physicalPurseMeasure weight + right.physicalPurseMeasure weight := by
  simp [CostConfig.physicalPurseMeasure]

@[simp]
theorem CostConfig.physicalPurseMeasure_cons_zero {Ground : Type u}
    {Measure : Type v} [AddCommMonoid Measure]
    (weight : CostStack Ground → Measure) (term : CostTerm Ground) :
    CostConfig.physicalPurseMeasure weight (term ::ₘ 0) =
      term.physicalPurseMeasure weight := by
  simp [CostConfig.physicalPurseMeasure]

/-- Code-only substitution cannot contribute any newly active purse readout. -/
theorem CostTerm.PurseFree.components_physicalPurseMeasure_zero {Ground : Type u}
    {Measure : Type v} [AddCommMonoid Measure]
    {term : CostTerm Ground} (free : term.PurseFree)
    (weight : CostStack Ground → Measure) : term.components.physicalPurseMeasure weight = 0 := by
  have mapZero : term.components.map (CostTerm.physicalPurseMeasure weight) =
      term.components.map (fun _ => (0 : Measure)) := by
    apply Multiset.map_congr rfl
    intro component member
    cases component with
    | purse location stack => exact False.elim (free.no_component_purse location stack member)
    | nil => rfl
    | signed process signature => rfl
    | par left right => rfl
    | drop name => rfl
  unfold CostConfig.physicalPurseMeasure
  rw [mapZero]
  simp

@[simp]
theorem LocatedPurse.configComponents_physicalPurseMeasure {Ground : Type u}
    {Measure : Type v} [AddCommMonoid Measure]
    (weight : CostStack Ground → Measure) (purses : Multiset (LocatedPurse Ground)) :
    (LocatedPurse.configComponents purses).physicalPurseMeasure weight =
      (purses.map fun purse => weight purse.stack).sum := by
  simp [CostConfig.physicalPurseMeasure, LocatedPurse.configComponents,
    LocatedPurse.toTerm, CostTerm.physicalPurseMeasure, Function.comp_def]

/-! ## Funded firings in the readouts of the purses

The readouts of the purses of a configuration are readouts of its bag of
purses. Funded firings then change them as the purse system does: exactly the
selected heads leave, no purse is added or removed, and the purses a contractum
releases are added. Where the code of a configuration holds no purse, the
contractum of an enabled event releases none. -/

section PaidFiring

open Mettapedia.GSLT.Causality.ResourceInteraction
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

/-- The number of cells of a stack is the length of its list of cells. -/
theorem CostStack.cellCount_eq_length {Ground : Type u} :
    ∀ stack : CostStack Ground, stack.cellCount = stack.toList.length
  | .empty => rfl
  | .cons _ tail => congrArg (· + 1) (CostStack.cellCount_eq_length tail)

/-- The readout of the purses of a configuration, from its bag of purses. -/
theorem CostConfig.physicalPurseMeasure_eq_purses {Ground : Type u} {Measure : Type v}
    [AddCommMonoid Measure] (weight : CostStack Ground → Measure) (config : CostConfig Ground) :
    config.physicalPurseMeasure weight =
      (config.purses.map fun purse => weight (CostStack.ofList purse.2)).sum := by
  induction config using Multiset.induction_on with
  | empty => rfl
  | cons term config ih =>
      unfold CostConfig.physicalPurseMeasure CostConfig.purses at ih ⊢
      rw [Multiset.map_cons, Multiset.sum_cons, ih]
      cases term with
      | purse location stack =>
          rw [Multiset.filterMap_cons_some CostTerm.purse? (CostTerm.purse location stack) config
              (b := (location, stack.toList)) rfl,
            Multiset.map_cons, Multiset.sum_cons, CostStack.ofList_toList]
          rfl
      | nil =>
          rw [Multiset.filterMap_cons_none (f := CostTerm.purse?) _ _ rfl]
          exact zero_add _
      | signed process signature =>
          rw [Multiset.filterMap_cons_none (f := CostTerm.purse?) _ _ rfl]
          exact zero_add _
      | par left right =>
          rw [Multiset.filterMap_cons_none (f := CostTerm.purse?) _ _ rfl]
          exact zero_add _
      | drop name =>
          rw [Multiset.filterMap_cons_none (f := CostTerm.purse?) _ _ rfl]
          exact zero_add _

/-- The stored cells are the cells of the purses. -/
theorem CostConfig.physicalPurseCells_eq {Ground : Type u} (config : CostConfig Ground) :
    config.physicalPurseCells = cells config.purses := by
  rw [CostConfig.physicalPurseCells, CostConfig.physicalPurseMeasure_eq_purses]
  unfold cells
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun purse _ => ?_)
  rw [CostStack.cellCount_eq_length, CostStack.toList_ofList]

/-- The purse occurrences are the purses. -/
theorem CostConfig.physicalPurseOccurrences_eq {Ground : Type u} (config : CostConfig Ground) :
    config.physicalPurseOccurrences = config.purses.card := by
  rw [CostConfig.physicalPurseOccurrences, CostConfig.physicalPurseMeasure_eq_purses,
    Multiset.map_const', Multiset.sum_replicate, smul_eq_mul, mul_one]

/-- The cells of located purses are counted on their stacks. -/
theorem LocatedPurse.cells_map_toPurse {Ground : Type u}
    (purses : Multiset (LocatedPurse Ground)) :
    cells (purses.map LocatedPurse.toPurse) =
      (purses.map fun purse => purse.stack.cellCount).sum := by
  unfold cells
  rw [Multiset.map_map]
  exact congrArg Multiset.sum (Multiset.map_congr rfl fun purse _ =>
    (CostStack.cellCount_eq_length purse.stack).symm)

/-- **Where the code of a configuration holds no purse, the contractum of an
event whose endpoints are present releases none.** -/
theorem CostedEvent.contractum_purses_eq_zero {Ground : Type u} {config : CostConfig Ground}
    (separated : config.ResourceSeparated) (event : CostedEvent Ground)
    (present : event.endpoints ≤ config) : event.contractum.purses = 0 := by
  have none : ∀ {term : CostTerm Ground}, term.PurseFree →
      CostConfig.purses term.components = 0 := by
    intro term free
    refine CostConfig.purses_eq_zero fun component member isPurse => ?_
    obtain ⟨purse, found⟩ := Option.isSome_iff_exists.mp isPurse
    rw [← purseTerm_of_purse? found] at member
    exact free.no_component_purse _ _ member
  cases event with
  | wholeRecvSend channel body payload outerSig valid funding =>
      have member : CostTerm.signed (.par (.recv channel body) (.send channel payload))
          outerSig ∈ config := Multiset.mem_of_le present (Multiset.mem_singleton_self _)
      have free := CostTerm.PurseFree.wholeRecvSend_payloads (separated _ member)
      exact none (free.1.substitute free.2 0)
  | wholeSendRecv channel body payload outerSig valid funding =>
      have member : CostTerm.signed (.par (.send channel payload) (.recv channel body))
          outerSig ∈ config := Multiset.mem_of_le present (Multiset.mem_singleton_self _)
      have free := CostTerm.PurseFree.wholeSendRecv_payloads (separated _ member)
      exact none (free.1.substitute free.2 0)
  | split channel body payload recvSeal sendSeal recvValid sendValid funding =>
      have recvMember : CostTerm.signed (.recv channel body) recvSeal ∈ config :=
        Multiset.mem_of_le present
          (Multiset.mem_add.mpr (Or.inl (Multiset.mem_singleton_self _)))
      have sendMember : CostTerm.signed (.send channel payload) sendSeal ∈ config :=
        Multiset.mem_of_le present
          (Multiset.mem_add.mpr (Or.inr (Multiset.mem_singleton_self _)))
      exact none ((CostTerm.PurseFree.recv_body (separated _ recvMember)).substitute
        (CostTerm.PurseFree.send_payload (separated _ sendMember)) 0)

/-- The contractum of an event enabled in a separated configuration has no
purse readout. -/
theorem contractum_physicalPurseMeasure_eq_zero {Ground : Type u} {Measure : Type v}
    [AddCommMonoid Measure] (weight : CostStack Ground → Measure) {config : CostConfig Ground}
    (separated : config.ResourceSeparated) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    event.val.contractum.physicalPurseMeasure weight = 0 := by
  rw [CostConfig.physicalPurseMeasure_eq_purses, event.val.contractum_purses_eq_zero separated
    (((costResource_enables_iff_le config event).mp enabled).1.trans (Multiset.filter_le _ _))]
  rfl

/-- An enabled funded firing keeps a configuration separated. -/
theorem costResource_preserves_resourceSeparated {Ground : Type u} [DecidableEq Ground]
    {config : CostConfig Ground} {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (separated : config.ResourceSeparated)
    (enabled : (costResourceSystem Ground).Enables config event) :
    CostConfig.ResourceSeparated ((costResourceSystem Ground).fire config event) :=
  CostStep.preserves_resourceSeparated
    (CostResourceWave.enabled_costStep config ⟨location, event⟩ enabled) separated

/-- **The stored cells drop by the number of selected purses** in a funded
firing, apart from the cells of the purses its contractum releases. -/
theorem costResource_physicalPurseCells {Ground : Type u} [DecidableEq Ground]
    (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    config.physicalPurseCells + event.val.contractum.physicalPurseCells =
      CostConfig.physicalPurseCells ((costResourceSystem Ground).fire config event) +
        event.val.funding.chosen.card := by
  have taken := congrArg Multiset.card (costResource_cells_taken config event enabled)
  rw [Multiset.card_add, Multiset.card_add, card_cellBag, card_cellBag, card_cellBag,
    Multiset.card_map] at taken
  rw [CostConfig.physicalPurseCells_eq, CostConfig.physicalPurseCells_eq,
    CostConfig.physicalPurseCells_eq]
  exact taken

/-- **A funded firing neither adds nor removes a purse**, apart from the purses
its contractum releases. -/
theorem costResource_physicalPurseOccurrences {Ground : Type u} [DecidableEq Ground]
    (config : CostConfig Ground) {location : CostName Ground}
    (event : {event : CostedEvent Ground // event.location = location})
    (enabled : (costResourceSystem Ground).Enables config event) :
    config.physicalPurseOccurrences + event.val.contractum.physicalPurseOccurrences =
      CostConfig.physicalPurseOccurrences ((costResourceSystem Ground).fire config event) := by
  rw [CostConfig.physicalPurseOccurrences_eq, CostConfig.physicalPurseOccurrences_eq,
    CostConfig.physicalPurseOccurrences_eq]
  exact costResource_purses_card config event enabled

/-- **Along a run of funded firings, no purse is added or removed**, apart from
the purses the contracta release. -/
theorem costResource_run_physicalPurseOccurrences {Ground : Type u} [DecidableEq Ground]
    {M N : CostConfig Ground} (p : OccurrencePath (costResourceSystem Ground).presentation M N) :
    M.physicalPurseOccurrences + ((costResourceSystem Ground).instanceValuation
        fun event => event.val.contractum.physicalPurseOccurrences).onPath p =
      N.physicalPurseOccurrences := by
  have released : ((costResourceSystem Ground).instanceValuation
        fun event => event.val.contractum.physicalPurseOccurrences).onPath p =
      ((costResourceSystem Ground).instanceValuation
        fun event => event.val.contractum.purses.card).onPath p :=
    (costResourceSystem Ground).instanceValuation_congr
      (fun event => CostConfig.physicalPurseOccurrences_eq event.val.contractum) p
  rw [released, CostConfig.physicalPurseOccurrences_eq, CostConfig.physicalPurseOccurrences_eq]
  exact costResource_run_purses_card p

/-- A real funding cover removes exactly one cell per selected occurrence;
every unselected purse and every selected tail remains in the residual. -/
theorem LocatedTokenCover.physical_cells_balance {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    (available.map fun purse => purse.stack.cellCount).sum =
      (residual.map fun purse => purse.stack.cellCount).sum + cover.chosen.card := by
  classical
  have taken := congrArg Multiset.card cover.cells_taken
  rwa [Multiset.card_add, card_cellBag, card_cellBag, Multiset.card_map,
    LocatedPurse.cells_map_toPurse, LocatedPurse.cells_map_toPurse] at taken

end PaidFiring

/-- A positive charge selects at least one actual purse cell. -/
theorem LocatedTokenCover.selected_card_pos {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual)
    (valid : demand.RuntimeValid) : 0 < cover.chosen.card := by
  have chosenNonzero : cover.chosen ≠ 0 := by
    intro zero
    apply valid
    rw [cover.demand_eq, zero]
    simp
  exact Nat.pos_of_ne_zero (fun zero => chosenNonzero (Multiset.card_eq_zero.mp zero))

/-- On the preserved separated domain, real temporal cells strictly decrease
by the exact number of selected heads.  This is a configuration statement,
independent of any receipt balance or price valuation. -/
theorem CostStep.physical_cells_decrease {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    ∃ consumedCells, 0 < consumedCells ∧
      source.physicalPurseCells = target.physicalPurseCells + consumedCells := by
  classical
  obtain ⟨entry, rfl, rfl, enabled, rfl⟩ := costStep_iff_exists_enabled_resource.mp step
  have balance := costResource_physicalPurseCells source entry.2 enabled
  have released : entry.2.val.contractum.physicalPurseCells = 0 :=
    contractum_physicalPurseMeasure_eq_zero _ separated entry.2 enabled
  rw [released, add_zero] at balance
  exact ⟨_, Multiset.card_pos.mpr (entry.2.val.funding.chosen_ne_zero entry.2.val.spend_valid),
    balance⟩

/-- A funded separated transition has strictly fewer actual temporal cells. -/
theorem CostStep.physical_cells_strictly_decrease {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    target.physicalPurseCells < source.physicalPurseCells := by
  obtain ⟨cells, positive, balance⟩ := step.physical_cells_decrease separated
  omega

@[simp]
theorem LocatedPurse.configComponents_physicalPurseOccurrences {Ground : Type u}
    (purses : Multiset (LocatedPurse Ground)) :
    (LocatedPurse.configComponents purses).physicalPurseOccurrences = purses.card := by
  simp [CostConfig.physicalPurseOccurrences]

/-- Head consumption exposes a tail in the same occurrence; it neither copies
nor discards purse occurrences. -/
theorem LocatedTokenCover.physical_purse_count_balance {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    available.card = residual.card := by
  classical
  obtain ⟨enabled, fired⟩ := cover.purses_firing
  simpa only [fired, Multiset.card_map] using
    (Mettapedia.GSLT.Causality.ResourceInteraction.pursesMany_card _ _ _ enabled).symm

/-- The preserved separated domain rules out creation of executable purse
occurrences, including through duplicating or discarding communicated code. -/
theorem CostStep.physical_purse_occurrences_preserved {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    source.physicalPurseOccurrences = target.physicalPurseOccurrences := by
  classical
  obtain ⟨entry, rfl, rfl, enabled, rfl⟩ := costStep_iff_exists_enabled_resource.mp step
  have balance := costResource_physicalPurseOccurrences source entry.2 enabled
  have released : entry.2.val.contractum.physicalPurseOccurrences = 0 :=
    contractum_physicalPurseMeasure_eq_zero _ separated entry.2 enabled
  rwa [released, add_zero] at balance

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
