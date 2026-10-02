import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationCodeImage

/-!
# Resource separation for the existing funded rho relation

Code components contain no purse constructors, including quoted or suspended
ones.  Located purses remain separate top-level components, and their locations
likewise contain no embedded purses.  This predicate restricts the existing
`CostStep`; it introduces no new execution relation.
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

/-- A real funding cover removes exactly one cell per selected occurrence;
every unselected purse and every selected tail remains in the residual. -/
theorem LocatedTokenCover.physical_cells_balance {Ground : Type u}
    {location : CostName Ground} {demand : CostSig Ground}
    {available residual : Multiset (LocatedPurse Ground)}
    (cover : LocatedTokenCover location demand available residual) :
    (available.map fun purse => purse.stack.cellCount).sum =
      (residual.map fun purse => purse.stack.cellCount).sum + cover.chosen.card := by
  have selected :
      (cover.chosen.map fun choice => choice.tail.cellCount + 1).sum =
        (cover.chosen.map fun choice => choice.tail.cellCount).sum + cover.chosen.card := by
    induction cover.chosen using Multiset.induction_on with
    | empty => simp
    | @cons choice choices inductionHypothesis =>
        simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons]
        omega
  simp only [cover.available_eq, cover.residual_eq, Multiset.map_add, Multiset.sum_add, Multiset.map_map,
    Function.comp_def, CostStack.cellCount]
  rw [selected]
  omega

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
  have spendValid := step.spend_runtimeValid
  cases step with
  | wholeRecvSend valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have free := CostTerm.PurseFree.wholeRecvSend_payloads separated.1.2
      refine ⟨cover.chosen.card, cover.selected_card_pos spendValid, ?_⟩
      simp only [CostConfig.physicalPurseCells, CostTerm.commSubst, CostConfig.physicalPurseMeasure_add,
        CostConfig.physicalPurseMeasure_cons_zero, CostTerm.physicalPurseMeasure,
        LocatedPurse.configComponents_physicalPurseMeasure,
        (free.1.substitute free.2 0).components_physicalPurseMeasure_zero, add_zero]
      rw [cover.physical_cells_balance]
      omega
  | wholeSendRecv valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have free := CostTerm.PurseFree.wholeSendRecv_payloads separated.1.2
      refine ⟨cover.chosen.card, cover.selected_card_pos spendValid, ?_⟩
      simp only [CostConfig.physicalPurseCells, CostTerm.commSubst, CostConfig.physicalPurseMeasure_add,
        CostConfig.physicalPurseMeasure_cons_zero, CostTerm.physicalPurseMeasure,
        LocatedPurse.configComponents_physicalPurseMeasure,
        (free.1.substitute free.2 0).components_physicalPurseMeasure_zero, add_zero]
      rw [cover.physical_cells_balance]
      omega
  | split recvValid sendValid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have bodyFree := CostTerm.PurseFree.recv_body separated.1.1.2
      have payloadFree := CostTerm.PurseFree.send_payload separated.1.2
      refine ⟨cover.chosen.card, cover.selected_card_pos spendValid, ?_⟩
      simp only [CostConfig.physicalPurseCells, CostTerm.commSubst, CostConfig.physicalPurseMeasure_add,
        CostConfig.physicalPurseMeasure_cons_zero, CostTerm.physicalPurseMeasure,
        LocatedPurse.configComponents_physicalPurseMeasure,
        (bodyFree.substitute payloadFree 0).components_physicalPurseMeasure_zero, add_zero]
      rw [cover.physical_cells_balance]
      omega

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
  simp only [cover.available_eq, cover.residual_eq, Multiset.card_add, Multiset.card_map]

/-- The preserved separated domain rules out creation of executable purse
occurrences, including through duplicating or discarding communicated code. -/
theorem CostStep.physical_purse_occurrences_preserved {Ground : Type u}
    {source target : CostConfig Ground} {location : CostName Ground} {spend : CostSig Ground}
    (step : CostStep source location spend target) (separated : source.ResourceSeparated) :
    source.physicalPurseOccurrences = target.physicalPurseOccurrences := by
  cases step with
  | wholeRecvSend valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have free := CostTerm.PurseFree.wholeRecvSend_payloads separated.1.2
      simp only [CostConfig.physicalPurseOccurrences, CostTerm.commSubst,
        CostConfig.physicalPurseMeasure_add, CostConfig.physicalPurseMeasure_cons_zero,
        CostTerm.physicalPurseMeasure, LocatedPurse.configComponents_physicalPurseMeasure,
        (free.1.substitute free.2 0).components_physicalPurseMeasure_zero, add_zero]
      simpa using cover.physical_purse_count_balance
  | wholeSendRecv valid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have free := CostTerm.PurseFree.wholeSendRecv_payloads separated.1.2
      simp only [CostConfig.physicalPurseOccurrences, CostTerm.commSubst,
        CostConfig.physicalPurseMeasure_add, CostConfig.physicalPurseMeasure_cons_zero,
        CostTerm.physicalPurseMeasure, LocatedPurse.configComponents_physicalPurseMeasure,
        (free.1.substitute free.2 0).components_physicalPurseMeasure_zero, add_zero]
      simpa using cover.physical_purse_count_balance
  | split recvValid sendValid cover =>
      simp only [CostConfig.resourceSeparated_add_iff,
        CostConfig.resourceSeparated_singleton_iff] at separated
      have bodyFree := CostTerm.PurseFree.recv_body separated.1.1.2
      have payloadFree := CostTerm.PurseFree.send_payload separated.1.2
      simp only [CostConfig.physicalPurseOccurrences, CostTerm.commSubst,
        CostConfig.physicalPurseMeasure_add, CostConfig.physicalPurseMeasure_cons_zero,
        CostTerm.physicalPurseMeasure, LocatedPurse.configComponents_physicalPurseMeasure,
        (bodyFree.substitute payloadFree 0).components_physicalPurseMeasure_zero, add_zero]
      simpa using cover.physical_purse_count_balance

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
