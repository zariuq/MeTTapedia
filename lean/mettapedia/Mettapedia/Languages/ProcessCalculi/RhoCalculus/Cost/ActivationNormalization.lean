import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationSeparation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Normalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawConfig

/-!
# Resource invariants through actual raw normalization

The executable normalizer reorders signature atoms, flattens parallel syntax
and simplifies quotation of a Drop.  The decoded literal purse inventory is
preserved through those operations.  In particular code-only admission is
stable without assuming that an arbitrary structural observer reflects
authority.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u

/-- Signature sorting changes no exact decoded stack cell. -/
theorem RawCostStack.decode_map_normalize : ∀ stack : RawCostStack,
    decodeCostStack (stack.map RawCostSig.normalize) = decodeCostStack stack
  | [] => rfl
  | signature :: stack => by
      simp only [List.map_cons, decodeCostStack]
      rw [show decodeCostSig signature.normalize = decodeCostSig signature from
        RawCostSig.normalize_toMultiset signature, RawCostStack.decode_map_normalize stack]

theorem RawCostProc.decoded_inventory_components : ∀ process : RawCostProc,
    (process.components.map fun component => (decodeCostProc component).purseInventory).sum =
      (decodeCostProc process).purseInventory
  | .nil => by simp [RawCostProc.components, decodeCostProc, CostProc.purseInventory]
  | .par left right => by
      simp [RawCostProc.components, decodeCostProc, CostProc.purseInventory,
        RawCostProc.decoded_inventory_components left,
        RawCostProc.decoded_inventory_components right]
  | .send channel payload => by simp [RawCostProc.components]
  | .recv channel body => by simp [RawCostProc.components]

theorem RawCostTerm.decoded_inventory_components : ∀ term : RawCostTerm,
    (term.components.map fun component => (decodeCostTerm component).purseInventory).sum =
      (decodeCostTerm term).purseInventory
  | .nil => by simp [RawCostTerm.components, decodeCostTerm, CostTerm.purseInventory]
  | .par left right => by
      simp [RawCostTerm.components, decodeCostTerm, CostTerm.purseInventory,
        RawCostTerm.decoded_inventory_components left,
        RawCostTerm.decoded_inventory_components right]
  | .signed process signature => by simp [RawCostTerm.components]
  | .drop name => by simp [RawCostTerm.components]
  | .purse location stack => by simp [RawCostTerm.components]

theorem RawCostProc.decoded_inventory_fromComponents : ∀ items : List RawCostProc,
    (decodeCostProc (RawCostProc.fromComponents items)).purseInventory =
      (items.map fun process => (decodeCostProc process).purseInventory).sum
  | [] => by simp [decodeCostProc, CostProc.purseInventory]
  | [process] => by simp
  | process :: next :: rest => by
      simp only [decodeCostProc, CostProc.purseInventory,
        List.map_cons, List.sum_cons]
      rw [RawCostProc.decoded_inventory_fromComponents (next :: rest)]
      rfl

theorem RawCostTerm.decoded_inventory_fromComponents : ∀ items : List RawCostTerm,
    (decodeCostTerm (RawCostTerm.fromComponents items)).purseInventory =
      (items.map fun term => (decodeCostTerm term).purseInventory).sum
  | [] => by simp [decodeCostTerm, CostTerm.purseInventory]
  | [term] => by simp
  | term :: next :: rest => by
      simp only [decodeCostTerm, CostTerm.purseInventory,
        List.map_cons, List.sum_cons]
      rw [RawCostTerm.decoded_inventory_fromComponents (next :: rest)]
      rfl

mutual
  /-- Quotation-of-Drop normalization preserves even latent purse stacks. -/
  theorem RawCostName.decoded_inventory_normalize : ∀ name : RawCostName,
      (decodeCostName name.normalize).purseInventory = (decodeCostName name).purseInventory
    | .bvar index => rfl
    | .signature signature => rfl
    | .quote term => by
        have same := RawCostTerm.decoded_inventory_normalize term
        simp only [RawCostName.normalize]
        generalize normalized : term.normalize = normalizedTerm at same ⊢
        cases normalizedTerm <;> exact same

  theorem RawCostProc.decoded_inventory_normalize : ∀ process : RawCostProc,
      (decodeCostProc process.normalize).purseInventory = (decodeCostProc process).purseInventory
    | .nil => rfl
    | .par left right => by
        simp only [RawCostProc.normalize]
        rw [RawCostProc.decoded_inventory_fromComponents, List.sum_map_stableKeySort]
        simp only [List.map_append, List.sum_append,
          RawCostProc.decoded_inventory_components,
          RawCostProc.decoded_inventory_normalize left,
          RawCostProc.decoded_inventory_normalize right]
        rfl
    | .send channel payload => by
        simp only [decodeCostProc, CostProc.purseInventory,
          RawCostName.decoded_inventory_normalize channel,
          RawCostTerm.decoded_inventory_normalize payload]
    | .recv channel body => by
        simp only [decodeCostProc, CostProc.purseInventory,
          RawCostName.decoded_inventory_normalize channel,
          RawCostTerm.decoded_inventory_normalize body]

  theorem RawCostTerm.decoded_inventory_normalize : ∀ term : RawCostTerm,
      (decodeCostTerm term.normalize).purseInventory = (decodeCostTerm term).purseInventory
    | .nil => rfl
    | .signed process signature => RawCostProc.decoded_inventory_normalize process
    | .par left right => by
        simp only [RawCostTerm.normalize]
        rw [RawCostTerm.decoded_inventory_fromComponents, List.sum_map_stableKeySort]
        simp only [List.map_append, List.sum_append,
          RawCostTerm.decoded_inventory_components,
          RawCostTerm.decoded_inventory_normalize left,
          RawCostTerm.decoded_inventory_normalize right]
        rfl
    | .drop name => RawCostName.decoded_inventory_normalize name
    | .purse location stack => by
        simp only [decodeCostTerm, CostTerm.purseInventory,
          RawCostStack.decode_map_normalize, RawCostName.decoded_inventory_normalize location]
end

/-- The actual executable normalizer preserves the code-only admission. -/
theorem RawCostTerm.purseFree_normalize_iff (term : RawCostTerm) :
    (decodeCostTerm term.normalize).PurseFree ↔ (decodeCostTerm term).PurseFree := by
  simp only [CostTerm.PurseFree, term.decoded_inventory_normalize]

/-- Sorting a list of occurrences changes no decoded multiset. -/
theorem decodeRawConfig_stableKeySort (key : RawCostTerm → String)
    (items : List RawCostTerm) :
    decodeRawConfig (stableKeySort key items) = decodeRawConfig items := by
  unfold decodeRawConfig
  change (stableKeySort key items : Multiset RawCostTerm).map decodeCostTerm =
    (items : Multiset RawCostTerm).map decodeCostTerm
  rw [stableKeySort_toMultiset]

theorem sum_map_stableKeySort_measure {Alpha : Type} {Measure : Type u}
    [AddCommMonoid Measure] (key : Alpha → String) (measure : Alpha → Measure)
    (items : List Alpha) :
    ((stableKeySort key items).map measure).sum = (items.map measure).sum := by
  change ((stableKeySort key items : Multiset Alpha).map measure).sum =
    ((items : Multiset Alpha).map measure).sum
  rw [stableKeySort_toMultiset]

/-- Folding a raw parallel list preserves the sum of the physical purse
readouts of each flattened constituent, without an admission assumption. -/
theorem RawCostTerm.decoded_physicalPurseMeasure_fromComponents
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure) :
    ∀ items : List RawCostTerm,
      (decodeCostTerm (RawCostTerm.fromComponents items)).components.physicalPurseMeasure weight =
        (items.map fun term => (decodeCostTerm term).components.physicalPurseMeasure weight).sum
  | [] => by simp [decodeCostTerm, CostTerm.components,
      CostConfig.physicalPurseMeasure]
  | [term] => by simp
  | term :: next :: rest => by
      simp only [decodeCostTerm, CostTerm.components, CostConfig.physicalPurseMeasure_add,
        List.map_cons, List.sum_cons]
      rw [RawCostTerm.decoded_physicalPurseMeasure_fromComponents weight (next :: rest)]
      rfl

theorem RawCostTerm.decoded_physicalPurseMeasure_components
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure) :
    ∀ term : RawCostTerm,
      (term.components.map fun component =>
        (decodeCostTerm component).components.physicalPurseMeasure weight).sum =
          (decodeCostTerm term).components.physicalPurseMeasure weight
  | .nil => by simp [RawCostTerm.components, decodeCostTerm, CostTerm.components,
      CostConfig.physicalPurseMeasure]
  | .par left right => by
      simp [RawCostTerm.components, decodeCostTerm, CostTerm.components,
        CostConfig.physicalPurseMeasure_add,
        RawCostTerm.decoded_physicalPurseMeasure_components weight left,
        RawCostTerm.decoded_physicalPurseMeasure_components weight right]
  | .signed process signature => by simp [RawCostTerm.components]
  | .drop name => by simp [RawCostTerm.components]
  | .purse location stack => by simp [RawCostTerm.components]

/-- Actual raw normalization preserves every additive readout of top-level
purse stacks.  It cannot change cell counts or decoded signing atoms. -/
theorem RawCostTerm.decoded_physicalPurseMeasure_normalize
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure) :
    ∀ term : RawCostTerm,
      (decodeCostTerm term.normalize).components.physicalPurseMeasure weight =
        (decodeCostTerm term).components.physicalPurseMeasure weight
  | .nil => rfl
  | .signed process signature => rfl
  | .drop name => rfl
  | .purse location stack => by
      simp only [decodeCostTerm, CostTerm.components,
        CostConfig.physicalPurseMeasure_cons_zero, CostTerm.physicalPurseMeasure,
        RawCostStack.decode_map_normalize]
  | .par left right => by
      simp only [RawCostTerm.normalize]
      rw [RawCostTerm.decoded_physicalPurseMeasure_fromComponents,
        sum_map_stableKeySort_measure]
      simp only [List.map_append, List.sum_append,
        RawCostTerm.decoded_physicalPurseMeasure_components,
        RawCostTerm.decoded_physicalPurseMeasure_normalize weight left,
        RawCostTerm.decoded_physicalPurseMeasure_normalize weight right]
      simp only [decodeCostTerm, CostTerm.components, CostConfig.physicalPurseMeasure_add]

/-- The runtime's normalized configuration has the same physical purse
readout as the decoded original flattened configuration. -/
theorem RawCostTerm.normalizeConfig_physicalPurseMeasure
    {Measure : Type u} [AddCommMonoid Measure] (weight : CostStack String → Measure)
    (term : RawCostTerm) :
    (decodeRawConfig term.normalizeConfig).physicalPurseMeasure weight =
      (decodeCostTerm term).components.physicalPurseMeasure weight := by
  unfold RawCostTerm.normalizeConfig
  rw [decodeRawConfig_stableKeySort, decodeRawConfig_components,
    term.decoded_physicalPurseMeasure_normalize weight]

/-- A separate code or purse component remains separate when flattened. -/
theorem CostTerm.ResourceSeparated.components_resourceSeparated
    {term : CostTerm String} (separated : term.ResourceSeparated) :
    term.components.ResourceSeparated := by
  cases term with
  | nil => exact CostTerm.PurseFree.components_resourceSeparated separated
  | signed process signature => exact CostTerm.PurseFree.components_resourceSeparated separated
  | par left right => exact CostTerm.PurseFree.components_resourceSeparated separated
  | drop name => exact CostTerm.PurseFree.components_resourceSeparated separated
  | purse location stack =>
      exact (CostConfig.resourceSeparated_singleton_iff _).mpr separated

/-- Unordered decoding preserves each occurrence's separation judgment. -/
theorem decodeRawConfig_resourceSeparated_iff (items : RawCostConfig) :
    (decodeRawConfig items).ResourceSeparated ↔
      items.Forall (fun raw => (decodeCostTerm raw).ResourceSeparated) := by
  constructor
  · intro separated
    rw [List.forall_iff_forall_mem]
    intro raw rawMember
    apply separated (decodeCostTerm raw)
    have mapped : decodeCostTerm raw ∈ items.map decodeCostTerm :=
      List.mem_map.mpr ⟨raw, rawMember, rfl⟩
    exact mapped
  · intro separated term termMember
    have mapped : term ∈ items.map decodeCostTerm := termMember
    obtain ⟨raw, rawMember, equality⟩ := List.mem_map.mp mapped
    exact equality ▸ List.forall_iff_forall_mem.mp separated raw rawMember

theorem RawCostTerm.decoded_components_resourceSeparated_fromComponents :
    ∀ (items : List RawCostTerm),
      items.Forall (fun raw => (decodeCostTerm raw).ResourceSeparated) →
        (decodeCostTerm (RawCostTerm.fromComponents items)).components.ResourceSeparated
  | [], _ => by simp [decodeCostTerm, CostTerm.components,
      CostConfig.ResourceSeparated]
  | [term], separated =>
      (List.forall_iff_forall_mem.mp separated term (by simp)).components_resourceSeparated
  | term :: next :: rest, separated => by
      have both := (List.forall_cons
        (fun raw => (decodeCostTerm raw).ResourceSeparated) term (next :: rest)).mp separated
      change CostConfig.ResourceSeparated
        ((decodeCostTerm term).components +
          (decodeCostTerm (RawCostTerm.fromComponents (next :: rest))).components)
      apply (CostConfig.resourceSeparated_add_iff _ _).mpr
      exact ⟨both.1.components_resourceSeparated,
        RawCostTerm.decoded_components_resourceSeparated_fromComponents (next :: rest) both.2⟩

/-- Every actual structural-normalization seam preserves the separate
code/resource domain on flattened decoded configurations. -/
theorem RawCostTerm.decoded_components_resourceSeparated_normalize :
    ∀ (term : RawCostTerm), (decodeCostTerm term).components.ResourceSeparated →
      (decodeCostTerm term.normalize).components.ResourceSeparated
  | .nil, separated => separated
  | .signed process signature, separated => by
      have free : (decodeCostTerm (.signed process signature)).PurseFree :=
        (CostConfig.resourceSeparated_singleton_iff _).mp separated
      exact ((RawCostTerm.purseFree_normalize_iff _).mpr free).components_resourceSeparated
  | .drop name, separated => by
      have free : (decodeCostTerm (.drop name)).PurseFree :=
        (CostConfig.resourceSeparated_singleton_iff _).mp separated
      exact ((RawCostTerm.purseFree_normalize_iff _).mpr free).components_resourceSeparated
  | .purse location stack, separated => by
      have locationFree : (decodeCostName location).purseInventory = 0 :=
        (CostConfig.resourceSeparated_singleton_iff _).mp separated
      apply (CostConfig.resourceSeparated_singleton_iff _).mpr
      change (decodeCostName location.normalize).purseInventory = 0
      rw [location.decoded_inventory_normalize]
      exact locationFree
  | .par left right, separated => by
      have parts := (CostConfig.resourceSeparated_add_iff _ _).mp separated
      have leftSafe := RawCostTerm.decoded_components_resourceSeparated_normalize left parts.1
      have rightSafe := RawCostTerm.decoded_components_resourceSeparated_normalize right parts.2
      simp only [RawCostTerm.normalize]
      apply RawCostTerm.decoded_components_resourceSeparated_fromComponents
      apply stableKeySort_forall
      apply List.forall_append.mpr
      exact ⟨(decodeRawConfig_resourceSeparated_iff _).mp
        ((decodeRawConfig_components _).symm ▸ leftSafe),
        (decodeRawConfig_resourceSeparated_iff _).mp
          ((decodeRawConfig_components _).symm ▸ rightSafe)⟩

/-- Sorting, normalization and flattening cannot move admitted code into the
authority-bearing payload profile. -/
theorem RawCostTerm.normalizeConfig_resourceSeparated (term : RawCostTerm)
    (separated : (decodeCostTerm term).components.ResourceSeparated) :
    (decodeRawConfig term.normalizeConfig).ResourceSeparated := by
  unfold RawCostTerm.normalizeConfig
  rw [decodeRawConfig_stableKeySort, decodeRawConfig_components]
  exact term.decoded_components_resourceSeparated_normalize separated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
