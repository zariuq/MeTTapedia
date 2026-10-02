import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.ActivationAmbientCanonicalEntry

/-!
# Physical balance for admitted canonical configuration candidates

The existing parser image supplies resource separation and full runtime scope.
Actual occurrence candidates then consume exactly their selected purse cells
and exact literal signing atoms. A singleton demand consumes one physical cell,
even in an arbitrary admitted ambient frame.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u v

theorem CostTerm.ResourceSeparated.relabel {Ground : Type u} {Target : Type v}
    (label : Ground → Target) {term : CostTerm Ground} (separated : term.ResourceSeparated) :
    (term.relabel label).ResourceSeparated := by
  cases term with
  | purse location stack =>
    change (location.relabel label).purseInventory = 0
    rw [CostName.relabel_purseInventory, separated]
    rfl
  | nil => exact CostTerm.PurseFree.relabel label separated
  | signed process signature => exact CostTerm.PurseFree.relabel label separated
  | par left right => exact CostTerm.PurseFree.relabel label separated
  | drop name => exact CostTerm.PurseFree.relabel label separated

theorem CostTerm.components_relabel {Ground : Type u} {Target : Type v}
    (label : Ground → Target) : ∀ term : CostTerm Ground,
    (term.relabel label).components = term.components.map (CostTerm.relabel label)
  | .nil => rfl
  | .signed _ _ => rfl
  | .par left right => by
      simp only [CostTerm.relabel, CostTerm.components, Multiset.map_add,
        CostTerm.components_relabel label left, CostTerm.components_relabel label right]
  | .drop _ => rfl
  | .purse _ _ => rfl

theorem CostConfig.ResourceSeparated.relabel {Ground : Type u} {Target : Type v}
    (label : Ground → Target) {config : CostConfig Ground} (separated : config.ResourceSeparated) :
    CostConfig.ResourceSeparated (config.map (CostTerm.relabel label)) := by
  intro term member
  obtain ⟨source, sourceMember, rfl⟩ := Multiset.mem_map.mp member
  exact (separated source sourceMember).relabel label

/-- Positive exact covers spend at least one signing atom per selected physical cell. -/
theorem rawSelectedSpend_length_le_card {selected : List RawSelectedPurse}
    (valid : selected.Forall fun purse => purse.head.valid = true) :
    selected.length ≤ (rawSelectedSpend selected).card := by
  induction selected with
  | nil => simp [rawSelectedSpend]
  | cons purse rest ih =>
      obtain ⟨headValid, restValid⟩ :=
        (List.forall_cons (fun purse : RawSelectedPurse => purse.head.valid = true) purse rest).mp valid
      have nonempty : purse.head ≠ [] := by simpa [RawCostSig.valid] using headValid
      have positive := List.length_pos_iff.mpr nonempty
      have tailBound := ih restValid
      change rest.length + 1 ≤ (purse.head.toMultiset + rawSelectedSpend rest).card
      simp only [Multiset.card_add, RawCostSig.toMultiset, Multiset.coe_card]
      omega

theorem runtime_candidate_cells_le_spend {config : RawCostConfig} {step : RawRuntimeStep}
    (configValid : config.Forall fun term => term.wellFormed = true)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    step.selectedPurses.length ≤ (decodeCostSig step.spend).card := by
  have valid : step.selectedPurses.Forall fun purse => purse.head.valid = true := by
    rw [List.forall_iff_forall_mem]
    intro purse member
    exact (step.selectedPurse_wellFormed configValid enabled member).head
  have bound := rawSelectedSpend_length_le_card valid
  rw [(runtimeCostCandidatesFromConfig_funding_valid enabled).exact_spend] at bound
  exact bound

theorem runtime_candidate_singleton_selects_one {config : RawCostConfig} {step : RawRuntimeStep}
    (configValid : config.Forall fun term => term.wellFormed = true)
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) {authority : String}
    (spent : decodeCostSig step.spend = {authority}) : step.selectedPurses.length = 1 := by
  have upper := runtime_candidate_cells_le_spend configValid enabled
  rw [spent, Multiset.card_singleton] at upper
  have nonempty : step.selectedPurses ≠ [] := by
    intro empty
    have exactSpend := (runtimeCostCandidatesFromConfig_funding_valid enabled).exact_spend
    rw [empty] at exactSpend
    change 0 = decodeCostSig step.spend at exactSpend
    rw [spent] at exactSpend
    exact Multiset.singleton_ne_zero authority exactSpend.symm
  have positive := List.length_pos_iff.mpr nonempty
  omega

namespace ActivationGenerated

theorem ConfigImage.components_resourceSeparated {channelSource source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term) :
    term.components.ResourceSeparated := by
  obtain ⟨fuel, readback⟩ := image.parser_eventually channelImage.purseInventory_zero channelImage.runtimeSupported
  obtain ⟨decoded, _, same⟩ := Option.map_eq_some_iff.mp (readback fuel (le_refl fuel))
  exact same ▸ decoded.property.1

theorem ConfigImage.literal_components_resourceSeparated
    {channelSource source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term) :
    (decodeCostTerm (literalEncodeTerm term)).components.ResourceSeparated := by
  rw [literalEncodeTerm, decodeCostTerm_encodeCostTerm, CostTerm.components_relabel]
  exact (image.components_resourceSeparated channelImage).relabel literalAuthorityKey

theorem ConfigImage.canonical_components_resourceSeparated
    {channelSource source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term) :
    (decodeRawConfig (literalEncodeTerm term).normalizeConfig).ResourceSeparated :=
  (literalEncodeTerm term).normalizeConfig_resourceSeparated
    (image.literal_components_resourceSeparated channelImage)

/-- Physical balances consume the existing parser admission and actual occurrence catalogue. -/
theorem ConfigImage.canonical_candidate_inventory
    {channelSource source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig) :
    (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0).map
      RawTraceComponent.term)).ResourceSeparated ∧
    (decodeRawConfig (literalEncodeTerm term).normalizeConfig).physicalPurseCells =
      (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0).map
        RawTraceComponent.term)).physicalPurseCells + step.selectedPurses.length ∧
    (decodeRawConfig (literalEncodeTerm term).normalizeConfig).storedSignatures =
      (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0).map
        RawTraceComponent.term)).storedSignatures + decodeCostSig step.spend ∧
    (decodeRawConfig (literalEncodeTerm term).normalizeConfig).physicalPurseOccurrences =
      (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0).map
        RawTraceComponent.term)).physicalPurseOccurrences := by
  have canonical := initialTraceComponents_canonical (literalEncodeTerm term)
  have separated : (decodeRawConfig ((initialTraceComponents (literalEncodeTerm term)).map
      RawTraceComponent.term)).ResourceSeparated := by
    rw [initialTraceComponents_terms]
    exact image.canonical_components_resourceSeparated channelImage
  have tracedEnabled : step ∈ runtimeCostCandidatesFromConfig
      ((initialTraceComponents (literalEncodeTerm term)).map RawTraceComponent.term) := by
    rw [initialTraceComponents_terms]
    exact enabled
  have result := And.intro (applyTracedStep_resourceSeparated canonical separated tracedEnabled 0)
    (And.intro (applyTracedStep_physical_cells_balance canonical separated tracedEnabled 0)
      (And.intro (applyTracedStep_stored_signatures_balance canonical separated tracedEnabled 0)
        (applyTracedStep_physical_purse_occurrences canonical separated tracedEnabled 0)))
  simpa only [initialTraceComponents_terms] using result

/-- One exact signature atom removes one physical cell in every admitted ambient configuration. -/
theorem ConfigImage.canonical_singleton_inventory
    {channelSource source : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {location : CostName LiteralAuthority} {term : CostTerm LiteralAuthority}
    (channelImage : NameImage 0 channelSource location) (image : ConfigImage location source term)
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig (literalEncodeTerm term).normalizeConfig)
    {authority : String} (spent : decodeCostSig step.spend = {authority}) :
    step.selectedPurses.length = 1 ∧
    (decodeRawConfig (literalEncodeTerm term).normalizeConfig).physicalPurseCells =
      (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0).map
        RawTraceComponent.term)).physicalPurseCells + 1 ∧
    (decodeRawConfig (literalEncodeTerm term).normalizeConfig).storedSignatures =
      (decodeRawConfig ((applyTracedStep (initialTraceComponents (literalEncodeTerm term)) step 0).map
        RawTraceComponent.term)).storedSignatures + {authority} := by
  have valid := RawCostTerm.normalizeConfig_forall_wellFormed
    (image.literal_wellFormed channelImage.literal_wellFormed)
  have count := runtime_candidate_singleton_selects_one valid enabled spent
  obtain ⟨_, cells, signatures, _⟩ := image.canonical_candidate_inventory channelImage enabled
  exact ⟨count, by simpa only [count] using cells, by simpa only [spent] using signatures⟩

/-- The constructed ambient firing has one exact cell debit and retains all other physical resources. -/
theorem NameImage.ambient_canonical_entry_resource_balance
    {channelSource bodySource payloadSource signatureSource tailSource ambientSource :
      Mettapedia.OSLF.MeTTaIL.Syntax.Pattern}
    {location : CostName LiteralAuthority} {body payload ambient : CostTerm LiteralAuthority}
    {tail : CostStack LiteralAuthority}
    (channelImage : NameImage 0 channelSource location)
    (bodyImage : CodeImage 1 bodySource body) (payloadImage : CodeImage 0 payloadSource payload)
    (signature : TypedSignature signatureSource) (accepted : signature? signatureSource = some signature)
    (tailImage : StackImage tailSource tail) (ambientImage : ConfigImage location ambientSource ambient) :
    let source := literalEncodeTerm (decodedAmbientReceiver location body payload signature.val tail ambient)
    ∃ step,
      step ∈ runtimeCostCandidatesFromConfig source.normalizeConfig ∧
      decodeCostSig step.spend = {literalAuthorityKey signatureSource} ∧
      (∃ path : CostPath 0 (initialTraceComponents source) 1
          (applyTracedStep (initialTraceComponents source) step 0), path.depth = 1) ∧
      (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
        RawTraceComponent.term)).ResourceSeparated ∧
      (decodeRawConfig source.normalizeConfig).physicalPurseCells =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).physicalPurseCells + 1 ∧
      (decodeRawConfig source.normalizeConfig).storedSignatures =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).storedSignatures + {literalAuthorityKey signatureSource} ∧
      (decodeRawConfig source.normalizeConfig).physicalPurseOccurrences =
        (decodeRawConfig ((applyTracedStep (initialTraceComponents source) step 0).map
          RawTraceComponent.term)).physicalPurseOccurrences := by
  obtain ⟨_, step, _, _, _, _, _, enabled, _, spent, _, path, _⟩ :=
    channelImage.ambient_canonical_entry_path_rhs bodyImage payloadImage signature accepted tailImage ambientImage
  have image := ambient_receiver_config_image channelImage bodyImage payloadImage signature accepted tailImage ambientImage
  obtain ⟨separated, _, _, occurrences⟩ := image.canonical_candidate_inventory channelImage enabled
  obtain ⟨_, cells, atoms⟩ := image.canonical_singleton_inventory channelImage enabled spent
  exact ⟨step, enabled, spent, path, separated, cells, atoms, occurrences⟩

end ActivationGenerated

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
