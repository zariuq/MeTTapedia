import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Valuation

/-!
# Naturality of located causal receipts

Maps of signing grounds and opaque funding locations act only on receipt
labels.  They do not reconstruct event occurrences, consumption arcs, or
emission order from label equality.  The resulting action preserves identity
and composition, commutes with the ordered-emission presentation, and is
compatible with the universal additive and multiplicative valuations.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

universe u u' u'' v v' v'' w x

namespace FundingContribution

/-- Componentwise transport of one located funding contribution. -/
def map {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (contribution : FundingContribution Ground Location) :
    FundingContribution Ground' Location' where
  location := locationMap contribution.location
  spend := contribution.spend.map groundMap
  spend_valid := by
    simpa [CostSig.RuntimeValid] using contribution.spend_valid

@[simp]
theorem map_location {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (contribution : FundingContribution Ground Location) :
    (contribution.map groundMap locationMap).location =
      locationMap contribution.location := by
  rfl

@[simp]
theorem map_spend {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (contribution : FundingContribution Ground Location) :
    (contribution.map groundMap locationMap).spend =
      contribution.spend.map groundMap := by
  rfl

@[simp]
theorem map_id {Ground : Type u} {Location : Type v}
    (contribution : FundingContribution Ground Location) :
    contribution.map id id = contribution := by
  cases contribution
  simp [map]

@[simp]
theorem map_comp {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Location : Type v} {Location' : Type v'} {Location'' : Type v''}
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (locationFirst : Location → Location') (locationSecond : Location' → Location'')
    (contribution : FundingContribution Ground Location) :
    (contribution.map groundFirst locationFirst).map groundSecond locationSecond =
      contribution.map (groundSecond ∘ groundFirst) (locationSecond ∘ locationFirst) := by
  cases contribution
  simp [map, Multiset.map_map]

end FundingContribution

namespace SpendEvent

private theorem sum_mapped_spends
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (funding : Multiset (FundingContribution Ground Location)) :
    (funding.map (FundingContribution.map groundMap locationMap) |>.map
        FundingContribution.spend).sum =
      (funding.map FundingContribution.spend).sum.map groundMap := by
  induction funding using Multiset.induction_on with
  | empty => simp
  | @cons contribution rest ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        FundingContribution.map_spend, Multiset.map_add, ih]

@[ext]
theorem ext {Ground : Type u} {Location : Type v}
    {left right : SpendEvent Ground Location}
    (funding : left.funding = right.funding) : left = right := by
  cases left
  cases right
  simp_all

/-- Transport every contribution label while retaining every occurrence. -/
def map {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (event : SpendEvent Ground Location) : SpendEvent Ground' Location' where
  funding := event.funding.map (FundingContribution.map groundMap locationMap)
  funding_nonempty := by
    simpa using event.funding_nonempty

@[simp]
theorem map_funding {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (event : SpendEvent Ground Location) :
    (event.map groundMap locationMap).funding =
      event.funding.map (FundingContribution.map groundMap locationMap) := by
  rfl

@[simp]
theorem map_id {Ground : Type u} {Location : Type v}
    (event : SpendEvent Ground Location) : event.map id id = event := by
  apply SpendEvent.ext
  simp [map]

@[simp]
theorem map_comp {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Location : Type v} {Location' : Type v'} {Location'' : Type v''}
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (locationFirst : Location → Location') (locationSecond : Location' → Location'')
    (event : SpendEvent Ground Location) :
    (event.map groundFirst locationFirst).map groundSecond locationSecond =
      event.map (groundSecond ∘ groundFirst) (locationSecond ∘ locationFirst) := by
  apply SpendEvent.ext
  simp [map, Multiset.map_map, Function.comp_def]

@[simp]
theorem rawSpend_map {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (event : SpendEvent Ground Location) :
    (event.map groundMap locationMap).rawSpend = event.rawSpend.map groundMap := by
  exact sum_mapped_spends groundMap locationMap event.funding

end SpendEvent

namespace CausalReceipt

variable {Event : Type w} [Fintype Event]

omit [Fintype Event] in
private theorem map_finset_sum
    {Ground : Type u} {Ground' : Type u'} [DecidableEq Event]
    (groundMap : Ground → Ground') (region : Finset Event)
    (value : Event → CostSig Ground) :
    (∑ event ∈ region, value event).map groundMap =
      ∑ event ∈ region, (value event).map groundMap := by
  induction region using Finset.induction with
  | empty => simp
  | @insert event region fresh ih =>
      simp [fresh, ih, Multiset.map_add]

@[ext]
theorem ext {Ground : Type u} {Location : Type v}
    {left right : CausalReceipt Event Ground Location}
    (label : left.label = right.label)
    (arcs : left.arcMultiplicity = right.arcMultiplicity)
    (rank : left.rank = right.rank) : left = right := by
  cases left
  cases right
  simp_all

/-- Relabel grounds and locations without changing event identity or causality. -/
def mapLabels {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    CausalReceipt Event Ground' Location' where
  label event := (receipt.label event).map groundMap locationMap
  arcMultiplicity := receipt.arcMultiplicity
  rank := receipt.rank
  arc_rank_lt := receipt.arc_rank_lt

@[simp]
theorem mapLabels_label {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (event : Event) :
    (receipt.mapLabels groundMap locationMap).label event =
      (receipt.label event).map groundMap locationMap := by
  rfl

@[simp]
theorem mapLabels_arcMultiplicity {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (cause effect : Event) :
    (receipt.mapLabels groundMap locationMap).arcMultiplicity cause effect =
      receipt.arcMultiplicity cause effect := by
  rfl

@[simp]
theorem mapLabels_rank {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (event : Event) :
    (receipt.mapLabels groundMap locationMap).rank event = receipt.rank event := by
  rfl

@[simp]
theorem mapLabels_id {Ground : Type u} {Location : Type v}
    (receipt : CausalReceipt Event Ground Location) :
    receipt.mapLabels id id = receipt := by
  apply CausalReceipt.ext
  · funext event
    simp
  · rfl
  · rfl

@[simp]
theorem mapLabels_comp
    {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Location : Type v} {Location' : Type v'} {Location'' : Type v''}
    (receipt : CausalReceipt Event Ground Location)
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (locationFirst : Location → Location') (locationSecond : Location' → Location'') :
    (receipt.mapLabels groundFirst locationFirst).mapLabels groundSecond locationSecond =
      receipt.mapLabels (groundSecond ∘ groundFirst) (locationSecond ∘ locationFirst) := by
  apply CausalReceipt.ext
  · funext event
    simp
  · rfl
  · rfl

theorem causalLE_mapLabels_iff
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (earlier later : Event) :
    (receipt.mapLabels groundMap locationMap).CausalLE earlier later ↔
      receipt.CausalLE earlier later := by
  rfl

theorem rawMeasure_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (region : Finset Event) :
    (receipt.mapLabels groundMap locationMap).rawMeasure region =
      (receipt.rawMeasure region).map groundMap := by
  unfold rawMeasure
  rw [map_finset_sum]
  apply Finset.sum_congr rfl
  intro event _member
  exact SpendEvent.rawSpend_map groundMap locationMap (receipt.label event)

theorem totalRawMeasure_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    (receipt.mapLabels groundMap locationMap).totalRawMeasure =
      receipt.totalRawMeasure.map groundMap := by
  exact receipt.rawMeasure_mapLabels groundMap locationMap Finset.univ

end CausalReceipt

namespace EmittedEvent

/-- Label transport for one ordered emission record. -/
def mapLabels {EventId : Type w}
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (event : EmittedEvent EventId Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    EmittedEvent EventId Ground' Location' where
  id := event.id
  causes := event.causes
  label := event.label.map groundMap locationMap

@[simp]
theorem mapLabels_id {EventId : Type w} {Ground : Type u} {Location : Type v}
    (event : EmittedEvent EventId Ground Location) :
    event.mapLabels _root_.id _root_.id = event := by
  cases event
  simp [mapLabels]

@[simp]
theorem mapLabels_comp {EventId : Type w}
    {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Location : Type v} {Location' : Type v'} {Location'' : Type v''}
    (event : EmittedEvent EventId Ground Location)
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (locationFirst : Location → Location') (locationSecond : Location' → Location'') :
    (event.mapLabels groundFirst locationFirst).mapLabels groundSecond locationSecond =
      event.mapLabels (groundSecond ∘ groundFirst) (locationSecond ∘ locationFirst) := by
  cases event
  simp [mapLabels]

end EmittedEvent

namespace ReceiptEmission

variable {EventId : Type w}

/-- Componentwise label transport of an ordered runtime emission. -/
def mapLabels {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (emission : ReceiptEmission EventId Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    ReceiptEmission EventId Ground' Location' :=
  emission.map fun event => event.mapLabels groundMap locationMap

@[simp]
theorem mapLabels_id {Ground : Type u} {Location : Type v}
    (emission : ReceiptEmission EventId Ground Location) :
    emission.mapLabels _root_.id _root_.id = emission := by
  simp [mapLabels]

@[simp]
theorem mapLabels_comp
    {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Location : Type v} {Location' : Type v'} {Location'' : Type v''}
    (emission : ReceiptEmission EventId Ground Location)
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (locationFirst : Location → Location') (locationSecond : Location' → Location'') :
    (emission.mapLabels groundFirst locationFirst).mapLabels groundSecond locationSecond =
      emission.mapLabels (groundSecond ∘ groundFirst) (locationSecond ∘ locationFirst) := by
  simp [mapLabels, List.map_map, Function.comp_def]

@[simp]
theorem length_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (emission : ReceiptEmission EventId Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    (emission.mapLabels groundMap locationMap).length = emission.length := by
  simp [mapLabels]

/-- The canonical occurrence-position equivalence induced by label transport. -/
def indexEquiv
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (emission : ReceiptEmission EventId Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    Fin emission.length ≃ Fin (emission.mapLabels groundMap locationMap).length where
  toFun := Fin.cast (by simp)
  invFun := Fin.cast (by simp)
  left_inv index := by
    apply Fin.ext
    rfl
  right_inv index := by
    apply Fin.ext
    rfl

@[simp]
theorem indexEquiv_val
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (emission : ReceiptEmission EventId Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (index : Fin emission.length) :
    (indexEquiv emission groundMap locationMap index).val = index.val := by
  rfl

@[simp]
theorem get_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    (emission : ReceiptEmission EventId Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (index : Fin emission.length) :
    (emission.mapLabels groundMap locationMap).get
        (indexEquiv emission groundMap locationMap index) =
      (emission.get index).mapLabels groundMap locationMap := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  apply Option.some.inj
  let mappedIndex := indexEquiv emission groundMap locationMap index
  calc
    some (emission.mapLabels groundMap locationMap)[mappedIndex.val] =
        (emission.mapLabels groundMap locationMap)[mappedIndex.val]? := by
          symm
          exact List.getElem?_eq_getElem mappedIndex.isLt
    _ = Option.map (fun event => event.mapLabels groundMap locationMap)
          emission[mappedIndex.val]? := by
          exact List.getElem?_map
    _ = Option.map (fun event => event.mapLabels groundMap locationMap)
          emission[index.val]? := by
          rw [show mappedIndex.val = index.val by rfl]
    _ = some (emission[index.val].mapLabels groundMap locationMap) := by
          rw [List.getElem?_eq_getElem index.isLt]
          rfl

theorem Valid.mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    {emission : ReceiptEmission EventId Ground Location}
    (valid : emission.Valid)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    (emission.mapLabels groundMap locationMap).Valid := by
  constructor
  · unfold ReceiptEmission.mapLabels
    simp only [List.map_map]
    change (emission.map EmittedEvent.id).Nodup
    exact valid.1
  · let positions := indexEquiv emission groundMap locationMap
    intro mappedEffect
    obtain ⟨effect, rfl⟩ := positions.surjective mappedEffect
    have sourceCauses := valid.2 effect
    rw [get_mapLabels]
    change (emission.get effect).causes.Forall _
    apply sourceCauses.imp
    intro causeId causeEarlier
    obtain ⟨cause, hcause, hid⟩ := causeEarlier
    refine ⟨positions cause, ?_, ?_⟩
    · change cause.val < effect.val at hcause
      change (positions cause).val < (positions effect).val
      simpa [positions] using hcause
    · rw [get_mapLabels]
      exact hid

/-- Constructing a causal pomset commutes with transport of receipt labels. -/
theorem toReceipt_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'}
    [DecidableEq EventId]
    (emission : ReceiptEmission EventId Ground Location)
    (valid : emission.Valid)
    (groundMap : Ground → Ground') (locationMap : Location → Location') :
    (emission.mapLabels groundMap locationMap).toReceipt
        (valid.mapLabels groundMap locationMap) =
      ((emission.toReceipt valid).mapLabels groundMap locationMap).relabel
        (indexEquiv emission groundMap locationMap) := by
  let positions := indexEquiv emission groundMap locationMap
  apply CausalReceipt.ext
  · funext event
    obtain ⟨source, rfl⟩ := positions.surjective event
    change ((emission.mapLabels groundMap locationMap).get
        (positions source)).label =
      (emission.get source).label.map groundMap locationMap
    exact congrArg EmittedEvent.label
      (get_mapLabels emission groundMap locationMap source)
  · funext cause effect
    obtain ⟨sourceCause, rfl⟩ := positions.surjective cause
    obtain ⟨sourceEffect, rfl⟩ := positions.surjective effect
    change ((emission.mapLabels groundMap locationMap).get
        (positions sourceEffect)).causes.count
          ((emission.mapLabels groundMap locationMap).get
            (positions sourceCause)).id =
      (emission.get sourceEffect).causes.count (emission.get sourceCause).id
    rw [get_mapLabels, get_mapLabels]
    rfl
  · funext event
    obtain ⟨source, rfl⟩ := positions.surjective event
    change (positions source).val = source.val
    exact indexEquiv_val emission groundMap locationMap source

end ReceiptEmission

namespace CostSig

theorem additiveFold_map
    {Ground : Type u} {Ground' : Type u'} {Delta : Type x}
    [AddCommMonoid Delta]
    (groundMap : Ground → Ground') (weight : Ground' → Delta)
    (sig : CostSig Ground) :
    additiveFold weight (sig.map groundMap) =
      additiveFold (weight ∘ groundMap) sig := by
  simp [additiveFold, Multiset.map_map]

theorem multiplicativeFold_map
    {Ground : Type u} {Ground' : Type u'} {Delta : Type x}
    [CommMonoid Delta]
    (groundMap : Ground → Ground') (weight : Ground' → Delta)
    (sig : CostSig Ground) :
    multiplicativeFold weight (sig.map groundMap) =
      multiplicativeFold (weight ∘ groundMap) sig := by
  simp [multiplicativeFold, Multiset.map_map]

end CostSig

namespace CausalReceipt

variable {Event : Type w} [Fintype Event] [DecidableEq Event]

theorem totalAdditiveValue_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'} {Delta : Type x}
    [AddCommMonoid Delta]
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (weight : Ground' → Delta) :
    (receipt.mapLabels groundMap locationMap).totalAdditiveValue weight =
      receipt.totalAdditiveValue (weight ∘ groundMap) := by
  simp [totalAdditiveValue, totalRawMeasure_mapLabels, CostSig.additiveFold_map]

theorem totalMultiplicativeValue_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Location : Type v} {Location' : Type v'} {Delta : Type x}
    [CommMonoid Delta]
    (receipt : CausalReceipt Event Ground Location)
    (groundMap : Ground → Ground') (locationMap : Location → Location')
    (weight : Ground' → Delta) :
    (receipt.mapLabels groundMap locationMap).totalMultiplicativeValue weight =
      receipt.totalMultiplicativeValue (weight ∘ groundMap) := by
  simp [totalMultiplicativeValue, totalRawMeasure_mapLabels,
    CostSig.multiplicativeFold_map]

end CausalReceipt

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
