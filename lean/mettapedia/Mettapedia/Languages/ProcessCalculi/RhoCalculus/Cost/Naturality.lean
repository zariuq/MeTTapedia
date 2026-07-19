import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Valuation

/-!
# Naturality of located causal receipts

Maps of signing grounds and opaque funding surfaces act only on receipt
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
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (contribution : FundingContribution Ground Surface) :
    FundingContribution Ground' Surface' where
  surface := surfaceMap contribution.surface
  spend := contribution.spend.map groundMap
  spend_valid := by
    simpa [CostSig.RuntimeValid] using contribution.spend_valid

@[simp]
theorem map_surface {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (contribution : FundingContribution Ground Surface) :
    (contribution.map groundMap surfaceMap).surface =
      surfaceMap contribution.surface := by
  rfl

@[simp]
theorem map_spend {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (contribution : FundingContribution Ground Surface) :
    (contribution.map groundMap surfaceMap).spend =
      contribution.spend.map groundMap := by
  rfl

@[simp]
theorem map_id {Ground : Type u} {Surface : Type v}
    (contribution : FundingContribution Ground Surface) :
    contribution.map id id = contribution := by
  cases contribution
  simp [map]

@[simp]
theorem map_comp {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Surface : Type v} {Surface' : Type v'} {Surface'' : Type v''}
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (surfaceFirst : Surface → Surface') (surfaceSecond : Surface' → Surface'')
    (contribution : FundingContribution Ground Surface) :
    (contribution.map groundFirst surfaceFirst).map groundSecond surfaceSecond =
      contribution.map (groundSecond ∘ groundFirst) (surfaceSecond ∘ surfaceFirst) := by
  cases contribution
  simp [map, Multiset.map_map]

end FundingContribution

namespace SpendEvent

private theorem sum_mapped_spends
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (funding : Multiset (FundingContribution Ground Surface)) :
    (funding.map (FundingContribution.map groundMap surfaceMap) |>.map
        FundingContribution.spend).sum =
      (funding.map FundingContribution.spend).sum.map groundMap := by
  induction funding using Multiset.induction_on with
  | empty => simp
  | @cons contribution rest ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons,
        FundingContribution.map_spend, Multiset.map_add, ih]

@[ext]
theorem ext {Ground : Type u} {Surface : Type v}
    {left right : SpendEvent Ground Surface}
    (funding : left.funding = right.funding) : left = right := by
  cases left
  cases right
  simp_all

/-- Transport every contribution label while retaining every occurrence. -/
def map {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (event : SpendEvent Ground Surface) : SpendEvent Ground' Surface' where
  funding := event.funding.map (FundingContribution.map groundMap surfaceMap)
  funding_nonempty := by
    simpa using event.funding_nonempty

@[simp]
theorem map_funding {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (event : SpendEvent Ground Surface) :
    (event.map groundMap surfaceMap).funding =
      event.funding.map (FundingContribution.map groundMap surfaceMap) := by
  rfl

@[simp]
theorem map_id {Ground : Type u} {Surface : Type v}
    (event : SpendEvent Ground Surface) : event.map id id = event := by
  apply SpendEvent.ext
  simp [map]

@[simp]
theorem map_comp {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Surface : Type v} {Surface' : Type v'} {Surface'' : Type v''}
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (surfaceFirst : Surface → Surface') (surfaceSecond : Surface' → Surface'')
    (event : SpendEvent Ground Surface) :
    (event.map groundFirst surfaceFirst).map groundSecond surfaceSecond =
      event.map (groundSecond ∘ groundFirst) (surfaceSecond ∘ surfaceFirst) := by
  apply SpendEvent.ext
  simp [map, Multiset.map_map, Function.comp_def]

@[simp]
theorem rawSpend_map {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (event : SpendEvent Ground Surface) :
    (event.map groundMap surfaceMap).rawSpend = event.rawSpend.map groundMap := by
  exact sum_mapped_spends groundMap surfaceMap event.funding

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
theorem ext {Ground : Type u} {Surface : Type v}
    {left right : CausalReceipt Event Ground Surface}
    (label : left.label = right.label)
    (arcs : left.arcMultiplicity = right.arcMultiplicity)
    (rank : left.rank = right.rank) : left = right := by
  cases left
  cases right
  simp_all

/-- Relabel grounds and locations without changing event identity or causality. -/
def mapLabels {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    CausalReceipt Event Ground' Surface' where
  label event := (receipt.label event).map groundMap surfaceMap
  arcMultiplicity := receipt.arcMultiplicity
  rank := receipt.rank
  arc_rank_lt := receipt.arc_rank_lt

@[simp]
theorem mapLabels_label {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (event : Event) :
    (receipt.mapLabels groundMap surfaceMap).label event =
      (receipt.label event).map groundMap surfaceMap := by
  rfl

@[simp]
theorem mapLabels_arcMultiplicity {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (cause effect : Event) :
    (receipt.mapLabels groundMap surfaceMap).arcMultiplicity cause effect =
      receipt.arcMultiplicity cause effect := by
  rfl

@[simp]
theorem mapLabels_rank {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (event : Event) :
    (receipt.mapLabels groundMap surfaceMap).rank event = receipt.rank event := by
  rfl

@[simp]
theorem mapLabels_id {Ground : Type u} {Surface : Type v}
    (receipt : CausalReceipt Event Ground Surface) :
    receipt.mapLabels id id = receipt := by
  apply CausalReceipt.ext
  · funext event
    simp
  · rfl
  · rfl

@[simp]
theorem mapLabels_comp
    {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Surface : Type v} {Surface' : Type v'} {Surface'' : Type v''}
    (receipt : CausalReceipt Event Ground Surface)
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (surfaceFirst : Surface → Surface') (surfaceSecond : Surface' → Surface'') :
    (receipt.mapLabels groundFirst surfaceFirst).mapLabels groundSecond surfaceSecond =
      receipt.mapLabels (groundSecond ∘ groundFirst) (surfaceSecond ∘ surfaceFirst) := by
  apply CausalReceipt.ext
  · funext event
    simp
  · rfl
  · rfl

theorem causalLE_mapLabels_iff
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (earlier later : Event) :
    (receipt.mapLabels groundMap surfaceMap).CausalLE earlier later ↔
      receipt.CausalLE earlier later := by
  rfl

theorem rawMeasure_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (region : Finset Event) :
    (receipt.mapLabels groundMap surfaceMap).rawMeasure region =
      (receipt.rawMeasure region).map groundMap := by
  unfold rawMeasure
  rw [map_finset_sum]
  apply Finset.sum_congr rfl
  intro event _member
  exact SpendEvent.rawSpend_map groundMap surfaceMap (receipt.label event)

theorem totalRawMeasure_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    (receipt.mapLabels groundMap surfaceMap).totalRawMeasure =
      receipt.totalRawMeasure.map groundMap := by
  exact receipt.rawMeasure_mapLabels groundMap surfaceMap Finset.univ

end CausalReceipt

namespace EmittedEvent

/-- Label transport for one ordered emission record. -/
def mapLabels {EventId : Type w}
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (event : EmittedEvent EventId Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    EmittedEvent EventId Ground' Surface' where
  id := event.id
  causes := event.causes
  label := event.label.map groundMap surfaceMap

@[simp]
theorem mapLabels_id {EventId : Type w} {Ground : Type u} {Surface : Type v}
    (event : EmittedEvent EventId Ground Surface) :
    event.mapLabels _root_.id _root_.id = event := by
  cases event
  simp [mapLabels]

@[simp]
theorem mapLabels_comp {EventId : Type w}
    {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Surface : Type v} {Surface' : Type v'} {Surface'' : Type v''}
    (event : EmittedEvent EventId Ground Surface)
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (surfaceFirst : Surface → Surface') (surfaceSecond : Surface' → Surface'') :
    (event.mapLabels groundFirst surfaceFirst).mapLabels groundSecond surfaceSecond =
      event.mapLabels (groundSecond ∘ groundFirst) (surfaceSecond ∘ surfaceFirst) := by
  cases event
  simp [mapLabels]

end EmittedEvent

namespace ReceiptEmission

variable {EventId : Type w}

/-- Componentwise label transport of an ordered runtime emission. -/
def mapLabels {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (emission : ReceiptEmission EventId Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    ReceiptEmission EventId Ground' Surface' :=
  emission.map fun event => event.mapLabels groundMap surfaceMap

@[simp]
theorem mapLabels_id {Ground : Type u} {Surface : Type v}
    (emission : ReceiptEmission EventId Ground Surface) :
    emission.mapLabels _root_.id _root_.id = emission := by
  simp [mapLabels]

@[simp]
theorem mapLabels_comp
    {Ground : Type u} {Ground' : Type u'} {Ground'' : Type u''}
    {Surface : Type v} {Surface' : Type v'} {Surface'' : Type v''}
    (emission : ReceiptEmission EventId Ground Surface)
    (groundFirst : Ground → Ground') (groundSecond : Ground' → Ground'')
    (surfaceFirst : Surface → Surface') (surfaceSecond : Surface' → Surface'') :
    (emission.mapLabels groundFirst surfaceFirst).mapLabels groundSecond surfaceSecond =
      emission.mapLabels (groundSecond ∘ groundFirst) (surfaceSecond ∘ surfaceFirst) := by
  simp [mapLabels, List.map_map, Function.comp_def]

@[simp]
theorem length_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (emission : ReceiptEmission EventId Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    (emission.mapLabels groundMap surfaceMap).length = emission.length := by
  simp [mapLabels]

/-- The canonical occurrence-position equivalence induced by label transport. -/
def indexEquiv
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (emission : ReceiptEmission EventId Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    Fin emission.length ≃ Fin (emission.mapLabels groundMap surfaceMap).length where
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
    {Surface : Type v} {Surface' : Type v'}
    (emission : ReceiptEmission EventId Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (index : Fin emission.length) :
    (indexEquiv emission groundMap surfaceMap index).val = index.val := by
  rfl

@[simp]
theorem get_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    (emission : ReceiptEmission EventId Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (index : Fin emission.length) :
    (emission.mapLabels groundMap surfaceMap).get
        (indexEquiv emission groundMap surfaceMap index) =
      (emission.get index).mapLabels groundMap surfaceMap := by
  rw [List.get_eq_getElem, List.get_eq_getElem]
  apply Option.some.inj
  let mappedIndex := indexEquiv emission groundMap surfaceMap index
  calc
    some (emission.mapLabels groundMap surfaceMap)[mappedIndex.val] =
        (emission.mapLabels groundMap surfaceMap)[mappedIndex.val]? := by
          symm
          exact List.getElem?_eq_getElem mappedIndex.isLt
    _ = Option.map (fun event => event.mapLabels groundMap surfaceMap)
          emission[mappedIndex.val]? := by
          exact List.getElem?_map
    _ = Option.map (fun event => event.mapLabels groundMap surfaceMap)
          emission[index.val]? := by
          rw [show mappedIndex.val = index.val by rfl]
    _ = some (emission[index.val].mapLabels groundMap surfaceMap) := by
          rw [List.getElem?_eq_getElem index.isLt]
          rfl

theorem Valid.mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'}
    {emission : ReceiptEmission EventId Ground Surface}
    (valid : emission.Valid)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    (emission.mapLabels groundMap surfaceMap).Valid := by
  constructor
  · unfold ReceiptEmission.mapLabels
    simp only [List.map_map]
    change (emission.map EmittedEvent.id).Nodup
    exact valid.1
  · let positions := indexEquiv emission groundMap surfaceMap
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
    {Surface : Type v} {Surface' : Type v'}
    [DecidableEq EventId]
    (emission : ReceiptEmission EventId Ground Surface)
    (valid : emission.Valid)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface') :
    (emission.mapLabels groundMap surfaceMap).toReceipt
        (valid.mapLabels groundMap surfaceMap) =
      ((emission.toReceipt valid).mapLabels groundMap surfaceMap).relabel
        (indexEquiv emission groundMap surfaceMap) := by
  let positions := indexEquiv emission groundMap surfaceMap
  apply CausalReceipt.ext
  · funext event
    obtain ⟨source, rfl⟩ := positions.surjective event
    change ((emission.mapLabels groundMap surfaceMap).get
        (positions source)).label =
      (emission.get source).label.map groundMap surfaceMap
    exact congrArg EmittedEvent.label
      (get_mapLabels emission groundMap surfaceMap source)
  · funext cause effect
    obtain ⟨sourceCause, rfl⟩ := positions.surjective cause
    obtain ⟨sourceEffect, rfl⟩ := positions.surjective effect
    change ((emission.mapLabels groundMap surfaceMap).get
        (positions sourceEffect)).causes.count
          ((emission.mapLabels groundMap surfaceMap).get
            (positions sourceCause)).id =
      (emission.get sourceEffect).causes.count (emission.get sourceCause).id
    rw [get_mapLabels, get_mapLabels]
    rfl
  · funext event
    obtain ⟨source, rfl⟩ := positions.surjective event
    change (positions source).val = source.val
    exact indexEquiv_val emission groundMap surfaceMap source

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
    {Surface : Type v} {Surface' : Type v'} {Delta : Type x}
    [AddCommMonoid Delta]
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (weight : Ground' → Delta) :
    (receipt.mapLabels groundMap surfaceMap).totalAdditiveValue weight =
      receipt.totalAdditiveValue (weight ∘ groundMap) := by
  simp [totalAdditiveValue, totalRawMeasure_mapLabels, CostSig.additiveFold_map]

theorem totalMultiplicativeValue_mapLabels
    {Ground : Type u} {Ground' : Type u'}
    {Surface : Type v} {Surface' : Type v'} {Delta : Type x}
    [CommMonoid Delta]
    (receipt : CausalReceipt Event Ground Surface)
    (groundMap : Ground → Ground') (surfaceMap : Surface → Surface')
    (weight : Ground' → Delta) :
    (receipt.mapLabels groundMap surfaceMap).totalMultiplicativeValue weight =
      receipt.totalMultiplicativeValue (weight ∘ groundMap) := by
  simp [totalMultiplicativeValue, totalRawMeasure_mapLabels,
    CostSig.multiplicativeFold_map]

end CausalReceipt

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
