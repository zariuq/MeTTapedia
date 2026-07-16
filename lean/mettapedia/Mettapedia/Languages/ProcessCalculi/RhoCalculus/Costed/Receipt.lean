import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.List.Count
import Mathlib.Logic.Relation
import Mathlib.Logic.Equiv.Fintype

/-!
# Located causal receipts for cost-accounted rho

The operational account is a finite pomset of firing occurrences.  Direct
arcs record consumption of resources produced by earlier firings; their
multiplicity is retained even though causal reachability only observes their
support.  Runtime emission order is represented separately and is required to
linearize this consumption order.

The raw measure is signature-valued.  More specialized cost algebras are
interpretations of this free commutative-monoid measure.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed

open scoped BigOperators

universe u v w

/-- One portion of a firing's spend, attributed to an opaque funding surface. -/
structure FundingContribution (Ground : Type u) (Surface : Type v) where
  surface : Surface
  spend : CostSig Ground
  spend_valid : spend.RuntimeValid

/-- A firing label with one or more funding contributions.

The multiset retains repeated contributions, including repeated uses of the
same surface.  Its nonemptiness prevents an unlocated firing record.
-/
structure SpendEvent (Ground : Type u) (Surface : Type v) where
  funding : Multiset (FundingContribution Ground Surface)
  funding_nonempty : funding ≠ 0

namespace SpendEvent

/-- Total uninterpreted spend of one firing. -/
def rawSpend {Ground : Type u} {Surface : Type v}
    (event : SpendEvent Ground Surface) : CostSig Ground :=
  (event.funding.map FundingContribution.spend).sum

/-- Contributions of one event funded at a particular surface. -/
def restrictFunding {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (surface : Surface) (event : SpendEvent Ground Surface) :
    Multiset (FundingContribution Ground Surface) :=
  event.funding.filter fun contribution => contribution.surface = surface

/-- Raw spend visible in the local account of one surface. -/
def rawSpendAt {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (surface : Surface) (event : SpendEvent Ground Surface) : CostSig Ground :=
  ((event.restrictFunding surface).map FundingContribution.spend).sum

/-- Whether an event has at least one funding contribution at a surface. -/
def FundedAt {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (event : SpendEvent Ground Surface) (surface : Surface) : Prop :=
  0 < (event.restrictFunding surface).card

/-- A one-surface event helper. -/
def singleton {Ground : Type u} {Surface : Type v}
    (surface : Surface) (spend : CostSig Ground) (spend_valid : spend.RuntimeValid) :
    SpendEvent Ground Surface where
  funding := {⟨surface, spend, spend_valid⟩}
  funding_nonempty := by simp

private theorem sum_restrictedFunding_spend
    {Ground : Type u} {Surface : Type v}
    [Fintype Surface] [DecidableEq Surface]
    (funding : Multiset (FundingContribution Ground Surface)) :
      (∑ surface : Surface,
        ((funding.filter fun contribution =>
          contribution.surface = surface).map FundingContribution.spend).sum) =
      (funding.map FundingContribution.spend).sum := by
  induction funding using Multiset.induction_on with
  | empty => simp
  | @cons contribution rest ih =>
      rw [Multiset.map_cons, Multiset.sum_cons]
      simp [Multiset.filter_cons, ih, Finset.sum_add_distrib]
      have contribution_at : ∀ surface : Surface,
          (Multiset.map FundingContribution.spend
            (if contribution.surface = surface then {contribution} else 0)).sum =
            if contribution.surface = surface then contribution.spend else 0 := by
        intro surface
        split <;> simp_all
      simp_rw [contribution_at]
      simp

/-- Local restrictions form an exact partition of a firing's spend.  Repeated
contributions at the same surface remain repeated inside that summand. -/
theorem sum_rawSpendAt_eq_rawSpend
    {Ground : Type u} {Surface : Type v}
    [Fintype Surface] [DecidableEq Surface]
    (event : SpendEvent Ground Surface) :
    (∑ surface : Surface, event.rawSpendAt surface) = event.rawSpend := by
  exact sum_restrictedFunding_spend event.funding

/-- Finite support of an event's opaque funding locations. -/
def fundingSurfaces {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (event : SpendEvent Ground Surface) : Finset Surface :=
  (event.funding.map FundingContribution.surface).toFinset

private theorem sum_restrictedFunding_spend_of_cover
    {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (surfaces : Finset Surface)
    (funding : Multiset (FundingContribution Ground Surface))
    (covered : ∀ contribution ∈ funding,
      contribution.surface ∈ surfaces) :
    (∑ surface ∈ surfaces,
      ((funding.filter fun contribution =>
        contribution.surface = surface).map FundingContribution.spend).sum) =
    (funding.map FundingContribution.spend).sum := by
  induction funding using Multiset.induction_on with
  | empty => simp
  | @cons contribution rest ih =>
      have contribution_mem : contribution.surface ∈ surfaces :=
        covered contribution (by simp)
      have rest_covered : ∀ candidate ∈ rest,
          candidate.surface ∈ surfaces := by
        intro candidate member
        exact covered candidate (by simp [member])
      rw [Multiset.map_cons, Multiset.sum_cons]
      simp [Multiset.filter_cons, ih rest_covered, Finset.sum_add_distrib]
      have contribution_at : ∀ surface : Surface,
          (Multiset.map FundingContribution.spend
            (if contribution.surface = surface then {contribution} else 0)).sum =
            if contribution.surface = surface then contribution.spend else 0 := by
        intro surface
        split <;> simp_all
      simp_rw [contribution_at]
      simp [contribution_mem]

/-- Summing over any finite family containing every funding location recovers
the event's global spend. -/
theorem sum_rawSpendAt_eq_rawSpend_of_cover
    {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (event : SpendEvent Ground Surface) (surfaces : Finset Surface)
    (covered : ∀ contribution ∈ event.funding,
      contribution.surface ∈ surfaces) :
    (∑ surface ∈ surfaces, event.rawSpendAt surface) = event.rawSpend :=
  sum_restrictedFunding_spend_of_cover surfaces event.funding covered

/-- The event's own finite support is sufficient for exact gluing. -/
theorem sum_rawSpendAt_fundingSurfaces_eq_rawSpend
    {Ground : Type u} {Surface : Type v} [DecidableEq Surface]
    (event : SpendEvent Ground Surface) :
    (∑ surface ∈ event.fundingSurfaces, event.rawSpendAt surface) =
      event.rawSpend := by
  apply event.sum_rawSpendAt_eq_rawSpend_of_cover
  intro contribution member
  rw [fundingSurfaces, Multiset.mem_toFinset]
  exact Multiset.mem_map.mpr ⟨contribution, member, rfl⟩

end SpendEvent

/-- A finite causal receipt.  `arcMultiplicity cause effect` counts consumed
resource occurrences produced by `cause` and consumed by `effect`.

The rank field is a certificate that direct consumption arcs are acyclic.  It
does not impose order on unrelated events.
-/
structure CausalReceipt (Event : Type w) [Fintype Event]
    (Ground : Type u) (Surface : Type v) where
  label : Event → SpendEvent Ground Surface
  arcMultiplicity : Event → Event → Nat
  rank : Event → Nat
  arc_rank_lt : ∀ cause effect,
    0 < arcMultiplicity cause effect → rank cause < rank effect

namespace CausalReceipt

variable {Event : Type w} {Ground : Type u} {Surface : Type v} [Fintype Event]

/-- The support of the occurrence-preserving consumption multigraph. -/
def DirectCause (receipt : CausalReceipt Event Ground Surface)
    (cause effect : Event) : Prop :=
  0 < receipt.arcMultiplicity cause effect

/-- Causal order generated by consumption, including reflexivity. -/
def CausalLE (receipt : CausalReceipt Event Ground Surface)
    (earlier later : Event) : Prop :=
  Relation.ReflTransGen receipt.DirectCause earlier later

/-- Independence is derived causal incomparability, not extra structure. -/
def Independent (receipt : CausalReceipt Event Ground Surface)
    (left right : Event) : Prop :=
  ¬receipt.CausalLE left right ∧ ¬receipt.CausalLE right left

@[refl]
theorem causalLE_refl (receipt : CausalReceipt Event Ground Surface) (event : Event) :
    receipt.CausalLE event event :=
  Relation.ReflTransGen.refl

@[trans]
theorem causalLE_trans (receipt : CausalReceipt Event Ground Surface)
    {first second third : Event}
    (h₁ : receipt.CausalLE first second)
    (h₂ : receipt.CausalLE second third) :
    receipt.CausalLE first third :=
  h₁.trans h₂

/-- A causal path is either reflexive or strictly increases the acyclicity rank. -/
theorem causalLE_eq_or_rank_lt (receipt : CausalReceipt Event Ground Surface)
    {earlier later : Event} (path : receipt.CausalLE earlier later) :
    earlier = later ∨ receipt.rank earlier < receipt.rank later := by
  induction path with
  | refl => exact Or.inl rfl
  | tail prior edge ih =>
      have hedge := receipt.arc_rank_lt _ _ edge
      rcases ih with rfl | hstrict
      · exact Or.inr hedge
      · exact Or.inr (Nat.lt_trans hstrict hedge)

/-- Causal reachability is monotone in the emission rank. -/
theorem causalLE_rank_le (receipt : CausalReceipt Event Ground Surface)
    {earlier later : Event} (path : receipt.CausalLE earlier later) :
    receipt.rank earlier ≤ receipt.rank later := by
  rcases receipt.causalLE_eq_or_rank_lt path with rfl | h
  · exact Nat.le_refl _
  · exact Nat.le_of_lt h

/-- Acyclic direct consumption makes generated causal reachability antisymmetric. -/
theorem causalLE_antisymm (receipt : CausalReceipt Event Ground Surface)
    {left right : Event}
    (hleft : receipt.CausalLE left right)
    (hright : receipt.CausalLE right left) : left = right := by
  rcases receipt.causalLE_eq_or_rank_lt hleft with h | hlt
  · exact h
  · rcases receipt.causalLE_eq_or_rank_lt hright with h | hgt
    · exact h.symm
    · exact (Nat.lt_asymm hlt hgt).elim

/-- The generated causal order is a partial order, so a causal receipt is a pomset. -/
theorem causalPartialOrder (receipt : CausalReceipt Event Ground Surface) :
    IsPartialOrder Event receipt.CausalLE where
  refl := receipt.causalLE_refl
  trans _ _ _ := receipt.causalLE_trans
  antisymm _ _ := receipt.causalLE_antisymm

/-- Signature-valued measure of a finite event region. -/
def rawMeasure [DecidableEq Event] (receipt : CausalReceipt Event Ground Surface)
    (region : Finset Event) : CostSig Ground :=
  ∑ event ∈ region, (receipt.label event).rawSpend

/-- The complete signature-valued measure of a finite receipt. -/
def totalRawMeasure [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Surface) : CostSig Ground :=
  receipt.rawMeasure Finset.univ

/-- Events visible from one funding surface. -/
def eventsAt [DecidableEq Event] [DecidableEq Surface]
    (receipt : CausalReceipt Event Ground Surface) (surface : Surface) : Finset Event :=
  Finset.univ.filter fun event =>
    0 < ((receipt.label event).restrictFunding surface).card

/-- Per-location restriction of the raw measure over an arbitrary region. -/
def rawMeasureAt [DecidableEq Event] [DecidableEq Surface]
    (receipt : CausalReceipt Event Ground Surface) (surface : Surface)
    (region : Finset Event) : CostSig Ground :=
  ∑ event ∈ region, (receipt.label event).rawSpendAt surface

/-- Per-location restrictions glue back to the complete raw measure on every
finite event region. -/
theorem sum_rawMeasureAt_eq_rawMeasure
    [DecidableEq Event] [Fintype Surface] [DecidableEq Surface]
    (receipt : CausalReceipt Event Ground Surface) (region : Finset Event) :
    (∑ surface : Surface, receipt.rawMeasureAt surface region) =
      receipt.rawMeasure region := by
  unfold rawMeasureAt rawMeasure
  calc
    (∑ surface : Surface,
        ∑ event ∈ region, (receipt.label event).rawSpendAt surface) =
        ∑ event ∈ region,
          ∑ surface : Surface, (receipt.label event).rawSpendAt surface := by
      rw [Finset.sum_comm]
    _ = ∑ event ∈ region, (receipt.label event).rawSpend := by
      simp [SpendEvent.sum_rawSpendAt_eq_rawSpend]

/-- Global raw accounting is exactly the glue of all local accounts. -/
theorem sum_totalRawMeasureAt_eq_totalRawMeasure
    [DecidableEq Event] [Fintype Surface] [DecidableEq Surface]
    (receipt : CausalReceipt Event Ground Surface) :
    (∑ surface : Surface, receipt.rawMeasureAt surface Finset.univ) =
      receipt.totalRawMeasure := by
  exact receipt.sum_rawMeasureAt_eq_rawMeasure Finset.univ

/-- Finite support of the located measure over an event region. -/
def fundingSurfaces [DecidableEq Event] [DecidableEq Surface]
    (receipt : CausalReceipt Event Ground Surface) (region : Finset Event) :
    Finset Surface :=
  region.biUnion fun event => (receipt.label event).fundingSurfaces

/-- The finite support of an arbitrary receipt region glues exactly to its
global signature-valued measure, without requiring the ambient surface type to
be finite. -/
theorem sum_rawMeasureAt_fundingSurfaces_eq_rawMeasure
    [DecidableEq Event] [DecidableEq Surface]
    (receipt : CausalReceipt Event Ground Surface) (region : Finset Event) :
    (∑ surface ∈ receipt.fundingSurfaces region,
      receipt.rawMeasureAt surface region) = receipt.rawMeasure region := by
  unfold rawMeasureAt rawMeasure
  calc
    (∑ surface ∈ receipt.fundingSurfaces region,
        ∑ event ∈ region, (receipt.label event).rawSpendAt surface) =
        ∑ event ∈ region,
          ∑ surface ∈ receipt.fundingSurfaces region,
            (receipt.label event).rawSpendAt surface := by
      rw [Finset.sum_comm]
    _ = ∑ event ∈ region, (receipt.label event).rawSpend := by
      apply Finset.sum_congr rfl
      intro event event_mem
      apply SpendEvent.sum_rawSpendAt_eq_rawSpend_of_cover
      intro contribution contribution_mem
      apply Finset.mem_biUnion.mpr
      refine ⟨event, event_mem, ?_⟩
      rw [SpendEvent.fundingSurfaces, Multiset.mem_toFinset]
      exact Multiset.mem_map.mpr ⟨contribution, contribution_mem, rfl⟩

/-- Largest rank in a finite receipt, used to place sequential composites. -/
def maxRank [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Surface) : Nat :=
  Finset.univ.sup receipt.rank

theorem rank_le_maxRank [DecidableEq Event]
    (receipt : CausalReceipt Event Ground Surface) (event : Event) :
    receipt.rank event ≤ receipt.maxRank :=
  Finset.le_sup (f := receipt.rank) (Finset.mem_univ event)

/-- Transport event identities along an equivalence.  Labels, consumption-arc
multiplicities, and ranks are preserved rather than reconstructed from event
contents. -/
def relabel {Other : Type*} [Fintype Other]
    (receipt : CausalReceipt Event Ground Surface)
    (ids : Event ≃ Other) : CausalReceipt Other Ground Surface where
  label event := receipt.label (ids.symm event)
  arcMultiplicity cause effect :=
    receipt.arcMultiplicity (ids.symm cause) (ids.symm effect)
  rank event := receipt.rank (ids.symm event)
  arc_rank_lt _cause _effect h := receipt.arc_rank_lt _ _ h

/-- Relabeling preserves the generated causal order exactly. -/
theorem causalLE_relabel_iff {Other : Type*} [Fintype Other]
    (receipt : CausalReceipt Event Ground Surface) (ids : Event ≃ Other)
    (earlier later : Event) :
    (receipt.relabel ids).CausalLE (ids earlier) (ids later) ↔
      receipt.CausalLE earlier later := by
  constructor
  · intro path
    simpa [CausalLE, DirectCause, relabel] using
      path.lift ids.symm (fun _ _ edge => by simpa [DirectCause, relabel] using edge)
  · intro path
    simpa [CausalLE, DirectCause, relabel] using
      path.lift ids (fun _ _ edge => by simpa [DirectCause, relabel] using edge)

/-- Relabeling by any bijection leaves the complete raw measure unchanged. -/
theorem totalRawMeasure_relabel {Other : Type*}
    [DecidableEq Event] [Fintype Other] [DecidableEq Other]
    (receipt : CausalReceipt Event Ground Surface) (ids : Event ≃ Other) :
    (receipt.relabel ids).totalRawMeasure = receipt.totalRawMeasure := by
  simpa [totalRawMeasure, rawMeasure, relabel] using
    ids.symm.sum_comp (fun event => (receipt.label event).rawSpend)

/-- An injection is an identity upgrade into its image.  This is the seam used
to replace local counter IDs by a collision-resistant external representation
without changing receipt semantics. -/
def relabelEmbedding {Other : Type*} [DecidableEq Other]
    (receipt : CausalReceipt Event Ground Surface) (ids : Event ↪ Other)
    [Fintype (Set.range ids)] :
    CausalReceipt (Set.range ids) Ground Surface :=
  receipt.relabel ids.toEquivRange

/-- Injective identity upgrades preserve the complete raw measure. -/
theorem totalRawMeasure_relabelEmbedding {Other : Type*}
    [DecidableEq Event] [DecidableEq Other]
    (receipt : CausalReceipt Event Ground Surface) (ids : Event ↪ Other)
    [Fintype (Set.range ids)] :
    (receipt.relabelEmbedding ids).totalRawMeasure = receipt.totalRawMeasure :=
  receipt.totalRawMeasure_relabel ids.toEquivRange

/-- Parallel composition is disjoint union with no cross-component causes. -/
def parallel {Other : Type*} [Fintype Other]
    (left : CausalReceipt Event Ground Surface)
    (right : CausalReceipt Other Ground Surface) :
    CausalReceipt (Event ⊕ Other) Ground Surface where
  label
    | .inl event => left.label event
    | .inr event => right.label event
  arcMultiplicity
    | .inl cause, .inl effect => left.arcMultiplicity cause effect
    | .inr cause, .inr effect => right.arcMultiplicity cause effect
    | _, _ => 0
  rank
    | .inl event => left.rank event
    | .inr event => right.rank event
  arc_rank_lt cause effect h := by
    cases cause <;> cases effect
    · exact left.arc_rank_lt _ _ h
    · simp at h
    · simp at h
    · exact right.arc_rank_lt _ _ h

/-- Sequential composition adds a causal boundary from every left event to
every right event.  Existing direct-consumption multiplicities are retained. -/
def sequential {Other : Type*} [Fintype Other] [DecidableEq Event]
    (left : CausalReceipt Event Ground Surface)
    (right : CausalReceipt Other Ground Surface) :
    CausalReceipt (Event ⊕ Other) Ground Surface where
  label
    | .inl event => left.label event
    | .inr event => right.label event
  arcMultiplicity
    | .inl cause, .inl effect => left.arcMultiplicity cause effect
    | .inr cause, .inr effect => right.arcMultiplicity cause effect
    | .inl _, .inr _ => 1
    | .inr _, .inl _ => 0
  rank
    | .inl event => left.rank event
    | .inr event => left.maxRank + 1 + right.rank event
  arc_rank_lt cause effect h := by
    cases cause with
    | inl cause =>
        cases effect with
        | inl effect => exact left.arc_rank_lt cause effect h
        | inr effect =>
            have hbound := left.rank_le_maxRank cause
            change left.rank cause < left.maxRank + 1 + right.rank effect
            omega
    | inr cause =>
        cases effect with
        | inl effect => simp at h
        | inr effect =>
            have hstrict := right.arc_rank_lt cause effect h
            change left.maxRank + 1 + right.rank cause <
              left.maxRank + 1 + right.rank effect
            omega

end CausalReceipt

/-! ## Ordered runtime emissions -/

/-- One ordered runtime record.  Repeated cause IDs represent distinct
consumed resource occurrences and are deliberately retained. -/
structure EmittedEvent (EventId : Type w) (Ground : Type u) (Surface : Type v) where
  id : EventId
  causes : List EventId
  label : SpendEvent Ground Surface

/-- An append-only presentation emitted by a concrete reducer run. -/
abbrev ReceiptEmission (EventId : Type w) (Ground : Type u) (Surface : Type v) :=
  List (EmittedEvent EventId Ground Surface)

namespace ReceiptEmission

variable {EventId : Type w} {Ground : Type u} {Surface : Type v}

/-- Valid emissions have unique IDs and every cause names an earlier record. -/
def Valid (emission : ReceiptEmission EventId Ground Surface) : Prop :=
  (emission.map EmittedEvent.id).Nodup ∧
    ∀ effect : Fin emission.length,
      (emission.get effect).causes.Forall fun causeId =>
        ∃ cause : Fin emission.length,
          cause < effect ∧ (emission.get cause).id = causeId

/-- Unique emitted IDs make position-to-ID injective. -/
theorem Valid.ids_injective {emission : ReceiptEmission EventId Ground Surface}
    (valid : emission.Valid) :
    Function.Injective (fun index : Fin emission.length => (emission.get index).id) := by
  intro left right hid
  let left' : Fin (emission.map EmittedEvent.id).length :=
    Fin.cast (by simp) left
  let right' : Fin (emission.map EmittedEvent.id).length :=
    Fin.cast (by simp) right
  have hget : (emission.map EmittedEvent.id).get left' =
      (emission.map EmittedEvent.id).get right' := by
    simpa [left', right'] using hid
  have hpositions : left' = right' := valid.1.injective_get hget
  apply Fin.ext
  change left'.val = right'.val
  exact congrArg Fin.val hpositions

/-- A valid emission presents a causal receipt whose event carrier is the set
of emission occurrences, not the set of distinct labels. -/
def toReceipt (emission : ReceiptEmission EventId Ground Surface)
    [DecidableEq EventId] (valid : emission.Valid) :
    CausalReceipt (Fin emission.length) Ground Surface where
  label index := (emission.get index).label
  arcMultiplicity cause effect :=
    (emission.get effect).causes.count (emission.get cause).id
  rank index := index.1
  arc_rank_lt cause effect hcount := by
    have hmem : (emission.get cause).id ∈ (emission.get effect).causes :=
      List.count_pos_iff.mp hcount
    obtain ⟨witness, hwitness, hid⟩ :=
      List.forall_iff_forall_mem.mp (valid.2 effect) _ hmem
    have hwitness_eq : witness = cause := valid.ids_injective hid
    simpa [hwitness_eq] using hwitness

/-- Receipt construction preserves every emitted occurrence, including equal labels. -/
@[simp]
theorem toReceipt_event_count (emission : ReceiptEmission EventId Ground Surface)
    (_valid : emission.Valid) :
    Fintype.card (Fin emission.length) = emission.length := by
  simp

/-- Receipt construction preserves the label at each emission position. -/
@[simp]
theorem toReceipt_label (emission : ReceiptEmission EventId Ground Surface)
    [DecidableEq EventId] (valid : emission.Valid) (index : Fin emission.length) :
    (emission.toReceipt valid).label index = (emission.get index).label :=
  rfl

private theorem sum_get_eq_sum_map {Alpha : Type*} {M : Type*} [AddCommMonoid M]
    (items : List Alpha) (value : Alpha → M) :
    (∑ index : Fin items.length, value (items.get index)) =
      (items.map value).sum := by
  induction items with
  | nil => simp
  | cons head tail ih =>
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      rw [Fin.sum_univ_succ]
      change value head + (∑ index : Fin tail.length, value (tail.get index)) =
        value head + (tail.map value).sum
      rw [ih]

/-- The canonical raw measure is exactly the fold of the emitted spends. -/
theorem toReceipt_totalRawMeasure
    (emission : ReceiptEmission EventId Ground Surface) [DecidableEq EventId]
    (valid : emission.Valid) :
    (emission.toReceipt valid).totalRawMeasure =
      (emission.map fun event => event.label.rawSpend).sum := by
  simpa [CausalReceipt.totalRawMeasure, CausalReceipt.rawMeasure, toReceipt] using
    sum_get_eq_sum_map emission (fun event => event.label.rawSpend)

/-- Every referenced cause in a valid emission exists at an earlier position. -/
theorem cause_exists_earlier {emission : ReceiptEmission EventId Ground Surface}
    (valid : emission.Valid) (effect : Fin emission.length) (causeId : EventId)
    (hcause : causeId ∈ (emission.get effect).causes) :
    ∃ cause : Fin emission.length,
      cause < effect ∧ (emission.get cause).id = causeId :=
  List.forall_iff_forall_mem.mp (valid.2 effect) causeId hcause

/-- A valid emission cannot name its own event ID as a cause. -/
theorem no_self_cause {emission : ReceiptEmission EventId Ground Surface}
    (valid : emission.Valid) (effect : Fin emission.length) :
    (emission.get effect).id ∉ (emission.get effect).causes := by
  intro hself
  obtain ⟨cause, hbefore, hid⟩ :=
    List.forall_iff_forall_mem.mp (valid.2 effect) _ hself
  have : cause = effect := valid.ids_injective hid
  subst cause
  exact (lt_irrefl effect hbefore).elim

/-- If an emitted event ID occurs as a cause, that event is strictly earlier. -/
theorem emitted_cause_is_earlier {emission : ReceiptEmission EventId Ground Surface}
    (valid : emission.Valid) (cause effect : Fin emission.length)
    (hcause : (emission.get cause).id ∈ (emission.get effect).causes) :
    cause < effect := by
  obtain ⟨witness, hbefore, hid⟩ :=
    List.forall_iff_forall_mem.mp (valid.2 effect) _ hcause
  have : witness = cause := valid.ids_injective hid
  simpa [this] using hbefore

/-- The ordered emission is a linear extension of its generated causal order. -/
theorem emission_linearizes_causal_order
    (emission : ReceiptEmission EventId Ground Surface) [DecidableEq EventId]
    (valid : emission.Valid)
    {earlier later : Fin emission.length}
    (path : (emission.toReceipt valid).CausalLE earlier later) :
    earlier ≤ later :=
  (emission.toReceipt valid).causalLE_rank_le path

end ReceiptEmission

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Costed
