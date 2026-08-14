import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Conservation
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Located
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Normalization
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.NormalizationErasure
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawConfig
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.RawScope
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost.Step
import Mathlib.Data.List.Sigma
import Mathlib.Tactic

/-!
# Declarative/executable cost-step bridge

The executable side remains the independent raw traversal from `Runtime`.
This module relates its occurrence indices and exact covers to the typed
`CostStep` relation, modulo the declared structural normalization boundary.
-/

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical

/-- Components selected by source occurrence index. -/
def selectIndices (config : RawCostConfig) (indices : List Nat) : RawCostConfig :=
  (config.zipIdx.filter fun entry => decide (entry.2 ∈ indices)).map Prod.fst

/-- Index selection and index erasure partition the source occurrence
multiset exactly; repeated syntax is never collapsed. -/
theorem eraseIndices_add_selectIndices
    (config : RawCostConfig) (indices : List Nat) :
    (eraseIndices config indices : Multiset RawCostTerm) +
        (selectIndices config indices : Multiset RawCostTerm) =
      (config : Multiset RawCostTerm) := by
  let indexed : Multiset (RawCostTerm × Nat) := config.zipIdx
  have partition := Multiset.filter_add_not
    (fun entry : RawCostTerm × Nat => entry.2 ∉ indices) indexed
  have mapped := congrArg (Multiset.map Prod.fst) partition
  simpa [indexed, eraseIndices, selectIndices, Multiset.map_add] using mapped

/-- Decoding preserves the occurrence partition. -/
theorem decodeRawConfig_erase_add_select
    (config : RawCostConfig) (indices : List Nat) :
    decodeRawConfig (eraseIndices config indices) +
        decodeRawConfig (selectIndices config indices) =
      decodeRawConfig config := by
  unfold decodeRawConfig
  simpa [Multiset.map_add] using
    congrArg (Multiset.map decodeCostTerm)
      (eraseIndices_add_selectIndices config indices)

/-- Selecting a duplicate-free family of witnessed source indices recovers
exactly those witnessed occurrences, irrespective of their presentation
order. -/
theorem selectIndices_eq_picked
    {config : RawCostConfig} {indices : List Nat}
    {picked : List (RawCostTerm × Nat)}
    (indices_eq : indices = picked.map Prod.snd)
    (indices_nodup : (picked.map Prod.snd).Nodup)
    (picked_source : ∀ entry ∈ picked, entry ∈ config.zipIdx) :
    (selectIndices config indices : Multiset RawCostTerm) =
      (picked.map Prod.fst : Multiset RawCostTerm) := by
  subst indices
  let filtered := config.zipIdx.filter fun entry =>
    decide (entry.2 ∈ picked.map Prod.snd)
  have zip_snd_nodup := List.nodup_zipIdx_map_snd config
  have zip_nodup : config.zipIdx.Nodup :=
    List.Nodup.of_map Prod.snd zip_snd_nodup
  have filtered_nodup : filtered.Nodup := zip_nodup.filter _
  have picked_nodup : picked.Nodup :=
    List.Nodup.of_map Prod.snd indices_nodup
  have zip_snd_injective := List.inj_on_of_nodup_map zip_snd_nodup
  have same_members : ∀ entry, entry ∈ filtered ↔ entry ∈ picked := by
    intro entry
    constructor
    · intro member
      have filtered_parts := List.mem_filter.mp member
      have index_member : entry.2 ∈ picked.map Prod.snd := by
        simpa using filtered_parts.2
      obtain ⟨source, source_member, source_index⟩ :=
        List.mem_map.mp index_member
      have source_in_zip := picked_source source source_member
      have entries_eq := zip_snd_injective filtered_parts.1 source_in_zip
        source_index.symm
      simpa [entries_eq] using source_member
    · intro member
      apply List.mem_filter.mpr
      refine ⟨picked_source entry member, ?_⟩
      have index_member : entry.2 ∈ picked.map Prod.snd :=
        List.mem_map.mpr ⟨entry, member, rfl⟩
      simpa using index_member
  have permutation : filtered.Perm picked :=
    (List.perm_ext_iff_of_nodup filtered_nodup picked_nodup).2 same_members
  rw [show selectIndices config (picked.map Prod.snd) =
      filtered.map Prod.fst by rfl]
  exact Multiset.coe_eq_coe.mpr (permutation.map Prod.fst)

/-- Recover concrete source occurrences beneath a multiset image.  Duplicate
values remain duplicate list occurrences in the recovered sublist. -/
theorem List.exists_sublist_map_coe_eq_of_le_map
    {Alpha Beta : Type} [DecidableEq Beta] (f : Alpha → Beta) :
    ∀ (source : List Alpha) (target : Multiset Beta),
      target ≤ (source.map f : Multiset Beta) →
        ∃ chosen : List Alpha, chosen.Sublist source ∧
          (chosen.map f : Multiset Beta) = target
  | [], target, covered => by
      have target_zero : target = 0 := le_antisymm covered zero_le
      subst target
      exact ⟨[], .slnil, rfl⟩
  | item :: rest, target, covered => by
      by_cases used : f item ∈ target
      · have erased_covered : target.erase (f item) ≤
            (rest.map f : Multiset Beta) := by
          have erased := Multiset.erase_le_erase (f item) covered
          simpa using erased
        obtain ⟨chosen, chosen_sublist, chosen_image⟩ :=
          List.exists_sublist_map_coe_eq_of_le_map f rest
            (target.erase (f item)) erased_covered
        refine ⟨item :: chosen, chosen_sublist.cons_cons item, ?_⟩
        change f item ::ₘ (chosen.map f : Multiset Beta) = target
        rw [chosen_image, Multiset.cons_erase used]
      · have rest_covered : target ≤ (rest.map f : Multiset Beta) := by
          exact (Multiset.le_cons_of_notMem used).mp covered
        obtain ⟨chosen, chosen_sublist, chosen_image⟩ :=
          List.exists_sublist_map_coe_eq_of_le_map f rest target rest_covered
        exact ⟨chosen, chosen_sublist.cons item, chosen_image⟩

/-- Recover one concrete source occurrence, including its stable source index,
from membership in the decoded unordered configuration. -/
theorem exists_raw_zipIdx_of_mem_decodeRawConfig
    {config : RawCostConfig} {typed : CostTerm String}
    (member : typed ∈ decodeRawConfig config) :
    ∃ raw index,
      (raw, index) ∈ config.zipIdx ∧ decodeCostTerm raw = typed := by
  unfold decodeRawConfig at member
  have typed_mem_list : typed ∈ config.map decodeCostTerm := by
    simpa using member
  obtain ⟨raw, raw_mem_list, decoded⟩ := List.mem_map.mp typed_mem_list
  obtain ⟨position, in_bounds, at_position⟩ :=
    List.exists_mem_iff_getElem.mp
      (show ∃ candidate ∈ config, candidate = raw from
        ⟨raw, raw_mem_list, rfl⟩)
  have decoded_at : decodeCostTerm config[position] = typed := by
    simpa [at_position] using decoded
  have zipped : ∃ entry ∈ config.zipIdx,
      decodeCostTerm entry.1 = typed :=
    List.exists_mem_zipIdx'
      (p := fun entry => decodeCostTerm entry.1 = typed) |>.mpr
        ⟨position, in_bounds, decoded_at⟩
  obtain ⟨entry, entry_mem, entry_decoded⟩ := zipped
  exact ⟨entry.1, entry.2, entry_mem, entry_decoded⟩

/-! ## Occurrence-preserving purse partition -/

/-- Reconstruct the exact active purse term represented by a collector row. -/
def RawIndexedPurse.toTerm (purse : RawIndexedPurse) : RawCostTerm :=
  .purse purse.location (purse.head :: purse.tail)

/-- Declarative view of one active purse collector row. -/
def RawIndexedPurse.toLocated (purse : RawIndexedPurse) : LocatedPurse String :=
  ⟨decodeCostName purse.location,
    .cons (decodeCostSig purse.head) (decodeCostStack purse.tail)⟩

/-- Extract exactly the active located purses from a declarative component.
Depleted purses remain observable terms but cannot fund a firing. -/
def CostTerm.activeLocatedPurse? : CostTerm String → Option (LocatedPurse String)
  | .purse location (.cons head tail) => some ⟨location, .cons head tail⟩
  | _ => none

@[simp]
theorem RawIndexedPurse.activeLocatedPurse?_decode_toTerm
    (purse : RawIndexedPurse) :
    CostTerm.activeLocatedPurse? (decodeCostTerm purse.toTerm) =
      some purse.toLocated := by
  simp [RawIndexedPurse.toTerm, RawIndexedPurse.toLocated,
    CostTerm.activeLocatedPurse?, decodeCostTerm, decodeCostStack]

@[simp]
theorem RawIndexedPurse.decode_toTerm (purse : RawIndexedPurse) :
    decodeCostTerm purse.toTerm = purse.toLocated.toTerm := by
  simp [RawIndexedPurse.toTerm, RawIndexedPurse.toLocated,
    LocatedPurse.toTerm, decodeCostTerm, decodeCostStack]

/-- Expose one temporal tail while retaining its location.  The empty case is
inert; selected-before purses are always in the nonempty case. -/
def LocatedPurse.exposeTail (purse : LocatedPurse String) :
    LocatedPurse String :=
  match purse.stack with
  | .empty => purse
  | .cons _ tail => ⟨purse.location, tail⟩

/-- Active purses have a spendable head.  Depleted purses remain ordinary
inert configuration components. -/
def RawCostTerm.isActivePurse : RawCostTerm → Bool
  | .purse _ (_ :: _) => true
  | _ => false

theorem collectPursesAux_map_toTerm :
    ∀ (config : RawCostConfig) (start : Nat),
      (collectPursesAux config start).map RawIndexedPurse.toTerm =
        config.filter RawCostTerm.isActivePurse
  | [], _ => rfl
  | term :: rest, start => by
      have tail := collectPursesAux_map_toTerm rest (start + 1)
      cases term with
      | purse location stack =>
          cases stack with
          | nil => simpa [collectPursesAux, RawCostTerm.isActivePurse] using tail
          | cons head stackTail =>
              simp [collectPursesAux, RawIndexedPurse.toTerm,
                RawCostTerm.isActivePurse, tail]
      | nil => simpa [collectPursesAux, RawCostTerm.isActivePurse] using tail
      | signed proc sig =>
          simpa [collectPursesAux, RawCostTerm.isActivePurse] using tail
      | par left right =>
          simpa [collectPursesAux, RawCostTerm.isActivePurse] using tail
      | drop name =>
          simpa [collectPursesAux, RawCostTerm.isActivePurse] using tail

/-- The raw collector is exactly the active-purse projection of the decoded
configuration.  This is the occurrence-preserving bridge used by completeness. -/
theorem collectPursesAux_map_toLocated :
    ∀ (config : RawCostConfig) (start : Nat),
      ((collectPursesAux config start).map RawIndexedPurse.toLocated :
          Multiset (LocatedPurse String)) =
        (decodeRawConfig config).filterMap CostTerm.activeLocatedPurse?
  | [], _ => rfl
  | term :: rest, start => by
      have tail := collectPursesAux_map_toLocated rest (start + 1)
      cases term with
      | purse location stack =>
          cases stack with
          | nil =>
              simpa [collectPursesAux, decodeRawConfig, decodeCostTerm,
                decodeCostStack, CostTerm.activeLocatedPurse?] using tail
          | cons head stackTail =>
              have prefixed := congrArg
                (fun purses : Multiset (LocatedPurse String) =>
                  RawIndexedPurse.toLocated
                    ⟨start, location, head, stackTail⟩ ::ₘ purses)
                tail
              simpa [collectPursesAux, decodeRawConfig, decodeCostTerm,
                decodeCostStack, CostTerm.activeLocatedPurse?,
                RawIndexedPurse.toLocated] using prefixed
      | nil =>
          simpa [collectPursesAux, decodeRawConfig, decodeCostTerm,
            CostTerm.activeLocatedPurse?] using tail
      | signed proc sig =>
          simpa [collectPursesAux, decodeRawConfig, decodeCostTerm,
            CostTerm.activeLocatedPurse?] using tail
      | par left right =>
          simpa [collectPursesAux, decodeRawConfig, decodeCostTerm,
            CostTerm.activeLocatedPurse?] using tail
      | drop name =>
          simpa [collectPursesAux, decodeRawConfig, decodeCostTerm,
            CostTerm.activeLocatedPurse?] using tail

@[simp]
theorem RawCostConfig.purses_map_toLocated (config : RawCostConfig) :
    (config.purses.map RawIndexedPurse.toLocated :
        Multiset (LocatedPurse String)) =
      (decodeRawConfig config).filterMap CostTerm.activeLocatedPurse? :=
  collectPursesAux_map_toLocated config 0

@[simp]
theorem activeLocatedPurses_selectedBefore
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual) :
    (LocatedPurse.configComponents cover.selectedBefore).filterMap
        CostTerm.activeLocatedPurse? =
      cover.selectedBefore := by
  rw [LocatedPurse.configComponents, Multiset.filterMap_map]
  rw [LocatedTokenCover.selectedBefore, Multiset.filterMap_map]
  change Multiset.filterMap
      (some ∘ fun choice : SelectedPurseHead String =>
        LocatedPurse.mk location (.cons choice.head choice.tail)) cover.chosen =
    Multiset.map
      (fun choice : SelectedPurseHead String =>
        LocatedPurse.mk location (.cons choice.head choice.tail)) cover.chosen
  exact congrFun (Multiset.filterMap_eq_map _) cover.chosen

/-- Every selected purse occurrence can be recovered from the active-purse
projection of any source configuration containing the cover's availability. -/
theorem LocatedTokenCover.selectedBefore_le_activePurses
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    {source : CostConfig String}
    (cover : LocatedTokenCover location demand available residual)
    (available_le : LocatedPurse.configComponents available ≤
      source) :
    cover.selectedBefore ≤
      source.filterMap CostTerm.activeLocatedPurse? := by
  have selected_le : cover.selectedBefore ≤ available := by
    calc
      cover.selectedBefore ≤ cover.selectedBefore + cover.untouched :=
        Multiset.le_add_right _ _
      _ = available := cover.available_decomposition.symm
  have selected_terms_le :
      LocatedPurse.configComponents cover.selectedBefore ≤ source :=
    (Multiset.map_le_map selected_le).trans available_le
  calc
    cover.selectedBefore =
        (LocatedPurse.configComponents cover.selectedBefore).filterMap
          CostTerm.activeLocatedPurse? :=
      (activeLocatedPurses_selectedBefore cover).symm
    _ ≤ source.filterMap CostTerm.activeLocatedPurse? :=
      Multiset.filterMap_le_filterMap _ selected_terms_le

/-- A declarative exact cover determines concrete raw purse occurrences in
source order, with multiplicity retained. -/
theorem exists_raw_selectedBefore
    {config : RawCostConfig} {location : CostName String}
    {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    (available_le : LocatedPurse.configComponents available ≤
      decodeRawConfig config) :
    ∃ selected : List RawSelectedPurse,
      selected.Sublist config.purses ∧
      (selected.map RawIndexedPurse.toLocated :
        Multiset (LocatedPurse String)) = cover.selectedBefore := by
  have covered := cover.selectedBefore_le_activePurses available_le
  rw [← RawCostConfig.purses_map_toLocated] at covered
  exact List.exists_sublist_map_coe_eq_of_le_map
    RawIndexedPurse.toLocated config.purses cover.selectedBefore covered

/-- Head measure used only after active-purse occurrence recovery. -/
def LocatedPurse.headSpend (purse : LocatedPurse String) : CostSig String :=
  match purse.stack with
  | .empty => 0
  | .cons head _ => head

theorem LocatedTokenCover.selectedBefore_headSpend_eq_demand
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual) :
    (cover.selectedBefore.map LocatedPurse.headSpend).sum = demand := by
  rw [LocatedTokenCover.selectedBefore, Multiset.map_map]
  simpa [LocatedPurse.headSpend, Function.comp_def] using cover.demand_eq.symm

theorem LocatedTokenCover.selectedBefore_exposeTail_eq_selectedAfter
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual) :
    cover.selectedBefore.map LocatedPurse.exposeTail = cover.selectedAfter := by
  rw [LocatedTokenCover.selectedBefore, LocatedTokenCover.selectedAfter,
    Multiset.map_map]
  rfl

theorem rawSelectedSpend_eq_toLocated_headSpend
    (selected : List RawSelectedPurse) :
    rawSelectedSpend selected =
      ((selected.map RawIndexedPurse.toLocated :
          Multiset (LocatedPurse String)).map LocatedPurse.headSpend).sum := by
  simp [rawSelectedSpend, RawIndexedPurse.toLocated,
    LocatedPurse.headSpend, RawCostSig.toMultiset, decodeCostSig,
    Function.comp_def]

/-- Recovered purse occurrences spend the declarative demand exactly. -/
theorem rawSelectedSpend_eq_demand
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    {selected : List RawSelectedPurse}
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore) :
    rawSelectedSpend selected = demand := by
  rw [rawSelectedSpend_eq_toLocated_headSpend, selected_eq]
  exact cover.selectedBefore_headSpend_eq_demand

theorem decodedSelectedTerms_eq_selectedBefore_components
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    {selected : List RawSelectedPurse}
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore) :
    (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
        Multiset (CostTerm String)) =
      LocatedPurse.configComponents cover.selectedBefore := by
  change (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
      Multiset (CostTerm String)) =
    cover.selectedBefore.map LocatedPurse.toTerm
  calc
    (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
        Multiset (CostTerm String)) =
        (selected.map RawIndexedPurse.toLocated :
          Multiset (LocatedPurse String)).map LocatedPurse.toTerm := by
      simp [Function.comp_def]
    _ = cover.selectedBefore.map LocatedPurse.toTerm := by rw [selected_eq]

@[simp]
theorem RawCostConfig.purses_map_toTerm (config : RawCostConfig) :
    config.purses.map RawIndexedPurse.toTerm =
      config.filter RawCostTerm.isActivePurse :=
  collectPursesAux_map_toTerm config 0

theorem collectPursesAux_indices_sublist :
    ∀ (config : RawCostConfig) (start : Nat),
      List.Sublist
        ((collectPursesAux config start).map RawIndexedPurse.index)
        ((config.zipIdx start).map Prod.snd)
  | [], _ => .slnil
  | term :: rest, start => by
      have tail := collectPursesAux_indices_sublist rest (start + 1)
      cases term with
      | purse location stack =>
          cases stack with
          | nil =>
              simpa [collectPursesAux, List.zipIdx] using tail.cons start
          | cons head stackTail =>
              simpa [collectPursesAux, List.zipIdx] using tail.cons_cons start
      | nil => simpa [collectPursesAux, List.zipIdx] using tail.cons start
      | signed proc sig =>
          simpa [collectPursesAux, List.zipIdx] using tail.cons start
      | par left right =>
          simpa [collectPursesAux, List.zipIdx] using tail.cons start
      | drop name =>
          simpa [collectPursesAux, List.zipIdx] using tail.cons start

theorem RawCostConfig.purse_indices_nodup (config : RawCostConfig) :
    (config.purses.map RawIndexedPurse.index).Nodup :=
  (collectPursesAux_indices_sublist config 0).nodup
    (List.nodup_zipIdx_map_snd config)

theorem selectedPurse_indices_nodup
    {config : RawCostConfig} {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses) :
    (selected.map RawIndexedPurse.index).Nodup :=
  (selected_source.map RawIndexedPurse.index).nodup
    (RawCostConfig.purse_indices_nodup config)

/-- A source-order purse sublist is an occurrence submultiset of the active
purse partition. -/
theorem selectedPurseTerms_le_active
    {config : RawCostConfig} {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses) :
    (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) ≤
      (config.filter RawCostTerm.isActivePurse : Multiset RawCostTerm) := by
  rw [← RawCostConfig.purses_map_toTerm]
  rw [Multiset.coe_le]
  exact (selected_source.map RawIndexedPurse.toTerm).subperm

/-- Two distinct present occurrences fit simultaneously in a multiset. -/
theorem singleton_add_singleton_le_of_ne {Alpha : Type} [DecidableEq Alpha]
    {left right : Alpha} {source : Multiset Alpha}
    (different : left ≠ right) (left_mem : left ∈ source)
    (right_mem : right ∈ source) :
    {left} + {right} ≤ source := by
  rw [Multiset.singleton_add]
  apply (Multiset.cons_le_of_notMem (by simp [different])).2
  exact ⟨left_mem, Multiset.singleton_le.mpr right_mem⟩

/-- Active and non-active source occurrences form an exact partition. -/
theorem activePurse_add_nonActive (config : RawCostConfig) :
    (config.filter RawCostTerm.isActivePurse : Multiset RawCostTerm) +
        (config.filter (fun term => !term.isActivePurse) :
          Multiset RawCostTerm) =
      (config : Multiset RawCostTerm) := by
  simpa using Multiset.filter_add_not
    (fun term : RawCostTerm => term.isActivePurse = true)
    (config : Multiset RawCostTerm)

/-! ## Canonical runtime configurations -/

/-- The executable collector receives fixed-point components in key order. -/
structure RawCostConfig.Canonical (config : RawCostConfig) : Prop where
  components : config.Forall RawCostTerm.Normalized
  ordered : KeySorted RawCostTerm.key config

theorem RawCostTerm.normalizeConfig_canonical (term : RawCostTerm) :
    term.normalizeConfig.Canonical :=
  ⟨RawCostTerm.normalizeConfig_forall_Normalized term,
    RawCostTerm.normalizeConfig_keySorted term⟩

/-- Canonicality data retained by an active purse occurrence. -/
structure RawIndexedPurse.Normalized (purse : RawIndexedPurse) : Prop where
  location : purse.location.normalize = purse.location
  head : purse.head.normalize = purse.head
  tail : purse.tail.map RawCostSig.normalize = purse.tail

theorem collectPursesAux_forall_normalized :
    ∀ (config : RawCostConfig) (start : Nat),
      config.Forall RawCostTerm.Normalized →
      (collectPursesAux config start).Forall RawIndexedPurse.Normalized
  | [], _, _ => by simp
  | term :: rest, start, canonical => by
      obtain ⟨term_fixed, rest_fixed⟩ :=
        (List.forall_cons RawCostTerm.Normalized term rest).mp canonical
      have tail_result :=
        collectPursesAux_forall_normalized rest (start + 1) rest_fixed
      cases term with
      | purse location stack =>
          cases stack with
          | nil => simpa [collectPursesAux] using tail_result
          | cons head tail =>
              change (RawCostTerm.purse location (head :: tail)).normalize =
                RawCostTerm.purse location (head :: tail) at term_fixed
              have purse_fixed := term_fixed
              simp only [RawCostTerm.normalize] at purse_fixed
              have parts := RawCostTerm.purse.inj purse_fixed
              have stack_parts := List.cons.inj parts.2
              exact (List.forall_cons RawIndexedPurse.Normalized
                ⟨start, location, head, tail⟩ _).mpr
                ⟨⟨parts.1, stack_parts.1, stack_parts.2⟩, tail_result⟩
      | nil => simpa [collectPursesAux] using tail_result
      | signed proc sig => simpa [collectPursesAux] using tail_result
      | par left right => simpa [collectPursesAux] using tail_result
      | drop name => simpa [collectPursesAux] using tail_result

theorem RawCostConfig.purses_forall_normalized
    {config : RawCostConfig} (canonical : config.Canonical) :
    config.purses.Forall RawIndexedPurse.Normalized :=
  collectPursesAux_forall_normalized config 0 canonical.components

theorem selectedPurses_forall_normalized
    {config : RawCostConfig} {selected : List RawSelectedPurse}
    (canonical : config.Canonical)
    (selected_source : selected.Sublist config.purses) :
    selected.Forall RawIndexedPurse.Normalized := by
  rw [List.forall_iff_forall_mem]
  intro purse member
  exact List.forall_iff_forall_mem.mp
    (RawCostConfig.purses_forall_normalized canonical) purse
    (selected_source.mem member)

theorem selectedPurses_location_eq
    {config : RawCostConfig} {step : RawRuntimeStep}
    (canonical : config.Canonical) (funding : step.FundingValidFor config)
    (location_fixed : step.location.normalize = step.location) :
    ∀ purse ∈ step.selectedPurses, purse.location = step.location := by
  intro purse member
  have selected_normalized := selectedPurses_forall_normalized canonical
    funding.selected_from_config
  have purse_fixed := List.forall_iff_forall_mem.mp selected_normalized purse member
  calc
    purse.location = purse.location.normalize := purse_fixed.location.symm
    _ = step.location.normalize := funding.selected_at_location purse member
    _ = step.location := location_fixed

theorem recoveredSelected_location_eq
    {config : RawCostConfig} (canonical : config.Canonical)
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses)
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore)
    {rawLocation : RawCostName}
    (raw_location_fixed : rawLocation.normalize = rawLocation)
    (decoded_location : decodeCostName rawLocation = location) :
    ∀ purse ∈ selected, purse.location = rawLocation := by
  intro purse purse_mem
  have purse_normalized := List.forall_iff_forall_mem.mp
    (selectedPurses_forall_normalized canonical selected_source) purse purse_mem
  have purse_canonical : purse.location.EncodingCanonical := by
    rw [← purse_normalized.location]
    exact RawCostName.normalize_encodingCanonical purse.location
  have raw_location_canonical : rawLocation.EncodingCanonical := by
    rw [← raw_location_fixed]
    exact RawCostName.normalize_encodingCanonical rawLocation
  have mapped_mem : purse.toLocated ∈
      (selected.map RawIndexedPurse.toLocated :
        Multiset (LocatedPurse String)) := by
    simpa using List.mem_map.mpr ⟨purse, purse_mem, rfl⟩
  rw [selected_eq] at mapped_mem
  have purse_location := cover.selected_before_location mapped_mem
  change decodeCostName purse.location = location at purse_location
  exact RawCostName.decode_injective_of_encodingCanonical
    purse_canonical raw_location_canonical
    (purse_location.trans decoded_location.symm)

theorem recoveredSelected_sublist_matching
    {config : RawCostConfig} (canonical : config.Canonical)
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses)
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore)
    {rawLocation : RawCostName}
    (raw_location_fixed : rawLocation.normalize = rawLocation)
    (decoded_location : decodeCostName rawLocation = location) :
    selected.Sublist (matchingPurses rawLocation config.purses) := by
  have located := recoveredSelected_location_eq canonical cover selected_source
    selected_eq raw_location_fixed decoded_location
  have filtered := selected_source.filter fun purse =>
    decide (purse.location.normalize = rawLocation.normalize)
  have selected_filter :
      selected.filter (fun purse =>
        decide (purse.location.normalize = rawLocation.normalize)) = selected := by
    apply List.filter_eq_self.mpr
    intro purse purse_mem
    simp [located purse purse_mem]
  rw [selected_filter] at filtered
  simpa [matchingPurses] using filtered

/-! ## Sort-correct decoding of COMM substitution -/

mutual
  @[simp]
  theorem decodeCostName_lift (amount cutoff : Nat) :
      ∀ name : RawCostName,
        decodeCostName (RawCostName.lift amount cutoff name) =
          CostName.lift amount cutoff (decodeCostName name)
    | .bvar index => by
        simp only [RawCostName.lift, CostName.lift, decodeCostName]
        split <;> rfl
    | .quote _ => rfl
    | .signature _ => rfl

  @[simp]
  theorem decodeCostProc_lift (amount cutoff : Nat) :
      ∀ proc : RawCostProc,
        decodeCostProc (RawCostProc.lift amount cutoff proc) =
          CostProc.lift amount cutoff (decodeCostProc proc)
    | .nil => rfl
    | .par left right => by
        simp only [decodeCostProc, CostProc.lift]
        rw [decodeCostProc_lift amount cutoff left,
          decodeCostProc_lift amount cutoff right]
    | .send channel payload => by
        simp only [decodeCostProc, CostProc.lift]
        rw [decodeCostName_lift amount cutoff channel,
          decodeCostTerm_lift amount cutoff payload]
    | .recv channel body => by
        simp only [decodeCostProc, CostProc.lift]
        rw [decodeCostName_lift amount cutoff channel,
          decodeCostTerm_lift amount (cutoff + 1) body]

  @[simp]
  theorem decodeCostTerm_lift (amount cutoff : Nat) :
      ∀ term : RawCostTerm,
        decodeCostTerm (RawCostTerm.lift amount cutoff term) =
          CostTerm.lift amount cutoff (decodeCostTerm term)
    | .nil => rfl
    | .signed proc sig => by
        simp only [decodeCostTerm, CostTerm.lift]
        rw [decodeCostProc_lift amount cutoff proc]
    | .par left right => by
        simp only [decodeCostTerm, CostTerm.lift]
        rw [decodeCostTerm_lift amount cutoff left,
          decodeCostTerm_lift amount cutoff right]
    | .drop name => by
        simp only [decodeCostTerm, CostTerm.lift]
        rw [decodeCostName_lift amount cutoff name]
    | .purse location stack => by
        simp only [decodeCostTerm, CostTerm.lift]
        rw [decodeCostName_lift amount cutoff location]
end

mutual
  @[simp]
  theorem decodeCostName_substitute (replacement : RawCostTerm) (depth : Nat)
      : ∀ name : RawCostName,
        decodeCostName (RawCostName.substitute replacement depth name) =
          CostName.substitute (decodeCostTerm replacement) depth
            (decodeCostName name)
    | .bvar index => by
        simp only [RawCostName.substitute, CostName.substitute, decodeCostName]
        split
        · change CostName.quote (decodeCostTerm
            (RawCostTerm.lift depth 0 replacement)) = _
          rw [decodeCostTerm_lift]
        · split <;> rfl
    | .quote _ => rfl
    | .signature _ => rfl

  @[simp]
  theorem decodeCostProc_substitute (replacement : RawCostTerm) (depth : Nat)
      : ∀ proc : RawCostProc,
        decodeCostProc (RawCostProc.substitute replacement depth proc) =
          CostProc.substitute (decodeCostTerm replacement) depth
            (decodeCostProc proc)
    | .nil => rfl
    | .par left right => by
        simp only [decodeCostProc, CostProc.substitute]
        rw [decodeCostProc_substitute replacement depth left,
          decodeCostProc_substitute replacement depth right]
    | .send channel payload => by
        simp only [decodeCostProc, CostProc.substitute]
        rw [decodeCostName_substitute replacement depth channel,
          decodeCostTerm_substitute replacement depth payload]
    | .recv channel body => by
        simp only [decodeCostProc, CostProc.substitute]
        rw [decodeCostName_substitute replacement depth channel,
          decodeCostTerm_substitute replacement (depth + 1) body]

  @[simp]
  theorem decodeCostTerm_substitute (replacement : RawCostTerm) (depth : Nat)
      : ∀ term : RawCostTerm,
        decodeCostTerm (RawCostTerm.substitute replacement depth term) =
          CostTerm.substitute (decodeCostTerm replacement) depth
            (decodeCostTerm term)
    | .nil => rfl
    | .signed proc sig => by
        simp only [decodeCostTerm, CostTerm.substitute]
        rw [decodeCostProc_substitute replacement depth proc]
    | .par left right => by
        simp only [decodeCostTerm, CostTerm.substitute]
        rw [decodeCostTerm_substitute replacement depth left,
          decodeCostTerm_substitute replacement depth right]
    | .drop name => by
        cases name with
        | bvar index =>
            simp only [RawCostTerm.substitute, CostTerm.substitute,
              decodeCostTerm, decodeCostName]
            split
            · rw [decodeCostTerm_lift]
            · split <;> rfl
        | quote term => rfl
        | signature sig => rfl
    | .purse location stack => by
        simp only [decodeCostTerm, CostTerm.substitute]
        rw [decodeCostName_substitute replacement depth location]
end

@[simp]
theorem decodeCostTerm_commSubst (body payload : RawCostTerm) :
    decodeCostTerm (RawCostTerm.commSubst body payload) =
      CostTerm.commSubst (decodeCostTerm body) (decodeCostTerm payload) := by
  simp [RawCostTerm.commSubst, CostTerm.commSubst]

/-! ## Decoding exact located covers -/

theorem decodeCostSig_runtimeValid {sig : RawCostSig}
    (valid : sig.valid = true) : (decodeCostSig sig).RuntimeValid := by
  have nonzero := (RawCostSig.valid_iff_toMultiset_ne_zero sig).mp valid
  exact nonzero

/-- Decode selected executable purse occurrences while retaining their
nonempty-head evidence. -/
def decodeSelectedHeads : (selected : List RawSelectedPurse) →
    selected.Forall RawIndexedPurse.WellFormed →
    List (SelectedPurseHead String)
  | [], _ => []
  | purse :: rest, valid =>
      let valid' := (List.forall_cons RawIndexedPurse.WellFormed purse rest).mp valid
      { head := decodeCostSig purse.head
        tail := decodeCostStack purse.tail
        head_valid := decodeCostSig_runtimeValid valid'.1.head } ::
      decodeSelectedHeads rest valid'.2

@[simp]
theorem decodeSelectedHeads_heads :
    ∀ (selected : List RawSelectedPurse)
      (valid : selected.Forall RawIndexedPurse.WellFormed),
      (decodeSelectedHeads selected valid).map SelectedPurseHead.head =
        selected.map (decodeCostSig ∘ RawIndexedPurse.head)
  | [], _ => rfl
  | purse :: rest, valid => by
      have valid' :=
        (List.forall_cons RawIndexedPurse.WellFormed purse rest).mp valid
      simp [decodeSelectedHeads, decodeSelectedHeads_heads rest valid'.2]

@[simp]
theorem decodeSelectedHeads_tails :
    ∀ (selected : List RawSelectedPurse)
      (valid : selected.Forall RawIndexedPurse.WellFormed),
      (decodeSelectedHeads selected valid).map SelectedPurseHead.tail =
        selected.map (decodeCostStack ∘ RawIndexedPurse.tail)
  | [], _ => rfl
  | purse :: rest, valid => by
      have valid' :=
        (List.forall_cons RawIndexedPurse.WellFormed purse rest).mp valid
      simp [decodeSelectedHeads, decodeSelectedHeads_tails rest valid'.2]

def decodedSelectedAvailable (location : RawCostName)
    (selected : List RawSelectedPurse)
    (valid : selected.Forall RawIndexedPurse.WellFormed) :
    Multiset (LocatedPurse String) :=
  (↑(decodeSelectedHeads selected valid) :
      Multiset (SelectedPurseHead String)).map fun choice =>
    ⟨decodeCostName location, .cons choice.head choice.tail⟩

def decodedSelectedResidual (location : RawCostName)
    (selected : List RawSelectedPurse)
    (valid : selected.Forall RawIndexedPurse.WellFormed) :
    Multiset (LocatedPurse String) :=
  (↑(decodeSelectedHeads selected valid) :
      Multiset (SelectedPurseHead String)).map fun choice =>
    ⟨decodeCostName location, choice.tail⟩

/-- The selected executable heads, viewed as a declarative exact cover at
the candidate's canonical interaction location. -/
def decodedSelectedCover (location : RawCostName) (demand : RawCostSig)
    (selected : List RawSelectedPurse)
    (valid : selected.Forall RawIndexedPurse.WellFormed)
    (exact : rawSelectedSpend selected = demand.toMultiset) :
    LocatedTokenCover (decodeCostName location) (decodeCostSig demand)
      (decodedSelectedAvailable location selected valid)
      (decodedSelectedResidual location selected valid) where
  chosen := decodeSelectedHeads selected valid
  untouched := 0
  available_eq := by simp [decodedSelectedAvailable]
  residual_eq := by simp [decodedSelectedResidual]
  demand_eq := by
    rw [Multiset.map_coe, Multiset.sum_coe]
    rw [decodeSelectedHeads_heads]
    change (demand : Multiset String) =
      (selected.map fun purse => (purse.head : Multiset String)).sum
    simpa [rawSelectedSpend, RawCostSig.toMultiset] using exact.symm

def RawIndexedPurse.toTailTerm (purse : RawIndexedPurse) : RawCostTerm :=
  .purse purse.location purse.tail

@[simp]
theorem RawIndexedPurse.decode_toTailTerm (purse : RawIndexedPurse) :
    decodeCostTerm purse.toTailTerm = purse.toLocated.exposeTail.toTerm := by
  simp [RawIndexedPurse.toTailTerm, RawIndexedPurse.toLocated,
    LocatedPurse.exposeTail, LocatedPurse.toTerm, decodeCostTerm]

theorem decodedSelectedTailTerms_eq_selectedAfter_components
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    {selected : List RawSelectedPurse}
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore) :
    (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
        Multiset (CostTerm String)) =
      LocatedPurse.configComponents cover.selectedAfter := by
  change (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
      Multiset (CostTerm String)) =
    cover.selectedAfter.map LocatedPurse.toTerm
  calc
    (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
        Multiset (CostTerm String)) =
        ((selected.map RawIndexedPurse.toLocated :
          Multiset (LocatedPurse String)).map LocatedPurse.exposeTail).map
            LocatedPurse.toTerm := by
      simp [Function.comp_def]
    _ = (cover.selectedBefore.map LocatedPurse.exposeTail).map
          LocatedPurse.toTerm := by rw [selected_eq]
    _ = cover.selectedAfter.map LocatedPurse.toTerm := by
      rw [cover.selectedBefore_exposeTail_eq_selectedAfter]

theorem decodedSelectedAvailable_components :
    ∀ (location : RawCostName) (selected : List RawSelectedPurse)
      (valid : selected.Forall RawIndexedPurse.WellFormed),
      (∀ purse ∈ selected, purse.location = location) →
      LocatedPurse.configComponents
          (decodedSelectedAvailable location selected valid) =
        (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
          Multiset (CostTerm String))
  | _, [], _, _ => by
      simp [decodedSelectedAvailable, LocatedPurse.configComponents,
        decodeSelectedHeads]
  | location, purse :: rest, valid, located => by
      have valid' :=
        (List.forall_cons RawIndexedPurse.WellFormed purse rest).mp valid
      have purse_location := located purse (by simp)
      have rest_located : ∀ candidate ∈ rest, candidate.location = location := by
        intro candidate member
        exact located candidate (by simp [member])
      rw [show valid = (List.forall_cons RawIndexedPurse.WellFormed purse rest).mpr
        valid' by rfl]
      change ({CostTerm.purse (decodeCostName location)
            (.cons (decodeCostSig purse.head) (decodeCostStack purse.tail))} :
          Multiset (CostTerm String)) +
          LocatedPurse.configComponents
            (decodedSelectedAvailable location rest valid'.2) =
        {decodeCostTerm purse.toTerm} +
          (rest.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
            Multiset (CostTerm String))
      rw [decodedSelectedAvailable_components location rest valid'.2 rest_located]
      simp [RawIndexedPurse.toTerm, decodeCostTerm, decodeCostStack,
        purse_location]

theorem decodedSelectedResidual_components :
    ∀ (location : RawCostName) (selected : List RawSelectedPurse)
      (valid : selected.Forall RawIndexedPurse.WellFormed),
      (∀ purse ∈ selected, purse.location = location) →
      LocatedPurse.configComponents
          (decodedSelectedResidual location selected valid) =
        (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
          Multiset (CostTerm String))
  | _, [], _, _ => by
      simp [decodedSelectedResidual, LocatedPurse.configComponents,
        decodeSelectedHeads]
  | location, purse :: rest, valid, located => by
      have valid' :=
        (List.forall_cons RawIndexedPurse.WellFormed purse rest).mp valid
      have purse_location := located purse (by simp)
      have rest_located : ∀ candidate ∈ rest, candidate.location = location := by
        intro candidate member
        exact located candidate (by simp [member])
      rw [show valid = (List.forall_cons RawIndexedPurse.WellFormed purse rest).mpr
        valid' by rfl]
      change ({CostTerm.purse (decodeCostName location)
            (decodeCostStack purse.tail)} : Multiset (CostTerm String)) +
          LocatedPurse.configComponents
            (decodedSelectedResidual location rest valid'.2) =
        {decodeCostTerm purse.toTailTerm} +
          (rest.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String))
      rw [decodedSelectedResidual_components location rest valid'.2 rest_located]
      simp [RawIndexedPurse.toTailTerm, decodeCostTerm, purse_location]

/-! ## Occurrence provenance of the raw collectors -/

theorem mem_collectPursesAux_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {purse : RawIndexedPurse},
      purse ∈ collectPursesAux config start →
        (RawCostTerm.purse purse.location (purse.head :: purse.tail), purse.index) ∈
          config.zipIdx start
  | [], _, _, member => by simp [collectPursesAux] at member
  | term :: rest, start, purse, member => by
      have lift_tail {entry : RawCostTerm × Nat}
          (tail_member : entry ∈ rest.zipIdx (start + 1)) :
          entry ∈ (term :: rest).zipIdx start := by
        simp [List.zipIdx, tail_member]
      cases term with
      | purse location stack =>
          cases stack with
          | nil =>
              exact lift_tail
                (mem_collectPursesAux_zipIdx
                  (by simpa [collectPursesAux] using member))
          | cons head tail =>
              simp only [collectPursesAux, List.mem_cons] at member
              rcases member with rfl | member
              · simp [List.zipIdx]
              · exact lift_tail (mem_collectPursesAux_zipIdx member)
      | nil =>
          exact lift_tail
            (mem_collectPursesAux_zipIdx
              (by simpa [collectPursesAux] using member))
      | signed proc sig =>
          exact lift_tail
            (mem_collectPursesAux_zipIdx
              (by simpa [collectPursesAux] using member))
      | par left right =>
          exact lift_tail
            (mem_collectPursesAux_zipIdx
              (by simpa [collectPursesAux] using member))
      | drop name =>
          exact lift_tail
            (mem_collectPursesAux_zipIdx
              (by simpa [collectPursesAux] using member))

theorem wholeAt?_index {index : Nat} {term : RawCostTerm}
    {redex : RawWholeRedex} (found : wholeAt? index term = some redex) :
    redex.index = index := by
  cases term with
  | signed proc sig =>
      cases proc with
      | par left right =>
          cases left <;> cases right <;> simp [wholeAt?] at found
          all_goals aesop
      | _ => simp [wholeAt?] at found
  | _ => simp [wholeAt?] at found

theorem recvAt?_index {index : Nat} {term : RawCostTerm}
    {endpoint : RawRecvEndpoint} (found : recvAt? index term = some endpoint) :
    endpoint.index = index := by
  cases term <;> simp [recvAt?] at found
  rename_i proc sig
  cases proc <;> simp at found
  all_goals subst endpoint; rfl

theorem sendAt?_index {index : Nat} {term : RawCostTerm}
    {endpoint : RawSendEndpoint} (found : sendAt? index term = some endpoint) :
    endpoint.index = index := by
  cases term <;> simp [sendAt?] at found
  rename_i proc sig
  cases proc <;> simp at found
  all_goals subst endpoint; rfl

theorem mem_collectWholesAux_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {redex : RawWholeRedex},
      redex ∈ collectWholesAux config start →
        ∃ term,
          (term, redex.index) ∈ config.zipIdx start ∧
          wholeAt? redex.index term = some redex
  | [], _, _, member => by simp [collectWholesAux] at member
  | term :: rest, start, redex, member => by
      cases found : wholeAt? start term with
      | none =>
          obtain ⟨source, source_member, source_found⟩ :=
            mem_collectWholesAux_zipIdx
              (by simpa [collectWholesAux, found] using member)
          exact ⟨source, by simp [List.zipIdx, source_member], source_found⟩
      | some headRedex =>
          have alternatives : redex = headRedex ∨
              redex ∈ collectWholesAux rest (start + 1) := by
            simpa [collectWholesAux, found] using member
          rcases alternatives with rfl | tail_member
          · have index_eq := wholeAt?_index found
            exact ⟨term, by simp [List.zipIdx, index_eq], by simpa [index_eq] using found⟩
          · obtain ⟨source, source_member, source_found⟩ :=
              mem_collectWholesAux_zipIdx tail_member
            exact ⟨source, by simp [List.zipIdx, source_member], source_found⟩

theorem mem_collectRecvsAux_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {endpoint : RawRecvEndpoint},
      endpoint ∈ collectRecvsAux config start →
        ∃ term,
          (term, endpoint.index) ∈ config.zipIdx start ∧
          recvAt? endpoint.index term = some endpoint
  | [], _, _, member => by simp [collectRecvsAux] at member
  | term :: rest, start, endpoint, member => by
      cases found : recvAt? start term with
      | none =>
          obtain ⟨source, source_member, source_found⟩ :=
            mem_collectRecvsAux_zipIdx
              (by simpa [collectRecvsAux, found] using member)
          exact ⟨source, by simp [List.zipIdx, source_member], source_found⟩
      | some headEndpoint =>
          have alternatives : endpoint = headEndpoint ∨
              endpoint ∈ collectRecvsAux rest (start + 1) := by
            simpa [collectRecvsAux, found] using member
          rcases alternatives with rfl | tail_member
          · have index_eq := recvAt?_index found
            exact ⟨term, by simp [List.zipIdx, index_eq], by simpa [index_eq] using found⟩
          · obtain ⟨source, source_member, source_found⟩ :=
              mem_collectRecvsAux_zipIdx tail_member
            exact ⟨source, by simp [List.zipIdx, source_member], source_found⟩

theorem mem_collectSendsAux_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {endpoint : RawSendEndpoint},
      endpoint ∈ collectSendsAux config start →
        ∃ term,
          (term, endpoint.index) ∈ config.zipIdx start ∧
          sendAt? endpoint.index term = some endpoint
  | [], _, _, member => by simp [collectSendsAux] at member
  | term :: rest, start, endpoint, member => by
      cases found : sendAt? start term with
      | none =>
          obtain ⟨source, source_member, source_found⟩ :=
            mem_collectSendsAux_zipIdx
              (by simpa [collectSendsAux, found] using member)
          exact ⟨source, by simp [List.zipIdx, source_member], source_found⟩
      | some headEndpoint =>
          have alternatives : endpoint = headEndpoint ∨
              endpoint ∈ collectSendsAux rest (start + 1) := by
            simpa [collectSendsAux, found] using member
          rcases alternatives with rfl | tail_member
          · have index_eq := sendAt?_index found
            exact ⟨term, by simp [List.zipIdx, index_eq], by simpa [index_eq] using found⟩
          · obtain ⟨source, source_member, source_found⟩ :=
              mem_collectSendsAux_zipIdx tail_member
            exact ⟨source, by simp [List.zipIdx, source_member], source_found⟩

theorem mem_collectWholesAux_of_mem_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {source : RawCostTerm}
      {index : Nat} {redex : RawWholeRedex},
      (source, index) ∈ config.zipIdx start →
      wholeAt? index source = some redex →
      redex ∈ collectWholesAux config start
  | [], _, _, _, _, member, _ => by simp [List.zipIdx] at member
  | term :: rest, start, source, index, redex, member, found => by
      simp only [List.zipIdx, List.mem_cons] at member
      rcases member with same | tail_member
      · have term_eq : term = source := (congrArg Prod.fst same).symm
        have index_eq : start = index := (congrArg Prod.snd same).symm
        subst source
        subst index
        simp [collectWholesAux, found]
      · have tail_result := mem_collectWholesAux_of_mem_zipIdx
          tail_member found
        cases head_found : wholeAt? start term with
        | none => simpa [collectWholesAux, head_found] using tail_result
        | some head => simp [collectWholesAux, head_found, tail_result]

theorem mem_collectRecvsAux_of_mem_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {source : RawCostTerm}
      {index : Nat} {recv : RawRecvEndpoint},
      (source, index) ∈ config.zipIdx start →
      recvAt? index source = some recv →
      recv ∈ collectRecvsAux config start
  | [], _, _, _, _, member, _ => by simp [List.zipIdx] at member
  | term :: rest, start, source, index, recv, member, found => by
      simp only [List.zipIdx, List.mem_cons] at member
      rcases member with same | tail_member
      · have term_eq : term = source := (congrArg Prod.fst same).symm
        have index_eq : start = index := (congrArg Prod.snd same).symm
        subst source
        subst index
        simp [collectRecvsAux, found]
      · have tail_result := mem_collectRecvsAux_of_mem_zipIdx
          tail_member found
        cases head_found : recvAt? start term with
        | none => simpa [collectRecvsAux, head_found] using tail_result
        | some head => simp [collectRecvsAux, head_found, tail_result]

theorem mem_collectSendsAux_of_mem_zipIdx :
    ∀ {config : RawCostConfig} {start : Nat} {source : RawCostTerm}
      {index : Nat} {send : RawSendEndpoint},
      (source, index) ∈ config.zipIdx start →
      sendAt? index source = some send →
      send ∈ collectSendsAux config start
  | [], _, _, _, _, member, _ => by simp [List.zipIdx] at member
  | term :: rest, start, source, index, send, member, found => by
      simp only [List.zipIdx, List.mem_cons] at member
      rcases member with same | tail_member
      · have term_eq : term = source := (congrArg Prod.fst same).symm
        have index_eq : start = index := (congrArg Prod.snd same).symm
        subst source
        subst index
        simp [collectSendsAux, found]
      · have tail_result := mem_collectSendsAux_of_mem_zipIdx
          tail_member found
        cases head_found : sendAt? start term with
        | none => simpa [collectSendsAux, head_found] using tail_result
        | some head => simp [collectSendsAux, head_found, tail_result]

/-! ## Candidate origins and canonical locations -/

theorem wholeAt?_location_normalized {index : Nat} {term : RawCostTerm}
    {redex : RawWholeRedex} (found : wholeAt? index term = some redex) :
    redex.location.normalize = redex.location := by
  cases term with
  | signed proc sig =>
      cases proc with
      | par left right =>
          cases left <;> cases right <;> simp [wholeAt?] at found
          all_goals aesop
      | _ => simp [wholeAt?] at found
  | _ => simp [wholeAt?] at found

theorem recvAt?_location_normalized {index : Nat} {term : RawCostTerm}
    {endpoint : RawRecvEndpoint} (found : recvAt? index term = some endpoint) :
    endpoint.location.normalize = endpoint.location := by
  cases term <;> simp [recvAt?] at found
  rename_i proc sig
  cases proc <;> simp at found
  all_goals subst endpoint; simp

theorem sendAt?_location_normalized {index : Nat} {term : RawCostTerm}
    {endpoint : RawSendEndpoint} (found : sendAt? index term = some endpoint) :
    endpoint.location.normalize = endpoint.location := by
  cases term <;> simp [sendAt?] at found
  rename_i proc sig
  cases proc <;> simp at found
  all_goals subst endpoint; simp

/-- Every raw candidate retains a concrete source occurrence for each
participant collector row. -/
theorem runtimeCostCandidatesFromConfig_origin
    {config : RawCostConfig} {step : RawRuntimeStep}
    (member : step ∈ runtimeCostCandidatesFromConfig config) :
    (∃ redex source,
        redex ∈ config.wholeRedexes ∧
        (source, redex.index) ∈ config.zipIdx ∧
        wholeAt? redex.index source = some redex ∧
        step ∈ wholeCandidates config config.purses redex) ∨
      (∃ recv send recvSource sendSource,
        recv ∈ config.recvEndpoints ∧
        send ∈ config.sendEndpoints ∧
        (recvSource, recv.index) ∈ config.zipIdx ∧
        (sendSource, send.index) ∈ config.zipIdx ∧
        recvAt? recv.index recvSource = some recv ∧
        sendAt? send.index sendSource = some send ∧
        step ∈ splitCandidates config config.purses recv send) := by
  simp only [runtimeCostCandidatesFromConfig, List.mem_append] at member
  rcases member with whole | split
  · obtain ⟨redex, redex_member, step_member⟩ := List.mem_flatMap.mp whole
    obtain ⟨source, source_member, source_found⟩ :=
      mem_collectWholesAux_zipIdx redex_member
    exact .inl ⟨redex, source, redex_member, source_member,
      source_found, step_member⟩
  · obtain ⟨recv, recv_member, send_branch⟩ := List.mem_flatMap.mp split
    obtain ⟨send, send_member, step_member⟩ :=
      List.mem_flatMap.mp send_branch
    obtain ⟨recvSource, recvSource_member, recv_found⟩ :=
      mem_collectRecvsAux_zipIdx recv_member
    obtain ⟨sendSource, sendSource_member, send_found⟩ :=
      mem_collectSendsAux_zipIdx send_member
    exact .inr ⟨recv, send, recvSource, sendSource, recv_member,
      send_member, recvSource_member, sendSource_member, recv_found,
      send_found, step_member⟩

theorem runtimeCostCandidatesFromConfig_location_normalized
    {config : RawCostConfig} {step : RawRuntimeStep}
    (member : step ∈ runtimeCostCandidatesFromConfig config) :
    step.location.normalize = step.location := by
  rcases runtimeCostCandidatesFromConfig_origin member with
    ⟨redex, source, _, _, found, step_member⟩ |
      ⟨recv, send, recvSource, sendSource, _, _, _, _, recv_found,
        send_found, step_member⟩
  · simp only [wholeCandidates] at step_member
    obtain ⟨cover, _, rfl⟩ := List.mem_map.mp step_member
    exact wholeAt?_location_normalized found
  · unfold splitCandidates at step_member
    split at step_member
    · obtain ⟨cover, _, rfl⟩ := List.mem_map.mp step_member
      exact recvAt?_location_normalized recv_found
    · contradiction

def selectedSourceEntries (selected : List RawSelectedPurse) :
    List (RawCostTerm × Nat) :=
  selected.map fun purse => (purse.toTerm, purse.index)

@[simp]
theorem selectedSourceEntries_map_fst (selected : List RawSelectedPurse) :
    (selectedSourceEntries selected).map Prod.fst =
      selected.map RawIndexedPurse.toTerm := by
  simp [selectedSourceEntries]

@[simp]
theorem selectedSourceEntries_map_snd (selected : List RawSelectedPurse) :
    (selectedSourceEntries selected).map Prod.snd =
      selected.map RawIndexedPurse.index := by
  simp [selectedSourceEntries]

theorem selectedSourceEntries_source
    {config : RawCostConfig} {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses) :
    ∀ entry ∈ selectedSourceEntries selected, entry ∈ config.zipIdx := by
  intro entry member
  obtain ⟨purse, purse_member, rfl⟩ := List.mem_map.mp member
  exact mem_collectPursesAux_zipIdx
    (selected_source.mem purse_member)

theorem zipIdx_eq_of_index_eq {config : RawCostConfig}
    {left right : RawCostTerm × Nat}
    (left_mem : left ∈ config.zipIdx) (right_mem : right ∈ config.zipIdx)
    (indices : left.2 = right.2) : left = right := by
  exact List.inj_on_of_nodup_map (List.nodup_zipIdx_map_snd config)
    left_mem right_mem indices

theorem whole_index_not_mem_selected
    {config : RawCostConfig} {redex : RawWholeRedex}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, redex.index) ∈ config.zipIdx)
    (found : wholeAt? redex.index source = some redex)
    (selected_source : selected.Sublist config.purses) :
    redex.index ∉ selected.map RawIndexedPurse.index := by
  intro member
  obtain ⟨purse, purse_member, purse_index⟩ := List.mem_map.mp member
  have purse_source := mem_collectPursesAux_zipIdx
    (selected_source.mem purse_member)
  have entries_eq := zipIdx_eq_of_index_eq source_mem purse_source purse_index.symm
  have source_eq : source = purse.toTerm := congrArg Prod.fst entries_eq
  rw [source_eq] at found
  simp [RawIndexedPurse.toTerm, wholeAt?] at found

theorem recv_index_not_mem_selected
    {config : RawCostConfig} {recv : RawRecvEndpoint}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, recv.index) ∈ config.zipIdx)
    (found : recvAt? recv.index source = some recv)
    (selected_source : selected.Sublist config.purses) :
    recv.index ∉ selected.map RawIndexedPurse.index := by
  intro member
  obtain ⟨purse, purse_member, purse_index⟩ := List.mem_map.mp member
  have purse_source := mem_collectPursesAux_zipIdx
    (selected_source.mem purse_member)
  have entries_eq := zipIdx_eq_of_index_eq source_mem purse_source purse_index.symm
  have source_eq : source = purse.toTerm := congrArg Prod.fst entries_eq
  rw [source_eq] at found
  simp [RawIndexedPurse.toTerm, recvAt?] at found

theorem send_index_not_mem_selected
    {config : RawCostConfig} {send : RawSendEndpoint}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, send.index) ∈ config.zipIdx)
    (found : sendAt? send.index source = some send)
    (selected_source : selected.Sublist config.purses) :
    send.index ∉ selected.map RawIndexedPurse.index := by
  intro member
  obtain ⟨purse, purse_member, purse_index⟩ := List.mem_map.mp member
  have purse_source := mem_collectPursesAux_zipIdx
    (selected_source.mem purse_member)
  have entries_eq := zipIdx_eq_of_index_eq source_mem purse_source purse_index.symm
  have source_eq : source = purse.toTerm := congrArg Prod.fst entries_eq
  rw [source_eq] at found
  simp [RawIndexedPurse.toTerm, sendAt?] at found

theorem recv_send_indices_ne
    {config : RawCostConfig} {recv : RawRecvEndpoint}
    {send : RawSendEndpoint} {recvSource sendSource : RawCostTerm}
    (recv_mem : (recvSource, recv.index) ∈ config.zipIdx)
    (send_mem : (sendSource, send.index) ∈ config.zipIdx)
    (recv_found : recvAt? recv.index recvSource = some recv)
    (send_found : sendAt? send.index sendSource = some send) :
    recv.index ≠ send.index := by
  intro indices
  have entries_eq := zipIdx_eq_of_index_eq recv_mem send_mem indices
  have sources_eq : recvSource = sendSource := congrArg Prod.fst entries_eq
  subst sendSource
  cases recvSource <;> simp [recvAt?, sendAt?] at recv_found send_found
  rename_i proc sig
  cases proc <;> simp at recv_found send_found

theorem wholePicked_indices_nodup
    {config : RawCostConfig} {redex : RawWholeRedex}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, redex.index) ∈ config.zipIdx)
    (found : wholeAt? redex.index source = some redex)
    (selected_source : selected.Sublist config.purses) :
    ((source, redex.index) :: selectedSourceEntries selected).map
      Prod.snd |>.Nodup := by
  simp only [List.map_cons, selectedSourceEntries_map_snd,
    List.nodup_cons]
  exact ⟨whole_index_not_mem_selected source_mem found selected_source,
    selectedPurse_indices_nodup selected_source⟩

theorem splitPicked_indices_nodup
    {config : RawCostConfig} {recv : RawRecvEndpoint}
    {send : RawSendEndpoint} {recvSource sendSource : RawCostTerm}
    {selected : List RawSelectedPurse}
    (recv_mem : (recvSource, recv.index) ∈ config.zipIdx)
    (send_mem : (sendSource, send.index) ∈ config.zipIdx)
    (recv_found : recvAt? recv.index recvSource = some recv)
    (send_found : sendAt? send.index sendSource = some send)
    (selected_source : selected.Sublist config.purses) :
    ((recvSource, recv.index) :: (sendSource, send.index) ::
      selectedSourceEntries selected).map Prod.snd |>.Nodup := by
  simp only [List.map_cons, selectedSourceEntries_map_snd,
    List.nodup_cons]
  refine ⟨?_, ?_, ?_⟩
  · simp only [List.mem_cons]
    intro member
    rcases member with indices | selected_member
    · exact recv_send_indices_ne recv_mem send_mem recv_found send_found indices
    · exact recv_index_not_mem_selected recv_mem recv_found selected_source
        selected_member
  · exact send_index_not_mem_selected send_mem send_found selected_source
  · exact selectedPurse_indices_nodup selected_source

theorem whole_selectIndices_eq
    {config : RawCostConfig} {redex : RawWholeRedex}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, redex.index) ∈ config.zipIdx)
    (found : wholeAt? redex.index source = some redex)
    (selected_source : selected.Sublist config.purses) :
    (selectIndices config
        ([redex.index] ++ selected.map RawIndexedPurse.index) :
      Multiset RawCostTerm) =
      ({source} : Multiset RawCostTerm) +
        (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) := by
  let picked := (source, redex.index) :: selectedSourceEntries selected
  have source_entries : ∀ entry ∈ picked, entry ∈ config.zipIdx := by
    intro entry member
    rcases List.mem_cons.mp member with rfl | selected_member
    · exact source_mem
    · exact selectedSourceEntries_source selected_source entry selected_member
  have selected := selectIndices_eq_picked
    (config := config) (indices := [redex.index] ++
      selected.map RawIndexedPurse.index) (picked := picked)
    (by simp [picked])
    (wholePicked_indices_nodup source_mem found selected_source)
    source_entries
  simpa [picked, selectedSourceEntries, Function.comp_def] using selected

theorem split_selectIndices_eq
    {config : RawCostConfig} {recv : RawRecvEndpoint}
    {send : RawSendEndpoint} {recvSource sendSource : RawCostTerm}
    {selected : List RawSelectedPurse}
    (recv_mem : (recvSource, recv.index) ∈ config.zipIdx)
    (send_mem : (sendSource, send.index) ∈ config.zipIdx)
    (recv_found : recvAt? recv.index recvSource = some recv)
    (send_found : sendAt? send.index sendSource = some send)
    (selected_source : selected.Sublist config.purses) :
    (selectIndices config
        ([recv.index, send.index] ++ selected.map RawIndexedPurse.index) :
      Multiset RawCostTerm) =
      ({recvSource} + {sendSource} : Multiset RawCostTerm) +
        (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) := by
  let picked := (recvSource, recv.index) :: (sendSource, send.index) ::
    selectedSourceEntries selected
  have source_entries : ∀ entry ∈ picked, entry ∈ config.zipIdx := by
    intro entry member
    rcases List.mem_cons.mp member with rfl | member
    · exact recv_mem
    · rcases List.mem_cons.mp member with rfl | selected_member
      · exact send_mem
      · exact selectedSourceEntries_source selected_source entry selected_member
  have selected := selectIndices_eq_picked
    (config := config) (indices := [recv.index, send.index] ++
      selected.map RawIndexedPurse.index) (picked := picked)
    (by simp [picked])
    (splitPicked_indices_nodup recv_mem send_mem recv_found send_found
      selected_source)
    source_entries
  simpa [picked, selectedSourceEntries, Function.comp_def, add_assoc] using selected

theorem whole_source_partition
    {config : RawCostConfig} {redex : RawWholeRedex}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, redex.index) ∈ config.zipIdx)
    (found : wholeAt? redex.index source = some redex)
    (selected_source : selected.Sublist config.purses) :
    (eraseIndices config
          ([redex.index] ++ selected.map RawIndexedPurse.index) :
        Multiset RawCostTerm) + {source} +
        (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) =
      (config : Multiset RawCostTerm) := by
  have partition := eraseIndices_add_selectIndices config
    ([redex.index] ++ selected.map RawIndexedPurse.index)
  rw [whole_selectIndices_eq source_mem found selected_source] at partition
  simpa [add_assoc] using partition

theorem split_source_partition
    {config : RawCostConfig} {recv : RawRecvEndpoint}
    {send : RawSendEndpoint} {recvSource sendSource : RawCostTerm}
    {selected : List RawSelectedPurse}
    (recv_mem : (recvSource, recv.index) ∈ config.zipIdx)
    (send_mem : (sendSource, send.index) ∈ config.zipIdx)
    (recv_found : recvAt? recv.index recvSource = some recv)
    (send_found : sendAt? send.index sendSource = some send)
    (selected_source : selected.Sublist config.purses) :
    (eraseIndices config
          ([recv.index, send.index] ++ selected.map RawIndexedPurse.index) :
        Multiset RawCostTerm) + {recvSource} + {sendSource} +
        (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) =
      (config : Multiset RawCostTerm) := by
  have partition := eraseIndices_add_selectIndices config
    ([recv.index, send.index] ++ selected.map RawIndexedPurse.index)
  rw [split_selectIndices_eq recv_mem send_mem recv_found send_found
    selected_source] at partition
  calc
    (eraseIndices config
          ([recv.index, send.index] ++ selected.map RawIndexedPurse.index) :
        Multiset RawCostTerm) + {recvSource} + {sendSource} +
        (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm) =
      (eraseIndices config
          ([recv.index, send.index] ++ selected.map RawIndexedPurse.index) :
        Multiset RawCostTerm) +
        (({recvSource} + {sendSource} : Multiset RawCostTerm) +
          (selected.map RawIndexedPurse.toTerm : Multiset RawCostTerm)) := by
            ac_rfl
    _ = (config : Multiset RawCostTerm) := partition

/-- Cancelling the recovered participant and selected purse occurrences leaves
the declarative context together with the cover's untouched purses. -/
theorem whole_recovered_frame_eq_context
    {config : RawCostConfig} {redex : RawWholeRedex}
    {source : RawCostTerm} {selected : List RawSelectedPurse}
    (source_mem : (source, redex.index) ∈ config.zipIdx)
    (found : wholeAt? redex.index source = some redex)
    (selected_source : selected.Sublist config.purses)
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore)
    {participant : CostTerm String}
    (decoded_source : decodeCostTerm source = participant)
    {context : CostConfig String}
    (source_eq : decodeRawConfig config =
      context + {participant} + LocatedPurse.configComponents available) :
    decodeRawConfig (eraseIndices config
        ([redex.index] ++ selected.map RawIndexedPurse.index)) =
      context + LocatedPurse.configComponents cover.untouched := by
  have raw_partition := whole_source_partition source_mem found selected_source
  have decoded_partition := congrArg (Multiset.map decodeCostTerm) raw_partition
  have selected_components :=
    decodedSelectedTerms_eq_selectedBefore_components cover selected_eq
  have runtime_partition_raw :
      decodeRawConfig (eraseIndices config
          ([redex.index] ++ selected.map RawIndexedPurse.index)) +
          {participant} +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
            Multiset (CostTerm String)) =
        decodeRawConfig config := by
    simpa [decodeRawConfig, Multiset.map_add, Function.comp_def,
      decoded_source] using decoded_partition
  have runtime_partition :
      decodeRawConfig (eraseIndices config
          ([redex.index] ++ selected.map RawIndexedPurse.index)) +
          {participant} + LocatedPurse.configComponents cover.selectedBefore =
        decodeRawConfig config := by
    rw [← selected_components]
    exact runtime_partition_raw
  have available_components :
      LocatedPurse.configComponents available =
        LocatedPurse.configComponents cover.selectedBefore +
          LocatedPurse.configComponents cover.untouched := by
    calc
      LocatedPurse.configComponents available =
          LocatedPurse.configComponents
            (cover.selectedBefore + cover.untouched) :=
        congrArg LocatedPurse.configComponents cover.available_decomposition
      _ = LocatedPurse.configComponents cover.selectedBefore +
          LocatedPurse.configComponents cover.untouched := by
        simp [LocatedPurse.configComponents, Multiset.map_add]
  apply add_right_cancel
    (b := {participant} + LocatedPurse.configComponents cover.selectedBefore)
  calc
    decodeRawConfig (eraseIndices config
        ([redex.index] ++ selected.map RawIndexedPurse.index)) +
        ({participant} + LocatedPurse.configComponents cover.selectedBefore) =
      decodeRawConfig config := by
        simpa [add_assoc] using runtime_partition
    _ = context + {participant} +
        LocatedPurse.configComponents available := source_eq
    _ = (context + LocatedPurse.configComponents cover.untouched) +
        ({participant} + LocatedPurse.configComponents cover.selectedBefore) := by
      rw [available_components]
      ac_rfl

theorem split_recovered_frame_eq_context
    {config : RawCostConfig} {recv : RawRecvEndpoint}
    {send : RawSendEndpoint} {recvSource sendSource : RawCostTerm}
    (recv_mem : (recvSource, recv.index) ∈ config.zipIdx)
    (send_mem : (sendSource, send.index) ∈ config.zipIdx)
    (recv_found : recvAt? recv.index recvSource = some recv)
    (send_found : sendAt? send.index sendSource = some send)
    {selected : List RawSelectedPurse}
    (selected_source : selected.Sublist config.purses)
    {location : CostName String} {demand : CostSig String}
    {available residual : Multiset (LocatedPurse String)}
    (cover : LocatedTokenCover location demand available residual)
    (selected_eq : (selected.map RawIndexedPurse.toLocated :
      Multiset (LocatedPurse String)) = cover.selectedBefore)
    {recvParticipant sendParticipant : CostTerm String}
    (decoded_recv : decodeCostTerm recvSource = recvParticipant)
    (decoded_send : decodeCostTerm sendSource = sendParticipant)
    {context : CostConfig String}
    (source_eq : decodeRawConfig config = context + {recvParticipant} +
      {sendParticipant} + LocatedPurse.configComponents available) :
    decodeRawConfig (eraseIndices config
        ([recv.index, send.index] ++ selected.map RawIndexedPurse.index)) =
      context + LocatedPurse.configComponents cover.untouched := by
  have raw_partition := split_source_partition recv_mem send_mem recv_found
    send_found selected_source
  have decoded_partition := congrArg (Multiset.map decodeCostTerm) raw_partition
  have selected_components :=
    decodedSelectedTerms_eq_selectedBefore_components cover selected_eq
  have runtime_partition_raw :
      decodeRawConfig (eraseIndices config
          ([recv.index, send.index] ++ selected.map RawIndexedPurse.index)) +
          {recvParticipant} + {sendParticipant} +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
            Multiset (CostTerm String)) =
        decodeRawConfig config := by
    simpa [decodeRawConfig, Multiset.map_add, Function.comp_def,
      decoded_recv, decoded_send] using decoded_partition
  have runtime_partition :
      decodeRawConfig (eraseIndices config
          ([recv.index, send.index] ++ selected.map RawIndexedPurse.index)) +
          {recvParticipant} + {sendParticipant} +
          LocatedPurse.configComponents cover.selectedBefore =
        decodeRawConfig config := by
    rw [← selected_components]
    exact runtime_partition_raw
  have available_components :
      LocatedPurse.configComponents available =
        LocatedPurse.configComponents cover.selectedBefore +
          LocatedPurse.configComponents cover.untouched := by
    calc
      LocatedPurse.configComponents available =
          LocatedPurse.configComponents
            (cover.selectedBefore + cover.untouched) :=
        congrArg LocatedPurse.configComponents cover.available_decomposition
      _ = LocatedPurse.configComponents cover.selectedBefore +
          LocatedPurse.configComponents cover.untouched := by
        simp [LocatedPurse.configComponents, Multiset.map_add]
  apply add_right_cancel
    (b := {recvParticipant} + {sendParticipant} +
      LocatedPurse.configComponents cover.selectedBefore)
  calc
    decodeRawConfig (eraseIndices config
        ([recv.index, send.index] ++ selected.map RawIndexedPurse.index)) +
        ({recvParticipant} + {sendParticipant} +
          LocatedPurse.configComponents cover.selectedBefore) =
      decodeRawConfig config := by
        simpa [add_assoc] using runtime_partition
    _ = context + {recvParticipant} + {sendParticipant} +
        LocatedPurse.configComponents available := source_eq
    _ = (context + LocatedPurse.configComponents cover.untouched) +
        ({recvParticipant} + {sendParticipant} +
          LocatedPurse.configComponents cover.selectedBefore) := by
      rw [available_components]
      ac_rfl

/-! ## Canonical participant decoding -/

theorem RawCostConfig.normalized_of_mem_zipIdx
    {config : RawCostConfig} (canonical : config.Canonical)
    {term : RawCostTerm} {index : Nat}
    (member : (term, index) ∈ config.zipIdx) : term.Normalized := by
  have term_mem : term ∈ config := by
    have mapped : term ∈ config.zipIdx.map Prod.fst :=
      List.mem_map.mpr ⟨(term, index), member, rfl⟩
    simpa using mapped
  exact List.forall_iff_forall_mem.mp canonical.components term term_mem

theorem RawCostConfig.encodingCanonical_of_mem_zipIdx
    {config : RawCostConfig}
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    {term : RawCostTerm} {index : Nat}
    (member : (term, index) ∈ config.zipIdx) : term.EncodingCanonical := by
  have term_mem : term ∈ config := by
    have mapped : term ∈ config.zipIdx.map Prod.fst :=
      List.mem_map.mpr ⟨(term, index), member, rfl⟩
    simpa using mapped
  exact List.forall_iff_forall_mem.mp encoding term term_mem

theorem RawCostTerm.eq_encode_of_decode
    {raw : RawCostTerm} (raw_canonical : raw.EncodingCanonical)
    (typed : CostTerm String) (decoded : decodeCostTerm raw = typed) :
    raw = encodeCostTerm typed := by
  apply RawCostTerm.decode_injective_of_encodingCanonical
    raw_canonical (encodeCostTerm_encodingCanonical typed)
  simpa using decoded

theorem exists_wholeAt?_of_decode_recv_send
    {raw : RawCostTerm} (raw_canonical : raw.EncodingCanonical)
    {index : Nat} {channel : CostName String} {body payload : CostTerm String}
    {sig : CostSig String}
    (decoded : decodeCostTerm raw =
      .signed (.par (.recv channel body) (.send channel payload)) sig) :
    ∃ redex, wholeAt? index raw = some redex := by
  have raw_eq := raw.eq_encode_of_decode raw_canonical _ decoded
  subst raw
  refine ⟨⟨index, (encodeCostName channel).normalize,
    encodeCostTerm body, encodeCostTerm payload,
    (encodeCostSig sig).normalize⟩, ?_⟩
  simp [wholeAt?, encodeCostTerm, encodeCostProc]

theorem exists_wholeAt?_of_decode_send_recv
    {raw : RawCostTerm} (raw_canonical : raw.EncodingCanonical)
    {index : Nat} {channel : CostName String} {body payload : CostTerm String}
    {sig : CostSig String}
    (decoded : decodeCostTerm raw =
      .signed (.par (.send channel payload) (.recv channel body)) sig) :
    ∃ redex, wholeAt? index raw = some redex := by
  have raw_eq := raw.eq_encode_of_decode raw_canonical _ decoded
  subst raw
  refine ⟨⟨index, (encodeCostName channel).normalize,
    encodeCostTerm body, encodeCostTerm payload,
    (encodeCostSig sig).normalize⟩, ?_⟩
  simp [wholeAt?, encodeCostTerm, encodeCostProc]

theorem exists_recvAt?_of_decode
    {raw : RawCostTerm} (raw_canonical : raw.EncodingCanonical)
    {index : Nat} {channel : CostName String} {body : CostTerm String}
    {sig : CostSig String}
    (decoded : decodeCostTerm raw = .signed (.recv channel body) sig) :
    ∃ recv, recvAt? index raw = some recv := by
  have raw_eq := raw.eq_encode_of_decode raw_canonical _ decoded
  subst raw
  refine ⟨⟨index, (encodeCostName channel).normalize,
    encodeCostTerm body, (encodeCostSig sig).normalize⟩, ?_⟩
  simp [recvAt?, encodeCostTerm, encodeCostProc]

theorem exists_sendAt?_of_decode
    {raw : RawCostTerm} (raw_canonical : raw.EncodingCanonical)
    {index : Nat} {channel : CostName String} {payload : CostTerm String}
    {sig : CostSig String}
    (decoded : decodeCostTerm raw = .signed (.send channel payload) sig) :
    ∃ send, sendAt? index raw = some send := by
  have raw_eq := raw.eq_encode_of_decode raw_canonical _ decoded
  subst raw
  refine ⟨⟨index, (encodeCostName channel).normalize,
    encodeCostTerm payload, (encodeCostSig sig).normalize⟩, ?_⟩
  simp [sendAt?, encodeCostTerm, encodeCostProc]

theorem RawCostProc.components_forall_normalized_of_normalized
    {proc : RawCostProc} (normalized : proc.normalize = proc) :
    proc.components.Forall (fun component => component.normalize = component) := by
  rw [← normalized]
  exact (RawCostProc.normalizationResult proc).components_fixed

theorem wholeAt?_decode_source_of_normalized
    {index : Nat} {source : RawCostTerm} {redex : RawWholeRedex}
    (normalized : source.Normalized)
    (found : wholeAt? index source = some redex) :
    decodeCostTerm source =
        .signed (.par
          (.recv (decodeCostName redex.location) (decodeCostTerm redex.body))
          (.send (decodeCostName redex.location) (decodeCostTerm redex.payload)))
          (decodeCostSig redex.sig) ∨
      decodeCostTerm source =
        .signed (.par
          (.send (decodeCostName redex.location) (decodeCostTerm redex.payload))
          (.recv (decodeCostName redex.location) (decodeCostTerm redex.body)))
          (decodeCostSig redex.sig) := by
  cases source with
  | nil => simp [wholeAt?] at found
  | par left right => simp [wholeAt?] at found
  | drop name => simp [wholeAt?] at found
  | purse location stack => simp [wholeAt?] at found
  | signed proc sig =>
      have signed_fixed := RawCostTerm.signed.inj normalized
      have proc_fixed := signed_fixed.1
      have sig_fixed := signed_fixed.2
      cases proc with
      | nil => simp [wholeAt?] at found
      | send channel payload => simp [wholeAt?] at found
      | recv channel body => simp [wholeAt?] at found
      | par left right =>
          have components_fixed :=
            RawCostProc.components_forall_normalized_of_normalized proc_fixed
          cases left <;> cases right <;>
            simp [wholeAt?, RawCostProc.components] at found components_fixed ⊢
          all_goals
            rcases found with ⟨channels_eq, redex_eq⟩
            subst redex
            simp_all [decodeCostTerm, decodeCostProc, decodeCostSig]
          all_goals
            apply congrArg decodeCostName
            grind

theorem recvAt?_decode_source_of_normalized
    {index : Nat} {source : RawCostTerm} {recv : RawRecvEndpoint}
    (normalized : source.Normalized)
    (found : recvAt? index source = some recv) :
    decodeCostTerm source =
      .signed (.recv (decodeCostName recv.location) (decodeCostTerm recv.body))
        (decodeCostSig recv.sig) := by
  cases source with
  | signed proc sig =>
      have signed_fixed := RawCostTerm.signed.inj normalized
      cases proc <;> simp [recvAt?] at found
      rename_i channel body
      simp only [RawCostProc.normalize] at signed_fixed
      have proc_parts := RawCostProc.recv.inj signed_fixed.1
      subst recv
      simp [decodeCostTerm, decodeCostProc, proc_parts.1, signed_fixed.2]
  | nil => simp [recvAt?] at found
  | par left right => simp [recvAt?] at found
  | drop name => simp [recvAt?] at found
  | purse location stack => simp [recvAt?] at found

theorem sendAt?_decode_source_of_normalized
    {index : Nat} {source : RawCostTerm} {send : RawSendEndpoint}
    (normalized : source.Normalized)
    (found : sendAt? index source = some send) :
    decodeCostTerm source =
      .signed (.send (decodeCostName send.location) (decodeCostTerm send.payload))
        (decodeCostSig send.sig) := by
  cases source with
  | signed proc sig =>
      have signed_fixed := RawCostTerm.signed.inj normalized
      cases proc <;> simp [sendAt?] at found
      rename_i channel payload
      simp only [RawCostProc.normalize] at signed_fixed
      have proc_parts := RawCostProc.send.inj signed_fixed.1
      subst send
      simp [decodeCostTerm, decodeCostProc, proc_parts.1, signed_fixed.2]
  | nil => simp [sendAt?] at found
  | par left right => simp [sendAt?] at found
  | drop name => simp [sendAt?] at found
  | purse location stack => simp [sendAt?] at found

theorem wholeAt?_decoded_fields_recv_send
    {index : Nat} {source : RawCostTerm} {redex : RawWholeRedex}
    {channel : CostName String} {body payload : CostTerm String}
    {sig : CostSig String}
    (normalized : source.Normalized)
    (found : wholeAt? index source = some redex)
    (decoded : decodeCostTerm source =
      .signed (.par (.recv channel body) (.send channel payload)) sig) :
    decodeCostName redex.location = channel ∧
      decodeCostTerm redex.body = body ∧
      decodeCostTerm redex.payload = payload ∧
      decodeCostSig redex.sig = sig := by
  rcases wholeAt?_decode_source_of_normalized normalized found with
    recv_send | send_recv
  · have same := decoded.symm.trans recv_send
    simp_all
  · have impossible := decoded.symm.trans send_recv
    simp at impossible

theorem wholeAt?_decoded_fields_send_recv
    {index : Nat} {source : RawCostTerm} {redex : RawWholeRedex}
    {channel : CostName String} {body payload : CostTerm String}
    {sig : CostSig String}
    (normalized : source.Normalized)
    (found : wholeAt? index source = some redex)
    (decoded : decodeCostTerm source =
      .signed (.par (.send channel payload) (.recv channel body)) sig) :
    decodeCostName redex.location = channel ∧
      decodeCostTerm redex.body = body ∧
      decodeCostTerm redex.payload = payload ∧
      decodeCostSig redex.sig = sig := by
  rcases wholeAt?_decode_source_of_normalized normalized found with
    recv_send | send_recv
  · have impossible := decoded.symm.trans recv_send
    simp at impossible
  · have same := decoded.symm.trans send_recv
    simp_all

theorem recvAt?_decoded_fields
    {index : Nat} {source : RawCostTerm} {recv : RawRecvEndpoint}
    {channel : CostName String} {body : CostTerm String}
    {sig : CostSig String}
    (normalized : source.Normalized)
    (found : recvAt? index source = some recv)
    (decoded : decodeCostTerm source = .signed (.recv channel body) sig) :
    decodeCostName recv.location = channel ∧
      decodeCostTerm recv.body = body ∧ decodeCostSig recv.sig = sig := by
  have same := decoded.symm.trans
    (recvAt?_decode_source_of_normalized normalized found)
  simp_all

theorem sendAt?_decoded_fields
    {index : Nat} {source : RawCostTerm} {send : RawSendEndpoint}
    {channel : CostName String} {payload : CostTerm String}
    {sig : CostSig String}
    (normalized : source.Normalized)
    (found : sendAt? index source = some send)
    (decoded : decodeCostTerm source = .signed (.send channel payload) sig) :
    decodeCostName send.location = channel ∧
      decodeCostTerm send.payload = payload ∧ decodeCostSig send.sig = sig := by
  have same := decoded.symm.trans
    (sendAt?_decode_source_of_normalized normalized found)
  simp_all

/-! ## Structural representation boundary -/

@[simp]
theorem RawCostSig.encode_decode_toMultiset (sig : RawCostSig) :
    (encodeCostSig (decodeCostSig sig) : Multiset String) =
      (sig : Multiset String) := by
  simp [encodeCostSig, decodeCostSig]
  exact List.mergeSort_perm _ _

theorem RawCostStack.encode_decode_structuralFrames :
    ∀ stack : RawCostStack,
      (encodeCostStack (decodeCostStack stack)).structuralFrames =
        stack.structuralFrames
  | [] => rfl
  | sig :: rest => by
      simp [encodeCostStack, decodeCostStack, RawCostStack.structuralFrames,
        RawCostStack.encode_decode_structuralFrames rest]

mutual
  theorem RawCostName.encode_decode_structuralDenote :
      ∀ name : RawCostName,
        (encodeCostName (decodeCostName name)).structuralDenote =
          name.structuralDenote
    | .bvar _ => rfl
    | .quote term => by
        simp [encodeCostName, decodeCostName, RawCostName.structuralDenote,
          RawCostTerm.encode_decode_structuralDenote term]
    | .signature sig => by
        simp [encodeCostName, decodeCostName, RawCostName.structuralDenote]

  theorem RawCostProc.encode_decode_structuralDenote :
      ∀ proc : RawCostProc,
        (encodeCostProc (decodeCostProc proc)).structuralDenote =
          proc.structuralDenote
    | .nil => rfl
    | .par left right => by
        simp [encodeCostProc, decodeCostProc, RawCostProc.structuralDenote,
          RawCostProc.encode_decode_structuralDenote left,
          RawCostProc.encode_decode_structuralDenote right]
    | .send channel payload => by
        simp [encodeCostProc, decodeCostProc, RawCostProc.structuralDenote,
          RawCostName.encode_decode_structuralDenote channel,
          RawCostTerm.encode_decode_structuralDenote payload]
    | .recv channel body => by
        simp [encodeCostProc, decodeCostProc, RawCostProc.structuralDenote,
          RawCostName.encode_decode_structuralDenote channel,
          RawCostTerm.encode_decode_structuralDenote body]

  theorem RawCostTerm.encode_decode_structuralDenote :
      ∀ term : RawCostTerm,
        (encodeCostTerm (decodeCostTerm term)).structuralDenote =
          term.structuralDenote
    | .nil => rfl
    | .signed proc sig => by
        simp [encodeCostTerm, decodeCostTerm, RawCostTerm.structuralDenote,
          RawCostProc.encode_decode_structuralDenote proc]
    | .par left right => by
        simp [encodeCostTerm, decodeCostTerm, RawCostTerm.structuralDenote,
          RawTermStructuralDenotation.combine,
          RawCostTerm.encode_decode_structuralDenote left,
          RawCostTerm.encode_decode_structuralDenote right]
    | .drop name => by
        simp [encodeCostTerm, decodeCostTerm, RawCostTerm.structuralDenote,
          RawCostName.encode_decode_structuralDenote name]
    | .purse location stack => by
        simp [encodeCostTerm, decodeCostTerm, RawCostTerm.structuralDenote,
          RawCostName.encode_decode_structuralDenote location,
          RawCostStack.encode_decode_structuralFrames stack]
end

/-- Aggregate structural meaning of an unordered raw configuration. -/
def rawConfigStructuralDenote (config : Multiset RawCostTerm) :
    RawTermStructuralDenotation :=
  ⟨(config.map fun term => term.structuralDenote.atoms).sum,
    (config.map fun term => term.structuralDenote.topDrops).sum⟩

/-- Encode a declarative configuration without choosing an occurrence order. -/
def encodeCostConfig (config : CostConfig String) : Multiset RawCostTerm :=
  config.map encodeCostTerm

/-- A raw component list and a declarative configuration denote the same
structural state independently of executable sorting and flattening. -/
def RawCostConfig.StructurallyRepresents (raw : RawCostConfig)
    (typed : CostConfig String) : Prop :=
  rawConfigStructuralDenote raw =
    rawConfigStructuralDenote (encodeCostConfig typed)

@[simp]
theorem rawConfigStructuralDenote_zero :
    rawConfigStructuralDenote 0 = RawTermStructuralDenotation.empty := by
  rfl

theorem rawConfigStructuralDenote_add
    (left right : Multiset RawCostTerm) :
    rawConfigStructuralDenote (left + right) =
      RawTermStructuralDenotation.combine
        (rawConfigStructuralDenote left) (rawConfigStructuralDenote right) := by
  ext <;> simp [rawConfigStructuralDenote,
    RawTermStructuralDenotation.combine, Multiset.map_add]

theorem rawConfigStructuralDenote_singleton (term : RawCostTerm) :
    rawConfigStructuralDenote {term} = term.structuralDenote := by
  ext <;> simp [rawConfigStructuralDenote]

theorem rawConfigStructuralDenote_encode_decode
    (config : RawCostConfig) :
    rawConfigStructuralDenote
        (encodeCostConfig (decodeRawConfig config)) =
      rawConfigStructuralDenote config := by
  ext <;>
    simp [encodeCostConfig, decodeRawConfig, rawConfigStructuralDenote,
      Function.comp_def, RawCostTerm.encode_decode_structuralDenote]

theorem RawCostConfig.structurallyRepresents_decode (config : RawCostConfig) :
    config.StructurallyRepresents (decodeRawConfig config) := by
  unfold RawCostConfig.StructurallyRepresents
  exact (rawConfigStructuralDenote_encode_decode config).symm

theorem rawConfigStructuralDenote_components (term : RawCostTerm) :
    rawConfigStructuralDenote term.components = term.structuralDenote := by
  apply RawTermStructuralDenotation.ext
  · simpa [rawConfigStructuralDenote] using
      RawCostTerm.structuralAtoms_components term
  · simpa [rawConfigStructuralDenote] using
      RawCostTerm.structuralDrops_components term

theorem rawConfigStructuralDenote_normalizeConfig (term : RawCostTerm) :
    rawConfigStructuralDenote term.normalizeConfig = term.structuralDenote := by
  have components_eq :
      (term.normalizeConfig : Multiset RawCostTerm) =
        (term.normalize.components : Multiset RawCostTerm) := by
    exact stableKeySort_toMultiset RawCostTerm.key term.normalize.components
  rw [components_eq, rawConfigStructuralDenote_components,
    RawCostTerm.structuralDenote_normalize]

theorem rawConfigStructuralDenote_normalized_components (term : RawCostTerm) :
    rawConfigStructuralDenote term.normalize.components =
      rawConfigStructuralDenote term.components := by
  rw [rawConfigStructuralDenote_components,
    rawConfigStructuralDenote_components,
    RawCostTerm.structuralDenote_normalize]

theorem RawCostConfig.structurallyRepresents_decode_iff
    (raw decodedFrom : RawCostConfig) :
    raw.StructurallyRepresents (decodeRawConfig decodedFrom) ↔
      rawConfigStructuralDenote raw =
        rawConfigStructuralDenote decodedFrom := by
  unfold RawCostConfig.StructurallyRepresents
  rw [rawConfigStructuralDenote_encode_decode]

/-- The executable residual builder preserves the canonical pure-rho erasure
of its retained components, contractum, and purse tails. -/
theorem residualFor_eraseCanonical_structural
    (signatureName : SignatureNameEncoding String)
    (signaturePure : ∀ signature, HashSetFree (signatureName signature))
    (config : RawCostConfig) (participants : List Nat)
    (selected : List RawSelectedPurse)
    (contractum : RawCostTerm) :
    StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig
          (residualFor config participants selected contractum).normalizeConfig))
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig
            (eraseIndices config
              (participants ++ selected.map RawIndexedPurse.index)) +
          (decodeCostTerm contractum).components +
          (selected.map
            (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
              Multiset (CostTerm String)))) := by
  let retained := eraseIndices config
    (participants ++ selected.map RawIndexedPurse.index)
  let tails := selected.map RawIndexedPurse.toTailTerm
  let runtimeItems := retained ++ contractum.normalize.components ++ tails
  have residualDecoded :
      decodeRawConfig
          (residualFor config participants selected contractum).normalizeConfig =
        decodeRawConfig
          (RawCostTerm.fromComponents runtimeItems).normalize.components := by
    have residualEq :
        residualFor config participants selected contractum =
          (RawCostTerm.fromComponents runtimeItems).normalize := by
      rfl
    rw [residualEq, decodeRawConfig_normalizeConfig,
      decodeRawConfig_components, RawCostTerm.normalize_idempotent]
  have normalizedComponents :=
    RawCostTerm.eraseCanonical_decode_normalizedComponents_structural
      signatureName signaturePure (RawCostTerm.fromComponents runtimeItems)
  have reassociatedComponents :=
    RawCostTerm.eraseCanonical_decode_fromComponents_structural
      signatureName signaturePure runtimeItems
  have residualComponents := StructuralCongruence.trans _ _ _
    normalizedComponents reassociatedComponents
  have retainedCongruence : StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig retained))
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig retained)) :=
    StructuralCongruence.refl _
  have contractumCongruence :=
    RawCostTerm.eraseCanonical_decode_normalizedComponents_structural
      signatureName signaturePure contractum
  have tailsCongruence : StructuralCongruence
      (CostConfig.eraseCanonical signatureName signaturePure
        (decodeRawConfig tails))
      (CostConfig.eraseCanonical signatureName signaturePure
      (decodeRawConfig tails)) :=
    StructuralCongruence.refl _
  have tailsDecoded :
      decodeRawConfig tails =
        (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
          Multiset (CostTerm String)) := by
    simp [tails, decodeRawConfig, Function.comp_def]
  have itemCongruence := CostConfig.eraseCanonical_add_congr_structural
    signatureName signaturePure
    (CostConfig.eraseCanonical_add_congr_structural signatureName signaturePure
      retainedCongruence contractumCongruence)
    tailsCongruence
  rw [tailsDecoded] at itemCongruence
  rw [residualDecoded]
  exact StructuralCongruence.trans _ _ _ residualComponents (by
    simpa only [runtimeItems, retained, decodeRawConfig_append,
      decodeRawConfig_components, tailsDecoded, add_assoc]
      using itemCongruence)

theorem residualFor_structurallyRepresents
    (config : RawCostConfig) (participants : List Nat)
    (selected : List RawSelectedPurse) (body payload : RawCostTerm) :
    (residualFor config participants selected
          (RawCostTerm.commSubst body payload).normalize).normalizeConfig
      |>.StructurallyRepresents
        (decodeRawConfig (eraseIndices config
            (participants ++ selected.map RawIndexedPurse.index)) +
          (CostTerm.commSubst (decodeCostTerm body)
              (decodeCostTerm payload)).components +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String))) := by
  let rawComm := RawCostTerm.commSubst body payload
  let retained := eraseIndices config
    (participants ++ selected.map RawIndexedPurse.index)
  let tails := selected.map RawIndexedPurse.toTailTerm
  let declarativeItems := retained ++ rawComm.components ++ tails
  have typed_eq :
      decodeRawConfig declarativeItems =
        decodeRawConfig retained +
          (CostTerm.commSubst (decodeCostTerm body)
              (decodeCostTerm payload)).components +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String)) := by
    simp only [declarativeItems, List.append_assoc, decodeRawConfig_append,
      decodeRawConfig_components]
    rw [decodeCostTerm_commSubst]
    simp [tails, Function.comp_def, decodeRawConfig, add_assoc]
  rw [← typed_eq]
  apply (RawCostConfig.structurallyRepresents_decode_iff _ _).2
  simp only [residualFor, RawCostTerm.normalize_idempotent]
  rw [rawConfigStructuralDenote_normalizeConfig,
    RawCostTerm.structuralDenote_normalize,
    RawCostTerm.structuralDenote_fromComponents]
  apply RawTermStructuralDenotation.ext <;>
    simp [declarativeItems, rawConfigStructuralDenote,
      rawComm, retained, tails, RawCostTerm.structuralAtoms_components,
      RawCostTerm.structuralDrops_components,
      RawCostTerm.structuralDenote_normalize,
      RawIndexedPurse.toTailTerm, Function.comp_def]

/-! ## Executable-to-declarative correspondence -/

/-- A raw candidate has a declarative step with the same location and spend;
its executable residual represents the declarative target structurally. -/
def RuntimeCostStepSound (config : RawCostConfig)
    (step : RawRuntimeStep) : Prop :=
  ∃ target : CostConfig String,
    CostStep (decodeRawConfig config)
        (decodeCostName step.location) (decodeCostSig step.spend) target ∧
      step.residual.normalizeConfig.StructurallyRepresents target ∧
      (∀ (signatureName : SignatureNameEncoding String)
          (signaturePure : ∀ signature,
            HashSetFree (signatureName signature)),
        StructuralCongruence
          (CostConfig.eraseCanonical signatureName signaturePure
            (decodeRawConfig step.residual.normalizeConfig))
          (CostConfig.eraseCanonical signatureName signaturePure target)) ∧
      ((decodeRawConfig config).BinderSafe →
        (decodeRawConfig step.residual.normalizeConfig).BinderSafe)

private theorem wholeCandidate_sound
    {config : RawCostConfig} (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {redex : RawWholeRedex} {source : RawCostTerm}
    (redex_member : redex ∈ config.wholeRedexes)
    (source_mem : (source, redex.index) ∈ config.zipIdx)
    (found : wholeAt? redex.index source = some redex)
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config)
    (step_member : step ∈ wholeCandidates config config.purses redex) :
    RuntimeCostStepSound config step := by
  simp only [wholeCandidates] at step_member
  obtain ⟨selected, selected_member, step_eq⟩ := List.mem_map.mp step_member
  subst step
  have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
  have location_fixed := wholeAt?_location_normalized found
  have located := selectedPurses_location_eq canonical funding location_fixed
  have selected_valid : selected.Forall RawIndexedPurse.WellFormed := by
    rw [List.forall_iff_forall_mem]
    intro purse purse_member
    exact RawRuntimeStep.selectedPurse_wellFormed config_ok enabled purse_member
  have redex_ok := List.forall_iff_forall_mem.mp
    (config.wholeRedexes_forall_wellFormed config_ok) redex redex_member
  let available := decodedSelectedAvailable redex.location selected selected_valid
  let residual := decodedSelectedResidual redex.location selected selected_valid
  let cover : LocatedTokenCover (decodeCostName redex.location)
      (decodeCostSig redex.sig) available residual :=
    decodedSelectedCover redex.location redex.sig selected selected_valid
      funding.exact_spend
  let context := decodeRawConfig
    (eraseIndices config ([redex.index] ++ selected.map RawIndexedPurse.index))
  let target := context +
    (CostTerm.commSubst (decodeCostTerm redex.body)
      (decodeCostTerm redex.payload)).components +
    LocatedPurse.configComponents residual
  have partition := whole_source_partition source_mem found
    funding.selected_from_config
  have decoded_partition := congrArg (Multiset.map decodeCostTerm) partition
  have source_partition :
      context + {decodeCostTerm source} +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
            Multiset (CostTerm String)) =
        decodeRawConfig config := by
    simpa [context, decodeRawConfig, Multiset.map_add, Function.comp_def]
      using decoded_partition
  have available_components :
      LocatedPurse.configComponents available =
        (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
          Multiset (CostTerm String)) := by
    simpa [available] using decodedSelectedAvailable_components
      redex.location selected selected_valid located
  have residual_components :
      LocatedPurse.configComponents residual =
        (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
          Multiset (CostTerm String)) := by
    simpa [residual] using decodedSelectedResidual_components
      redex.location selected selected_valid located
  have source_normalized :=
    RawCostConfig.normalized_of_mem_zipIdx canonical source_mem
  rcases wholeAt?_decode_source_of_normalized source_normalized found with
    source_recv_send | source_send_recv
  · have source_eq :
        context +
            {CostTerm.signed (.par
              (.recv (decodeCostName redex.location) (decodeCostTerm redex.body))
              (.send (decodeCostName redex.location)
                (decodeCostTerm redex.payload)))
              (decodeCostSig redex.sig)} +
            LocatedPurse.configComponents available =
          decodeRawConfig config := by
      rw [available_components]
      simpa [source_recv_send] using source_partition
    have declarative0 : CostStep
        (context +
          (.signed (.par
            (.recv (decodeCostName redex.location) (decodeCostTerm redex.body))
            (.send (decodeCostName redex.location)
              (decodeCostTerm redex.payload)))
            (decodeCostSig redex.sig) ::ₘ 0) +
          LocatedPurse.configComponents available)
        (decodeCostName redex.location) (decodeCostSig redex.sig) target :=
      CostStep.wholeRecvSend (decodeCostSig_runtimeValid redex_ok.sig) cover
    change CostStep
      (context +
        {CostTerm.signed (.par
          (.recv (decodeCostName redex.location) (decodeCostTerm redex.body))
          (.send (decodeCostName redex.location)
            (decodeCostTerm redex.payload)))
          (decodeCostSig redex.sig)} +
        LocatedPurse.configComponents available)
      (decodeCostName redex.location) (decodeCostSig redex.sig) target
      at declarative0
    rw [source_eq] at declarative0
    refine ⟨target, declarative0, ?_, ?_, ?_⟩
    · have represented := residualFor_structurallyRepresents config [redex.index]
        selected redex.body redex.payload
      simpa [target, context, residual, residual_components] using represented
    · intro signatureName signaturePure
      have erased := residualFor_eraseCanonical_structural signatureName
        signaturePure config [redex.index] selected
        (RawCostTerm.commSubst redex.body redex.payload)
      simpa [target, context, residual, residual_components,
        RawCostTerm.normalize_idempotent, decodeCostTerm_commSubst,
        CostTerm.commSubst] using erased
    · intro sourceSafe
      have targetSafe := declarative0.preserves_binderSafe sourceSafe
      have residualSafe := residualFor_decode_binderSafe config [redex.index]
        selected (RawCostTerm.commSubst redex.body redex.payload) (by
          simpa [target, context, residual, residual_components,
            decodeCostTerm_commSubst, CostTerm.commSubst,
            RawIndexedPurse.toTailTerm, Function.comp_def] using targetSafe)
      simpa [RawCostTerm.normalize_idempotent] using residualSafe
  · have source_eq :
        context +
            {CostTerm.signed (.par
              (.send (decodeCostName redex.location)
                (decodeCostTerm redex.payload))
              (.recv (decodeCostName redex.location) (decodeCostTerm redex.body)))
              (decodeCostSig redex.sig)} +
            LocatedPurse.configComponents available =
          decodeRawConfig config := by
      rw [available_components]
      simpa [source_send_recv] using source_partition
    have declarative0 : CostStep
        (context +
          (.signed (.par
            (.send (decodeCostName redex.location)
              (decodeCostTerm redex.payload))
            (.recv (decodeCostName redex.location) (decodeCostTerm redex.body)))
            (decodeCostSig redex.sig) ::ₘ 0) +
          LocatedPurse.configComponents available)
        (decodeCostName redex.location) (decodeCostSig redex.sig) target :=
      CostStep.wholeSendRecv (decodeCostSig_runtimeValid redex_ok.sig) cover
    change CostStep
      (context +
        {CostTerm.signed (.par
          (.send (decodeCostName redex.location)
            (decodeCostTerm redex.payload))
          (.recv (decodeCostName redex.location) (decodeCostTerm redex.body)))
          (decodeCostSig redex.sig)} +
        LocatedPurse.configComponents available)
      (decodeCostName redex.location) (decodeCostSig redex.sig) target
      at declarative0
    rw [source_eq] at declarative0
    refine ⟨target, declarative0, ?_, ?_, ?_⟩
    · have represented := residualFor_structurallyRepresents config [redex.index]
        selected redex.body redex.payload
      simpa [target, context, residual, residual_components] using represented
    · intro signatureName signaturePure
      have erased := residualFor_eraseCanonical_structural signatureName
        signaturePure config [redex.index] selected
        (RawCostTerm.commSubst redex.body redex.payload)
      simpa [target, context, residual, residual_components,
        RawCostTerm.normalize_idempotent, decodeCostTerm_commSubst,
        CostTerm.commSubst] using erased
    · intro sourceSafe
      have targetSafe := declarative0.preserves_binderSafe sourceSafe
      have residualSafe := residualFor_decode_binderSafe config [redex.index]
        selected (RawCostTerm.commSubst redex.body redex.payload) (by
          simpa [target, context, residual, residual_components,
            decodeCostTerm_commSubst, CostTerm.commSubst,
            RawIndexedPurse.toTailTerm, Function.comp_def] using targetSafe)
      simpa [RawCostTerm.normalize_idempotent] using residualSafe

private theorem splitCandidate_sound
    {config : RawCostConfig} (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {recv : RawRecvEndpoint} {send : RawSendEndpoint}
    {recvSource sendSource : RawCostTerm}
    (recv_member : recv ∈ config.recvEndpoints)
    (send_member : send ∈ config.sendEndpoints)
    (recv_mem : (recvSource, recv.index) ∈ config.zipIdx)
    (send_mem : (sendSource, send.index) ∈ config.zipIdx)
    (recv_found : recvAt? recv.index recvSource = some recv)
    (send_found : sendAt? send.index sendSource = some send)
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config)
    (step_member : step ∈ splitCandidates config config.purses recv send) :
    RuntimeCostStepSound config step := by
  unfold splitCandidates at step_member
  split at step_member
  next locations_match =>
    obtain ⟨selected, selected_member, step_eq⟩ := List.mem_map.mp step_member
    subst step
    have funding := runtimeCostCandidatesFromConfig_funding_valid enabled
    have location_fixed := recvAt?_location_normalized recv_found
    have send_location_fixed := sendAt?_location_normalized send_found
    have locations_eq : send.location = recv.location := by
      calc
        send.location = send.location.normalize := send_location_fixed.symm
        _ = recv.location.normalize := locations_match.symm
        _ = recv.location := location_fixed
    have located := selectedPurses_location_eq canonical funding location_fixed
    have selected_valid : selected.Forall RawIndexedPurse.WellFormed := by
      rw [List.forall_iff_forall_mem]
      intro purse purse_member
      exact RawRuntimeStep.selectedPurse_wellFormed config_ok enabled purse_member
    have recv_ok := List.forall_iff_forall_mem.mp
      (config.recvEndpoints_forall_wellFormed config_ok) recv recv_member
    have send_ok := List.forall_iff_forall_mem.mp
      (config.sendEndpoints_forall_wellFormed config_ok) send send_member
    let spend := (recv.sig ++ send.sig).normalize
    have decoded_spend : decodeCostSig spend =
        decodeCostSig recv.sig + decodeCostSig send.sig := by
      change ((recv.sig ++ send.sig).normalize : Multiset String) =
        (recv.sig : Multiset String) + (send.sig : Multiset String)
      rw [RawCostSig.normalize_toMultiset]
      rfl
    let available := decodedSelectedAvailable recv.location selected selected_valid
    let residual := decodedSelectedResidual recv.location selected selected_valid
    let runtimeCover : LocatedTokenCover (decodeCostName recv.location)
        (decodeCostSig spend) available residual :=
      decodedSelectedCover recv.location spend selected selected_valid
        funding.exact_spend
    let cover : LocatedTokenCover (decodeCostName recv.location)
        (decodeCostSig recv.sig + decodeCostSig send.sig) available residual := by
      rw [← decoded_spend]
      exact runtimeCover
    let context := decodeRawConfig
      (eraseIndices config ([recv.index, send.index] ++
        selected.map RawIndexedPurse.index))
    let target := context +
      (CostTerm.commSubst (decodeCostTerm recv.body)
        (decodeCostTerm send.payload)).components +
      LocatedPurse.configComponents residual
    have partition := split_source_partition recv_mem send_mem recv_found
      send_found funding.selected_from_config
    have decoded_partition := congrArg (Multiset.map decodeCostTerm) partition
    have source_partition :
        context + {decodeCostTerm recvSource} + {decodeCostTerm sendSource} +
            (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
              Multiset (CostTerm String)) =
          decodeRawConfig config := by
      simpa [context, decodeRawConfig, Multiset.map_add, Function.comp_def]
        using decoded_partition
    have available_components :
        LocatedPurse.configComponents available =
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTerm) :
            Multiset (CostTerm String)) := by
      simpa [available] using decodedSelectedAvailable_components
        recv.location selected selected_valid located
    have residual_components :
        LocatedPurse.configComponents residual =
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String)) := by
      simpa [residual] using decodedSelectedResidual_components
        recv.location selected selected_valid located
    have recv_normalized :=
      RawCostConfig.normalized_of_mem_zipIdx canonical recv_mem
    have send_normalized :=
      RawCostConfig.normalized_of_mem_zipIdx canonical send_mem
    have recv_source := recvAt?_decode_source_of_normalized
      recv_normalized recv_found
    have send_source := sendAt?_decode_source_of_normalized
      send_normalized send_found
    have source_eq :
        context +
            {CostTerm.signed
              (.recv (decodeCostName recv.location) (decodeCostTerm recv.body))
              (decodeCostSig recv.sig)} +
            {CostTerm.signed
              (.send (decodeCostName recv.location) (decodeCostTerm send.payload))
              (decodeCostSig send.sig)} +
            LocatedPurse.configComponents available =
          decodeRawConfig config := by
      rw [available_components]
      simpa [recv_source, send_source, locations_eq] using source_partition
    have declarative0 : CostStep
        (context +
          (.signed (.recv (decodeCostName recv.location)
            (decodeCostTerm recv.body)) (decodeCostSig recv.sig) ::ₘ 0) +
          (.signed (.send (decodeCostName recv.location)
            (decodeCostTerm send.payload)) (decodeCostSig send.sig) ::ₘ 0) +
          LocatedPurse.configComponents available)
        (decodeCostName recv.location)
        (decodeCostSig recv.sig + decodeCostSig send.sig) target :=
      CostStep.split (decodeCostSig_runtimeValid recv_ok.sig)
        (decodeCostSig_runtimeValid send_ok.sig) cover
    change CostStep
      (context +
        {CostTerm.signed
          (.recv (decodeCostName recv.location) (decodeCostTerm recv.body))
          (decodeCostSig recv.sig)} +
        {CostTerm.signed
          (.send (decodeCostName recv.location) (decodeCostTerm send.payload))
          (decodeCostSig send.sig)} +
        LocatedPurse.configComponents available)
      (decodeCostName recv.location)
      (decodeCostSig recv.sig + decodeCostSig send.sig) target
      at declarative0
    rw [source_eq] at declarative0
    rw [← decoded_spend] at declarative0
    refine ⟨target, declarative0, ?_, ?_, ?_⟩
    · have represented := residualFor_structurallyRepresents config
        [recv.index, send.index] selected recv.body send.payload
      simpa [target, context, residual, residual_components] using represented
    · intro signatureName signaturePure
      have erased := residualFor_eraseCanonical_structural signatureName
        signaturePure config [recv.index, send.index] selected
        (RawCostTerm.commSubst recv.body send.payload)
      simpa [target, context, residual, residual_components,
        RawCostTerm.normalize_idempotent, decodeCostTerm_commSubst,
        CostTerm.commSubst] using erased
    · intro sourceSafe
      have targetSafe := declarative0.preserves_binderSafe sourceSafe
      have residualSafe := residualFor_decode_binderSafe config
        [recv.index, send.index] selected
        (RawCostTerm.commSubst recv.body send.payload) (by
          simpa [target, context, residual, residual_components,
            decodeCostTerm_commSubst, CostTerm.commSubst,
            RawIndexedPurse.toTailTerm, Function.comp_def] using targetSafe)
      simpa [RawCostTerm.normalize_idempotent] using residualSafe
  next locations_mismatch => contradiction

/-- Every occurrence-sensitive executable candidate is justified by the
declarative located cost relation, modulo only structural normalization of
the successor. -/
theorem costStep_sound_runtime
    {config : RawCostConfig} (canonical : config.Canonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {step : RawRuntimeStep}
    (enabled : step ∈ runtimeCostCandidatesFromConfig config) :
    RuntimeCostStepSound config step := by
  rcases runtimeCostCandidatesFromConfig_origin enabled with
    ⟨redex, source, redex_member, source_mem, found, step_member⟩ |
      ⟨recv, send, recvSource, sendSource, recv_member, send_member,
        recv_mem, send_mem, recv_found, send_found, step_member⟩
  · exact wholeCandidate_sound canonical config_ok redex_member source_mem
      found enabled step_member
  · exact splitCandidate_sound canonical config_ok recv_member send_member
      recv_mem send_mem recv_found send_found enabled step_member

/-- Public successor deduplication preserves the executable soundness result. -/
theorem runtimeCostFrontier_sound
    {term : RawCostTerm} (supported : term.supported = true)
    {frontier : List RawRuntimeStep} {step : RawRuntimeStep}
    (evaluated : runtimeCostFrontier term = some frontier)
    (member : step ∈ frontier) :
    RuntimeCostStepSound term.normalizeConfig step := by
  have candidates_eval : runtimeCostCandidates term =
      some (runtimeCostCandidatesFromConfig term.normalizeConfig) := by
    simp [runtimeCostCandidates, supported]
  have wellFormed : term.wellFormed = true := by
    simp only [RawCostTerm.supported, Bool.and_eq_true] at supported
    exact supported.1
  unfold runtimeCostFrontier at evaluated
  rw [candidates_eval] at evaluated
  change some (deduplicatePublicTransitions
    (runtimeCostCandidatesFromConfig term.normalizeConfig)) = some frontier
    at evaluated
  have frontier_eq := Option.some.inj evaluated
  subst frontier
  have candidate := mem_of_mem_deduplicatePublicTransitions member
  exact costStep_sound_runtime (RawCostTerm.normalizeConfig_canonical term)
    (RawCostTerm.normalizeConfig_forall_wellFormed wellFormed) candidate

/-! ## Declarative-to-executable completeness -/

/-- Exact frame preservation is intensional: the successor is rebuilt from
the unselected source occurrences, the contractum, and only the selected
purse tails.  Structural equivalence alone is deliberately insufficient. -/
def RawRuntimeStep.FrameExactFor (step : RawRuntimeStep)
    (config : RawCostConfig) : Prop :=
  step.residual = residualFor config step.participantIndices
    step.selectedPurses step.contractum

private theorem wholeCandidates_frameExact
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {redex : RawWholeRedex} {step : RawRuntimeStep}
    (member : step ∈ wholeCandidates config purses redex) :
    step.FrameExactFor config := by
  simp only [wholeCandidates] at member
  obtain ⟨selected, _selected_member, rfl⟩ := List.mem_map.mp member
  rfl

private theorem splitCandidates_frameExact
    {config : RawCostConfig} {purses : List RawIndexedPurse}
    {recv : RawRecvEndpoint} {send : RawSendEndpoint}
    {step : RawRuntimeStep}
    (member : step ∈ splitCandidates config purses recv send) :
    step.FrameExactFor config := by
  unfold splitCandidates at member
  split at member
  · obtain ⟨selected, _selected_member, rfl⟩ := List.mem_map.mp member
    rfl
  · contradiction

theorem runtimeCostCandidatesFromConfig_frameExact
    {config : RawCostConfig} {step : RawRuntimeStep}
    (member : step ∈ runtimeCostCandidatesFromConfig config) :
    step.FrameExactFor config := by
  rcases runtimeCostCandidatesFromConfig_origin member with
    ⟨redex, source, _redex_member, _source_mem, _found, step_member⟩ |
      ⟨recv, send, recvSource, sendSource, _recv_member, _send_member,
        _recv_mem, _send_mem, _recv_found, _send_found, step_member⟩
  · exact wholeCandidates_frameExact step_member
  · exact splitCandidates_frameExact step_member

/-- Located forcing changes only the consumed participants and purse heads;
the exact unselected occurrence frame is retained by construction. -/
theorem located_forcing_locality
    {config : RawCostConfig} {step : RawRuntimeStep}
    (member : step ∈ runtimeCostCandidatesFromConfig config) :
    step.residual = residualFor config step.participantIndices
      step.selectedPurses step.contractum :=
  runtimeCostCandidatesFromConfig_frameExact member

/-- Full one-step completeness witness.  It identifies the exact raw firing,
matches its labels, relates its successor to the requested declarative target,
and retains the untouched raw frame by occurrence identity. -/
def RuntimeCostStepComplete (config : RawCostConfig)
    (location : CostName String) (spend : CostSig String)
    (target : CostConfig String) : Prop :=
  ∃ step : RawRuntimeStep,
    step ∈ runtimeCostCandidatesFromConfig config ∧
    decodeCostName step.location = location ∧
    decodeCostSig step.spend = spend ∧
    step.residual.normalizeConfig.StructurallyRepresents target ∧
    step.FrameExactFor config

/-- Invert a declarative step without eliminating a fixed multiset quotient
index.  The equalities expose the concrete source and target shape to the
independent runtime completeness proof. -/
theorem CostStep.exists_shape
    {source : CostConfig String} {observed : CostName String}
    {spent : CostSig String} {target : CostConfig String}
    (step : CostStep source observed spent target) :
    (∃ context available residual channel body payload outerSig,
        outerSig.RuntimeValid ∧
        Nonempty (LocatedTokenCover channel outerSig available residual) ∧
        source = context +
          ({.signed (.par (.recv channel body) (.send channel payload))
            outerSig} : CostConfig String) +
          LocatedPurse.configComponents available ∧
        observed = channel ∧ spent = outerSig ∧
        target = context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual) ∨
    (∃ context available residual channel body payload outerSig,
        outerSig.RuntimeValid ∧
        Nonempty (LocatedTokenCover channel outerSig available residual) ∧
        source = context +
          ({.signed (.par (.send channel payload) (.recv channel body))
            outerSig} : CostConfig String) +
          LocatedPurse.configComponents available ∧
        observed = channel ∧ spent = outerSig ∧
        target = context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual) ∨
    (∃ context available residual channel body payload recvSeal sendSeal,
        recvSeal.RuntimeValid ∧ sendSeal.RuntimeValid ∧
        Nonempty (LocatedTokenCover channel (recvSeal + sendSeal)
          available residual) ∧
        source = context +
          ({.signed (.recv channel body) recvSeal} : CostConfig String) +
          ({.signed (.send channel payload) sendSeal} : CostConfig String) +
          LocatedPurse.configComponents available ∧
        observed = channel ∧ spent = recvSeal + sendSeal ∧
        target = context + (body.commSubst payload).components +
          LocatedPurse.configComponents residual) := by
  cases step with
  | wholeRecvSend signature_valid cover =>
      exact .inl ⟨_, _, _, _, _, _, _, signature_valid, ⟨cover⟩,
        rfl, rfl, rfl, rfl⟩
  | wholeSendRecv signature_valid cover =>
      exact .inr (.inl ⟨_, _, _, _, _, _, _, signature_valid, ⟨cover⟩,
        rfl, rfl, rfl, rfl⟩)
  | split recv_valid send_valid cover =>
      exact .inr (.inr ⟨_, _, _, _, _, _, _, _, recv_valid, send_valid,
        ⟨cover⟩, rfl, rfl, rfl, rfl⟩)

private theorem wholeRecvSend_complete
    {config : RawCostConfig} (canonical : config.Canonical)
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {context : CostConfig String}
    {available residual : Multiset (LocatedPurse String)}
    {channel : CostName String} {body payload : CostTerm String}
    {outerSig : CostSig String}
    (cover : LocatedTokenCover channel outerSig available residual)
    (source_eq : decodeRawConfig config = context +
      ({.signed (.par (.recv channel body) (.send channel payload))
        outerSig} : CostConfig String) +
      LocatedPurse.configComponents available)
    {target : CostConfig String}
    (target_eq : target = context + (body.commSubst payload).components +
      LocatedPurse.configComponents residual) :
    RuntimeCostStepComplete config channel outerSig target := by
  let participant : CostTerm String :=
    .signed (.par (.recv channel body) (.send channel payload)) outerSig
  have participant_mem : participant ∈ decodeRawConfig config := by
    rw [source_eq]
    simp [participant]
  obtain ⟨source, index, source_mem, decoded_source⟩ :=
    exists_raw_zipIdx_of_mem_decodeRawConfig participant_mem
  have source_encoding :=
    RawCostConfig.encodingCanonical_of_mem_zipIdx encoding source_mem
  obtain ⟨redex, found⟩ := exists_wholeAt?_of_decode_recv_send
    (index := index) source_encoding decoded_source
  have redex_index := wholeAt?_index found
  subst index
  have redex_member : redex ∈ config.wholeRedexes :=
    mem_collectWholesAux_of_mem_zipIdx source_mem found
  have source_normalized :=
    RawCostConfig.normalized_of_mem_zipIdx canonical source_mem
  obtain ⟨decoded_location, decoded_body, decoded_payload, decoded_sig⟩ :=
    wholeAt?_decoded_fields_recv_send source_normalized found decoded_source
  have available_le : LocatedPurse.configComponents available ≤
      decodeRawConfig config := by
    rw [source_eq]
    exact Multiset.le_add_left _ _
  obtain ⟨selected, selected_source, selected_eq⟩ :=
    exists_raw_selectedBefore cover available_le
  have selected_valid : selected.Forall
      (fun purse => purse.head.valid = true) := by
    rw [List.forall_iff_forall_mem]
    intro purse purse_mem
    have purse_ok := List.forall_iff_forall_mem.mp
      (RawCostConfig.purses_forall_wellFormed config_ok) purse
      (selected_source.mem purse_mem)
    exact purse_ok.head
  have matching := recoveredSelected_sublist_matching canonical cover
    selected_source selected_eq (wholeAt?_location_normalized found)
    decoded_location
  have exact_spend : rawSelectedSpend selected = redex.sig.toMultiset := by
    calc
      rawSelectedSpend selected = outerSig :=
        rawSelectedSpend_eq_demand cover selected_eq
      _ = decodeCostSig redex.sig := decoded_sig.symm
      _ = redex.sig.toMultiset := rfl
  have cover_member : selected ∈ exactPurseCovers redex.sig
      (matchingPurses redex.location config.purses) :=
    exactPurseCovers_complete matching selected_valid exact_spend
  let contractum :=
    (RawCostTerm.commSubst redex.body redex.payload).normalize
  let runtimeStep : RawRuntimeStep :=
    { shape :=
        match config[redex.index]? with
        | some (.signed (.par (.send _ _) (.recv _ _)) _) => .wholeSendRecv
        | _ => .wholeRecvSend
      location := redex.location
      spend := redex.sig
      participantIndices := [redex.index]
      selectedPurses := selected
      contractum
      residual := residualFor config [redex.index] selected contractum }
  have step_member : runtimeStep ∈
      wholeCandidates config config.purses redex := by
    unfold wholeCandidates
    apply List.mem_map.mpr
    exact ⟨selected, cover_member, rfl⟩
  have enabled : runtimeStep ∈ runtimeCostCandidatesFromConfig config := by
    unfold runtimeCostCandidatesFromConfig
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl ⟨redex, redex_member, step_member⟩
  have frame_eq := whole_recovered_frame_eq_context source_mem found
    selected_source cover selected_eq decoded_source source_eq
  have selected_tails :=
    decodedSelectedTailTerms_eq_selectedAfter_components cover selected_eq
  have residual_components : LocatedPurse.configComponents residual =
      LocatedPurse.configComponents cover.selectedAfter +
        LocatedPurse.configComponents cover.untouched := by
    calc
      LocatedPurse.configComponents residual =
          LocatedPurse.configComponents
            (cover.selectedAfter + cover.untouched) :=
        congrArg LocatedPurse.configComponents cover.residual_decomposition
      _ = LocatedPurse.configComponents cover.selectedAfter +
          LocatedPurse.configComponents cover.untouched := by
        simp [LocatedPurse.configComponents, Multiset.map_add]
  have declarative_target :
      decodeRawConfig (eraseIndices config
          ([redex.index] ++ selected.map RawIndexedPurse.index)) +
          (CostTerm.commSubst (decodeCostTerm redex.body)
            (decodeCostTerm redex.payload)).components +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String)) = target := by
    rw [frame_eq, decoded_body, decoded_payload, selected_tails, target_eq]
    rw [residual_components]
    ac_rfl
  have represented := residualFor_structurallyRepresents config [redex.index]
    selected redex.body redex.payload
  rw [declarative_target] at represented
  refine ⟨runtimeStep, enabled, ?_, ?_, ?_,
    runtimeCostCandidatesFromConfig_frameExact enabled⟩
  · simpa [runtimeStep] using decoded_location
  · simpa [runtimeStep] using decoded_sig
  · simpa [runtimeStep, contractum] using represented

private theorem wholeSendRecv_complete
    {config : RawCostConfig} (canonical : config.Canonical)
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {context : CostConfig String}
    {available residual : Multiset (LocatedPurse String)}
    {channel : CostName String} {body payload : CostTerm String}
    {outerSig : CostSig String}
    (cover : LocatedTokenCover channel outerSig available residual)
    (source_eq : decodeRawConfig config = context +
      ({.signed (.par (.send channel payload) (.recv channel body))
        outerSig} : CostConfig String) +
      LocatedPurse.configComponents available)
    {target : CostConfig String}
    (target_eq : target = context + (body.commSubst payload).components +
      LocatedPurse.configComponents residual) :
    RuntimeCostStepComplete config channel outerSig target := by
  let participant : CostTerm String :=
    .signed (.par (.send channel payload) (.recv channel body)) outerSig
  have participant_mem : participant ∈ decodeRawConfig config := by
    rw [source_eq]
    simp [participant]
  obtain ⟨source, index, source_mem, decoded_source⟩ :=
    exists_raw_zipIdx_of_mem_decodeRawConfig participant_mem
  have source_encoding :=
    RawCostConfig.encodingCanonical_of_mem_zipIdx encoding source_mem
  obtain ⟨redex, found⟩ := exists_wholeAt?_of_decode_send_recv
    (index := index) source_encoding decoded_source
  have redex_index := wholeAt?_index found
  subst index
  have redex_member : redex ∈ config.wholeRedexes :=
    mem_collectWholesAux_of_mem_zipIdx source_mem found
  have source_normalized :=
    RawCostConfig.normalized_of_mem_zipIdx canonical source_mem
  obtain ⟨decoded_location, decoded_body, decoded_payload, decoded_sig⟩ :=
    wholeAt?_decoded_fields_send_recv source_normalized found decoded_source
  have available_le : LocatedPurse.configComponents available ≤
      decodeRawConfig config := by
    rw [source_eq]
    exact Multiset.le_add_left _ _
  obtain ⟨selected, selected_source, selected_eq⟩ :=
    exists_raw_selectedBefore cover available_le
  have selected_valid : selected.Forall
      (fun purse => purse.head.valid = true) := by
    rw [List.forall_iff_forall_mem]
    intro purse purse_mem
    have purse_ok := List.forall_iff_forall_mem.mp
      (RawCostConfig.purses_forall_wellFormed config_ok) purse
      (selected_source.mem purse_mem)
    exact purse_ok.head
  have matching := recoveredSelected_sublist_matching canonical cover
    selected_source selected_eq (wholeAt?_location_normalized found)
    decoded_location
  have exact_spend : rawSelectedSpend selected = redex.sig.toMultiset := by
    calc
      rawSelectedSpend selected = outerSig :=
        rawSelectedSpend_eq_demand cover selected_eq
      _ = decodeCostSig redex.sig := decoded_sig.symm
      _ = redex.sig.toMultiset := rfl
  have cover_member : selected ∈ exactPurseCovers redex.sig
      (matchingPurses redex.location config.purses) :=
    exactPurseCovers_complete matching selected_valid exact_spend
  let contractum :=
    (RawCostTerm.commSubst redex.body redex.payload).normalize
  let runtimeStep : RawRuntimeStep :=
    { shape :=
        match config[redex.index]? with
        | some (.signed (.par (.send _ _) (.recv _ _)) _) => .wholeSendRecv
        | _ => .wholeRecvSend
      location := redex.location
      spend := redex.sig
      participantIndices := [redex.index]
      selectedPurses := selected
      contractum
      residual := residualFor config [redex.index] selected contractum }
  have step_member : runtimeStep ∈
      wholeCandidates config config.purses redex := by
    unfold wholeCandidates
    apply List.mem_map.mpr
    exact ⟨selected, cover_member, rfl⟩
  have enabled : runtimeStep ∈ runtimeCostCandidatesFromConfig config := by
    unfold runtimeCostCandidatesFromConfig
    simp only [List.mem_append, List.mem_flatMap]
    exact .inl ⟨redex, redex_member, step_member⟩
  have frame_eq := whole_recovered_frame_eq_context source_mem found
    selected_source cover selected_eq decoded_source source_eq
  have selected_tails :=
    decodedSelectedTailTerms_eq_selectedAfter_components cover selected_eq
  have residual_components : LocatedPurse.configComponents residual =
      LocatedPurse.configComponents cover.selectedAfter +
        LocatedPurse.configComponents cover.untouched := by
    calc
      LocatedPurse.configComponents residual =
          LocatedPurse.configComponents
            (cover.selectedAfter + cover.untouched) :=
        congrArg LocatedPurse.configComponents cover.residual_decomposition
      _ = LocatedPurse.configComponents cover.selectedAfter +
          LocatedPurse.configComponents cover.untouched := by
        simp [LocatedPurse.configComponents, Multiset.map_add]
  have declarative_target :
      decodeRawConfig (eraseIndices config
          ([redex.index] ++ selected.map RawIndexedPurse.index)) +
          (CostTerm.commSubst (decodeCostTerm redex.body)
            (decodeCostTerm redex.payload)).components +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String)) = target := by
    rw [frame_eq, decoded_body, decoded_payload, selected_tails, target_eq]
    rw [residual_components]
    ac_rfl
  have represented := residualFor_structurallyRepresents config [redex.index]
    selected redex.body redex.payload
  rw [declarative_target] at represented
  refine ⟨runtimeStep, enabled, ?_, ?_, ?_,
    runtimeCostCandidatesFromConfig_frameExact enabled⟩
  · simpa [runtimeStep] using decoded_location
  · simpa [runtimeStep] using decoded_sig
  · simpa [runtimeStep, contractum] using represented

private theorem split_complete
    {config : RawCostConfig} (canonical : config.Canonical)
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {context : CostConfig String}
    {available residual : Multiset (LocatedPurse String)}
    {channel : CostName String} {body payload : CostTerm String}
    {recvSeal sendSeal : CostSig String}
    (cover : LocatedTokenCover channel (recvSeal + sendSeal)
      available residual)
    (source_eq : decodeRawConfig config = context +
      ({.signed (.recv channel body) recvSeal} : CostConfig String) +
      ({.signed (.send channel payload) sendSeal} : CostConfig String) +
      LocatedPurse.configComponents available)
    {target : CostConfig String}
    (target_eq : target = context + (body.commSubst payload).components +
      LocatedPurse.configComponents residual) :
    RuntimeCostStepComplete config channel (recvSeal + sendSeal) target := by
  let recvParticipant : CostTerm String := .signed (.recv channel body) recvSeal
  let sendParticipant : CostTerm String := .signed (.send channel payload) sendSeal
  have recv_participant_mem : recvParticipant ∈ decodeRawConfig config := by
    rw [source_eq]
    simp [recvParticipant]
  have send_participant_mem : sendParticipant ∈ decodeRawConfig config := by
    rw [source_eq]
    simp [sendParticipant]
  obtain ⟨recvSource, recvIndex, recv_mem, decoded_recvSource⟩ :=
    exists_raw_zipIdx_of_mem_decodeRawConfig recv_participant_mem
  obtain ⟨sendSource, sendIndex, send_mem, decoded_sendSource⟩ :=
    exists_raw_zipIdx_of_mem_decodeRawConfig send_participant_mem
  have recv_encoding :=
    RawCostConfig.encodingCanonical_of_mem_zipIdx encoding recv_mem
  have send_encoding :=
    RawCostConfig.encodingCanonical_of_mem_zipIdx encoding send_mem
  obtain ⟨recv, recv_found⟩ := exists_recvAt?_of_decode
    (index := recvIndex) recv_encoding decoded_recvSource
  obtain ⟨send, send_found⟩ := exists_sendAt?_of_decode
    (index := sendIndex) send_encoding decoded_sendSource
  have recv_index := recvAt?_index recv_found
  have send_index := sendAt?_index send_found
  subst recvIndex
  subst sendIndex
  have recv_member : recv ∈ config.recvEndpoints :=
    mem_collectRecvsAux_of_mem_zipIdx recv_mem recv_found
  have send_member : send ∈ config.sendEndpoints :=
    mem_collectSendsAux_of_mem_zipIdx send_mem send_found
  have recv_normalized :=
    RawCostConfig.normalized_of_mem_zipIdx canonical recv_mem
  have send_normalized :=
    RawCostConfig.normalized_of_mem_zipIdx canonical send_mem
  obtain ⟨decoded_recv_location, decoded_body, decoded_recv_sig⟩ :=
    recvAt?_decoded_fields recv_normalized recv_found decoded_recvSource
  obtain ⟨decoded_send_location, decoded_payload, decoded_send_sig⟩ :=
    sendAt?_decoded_fields send_normalized send_found decoded_sendSource
  have recv_location_fixed := recvAt?_location_normalized recv_found
  have send_location_fixed := sendAt?_location_normalized send_found
  have recv_location_canonical : recv.location.EncodingCanonical := by
    rw [← recv_location_fixed]
    exact RawCostName.normalize_encodingCanonical recv.location
  have send_location_canonical : send.location.EncodingCanonical := by
    rw [← send_location_fixed]
    exact RawCostName.normalize_encodingCanonical send.location
  have locations_eq : send.location = recv.location :=
    RawCostName.decode_injective_of_encodingCanonical
      send_location_canonical recv_location_canonical
      (decoded_send_location.trans decoded_recv_location.symm)
  have locations_match : recv.location.normalize = send.location.normalize := by
    simp [locations_eq]
  have available_le : LocatedPurse.configComponents available ≤
      decodeRawConfig config := by
    rw [source_eq]
    exact Multiset.le_add_left _ _
  obtain ⟨selected, selected_source, selected_eq⟩ :=
    exists_raw_selectedBefore cover available_le
  have selected_valid : selected.Forall
      (fun purse => purse.head.valid = true) := by
    rw [List.forall_iff_forall_mem]
    intro purse purse_mem
    have purse_ok := List.forall_iff_forall_mem.mp
      (RawCostConfig.purses_forall_wellFormed config_ok) purse
      (selected_source.mem purse_mem)
    exact purse_ok.head
  have matching := recoveredSelected_sublist_matching canonical cover
    selected_source selected_eq recv_location_fixed decoded_recv_location
  let runtimeSpend := (recv.sig ++ send.sig).normalize
  have decoded_runtimeSpend : decodeCostSig runtimeSpend = recvSeal + sendSeal := by
    change ((recv.sig ++ send.sig).normalize : Multiset String) =
      recvSeal + sendSeal
    rw [RawCostSig.normalize_toMultiset]
    change decodeCostSig recv.sig + decodeCostSig send.sig = recvSeal + sendSeal
    rw [decoded_recv_sig, decoded_send_sig]
  have exact_spend : rawSelectedSpend selected = runtimeSpend.toMultiset := by
    calc
      rawSelectedSpend selected = recvSeal + sendSeal :=
        rawSelectedSpend_eq_demand cover selected_eq
      _ = decodeCostSig runtimeSpend := decoded_runtimeSpend.symm
      _ = runtimeSpend.toMultiset := rfl
  have cover_member : selected ∈ exactPurseCovers runtimeSpend
      (matchingPurses recv.location config.purses) :=
    exactPurseCovers_complete matching selected_valid exact_spend
  let contractum :=
    (RawCostTerm.commSubst recv.body send.payload).normalize
  let runtimeStep : RawRuntimeStep :=
    { shape := .split
      location := recv.location
      spend := runtimeSpend
      participantIndices := [recv.index, send.index]
      selectedPurses := selected
      contractum
      residual := residualFor config [recv.index, send.index] selected contractum }
  have step_member : runtimeStep ∈
      splitCandidates config config.purses recv send := by
    unfold splitCandidates
    rw [if_pos locations_match]
    apply List.mem_map.mpr
    exact ⟨selected, cover_member, rfl⟩
  have enabled : runtimeStep ∈ runtimeCostCandidatesFromConfig config := by
    unfold runtimeCostCandidatesFromConfig
    simp only [List.mem_append, List.mem_flatMap]
    exact .inr ⟨recv, recv_member, ⟨send, send_member, step_member⟩⟩
  have frame_eq := split_recovered_frame_eq_context recv_mem send_mem
    recv_found send_found selected_source cover selected_eq decoded_recvSource
    decoded_sendSource source_eq
  have selected_tails :=
    decodedSelectedTailTerms_eq_selectedAfter_components cover selected_eq
  have residual_components : LocatedPurse.configComponents residual =
      LocatedPurse.configComponents cover.selectedAfter +
        LocatedPurse.configComponents cover.untouched := by
    calc
      LocatedPurse.configComponents residual =
          LocatedPurse.configComponents
            (cover.selectedAfter + cover.untouched) :=
        congrArg LocatedPurse.configComponents cover.residual_decomposition
      _ = LocatedPurse.configComponents cover.selectedAfter +
          LocatedPurse.configComponents cover.untouched := by
        simp [LocatedPurse.configComponents, Multiset.map_add]
  have declarative_target :
      decodeRawConfig (eraseIndices config
          ([recv.index, send.index] ++ selected.map RawIndexedPurse.index)) +
          (CostTerm.commSubst (decodeCostTerm recv.body)
            (decodeCostTerm send.payload)).components +
          (selected.map (decodeCostTerm ∘ RawIndexedPurse.toTailTerm) :
            Multiset (CostTerm String)) = target := by
    rw [frame_eq, decoded_body, decoded_payload, selected_tails, target_eq]
    rw [residual_components]
    ac_rfl
  have represented := residualFor_structurallyRepresents config
    [recv.index, send.index] selected recv.body send.payload
  rw [declarative_target] at represented
  refine ⟨runtimeStep, enabled, ?_, ?_, ?_,
    runtimeCostCandidatesFromConfig_frameExact enabled⟩
  · simpa [runtimeStep] using decoded_recv_location
  · simpa [runtimeStep] using decoded_runtimeSpend
  · simpa [runtimeStep, contractum] using represented

/-- Every declarative step over a canonical, supported raw configuration is
enumerated by the independent executable frontier, with the requested target
matched modulo only structural normalization and with exact raw frame
preservation. -/
theorem costStep_complete_runtime_up_to_struct
    {config : RawCostConfig} (canonical : config.Canonical)
    (encoding : config.Forall RawCostTerm.EncodingCanonical)
    (config_ok : config.Forall (fun term => term.wellFormed = true))
    {location : CostName String} {spend : CostSig String}
    {target : CostConfig String}
    (declarative : CostStep (decodeRawConfig config) location spend target) :
    RuntimeCostStepComplete config location spend target := by
  rcases declarative.exists_shape with whole_recv | whole_send | split
  · obtain ⟨context, available, residual, channel, body, payload, outerSig,
      _sig_valid, ⟨cover⟩, source_eq, location_eq, spend_eq, target_eq⟩ :=
      whole_recv
    subst location
    subst spend
    exact wholeRecvSend_complete canonical encoding config_ok cover source_eq
      target_eq
  · obtain ⟨context, available, residual, channel, body, payload, outerSig,
      _sig_valid, ⟨cover⟩, source_eq, location_eq, spend_eq, target_eq⟩ :=
      whole_send
    subst location
    subst spend
    exact wholeSendRecv_complete canonical encoding config_ok cover source_eq
      target_eq
  · obtain ⟨context, available, residual, channel, body, payload,
      recvSeal, sendSeal, _recv_valid, _send_valid, ⟨cover⟩, source_eq,
      location_eq, spend_eq, target_eq⟩ := split
    subst location
    subst spend
    exact split_complete canonical encoding config_ok cover source_eq target_eq

/-- Canonicalization supplies every hypothesis of one-step completeness for a
well-formed executable input term. -/
theorem runtimeCostCandidates_complete_up_to_struct
    {term : RawCostTerm} (supported : term.wellFormed = true)
    {location : CostName String} {spend : CostSig String}
    {target : CostConfig String}
    (declarative : CostStep (decodeRawConfig term.normalizeConfig)
      location spend target) :
    RuntimeCostStepComplete term.normalizeConfig location spend target :=
  costStep_complete_runtime_up_to_struct
    (RawCostTerm.normalizeConfig_canonical term)
    (RawCostTerm.normalizeConfig_forall_encodingCanonical term)
    (RawCostTerm.normalizeConfig_forall_wellFormed supported)
    declarative

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.Cost
