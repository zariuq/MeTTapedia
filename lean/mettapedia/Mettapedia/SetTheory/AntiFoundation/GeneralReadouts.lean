import Mettapedia.SetTheory.AntiFoundation.Distinctions
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualSeparationCollectionControls
import Mettapedia.TypeTheory.MaterialSets.Hypersets.MaterialIdentityObservation
import Mettapedia.TypeTheory.MaterialSets.Hypersets.UnfoldingIdentityComparison

/-!
# General anti-foundation readouts and the finite menu

The finite picture menu compares Boffa, Finsler, Scott, Aczel and Foundation
by recovery on eleven pictures. Those recoveries are not embeddings of the
material sets.

Four general criteria sit above that menu. Bisimulation is the kernel of
Aczel decoration. Full unfolding-tree isomorphism is Scott equality of roots
on a Scott-extensional graph, and it is strictly finer than bisimulation.
Pointed-downset isomorphism is a bijection of the accessible graph that
preserves the child relation and the distinguished node. Retained occurrence
identity keeps a presentation witness beside its material picture.

A material member family descends along the discrete readout. An
occurrence-sensitive family does not, even up to a natural fibre equivalence.
A supplied separation section can vary. Coverage of an infinite Nat-loop
action is not a natural section, and the all-witness collection of that
action is not coherent dependent choice.
-/

set_option autoImplicit false

open _root_.CategoryTheory
open scoped _root_.CategoryTheory

namespace Mettapedia.SetTheory.AntiFoundation.GeneralReadouts

open Mettapedia.SetTheory.AntiFoundation
open Mettapedia.GSLT.Core.NonFactorization
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open Mettapedia.TypeTheory.GroupoidIdentityElimination
open AccessiblePointedGraph
open PresentationIdentityControls
open UnfoldingIdentityComparison
open MaterialIdentityObservation
open ContextualSeparationCollectionControls

/-! ## The picture menu does not receive the naturals -/

def picIndex : Pic → Fin 11
  | .empty => 0
  | .loopA => 1
  | .loopB => 2
  | .cycL => 3
  | .cycR => 4
  | .scott0 => 5
  | .scott1 => 6
  | .fin0 => 7
  | .fin1 => 8
  | .fin2 => 9
  | .nest => 10

theorem picIndex_injective : Function.Injective picIndex := by
  intro a b same
  cases a <;> cases b <;> first | rfl | exact absurd (congrArg Fin.val same) (by decide)

/-- Values other than `target` land in `Fin n` by closing the hole at `target`. -/
def squash {n : Nat} (target value : Fin (n + 1)) (different : value ≠ target) : Fin n :=
  if lower : value.val < target.val then
    ⟨value.val, Nat.lt_of_lt_of_le lower (Nat.le_of_lt_succ target.isLt)⟩
  else
    ⟨value.val - 1, by
      have notLower : target.val ≤ value.val := Nat.le_of_not_lt lower
      have greater : target.val < value.val :=
        Nat.lt_of_le_of_ne notLower (fun equal => different (Fin.ext equal.symm))
      have oneLe : 1 ≤ value.val :=
        Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le target.val) greater)
      have valueLe : value.val ≤ n := Nat.le_of_lt_succ value.isLt
      cases Nat.lt_or_eq_of_le valueLe with
      | inl below => exact Nat.lt_of_le_of_lt (Nat.pred_le value.val) below
      | inr atTop =>
        have nPos : 0 < n := Nat.lt_of_lt_of_le (Nat.zero_lt_one) (atTop ▸ oneLe)
        rw [atTop]
        exact Nat.sub_lt nPos (Nat.zero_lt_one)⟩

theorem squash_val_below {n : Nat} {target value : Fin (n + 1)} (different : value ≠ target)
    (lower : value.val < target.val) : (squash target value different).val = value.val := by
  unfold squash
  rw [dif_pos lower]

theorem squash_val_above {n : Nat} {target value : Fin (n + 1)} (different : value ≠ target)
    (notLower : ¬ value.val < target.val) : (squash target value different).val = value.val - 1 := by
  unfold squash
  rw [dif_neg notLower]

private theorem not_target_is_positive {n : Nat} {target value : Fin (n + 1)}
    (different : value ≠ target) (notLower : ¬ value.val < target.val) : 0 < value.val := by
  cases valueZero : value.val with
  | zero =>
    have targetLeValue : target.val ≤ value.val := Nat.le_of_not_lt notLower
    have targetLeZero : target.val ≤ 0 := by
      rw [valueZero] at targetLeValue
      exact targetLeValue
    have targetZero : target.val = 0 := Nat.le_antisymm targetLeZero (Nat.zero_le _)
    exact absurd (Fin.ext (valueZero.trans targetZero.symm)) different
  | succ _ => exact Nat.succ_pos _

theorem squash_injective {n : Nat} (target : Fin (n + 1))
    {first second : Fin (n + 1)} (firstNe : first ≠ target) (secondNe : second ≠ target)
    (same : squash target first firstNe = squash target second secondNe) : first = second := by
  have values : (squash target first firstNe).val = (squash target second secondNe).val :=
    congrArg Fin.val same
  by_cases firstLower : first.val < target.val
  · by_cases secondLower : second.val < target.val
    · rw [squash_val_below firstNe firstLower, squash_val_below secondNe secondLower] at values
      exact Fin.ext values
    · rw [squash_val_below firstNe firstLower, squash_val_above secondNe secondLower] at values
      have predLt : second.val - 1 < target.val := by rw [← values]; exact firstLower
      have secondPos : 0 < second.val := not_target_is_positive secondNe secondLower
      have secondLe : second.val ≤ target.val := by
        have step : (second.val - 1).succ ≤ target.val := Nat.succ_le_of_lt predLt
        have restored : second.val = (second.val - 1).succ := by
          rw [Nat.succ_eq_add_one]
          exact (Nat.sub_add_cancel (Nat.succ_le_of_lt secondPos)).symm
        rw [restored]
        exact step
      exact absurd (Fin.ext (Nat.le_antisymm (Nat.le_of_not_lt secondLower) secondLe))
        (Ne.symm secondNe)
  · by_cases secondLower : second.val < target.val
    · rw [squash_val_above firstNe firstLower, squash_val_below secondNe secondLower] at values
      have predLt : first.val - 1 < target.val := by rw [values]; exact secondLower
      have firstPos : 0 < first.val := not_target_is_positive firstNe firstLower
      have firstLe : first.val ≤ target.val := by
        have step : (first.val - 1).succ ≤ target.val := Nat.succ_le_of_lt predLt
        have restored : first.val = (first.val - 1).succ := by
          rw [Nat.succ_eq_add_one]
          exact (Nat.sub_add_cancel (Nat.succ_le_of_lt firstPos)).symm
        rw [restored]
        exact step
      exact absurd (Fin.ext (Nat.le_antisymm (Nat.le_of_not_lt firstLower) firstLe))
        (Ne.symm firstNe)
    · rw [squash_val_above firstNe firstLower, squash_val_above secondNe secondLower] at values
      have firstPos : 0 < first.val := not_target_is_positive firstNe firstLower
      have secondPos : 0 < second.val := not_target_is_positive secondNe secondLower
      have firstRestore : (first.val - 1).succ = first.val := by
        rw [Nat.succ_eq_add_one]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt firstPos)
      have secondRestore : (second.val - 1).succ = second.val := by
        rw [Nat.succ_eq_add_one]
        exact Nat.sub_add_cancel (Nat.succ_le_of_lt secondPos)
      apply Fin.ext
      rw [← firstRestore, ← secondRestore]
      exact congrArg Nat.succ values

def findFrom (n : Nat) (p : Fin n → Bool) (start : Nat) : Option (Fin n) :=
  if enough : start < n then
    match p ⟨start, enough⟩ with
    | true => some ⟨start, enough⟩
    | false => findFrom n p (start + 1)
  else
    none
termination_by n - start

theorem findFrom_some_agrees {n : Nat} (p : Fin n → Bool) (start : Nat) (found : Fin n)
    (hit : findFrom n p start = some found) : start ≤ found.val ∧ p found = true := by
  rw [findFrom] at hit
  by_cases enough : start < n
  · rw [dif_pos enough] at hit
    cases agrees : p ⟨start, enough⟩ with
    | true =>
      rw [agrees] at hit
      cases hit
      exact ⟨Nat.le_refl _, agrees⟩
    | false =>
      rw [agrees] at hit
      have later := findFrom_some_agrees p (start + 1) found hit
      exact ⟨Nat.le_trans (Nat.le_succ _) later.1, later.2⟩
  · rw [dif_neg enough] at hit
    cases hit
termination_by n - start
decreasing_by
  exact Nat.sub_succ_lt_self n start enough

theorem findFrom_none_avoids {n : Nat} (p : Fin n → Bool) (start : Nat)
    (miss : findFrom n p start = none) (index : Fin n) (fromStart : start ≤ index.val) :
    p index = false := by
  rw [findFrom] at miss
  by_cases enough : start < n
  · rw [dif_pos enough] at miss
    cases agrees : p ⟨start, enough⟩ with
    | true =>
      rw [agrees] at miss
      cases miss
    | false =>
      rw [agrees] at miss
      by_cases here : index.val = start
      · have indexHere : index = ⟨start, enough⟩ := Fin.ext here
        rw [indexHere]
        exact agrees
      · exact findFrom_none_avoids p (start + 1) miss index
          (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne fromStart (Ne.symm here)))
  · exact absurd (Nat.lt_of_le_of_lt fromStart index.isLt) enough
termination_by n - start
decreasing_by
  exact Nat.sub_succ_lt_self n start enough

def locateDuplicate :
    (n : Nat) → (g : Fin (n + 1) → Fin n) →
      {pair : Fin (n + 1) × Fin (n + 1) // pair.1 ≠ pair.2 ∧ g pair.1 = g pair.2}
  | 0, g =>
    False.elim (Nat.not_lt_zero (g ⟨0, Nat.zero_lt_one⟩).val (g ⟨0, Nat.zero_lt_one⟩).isLt)
  | n + 1, g =>
    let last := Fin.last (n + 1)
    let earlier (index : Fin (n + 1)) : Bool :=
      decide (g (Fin.castSucc index) = g last)
    match found : findFrom (n + 1) earlier 0 with
    | some index => by
      have agreed := findFrom_some_agrees earlier 0 index found
      have sameImage : g (Fin.castSucc index) = g last :=
        of_decide_eq_true agreed.2
      exact ⟨(Fin.castSucc index, last), by
        refine ⟨?_, sameImage⟩
        intro same
        exact Nat.ne_of_lt index.isLt (congrArg Fin.val same)⟩
    | none => by
      let target := g last
      let avoided (index : Fin (n + 1)) : g (Fin.castSucc index) ≠ target := by
        intro same
        have hit : earlier index = true := decide_eq_true same
        have missed : earlier index = false :=
          findFrom_none_avoids earlier 0 found index (Nat.zero_le _)
        cases hit.symm.trans missed
      let smaller : Fin (n + 1) → Fin n :=
        fun index => squash target (g (Fin.castSucc index)) (avoided index)
      let nested := locateDuplicate n smaller
      have different : Fin.castSucc nested.1.1 ≠ Fin.castSucc nested.1.2 := by
        intro same
        exact nested.2.1 (Fin.castSucc_inj.mp same)
      have sameImage : g (Fin.castSucc nested.1.1) = g (Fin.castSucc nested.1.2) :=
        squash_injective target (avoided nested.1.1) (avoided nested.1.2) nested.2.2
      exact ⟨(Fin.castSucc nested.1.1, Fin.castSucc nested.1.2), different, sameImage⟩

theorem nat_fin_not_injective (n : Nat) (g : Fin (n + 1) → Fin n) : ¬ Function.Injective g := by
  intro injective
  let found := locateDuplicate n g
  exact found.2.1 (injective found.2.2)

theorem picture_menu_admits_no_nat_section (assign : Nat → Pic) : ¬ Function.Injective assign := by
  intro injective
  let indexed : Fin 12 → Fin 11 := fun index => picIndex (assign index.val)
  have indexedInjective : Function.Injective indexed := by
    intro first second same
    exact Fin.ext (injective (picIndex_injective same))
  exact nat_fin_not_injective 11 indexed indexedInjective

/-- Recovery along the finite menu is not an embedding of the material sets.
`naturalMembers` injects the host naturals into the constructed natural set. -/
theorem finite_menu_does_not_embed_material_sets.{u} (embed : HSet.{u} → Pic) :
    Factors denoteBAFA denoteFAFA ∧ Factors denoteFAFA denoteSAFA ∧
      Factors denoteSAFA denoteAFA ∧ Factors denoteAFA denoteFoundation ∧
      ¬ Function.Injective embed := by
  refine ⟨factors_bafa_fafa, factors_fafa_safa, factors_safa_afa, factors_afa_found, ?_⟩
  intro injective
  apply picture_menu_admits_no_nat_section
    (fun number => embed (NaturalOrdinalModel.naturalMembers number).val)
  intro first second same
  exact NaturalOrdinalModel.naturalMembers_injective (Subtype.ext (injective same))

theorem finite_scott_denotation_collapses :
    Bisimilar scottEdge scottEdge .s0 .s1 ∧ denoteAFA .scott0 = denoteAFA .scott1 ∧
      Pic.scott0 ≠ Pic.scott1 := by
  refine ⟨scott_s0_bisim_s1, rfl, ?_⟩
  intro same
  exact Pic.noConfusion same

/-! ## Bisimulation and full unfolding trees -/

/-- On the Scott-extensional unary/binary graph, unfolding-tree isomorphism
is equality of roots. Bisimulation identifies the two roots, and the Aczel
decoration therefore has no injective section. -/
theorem unfolding_kernel_finer_than_bisimulation.{u} :
    ScottExtensional UnaryBinary.edge.{u} ∧
      Bisimilar UnaryBinary.edge.{u} UnaryBinary.edge
        (⟨true⟩ : ULift.{u, 0} Bool) (⟨false⟩ : ULift.{u, 0} Bool) ∧
      ¬ (⟨true⟩ : ULift.{u, 0} Bool) = ⟨false⟩ ∧
      ¬ Nonempty (PresentationIso (unfold UnaryBinary.edge.{u} ⟨true⟩)
        (unfold UnaryBinary.edge ⟨false⟩)) ∧
      ¬ ∃ decoration : ULift.{u, 0} Bool → HSet.{u},
        HSet.IsDecoration UnaryBinary.edge.{u} decoration ∧ Function.Injective decoration :=
  ⟨UnaryBinary.scottExtensional,
    UnaryBinary.all_nodes_bisimilar (⟨true⟩ : ULift.{u, 0} Bool) (⟨false⟩ : ULift.{u, 0} Bool),
    fun same => Bool.noConfusion (congrArg ULift.down same),
    UnaryBinary.no_binary_unary_unfolding_iso, UnaryBinary.no_injective_afa_decoration⟩

/-- Root occurrences of a complete unfolding tree descend to the original
successors. Both directions are constructed; neither is chosen. -/
def unfolding_root_occurrences_descend.{u} {α : Type u} (edge : α → α → Prop) (root : α) :
    Occurrence (unfold edge root) ≃ {target : α // edge root target} :=
  unfoldOccurrencesEquiv edge root

/-- The finite Scott picture agrees in direction with that general kernel:
the nodes are bisimilar, and no root-preserving map can hit both children. -/
theorem finite_scott_agrees_with_unfolding_kernel :
    Bisimilar scottEdge scottEdge .s0 .s1 ∧ ¬ ∃ f : PathS0 → PathS1,
      f .here = .here ∧ (∃ p, f p = .to0 .here) ∧ (∃ p, f p = .to1 .here) ∧
        (∀ p, f p = .to0 .here ∨ f p = .to1 .here → p = .step .here) :=
  ⟨scott_s0_bisim_s1, not_scott_unfolding_iso⟩

/-! ## Pointed downsets and retained occurrences -/

/-- Bisimilar Finsler nodes have inverse unfolding-path maps and no
pointed-downset isomorphism. Every node lies in every downset, so the
obstruction is the distinguished point and the child relation. -/
theorem pointed_downset_finer_than_bisimulation_and_unfolding_paths :
    (∀ root node : Fin3, InDownset finEdge node root) ∧
      Bisimilar finEdge finEdge .n1 .n2 ∧
      (∀ path, f21 (f12 path) = path) ∧ (∀ path, f12 (f21 path) = path) ∧
      ¬ Nonempty (PointedIso finEdge finEdge .n1 .n2) :=
  ⟨fun root node => fin_inDownset node root, fin_n1_bisim_n2, f21_f12, f12_f21,
    not_finsler_iso_n1_n2⟩

/-- A pointed presentation isomorphism can exchange occurrences while the
material readout records the same value as reflexivity. -/
theorem pointed_iso_kernel_erases_occurrence_transport.{u} :
    MaterialIdentityObservation.readout.map
        PresentationIdentityControls.swapOccurrences.{u} =
      MaterialIdentityObservation.readout.map (PresentationIso.refl twoChildren.{u}) ∧
      PresentationIdentityControls.swapOccurrences.{u} ≠
        PresentationIso.refl twoChildren.{u} ∧
      basedJ occurrenceMotive.{u} (twoChildrenOccurrence.{u} true)
          PresentationIdentityControls.swapOccurrences.{u} ≠
        basedJ occurrenceMotive.{u} (twoChildrenOccurrence.{u} true)
          (PresentationIso.refl twoChildren.{u}) := by
  have retained :=
    MaterialIdentityObservation.Controls.identity_witness_erased_but_transport_retained.{u}
  exact ⟨retained.1, PresentationIdentityControls.swap_not_reflexivity.{u}, retained.2⟩

/-- The material picture is available beside the occurrence. The reading is
propositionally surjective and not injective, and the occurrence family does
not descend through a natural fibre equivalence. -/
theorem occurrence_family_does_not_descend.{u} :
    (∀ (graph : AccessiblePointedGraph.{u}) (occurrence : Occurrence graph),
      (occurrenceMember graph occurrence).val = occurrence.picture) ∧
      (∀ graph : AccessiblePointedGraph.{u},
        Function.Surjective (occurrenceReading.app graph)) ∧
      ¬ Function.Injective (occurrenceReading.app twoChildren.{u}) ∧
      ¬ ∃ family : _root_.CategoryTheory.Discrete HSet.{u} ⥤ Type u,
        Nonempty (NaturalEquivalence presentationOccurrences
          (compose readout family)) :=
  ⟨fun _ _ => rfl, occurrenceReading_surjective,
    MaterialIdentityObservation.Controls.occurrenceReading_not_injective,
    MaterialIdentityObservation.Controls.occurrences_no_material_descent⟩

/-- Coherent motives for the material readout commute with dependent J.
This is descent for those motives, not descent for occurrence transport. -/
theorem coherent_material_motives_descend.{u, v}
    (motive : _root_.CategoryTheory.Arrow (_root_.CategoryTheory.Discrete HSet.{u}) ⥤ Type v)
    (atReflexivity : NaturalSection (compose diagonal motive)) :
    J (compose readout.mapArrow motive)
        (reindexReflexivity readout motive atReflexivity) =
      (J motive atReflexivity).reindex readout.mapArrow :=
  J_readout motive atReflexivity

/-! ## Sections: varying separation, and collection that is not dependent choice -/

section VaryingReadout
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open Mettapedia.GSLT.ObservedGeneratedModel

/-- Typed separation at the labelled-path model follows a supplied section,
and the separated carriers at the two observed points are different. -/
theorem typed_separation_has_a_varying_section :
    Nonempty Varying.separated.family.sections ∧
      (Varying.separated.model (observedPoint model worldCoding oldRaw)).carrier ≠
        (Varying.separated.model (observedPoint model worldCoding newRaw)).carrier :=
  ⟨Varying.section_exists, Varying.genuinely_varying⟩

end VaryingReadout

/-- Each Nat-loop fibre is inhabited. The loop action has no natural section.
The all-witness collection covers every argument and still has no natural
section. Coverage is not coherent dependent choice. -/
theorem collection_is_not_coherent_dependent_choice.{u} :
    (∀ atPoint : Advancing.context.{u}.base.Elements,
      Nonempty (Advancing.family.family.obj atPoint)) ∧
      ¬ Nonempty Advancing.family.{u}.family.sections ∧
      (∀ atPoint : Advancing.context.{u}.base.Elements,
        Function.Surjective
          ((ContextualSeparationCollection.projection Advancing.domain Advancing.body
            (ContextualSeparationCollection.StablePredicate.full Advancing.body)).app
              atPoint)) ∧
      ¬ Nonempty Advancing.collected.{u}.family.sections :=
  ⟨Advancing.all_fibres_inhabited, Advancing.no_natural_section,
    Advancing.collection_projection_covers, Advancing.collected_no_natural_section⟩

end Mettapedia.SetTheory.AntiFoundation.GeneralReadouts
