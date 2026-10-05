import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadout
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotientControls

/-!
# Infinite histories and cyclic material-readout controls

The infinite labelled-path category supplies actual faithful dictionaries
for its worlds and arrows. Declared result histories have distinct material
values even when their present children are empty. Parallel arrows retain
different material labels and different admitted child rows.

An actual two-state cyclic coalgebra has equal behavioral values at its
distinct states. Its source retains both states, and their material reading
has no left inverse recovering both. Unencoded dead terminal tags likewise
remain indistinguishable. Context labels still distinguish different worlds.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadoutControls

open _root_.CategoryTheory PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover
open ContextualCoalgebraLabelledGraph LabelledContextPaths

namespace Results

abbrev original := ContextualCoalgebraQuotientControls.Results.coalgebra
abbrev arguments := ContextualCoalgebraQuotientControls.Results.states
abbrev result := ContextualCoalgebraQuotientControls.Results.result
abbrev child := ContextualCoalgebraQuotientControls.Results.child
abbrev reading := ContextualCoalgebraMaterialReadout.value original worlds arrows
abbrev materialResult (tag : Nat) := reading ⟨initial, result tag⟩

theorem materialResult_injective : Function.Injective materialResult := by
  intro first second same
  exact (ContextualCoalgebraQuotientControls.Results.result_bisimilar_iff first second).mp
    ((ContextualCoalgebraMaterialReadout.value_eq_iff original worlds arrows initial _ _).mp same)

def resultMember (tag : Nat) :
    {member : HSet // member ∈ ContextualCoalgebraMaterialReadout.carrier original worlds arrows initial} :=
  ⟨materialResult tag,
    (ContextualCoalgebraMaterialReadout.mem_carrier_iff original worlds arrows initial _).mpr
      ⟨result tag, rfl⟩⟩

theorem resultMember_injective : Function.Injective resultMember :=
  fun _ _ same => materialResult_injective (congrArg Subtype.val same)

theorem declared_results_materially_different : materialResult 0 ≠ materialResult 1 :=
  fun same => Nat.zero_ne_one (materialResult_injective same)

theorem no_present_child_row (tag : Nat) (argument : arguments.obj initial) :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.child initial initial (𝟙 initial))) (reading ⟨initial, argument⟩) ∉ materialResult tag := by
  intro present
  obtain ⟨matching, available, _⟩ :=
    (ContextualCoalgebraMaterialReadout.child_row_iff original worlds arrows
      (𝟙 initial) (result tag) argument).mp present
  exact ContextualCoalgebraQuotientControls.Results.no_present_children tag matching available

theorem own_result_future_row (tag : Nat) :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.child initial next (extension tag))) (reading ⟨next, child tag⟩) ∈ materialResult tag :=
  (ContextualCoalgebraMaterialReadout.child_row_iff original worlds arrows
    (extension tag) (result tag) (child tag)).mpr
      ⟨child tag,
        (ContextualCoalgebraQuotientControls.Results.emitted_label_iff tag tag _).mpr rfl,
        ContextualCoalgebraBisimulation.bisimilar_refl original next (child tag)⟩

theorem another_result_future_row_absent {first second : Nat} (different : first ≠ second)
    (argument : arguments.obj next) :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.child initial next (extension second))) (reading ⟨next, argument⟩) ∉ materialResult first := by
  intro present
  obtain ⟨matching, available, _⟩ :=
    (ContextualCoalgebraMaterialReadout.child_row_iff original worlds arrows
      (extension second) (result first) argument).mp present
  exact different ((ContextualCoalgebraQuotientControls.Results.emitted_label_iff first second _).mp available)

theorem parallel_history_labels_differ :
    (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading (.child initial next (extension 0)) ≠
      (ContextualCoalgebraMaterialReadout.labels worlds arrows).reading (.child initial next (extension 1)) := by
  intro same
  have labels := (ContextualCoalgebraMaterialReadout.labels worlds arrows).injective same
  have receipts := congrArg (fun label : Label World =>
    match label with
    | .context _ _ _ => ([] : List Nat)
    | .child _ _ arrow => arrow.val) labels
  exact Nat.zero_ne_one (List.cons.inj receipts).1

theorem parallel_history_rows_differ :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.child initial next (extension 0))) (reading ⟨next, child 0⟩) ∈ materialResult 0 ∧
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.child initial next (extension 1))) (reading ⟨next, child 0⟩) ∉ materialResult 0 :=
  ⟨own_result_future_row 0,
    another_result_future_row_absent Nat.zero_ne_one (child 0)⟩

theorem context_transport_row (tag history : Nat) :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.context initial next (extension history)))
      (reading ⟨next, arguments.map (extension history) (result tag)⟩) ∈ materialResult tag :=
  (ContextualCoalgebraMaterialReadout.context_row_iff original worlds arrows (extension history)
    (result tag) _).mpr
      (ContextualCoalgebraBisimulation.bisimilar_refl original next _)

theorem context_change_changes_material_value (tag history : Nat) :
    materialResult tag ≠ reading ⟨next, arguments.map (extension history) (result tag)⟩ := by
  intro same
  have contexts := ContextualCoalgebraMaterialReadout.value_contexts_eq original worlds arrows same
  exact Nat.zero_ne_one (congrArg World.length contexts)

theorem present_empty_does_not_determine_material_value :
    (∀ argument, ¬ (original.app initial (result 0)).val.holds
      (CoveredFuturePowerFamilies.current arguments initial argument)) ∧
    (∀ argument, ¬ (original.app initial (result 1)).val.holds
      (CoveredFuturePowerFamilies.current arguments initial argument)) ∧
    materialResult 0 ≠ materialResult 1 :=
  ⟨ContextualCoalgebraQuotientControls.Results.no_present_children 0,
    ContextualCoalgebraQuotientControls.Results.no_present_children 1,
    declared_results_materially_different⟩

end Results

namespace Cycles

def states : World ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def children (point : World) (state : states.obj point) :
    CoveredFuturePowerFamilies.Predicate states point where
  holds argument := argument.2 = !state
  closed {_ _} move available := by
    exact move.2.symm.trans available

def coalgebra : NaturalHom states (CoveredFuturePowerFamilies.family states) where
  app point state := ⟨children point state, ⟨CoveredFuturePowerFamilies.smallEnumeration (children point state)⟩⟩
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

abbrev reading := ContextualCoalgebraMaterialReadout.value coalgebra worlds arrows

theorem cycle_bisimulation : ContextualCoalgebraBisimulation.IsBisimulation coalgebra
    (fun _ left right => left = right ∨ left = !right) where
  stable {_ _} _ {_ _} related := related
  forth {_ left right} related future {child} available := by
    change child = !left at available
    cases available
    refine ⟨!right, rfl, ?_⟩
    exact related.elim (fun same => Or.inl (congrArg Bool.not same))
      (fun same => Or.inr (congrArg Bool.not same))
  back {_ left right} related future {child} available := by
    change child = !right at available
    cases available
    refine ⟨!left, rfl, ?_⟩
    exact related.elim (fun same => Or.inl (congrArg Bool.not same))
      (fun same => Or.inr (congrArg Bool.not same))

theorem distinct_cyclic_states_same_material_value (point : World) :
    (false : states.obj point) ≠ true ∧ reading ⟨point, false⟩ = reading ⟨point, true⟩ :=
  ⟨Bool.false_ne_true,
    (ContextualCoalgebraMaterialReadout.value_eq_iff coalgebra worlds arrows point false true).mpr
      ⟨_, cycle_bisimulation, Or.inr rfl⟩⟩

theorem cyclic_child_row (point : World) (state : states.obj point) :
    HSet.kpair ((ContextualCoalgebraMaterialReadout.labels worlds arrows).reading
      (.child point point (𝟙 point))) (reading ⟨point, !state⟩) ∈ reading ⟨point, state⟩ :=
  (ContextualCoalgebraMaterialReadout.child_row_iff coalgebra worlds arrows (𝟙 point) state (!state)).mpr
    ⟨!state, rfl, ContextualCoalgebraBisimulation.bisimilar_refl coalgebra point (!state)⟩

theorem no_left_decoder_recovers_both_cyclic_states (point : World) :
    ¬ ∃ decode : HSet → states.obj point,
      ∀ state, decode (reading ⟨point, state⟩) = state := by
  rintro ⟨decode, recovers⟩
  exact (distinct_cyclic_states_same_material_value point).1
    ((recovers false).symm.trans
      ((congrArg decode (distinct_cyclic_states_same_material_value point).2).trans (recovers true)))

end Cycles

namespace UnencodedTerminals

abbrev original := ContextualCoalgebraQuotientControls.UnobservedTerminals.coalgebra
abbrev reading := ContextualCoalgebraMaterialReadout.value original worlds arrows

theorem dead_terminal_tags_still_merge : reading ⟨initial, false⟩ = reading ⟨initial, true⟩ :=
  (ContextualCoalgebraMaterialReadout.value_eq_iff original worlds arrows initial false true).mpr
    ((ContextualCoalgebraQuotient.projection_eq_iff original initial false true).mp
      ContextualCoalgebraQuotientControls.UnobservedTerminals.unencoded_terminal_tags_merge)

end UnencodedTerminals

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraMaterialReadoutControls
