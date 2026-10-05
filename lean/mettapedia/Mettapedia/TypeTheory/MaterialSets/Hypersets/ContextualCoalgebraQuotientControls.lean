import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotient
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualReachableCoalgebrasControls

/-!
# Infinite contextual quotient and observation controls

The actual generated member coalgebra retains infinite context histories
and cyclic future values. Behavioral projection identifies two distinct
authored branch receipts with the same reachable value; no inverse can
recover every receipt from its class.

A separate result profile declares literal history labels as its reading.
Its coalgebra emits those labels through actual future arrows. Present
children are empty for both initial results, but their quotient classes
differ. Conversely an explicitly dead transition profile forgets all
unencoded terminal tags.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotientControls

open _root_.CategoryTheory
open PowerClassPresheafBaseChange
open Mettapedia.TypeTheory.ContextualWitnessCover

namespace Generated

open ContextualGeneratedCoalgebrasControls ContextualPowerFamiliesControls
open Mettapedia.GSLT.ObservedGeneratedModel
open Mettapedia.GSLT.ObservedGeneratedModelControls.Paths
open ContextualReachableCoalgebrasControls

abbrev original := ContextualGeneratedCoalgebras.generatedCoalgebra wide allCoalgebra branchEnumerations seed
abbrev classes := ContextualCoalgebraQuotient.family original
abbrev observe := ContextualCoalgebraQuotient.projection original
abbrev quotientCoalgebra := ContextualCoalgebraQuotient.coalgebra original

theorem tagged_receipts_bisimilar :
    ContextualCoalgebraBisimulation.Bisimilar original (observedPoint model worldCoding futureRaw)
      (taggedReceipt true) (taggedReceipt false) :=
  ContextualCoalgebraBisimulation.bisimilar_of_coalgebra_map_eq original reachCover reachCoalgebra
    actual_generated_cover_square tagged_cover_equal

theorem distinct_receipts_same_class :
    taggedReceipt true ≠ taggedReceipt false ∧
      observe.app (observedPoint model worldCoding futureRaw) (taggedReceipt true) =
        observe.app (observedPoint model worldCoding futureRaw) (taggedReceipt false) :=
  ⟨taggedReceipt_distinct,
    (ContextualCoalgebraQuotient.projection_eq_iff original _ _ _).mpr tagged_receipts_bisimilar⟩

theorem no_class_decoder_recovers_all_receipts :
    ¬ ∃ decode : classes.obj (observedPoint model worldCoding futureRaw) →
          generated.obj (observedPoint model worldCoding futureRaw),
      ∀ receipt, decode (observe.app (observedPoint model worldCoding futureRaw) receipt) = receipt := by
  rintro ⟨decode, recovers⟩
  exact distinct_receipts_same_class.1
    ((recovers (taggedReceipt true)).symm.trans
      ((congrArg decode distinct_receipts_same_class.2).trans (recovers (taggedReceipt false))))

theorem cyclic_future_survives :
    (quotientCoalgebra.app initialPoint (observe.app initialPoint rootReceipt)).val.holds
      ⟨⟨observedPoint model worldCoding futureRaw, futureArrow⟩,
        observe.app (observedPoint model worldCoding futureRaw) newCyclicReceipt⟩ :=
  (ContextualCoalgebraQuotient.quotient_truth original initialPoint rootReceipt
    ⟨observedPoint model worldCoding futureRaw, futureArrow⟩ _).mpr
      ⟨newCyclicReceipt, rfl, generated_cyclic_future⟩

theorem whole_future_coalgebra_square :
    original.comp (CoveredFuturePowerFunctor.imageHom observe) = observe.comp quotientCoalgebra :=
  ContextualCoalgebraQuotient.coalgebra_square original

theorem quotient_context {first second : actualContext.base.Elements} (step : first ⟶ second)
    (receipt : generated.obj first) :
    classes.map step (observe.app first receipt) = observe.app second (generated.map step receipt) :=
  ContextualCoalgebraQuotient.projection_restriction original step receipt

theorem infinite_source_histories_retained : Function.Injective contextHistory := contextHistory_injective

end Generated

namespace Results

open LabelledContextPaths

/-- The literal result reading is declared as a history label. -/
def label : Bool → Nat
  | false => 0
  | true => 1

def states : World ⥤ Type where
  obj point := Nat × (ContextualWitnessCover.free (E := World)).obj point
  map step := TypeCat.ofHom fun state => ⟨state.1, (ContextualWitnessCover.free (E := World)).map step state.2⟩
  map_id point := by
    apply ConcreteCategory.hom_ext
    intro state
    exact Prod.ext rfl (congrArg (fun map => map state.2) (ContextualWitnessCover.free.map_id point))
  map_comp first second := by
    apply ConcreteCategory.hom_ext
    intro state
    exact Prod.ext rfl
      (congrArg (fun map => map state.2) (ContextualWitnessCover.free.map_comp first second))

/-- Context transport appends the actual receipt history. Emission checks
the whole generator-to-future path, not merely its endpoint. -/
def children (point : World) (state : states.obj point) : CoveredFuturePowerFamilies.Predicate states point where
  holds argument := ∃ rest, (state.2.2 ≫ argument.1.2).val = state.1 :: rest
  closed {first second} move available := by
    obtain ⟨rest, starts⟩ := available
    have triangle := congrArg (fun arrow : state.2.1 ⟶ second.1.1 => arrow.val)
      ((Category.assoc state.2.2 first.1.2 move.1.1).trans
        (congrArg (fun arrow => state.2.2 ≫ arrow) move.1.2))
    change (state.2.2 ≫ first.1.2).val ++ move.1.1.val =
      (state.2.2 ≫ second.1.2).val at triangle
    refine ⟨rest ++ move.1.1.val, ?_⟩
    rw [← triangle, starts]
    rfl

def coalgebra : NaturalHom states (CoveredFuturePowerFamilies.family states) where
  app point state := ⟨children point state, ⟨CoveredFuturePowerFamilies.smallEnumeration (children point state)⟩⟩
  naturality {first second} step state := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro argument
    change (∃ rest, (state.2.2 ≫ (step ≫ argument.1.2)).val = state.1 :: rest) ↔
      ∃ rest, ((state.2.2 ≫ step) ≫ argument.1.2).val = state.1 :: rest
    rw [Category.assoc]

def result (tag : Nat) : states.obj initial := ⟨tag, ContextualWitnessCover.seed initial⟩
def child (tag : Nat) : states.obj next := ⟨tag, ContextualWitnessCover.seed next⟩

theorem no_present_children (tag : Nat) (argument : states.obj initial) :
    ¬ (coalgebra.app initial (result tag)).val.holds (CoveredFuturePowerFamilies.current states initial argument) := by
  change ¬ ∃ rest, [] = tag :: rest
  rintro ⟨_, impossible⟩
  cases impossible

theorem emitted_label_iff (tag other : Nat) (argument : states.obj next) :
    (coalgebra.app initial (result tag)).val.holds ⟨⟨next, extension other⟩, argument⟩ ↔
      tag = other := by
  change (∃ rest, [other] = tag :: rest) ↔ _
  constructor
  · rintro ⟨rest, same⟩
    exact (List.cons.inj same).1.symm
  · intro same
    exact ⟨[], same ▸ rfl⟩

theorem result_bisimilar_iff (first second : Nat) :
    ContextualCoalgebraBisimulation.Bisimilar coalgebra initial (result first) (result second) ↔
      first = second := by
  constructor
  · intro related
    have admitted := (emitted_label_iff first first (child first)).mpr rfl
    obtain ⟨matching, matched, _⟩ :=
      (ContextualCoalgebraBisimulation.bisimilar_isBisimulation coalgebra).forth related
        ⟨next, extension first⟩ admitted
    exact ((emitted_label_iff second first matching).mp matched).symm
  · intro same
    cases same
    exact ContextualCoalgebraBisimulation.bisimilar_refl coalgebra initial (result first)

theorem result_classes_injective : Function.Injective
    (fun tag => (ContextualCoalgebraQuotient.projection coalgebra).app initial (result tag)) := by
  intro first second same
  exact (result_bisimilar_iff first second).mp
    ((ContextualCoalgebraQuotient.projection_eq_iff coalgebra initial _ _).mp same)

theorem declared_results_not_bisimilar :
    ¬ ContextualCoalgebraBisimulation.Bisimilar coalgebra initial
      (result (label false)) (result (label true)) :=
  fun related => Nat.zero_ne_one ((result_bisimilar_iff _ _).mp related)

theorem declared_result_classes_differ :
    (ContextualCoalgebraQuotient.projection coalgebra).app initial (result (label false)) ≠
      (ContextualCoalgebraQuotient.projection coalgebra).app initial (result (label true)) :=
  fun same => declared_results_not_bisimilar
    ((ContextualCoalgebraQuotient.projection_eq_iff coalgebra initial _ _).mp same)

theorem parallel_endpoints_distinct_truth :
    (extension 0).val.length = (extension 1).val.length ∧
      (coalgebra.app initial (result 0)).val.holds ⟨⟨next, extension 0⟩, child 0⟩ ∧
      ¬ (coalgebra.app initial (result 0)).val.holds ⟨⟨next, extension 1⟩, child 0⟩ :=
  ⟨rfl, (emitted_label_iff 0 0 _).mpr rfl,
    fun available => Nat.zero_ne_one ((emitted_label_iff 0 1 _).mp available)⟩

theorem present_matching_does_not_determine_bisimilarity :
    (∀ argument, ¬ (coalgebra.app initial (result 0)).val.holds
      (CoveredFuturePowerFamilies.current states initial argument)) ∧
    (∀ argument, ¬ (coalgebra.app initial (result 1)).val.holds
      (CoveredFuturePowerFamilies.current states initial argument)) ∧
    ¬ ContextualCoalgebraBisimulation.Bisimilar coalgebra initial (result 0) (result 1) :=
  ⟨no_present_children 0, no_present_children 1, declared_results_not_bisimilar⟩

end Results

namespace UnobservedTerminals

open LabelledContextPaths

def states : World ⥤ Type where
  obj _ := Bool
  map _ := TypeCat.ofHom id
  map_id _ := rfl
  map_comp _ _ := rfl

def noChildren (point : World) : CoveredFuturePowerFamilies.Predicate states point where
  holds _ := False
  closed _ impossible := impossible.elim

def coalgebra : NaturalHom states (CoveredFuturePowerFamilies.family states) where
  app point _ := ⟨noChildren point, ⟨CoveredFuturePowerFamilies.smallEnumeration (noChildren point)⟩⟩
  naturality _ _ := by
    apply Subtype.ext
    apply CoveredFuturePowerFamilies.Predicate.ext
    intro _
    exact Iff.rfl

/-- A dead transition profile has no reading that distinguishes its tags.
The displayed relation identifies both Boolean values. -/
theorem unencoded_terminal_tags_merge :
    (ContextualCoalgebraQuotient.projection coalgebra).app initial false =
      (ContextualCoalgebraQuotient.projection coalgebra).app initial true := by
  apply (ContextualCoalgebraQuotient.projection_eq_iff coalgebra initial false true).mpr
  refine ⟨fun _ left right => left = right ∨ left = false ∧ right = true ∨ left = true ∧ right = false,
    ?_, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
  constructor
  · intro _ _ _ _ _ related
    exact related
  · intro _ _ _ _ _ _ impossible
    exact impossible.elim
  · intro _ _ _ _ _ _ impossible
    exact impossible.elim

end UnobservedTerminals

end Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCoalgebraQuotientControls
