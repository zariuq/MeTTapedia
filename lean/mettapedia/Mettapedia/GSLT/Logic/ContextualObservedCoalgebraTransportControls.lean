import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraTransport
import Mettapedia.GSLT.Logic.ContextualObservedCoalgebraControls

/-!
# Infinite full-observation transport controls

The source has infinitely many result parameters and new occurrence receipts
at every context. Its nonempty execution child sets retain the result. The
actual indexed quotient forgets receipt aliases and keeps every result,
while all contextual material values and modal formulas commute.

The same state map from an execution with no children into this execution
preserves atoms and simulates every source action. It has no outgoing lifting
cover, since the target has an additional execution child. Its material
value differs. Thus forward simulation does not justify full transport.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextualObservedCoalgebraTransportControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory.ContextualWitnessCover
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open PowerClassPresheafDescent.Controls
open ContextualCoalgebraLabelledGraph
open ContextualObservedCoalgebra HennessyMilner

abbrev source := IndexedCoalgebraQuotientControls.source
abbrev coalgebra := IndexedCoalgebraQuotientControls.underlying
abbrev quotient := IndexedCoalgebraQuotientControls.indexedFamily
abbrev quotientMap := IndexedCoalgebraQuotientControls.indexedProjection
abbrev quotientCoalgebra := IndexedCoalgebraQuotient.coalgebra
  IndexedCoalgebraQuotientControls.parameter IndexedCoalgebraQuotientControls.transition
  IndexedCoalgebraQuotientControls.parameter_square
abbrev quotientParameter := IndexedCoalgebraQuotient.quotientParameter
  IndexedCoalgebraQuotientControls.parameter IndexedCoalgebraQuotientControls.transition

def atoms (reading : Nat) (state : State source) : Prop := reading = state.2.1

def quotientAtoms (reading : Nat) (state : State quotient) : Prop := reading = quotientParameter.app state.1 state.2

theorem full_square : coalgebra.comp (CoveredFuturePowerFunctor.imageHom quotientMap) =
    quotientMap.comp quotientCoalgebra := IndexedCoalgebraQuotient.coalgebra_square _ _ _

theorem atoms_square (reading : Nat) (state : State source) :
    atoms reading state ↔ quotientAtoms reading (graphMap quotientMap state) := Iff.rfl

abbrev worlds := ContextualObservedCoalgebraControls.worlds
abbrev arrows := ContextualObservedCoalgebraControls.arrows
abbrev atomCoding := ContextualObservedCoalgebraControls.naturalAtoms

abbrev value := ContextualObservedCoalgebra.value coalgebra atoms worlds arrows atomCoding
abbrev quotientValue := ContextualObservedCoalgebra.value quotientCoalgebra quotientAtoms worlds arrows atomCoding

theorem whole_value_transport (state : State source) : value state = quotientValue (graphMap quotientMap state) :=
  ContextualObservedCoalgebraTransport.value_preservation coalgebra quotientCoalgebra quotientMap full_square
    atoms quotientAtoms atoms_square worlds arrows atomCoding state

theorem whole_formula_transport (formula : Formula Nat (Label Stagesᵒᵖ)) (state : State source) :
    (system quotientCoalgebra quotientAtoms).sat formula (graphMap quotientMap state) ↔
      (system coalgebra atoms).sat formula state :=
  ContextualObservedCoalgebraTransport.formula_preservation_reflection coalgebra quotientCoalgebra quotientMap
    full_square atoms quotientAtoms atoms_square worlds arrows formula state

theorem infinitely_many_values : Function.Injective
    (fun result => value ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result false⟩) := by
  intro first second same
  exact (observed_bisimilar_atoms coalgebra atoms
    ((value_eq_iff coalgebra atoms worlds arrows atomCoding (world 0) _ _).mp same) first).mp rfl

theorem receipt_aliases_transport (result : Nat) :
    IndexedCoalgebraQuotientControls.initialValue result true ≠
        IndexedCoalgebraQuotientControls.initialValue result false ∧
      value ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result true⟩ =
        value ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result false⟩ := by
  refine ⟨IndexedCoalgebraQuotientControls.raw_provenance_distinct result, ?_⟩
  rw [whole_value_transport, whole_value_transport]
  exact congrArg (fun reading => quotientValue ⟨world 0, reading⟩)
    (IndexedCoalgebraQuotientControls.indexed_provenance_agrees result)

theorem actual_new_child_every_stage (stage result : Nat) :
    ¬ (∃ earlier : source.obj (world stage),
        source.map (IndexedCoalgebraQuotientControls.advance stage) earlier =
          IndexedCoalgebraQuotientControls.newReceipt stage result) ∧
      (coalgebra.app (world stage)
        (result, stageValue stage 0 (Nat.zero_lt_succ stage) false)).val.holds
          ⟨⟨world (stage + 1), IndexedCoalgebraQuotientControls.advance stage⟩,
            IndexedCoalgebraQuotientControls.newReceipt stage result⟩ :=
  ⟨IndexedCoalgebraQuotientControls.new_receipt_every_stage stage result,
    IndexedCoalgebraQuotientControls.new_receipt_admitted stage result⟩

abbrev noChildren := ContextualObservedCoalgebraControls.emptyCoalgebra source
abbrev noChildValue := ContextualObservedCoalgebra.value noChildren atoms worlds arrows atomCoding

def forwardOnly : SystemTranslation (system noChildren atoms) (system coalgebra atoms) where
  mapTerm := id
  mapAtom := id
  mapLabel := id
  mapEquiv same := same
  observes_iff _ _ := Iff.rfl
  mapAct {label first last} step := by
    cases label with
    | context source target arrow => exact step
    | child source target arrow =>
        obtain ⟨_, _, _, _, impossible⟩ := step
        exact impossible.elim

theorem extra_child (result : Nat) : Step coalgebra
    ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result false⟩
    (.child (world 0) (world 0) (𝟙 (world 0)))
    ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result false⟩ :=
  child_step coalgebra _ _ _ rfl

theorem no_empty_child (first last : State source) (source target : Stagesᵒᵖ)
    (arrow : source ⟶ target) : ¬ Step noChildren first (.child source target arrow) last := by
  rintro ⟨_, _, _, _, impossible⟩
  exact impossible.elim

theorem forward_map_has_no_outgoing_cover :
    ¬ ∃ cover : SystemCover (system noChildren atoms) (system coalgebra atoms), cover.mapTerm = id ∧ cover.mapLabel = id := by
  rintro ⟨cover, termIdentity, labelIdentity⟩
  have targetStep : (system coalgebra atoms).act
      (cover.mapLabel (.child (world 0) (world 0) (𝟙 (world 0))))
      (cover.mapTerm ⟨world 0, IndexedCoalgebraQuotientControls.initialValue 0 false⟩)
      ⟨world 0, IndexedCoalgebraQuotientControls.initialValue 0 false⟩ := by
    rw [termIdentity, labelIdentity]
    exact extra_child 0
  obtain ⟨_, impossible, _⟩ := cover.liftAct targetStep
  exact no_empty_child _ _ _ _ _ impossible

theorem forward_simulation_changes_material (result : Nat) :
    noChildValue ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result false⟩ ≠
      value ⟨world 0, IndexedCoalgebraQuotientControls.initialValue result false⟩ := by
  intro same
  let argument := IndexedCoalgebraQuotientControls.initialValue result false
  have row := (ObservedMaterialization.LabelReadings.action_iff
    (readings coalgebra atoms worlds arrows atomCoding)
    (faithful coalgebra atoms worlds arrows atomCoding) ⟨world 0, argument⟩
    (.child (world 0) (world 0) (𝟙 (world 0))) (value ⟨world 0, argument⟩)).mpr
      ⟨_, extra_child result, rfl⟩
  change HSet.kpair (readings noChildren atoms worlds arrows atomCoding |>.taggedReading
    (.inr (.child (world 0) (world 0) (𝟙 (world 0))))) (value ⟨world 0, argument⟩) ∈
      value ⟨world 0, argument⟩ at row
  rw [← same] at row
  obtain ⟨_, impossible, _⟩ := (ObservedMaterialization.LabelReadings.action_iff
    (readings noChildren atoms worlds arrows atomCoding)
    (faithful noChildren atoms worlds arrows atomCoding) ⟨world 0, argument⟩ _ _).mp row
  exact no_empty_child _ _ _ _ _ impossible

end Mettapedia.GSLT.ContextualObservedCoalgebraTransportControls
