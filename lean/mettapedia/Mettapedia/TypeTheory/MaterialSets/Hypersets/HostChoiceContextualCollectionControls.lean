import Mettapedia.TypeTheory.HostChoiceContextualCollection
import Mettapedia.TypeTheory.MaterialSets.Hypersets.ContextualCollectionGeneratorsControls

/-!
# External-Choice Collection and the absence of natural witness selection

The comparison theorem builds its actual full diagram for the wider
hyperset cover without a supplied bounded reading. Selected host receipts
in the advancing-loop example fail contextual compatibility. The internal
cover has no natural splitting, independently of that external selection.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCollectionControls

open _root_.CategoryTheory Mettapedia.TypeTheory ContextualWitnessCover ContextualImageFactorization
open ContextualCoherentSmallMaps

namespace Wider

open ContextualBoundedCollectionControls

theorem external_choice_collection :
    Cover (ContextualCollectionGenerators.parameterMap operation wideCover) ∧
      Cover (ContextualCollectionGenerators.comparison operation wideCover) ∧
      SmallFibres (ContextualCollectionGenerators.collectedMap operation wideCover) ∧
      (ContextualCollectionGenerators.top operation wideCover).comp (wideCover.comp operation) =
        (ContextualCollectionGenerators.collectedMap operation wideCover).comp
          (ContextualCollectionGenerators.parameterMap operation wideCover) :=
  HostChoiceContextualCollection.collection operation wideCover
    (ContextualGeneratedWitnessCollection.mapData ContextualGeneratedUniverse.Growing.input operation).smallFibres
    wideCover_onto

end Wider

namespace Advancing

open ContextualCollectionGeneratorsControls.Advancing
open ContextualSeparationCollectionControls.Advancing
open ContextualWitnessCoverControls.Advancing

noncomputable def selected : NaturalMember :=
  (HostChoiceContextualCollection.selectedWitness cover cover_onto point PUnit.unit).val

theorem selected_not_compatible : advance 1 selected ≠ selected := advance_no_fixed_point selected

theorem no_internal_natural_splitting :
    ¬ ∃ choice : NaturalHom parameters wide,
      choice.comp cover = ContextualSmallMapConstructions.identity parameters :=
  cover_has_no_natural_splitting

end Advancing

end Mettapedia.TypeTheory.MaterialSets.Hypersets.HostChoiceContextualCollectionControls
