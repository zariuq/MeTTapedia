import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeFamilyContainerLifting
import Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection

/-!
# NIK selection from checked native-family capabilities

An exact unary container representation earns compositional relation lifting
and direct functional realization.  Finitarity earns the additional ability
to enumerate every proof occurrence of an arbitrary finite element relation.
This module connects those separately proved capabilities to request-local NIK
selection.

The examples distinguish three cases without a datatype-specific dispatcher:

* polynomial List plus its finitary container representation preserves a
  nondeterministic two-answer fibre and selects exact finite search;
* the infinitary positive reader cannot preserve that finite search, but a
  functional element relation still selects direct pointwise realization;
* the recursively positive parameter-negative family has no covariant
  container representation and therefore cannot enter either request through
  this bridge.

Thus maximal-native selection means the strongest realization justified for
one semantic request, never a global ranking that confuses construction,
functional mapping, and exhaustive search.
-/

namespace Mettapedia.Languages.MeTTa.Prime
namespace NativeFamilyCapabilityNIKSelection

open Mettapedia.GSLT.LanguageDef.NIKRouteAdmission
open Mettapedia.GSLT.LanguageDef.NIKMaximalNativeAdmission
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RelationalInternalLanguage.Semantic
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RelationalEvidence
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILNativeSearch
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.IntrinsicMILNativeLiftingSearch
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeFamilyContainerLifting
open Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.NativeIndexedContainerLiftingSearch
open Mettapedia.Languages.MeTTa.Prime.NativeRelationalSearchNIKSelection
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial
open Mettapedia.TypeTheory.NativeFamilyCapabilitySeparation

/-! ## One currentness discipline for the canaries -/

def dependencies : DependencySystem where
  Revision := Bool
  Dependency := Unit
  Value := Bool
  read revision _ := revision

/-! ## Finitary List: complete nondeterministic search -/

noncomputable def listLifting :
    NativeRelationLifting.CompositionalLifting ListExample.ListP :=
  UnaryContainerRepresentation.compositionalLifting
    listContainerRepresentation

noncomputable def listFiniteSearch :
    FiniteSearchLifting ListExample.ListP listLifting :=
  UnaryContainerRepresentation.finiteSearchLifting
    listContainerRepresentation IndexedContainer.Examples.listFinitary

def singletonUnit : ListExample.ListP Unit :=
  ListExample.cons () ListExample.nil

noncomputable def listChoiceProvider : FiniteEvidenceProvider
    (listLifting.lift IntrinsicMILNativeSearch.Canary.choice) :=
  listFiniteSearch.provide IntrinsicMILNativeSearch.Canary.choice
    IntrinsicMILNativeSearch.Canary.choiceProvider

/-- Transport through the exact family representation preserves both answer
occurrences of the nondeterministic element relation. -/
theorem list_choice_retains_two_occurrences :
    (listChoiceProvider.answers singletonUnit).card = 2 := by
  rw [FiniteEvidenceProvider.answers_card]
  change Fintype.card (Fin 1 → Bool) = 2
  decide

noncomputable def listChoiceFamily :=
  finiteOnlyFamily listChoiceProvider

noncomputable def listChoiceAdmission :=
  admitStrongestAt listChoiceFamily
    (finiteOnlyRequest listChoiceProvider)
    (finiteOnlySelection listChoiceProvider)
    dependencies false

noncomputable def activeListChoice : listChoiceAdmission.Active false :=
  listChoiceAdmission.activate (dependencies.sameDependencies_refl false)

/-- The family-level bridge reaches NIK unchanged: the selected operation is
complete finite search, not a collapsed endpoint set. -/
theorem list_family_selects_complete_search :
    ((activeListChoice.run singletonUnit).face = .finiteSearch) ∧
      (activeListChoice.run singletonUnit).result.answers.card = 2 := by
  constructor
  · rfl
  · exact list_choice_retains_two_occurrences

/-! ## Infinitary reader: direct functional realization only -/

noncomputable def readerLifting :
    NativeRelationLifting.CompositionalLifting
      (fun Parameter : Type => Nat → Parameter) :=
  UnaryContainerRepresentation.compositionalLifting
    readerContainerRepresentation

noncomputable def readerRepresentationLifting :
    RepresentationLifting (fun Parameter : Type => Nat → Parameter)
      readerLifting :=
  UnaryContainerRepresentation.representationLifting
    readerContainerRepresentation

noncomputable def readerToggleRepresentation : Rel.Representation
    (readerLifting.lift (Rel.graph Bool.not)) :=
  readerRepresentationLifting.represent (Rel.graph Bool.not)
    (Rel.graphRepresentation Bool.not)

noncomputable def readerToggleProvider : FiniteEvidenceProvider
    (readerLifting.lift (Rel.graph Bool.not)) :=
  FiniteEvidenceProvider.ofRepresentation readerToggleRepresentation

@[simp] theorem readerToggleRepresentation_map :
    readerToggleRepresentation.map =
      fun source position => Bool.not (source position) :=
  rfl

noncomputable def readerToggleFamily :=
  representedFamily readerToggleProvider readerToggleRepresentation

noncomputable def readerToggleAdmission :=
  admitStrongestAt readerToggleFamily
    (completeSearchRequest readerToggleProvider readerToggleRepresentation)
    (directSelection readerToggleProvider readerToggleRepresentation)
    dependencies false

noncomputable def activeReaderToggle : readerToggleAdmission.Active false :=
  readerToggleAdmission.activate (dependencies.sameDependencies_refl false)

def readerFalse : Nat → Bool := fun _ => false

/-- Infinitary structure does not prevent a direct native operation when the
element relation itself is functional. -/
theorem reader_function_selects_direct :
    (activeReaderToggle.run readerFalse).face = .directMap ∧
      RelationalEvidence.AnswerBag.Complete
        (activeReaderToggle.run readerFalse).result.answers := by
  constructor
  · rfl
  · exact readerToggleAdmission.refinement.preservesMeaning _ trivial

def spike (index position : Nat) : Bool := decide (position = index)

theorem spike_injective : Function.Injective spike := by
  intro first second equal
  by_contra distinct
  have atFirst := congrFun equal first
  simp [spike, distinct] at atFirst

def readerUnit : Nat → Unit := fun _ => ()

def spikeOccurrence (index : Nat) :
    AnswerOccurrence
      (readerLifting.lift IntrinsicMILNativeSearch.Canary.choice)
      readerUnit :=
  ⟨spike index, .same (fun _ => ())⟩

theorem spikeOccurrence_injective : Function.Injective spikeOccurrence := by
  intro first second equal
  apply spike_injective
  exact congrArg AnswerOccurrence.target equal

/-- Independent binary choices at every natural-number position have an
infinite proof-occurrence fibre, so no exact finite provider exists. -/
theorem reader_choice_has_no_finite_provider :
    ¬ Nonempty
      (FiniteEvidenceProvider
        (readerLifting.lift IntrinsicMILNativeSearch.Canary.choice)) := by
  rintro ⟨provider⟩
  let fibre := provider.fibre readerUnit
  letI : Fintype
      (AnswerOccurrence
        (readerLifting.lift IntrinsicMILNativeSearch.Canary.choice)
        readerUnit) :=
    Fintype.ofEquiv fibre.Index fibre.occurrenceEquiv
  letI : Fintype Nat :=
    Fintype.ofInjective spikeOccurrence spikeOccurrence_injective
  exact not_finite Nat

/-- Consequently the reader cannot advertise a general finite-search lifting,
even though its functional fragment earns the direct face above. -/
theorem reader_has_no_finite_search_lifting :
    ¬ Nonempty
      (FiniteSearchLifting (fun Parameter : Type => Nat → Parameter)
        readerLifting) := by
  rintro ⟨finiteLifting⟩
  exact reader_choice_has_no_finite_provider
    ⟨finiteLifting.provide IntrinsicMILNativeSearch.Canary.choice
      IntrinsicMILNativeSearch.Canary.choiceProvider⟩

/-- The generic reflection law independently derives the same refusal from
the exact Reader representation and its non-finitary position fibre. -/
theorem reader_reflection_refuses_finite_search :
    ¬ Nonempty
      (FiniteSearchLifting (fun Parameter : Type => Nat → Parameter)
        readerLifting) := by
  intro finiteSearch
  have finitary :
      Nonempty readerContainerRepresentation.container.Finitary :=
    (UnaryContainerRepresentation.finitary_iff_finiteSearchLifting
      readerContainerRepresentation).mpr finiteSearch
  exact IndexedContainer.Examples.reader_not_finitary finitary

/-- The positive List control exhibits the other direction of the exact
capability characterization. -/
theorem list_finitarity_exactly_finite_search :
    Nonempty listContainerRepresentation.container.Finitary ↔
      Nonempty (FiniteSearchLifting ListExample.ListP listLifting) :=
  UnaryContainerRepresentation.finitary_iff_finiteSearchLifting
    listContainerRepresentation

/-! ## Refusing parameter-negative boundary -/

/-- Recursive strict positivity alone cannot enter the covariant lifting
request.  The parameter-negative family has no exact container bridge from
which NIK could obtain either mapping or finite search. -/
theorem parameter_negative_family_has_no_lifting_bridge :
    ¬ Nonempty (UnaryContainerRepresentation NegativeParameterFamily) :=
  negativeParameterFamily_has_no_container_representation

/-! ## Axiom audit -/

#print axioms list_choice_retains_two_occurrences
#print axioms list_family_selects_complete_search
#print axioms reader_function_selects_direct
#print axioms readerToggleRepresentation_map
#print axioms reader_choice_has_no_finite_provider
#print axioms reader_has_no_finite_search_lifting
#print axioms reader_reflection_refuses_finite_search
#print axioms list_finitarity_exactly_finite_search
#print axioms parameter_negative_family_has_no_lifting_bridge

end NativeFamilyCapabilityNIKSelection
end Mettapedia.Languages.MeTTa.Prime
