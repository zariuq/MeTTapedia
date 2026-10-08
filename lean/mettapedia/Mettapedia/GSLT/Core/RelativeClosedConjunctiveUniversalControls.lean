import Mettapedia.CategoryTheory.RelativeClosedConjunctiveModelReadout
import Mettapedia.GSLT.Core.RelativeClosedConjunctiveMapControls

/-!
# A nonidentity complete coherent conjunctive comparison

An independently evaluated conjunction/true interpretation is compared with
an independently evaluated disjunction/false interpretation. Boolean negation
supplies the fresh-proposition comparison and satisfies the two local finite
operation squares. The universal comparison retains both complete Boolean
values and commutes with the whole conjunction arrow. Its admitted complete
cell is unique, while negation with the original truth meaning is rejected.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.GSLT.Core.RelativeClosedConjunctiveUniversalControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open scoped _root_.CategoryTheory.SemilatticeInf
open scoped Mettapedia.CategoryTheory.PredicateDoctrine.HeytingClosed
open Mettapedia.CategoryTheory
open RelativeClosedSyntax GeneratedCategory RelativeClosedConjunctive

abbrev base := RelativeClosedWeakBaseControls.truthFunctor
abbrev firstMeaning := RelativeClosedConjunctiveControls.boolean
abbrev lastMeaning := RelativeClosedConjunctiveMapControls.disjunction
abbrev firstLaws := RelativeClosedConjunctiveControls.boolean_laws
abbrev lastLaws := RelativeClosedConjunctiveMapControls.disjunction_laws

def independentMapping : InternalConjunctiveObject.Map
    (NativePredicates.operations (C := Bool)) lastMeaning :=
  InternalConjunctiveObject.Map.comp (ModelReadout.mapping base firstMeaning firstLaws)
    RelativeClosedConjunctiveMapControls.duality

instance mapping_lex : PreservesFiniteLimits independentMapping.functor := by
  change PreservesFiniteLimits (ModelReadout.diagram base firstMeaning firstLaws ⋙ 𝟭 Type)
  infer_instance

instance mapping_closed : MonoidalClosedFunctor independentMapping.functor := by
  change MonoidalClosedFunctor (ModelReadout.diagram base firstMeaning firstLaws ⋙ 𝟭 Type)
  exact CartesianClosedFunctorCoherence.closed_of_naturalIso
    (eqToIso (Functor.comp_id (ModelReadout.diagram base firstMeaning firstLaws)))

def baseComparison : baseFunctor (nativeSignature (C := Bool)) ⋙ independentMapping.functor ≅ base := by
  apply eqToIso
  change (baseFunctor (nativeSignature (C := Bool)) ⋙
    ModelReadout.diagram base firstMeaning firstLaws) ⋙ 𝟭 Type = base
  exact (congrArg (fun diagram => diagram ⋙ 𝟭 Type)
    (RelativeClosedSyntax.Interpretation.functor_base
      (ModelReadout.model base firstMeaning firstLaws).meanings
      (ModelReadout.model base firstMeaning firstLaws).realization)).trans (Functor.comp_id base)

def completeComparison := Universal.comparison base lastMeaning independentMapping baseComparison lastLaws

theorem independently_admitted : Universal.CellAdmission base lastMeaning independentMapping baseComparison lastLaws
    completeComparison.hom :=
  Universal.comparison_admitted base lastMeaning independentMapping baseComparison lastLaws

theorem every_admitted_complete_cell_agrees
    (candidate : independentMapping.functor ⟶ (ModelReadout.model base lastMeaning lastLaws).diagram)
    (localReadings : Universal.CellAdmission base lastMeaning independentMapping baseComparison lastLaws candidate) :
    candidate = completeComparison.hom :=
  Universal.admitted_cell_unique base lastMeaning independentMapping baseComparison lastLaws candidate localReadings

def completePropositionComparison : ULift.{0} Bool ⟶ ULift.{0} Bool :=
  eqToHom (ModelReadout.proposition_read base firstMeaning firstLaws).symm ≫
    completeComparison.hom.app (NativePredicates.operations (C := Bool)).proposition ≫
      eqToHom (ModelReadout.proposition_read base lastMeaning lastLaws)

theorem complete_proposition_comparison :
    completePropositionComparison = RelativeClosedConjunctiveMapControls.negation.hom := by
  have component := independently_admitted.object (ULift.up (ULift.up ()))
  change completeComparison.hom.app (NativePredicates.operations (C := Bool)).proposition =
    independentMapping.proposition.hom ≫
      eqToHom (ModelReadout.proposition_read base lastMeaning lastLaws).symm at component
  change eqToHom (ModelReadout.proposition_read base firstMeaning firstLaws).symm ≫
    completeComparison.hom.app (NativePredicates.operations (C := Bool)).proposition ≫
      eqToHom (ModelReadout.proposition_read base lastMeaning lastLaws) = _
  rw [component]
  change eqToHom (ModelReadout.proposition_read base firstMeaning firstLaws).symm ≫
    (eqToHom (ModelReadout.proposition_read base firstMeaning firstLaws) ≫
      RelativeClosedConjunctiveMapControls.negation.hom) ≫
        eqToHom (ModelReadout.proposition_read base lastMeaning lastLaws).symm ≫
          eqToHom (ModelReadout.proposition_read base lastMeaning lastLaws) = _
  change 𝟙 (ULift.{0} Bool) ≫ (𝟙 (ULift.{0} Bool) ≫
    RelativeClosedConjunctiveMapControls.negation.hom) ≫
      𝟙 (ULift.{0} Bool) ≫ 𝟙 (ULift.{0} Bool) = _
  simp only [Category.id_comp, Category.comp_id]

theorem complete_nonidentity_values :
    (completePropositionComparison (ULift.up true)).down = false ∧
      (completePropositionComparison (ULift.up false)).down = true := by
  rw [complete_proposition_comparison]
  exact ⟨rfl, rfl⟩

theorem comparison_is_not_identity : completePropositionComparison ≠ 𝟙 (ULift.{0} Bool) := by
  intro same
  have impossible := (congrArg (fun arrow : ULift.{0} Bool ⟶ ULift.{0} Bool =>
    (arrow (ULift.up true)).down) same).symm.trans complete_nonidentity_values.1
  exact Bool.false_ne_true impossible.symm

theorem whole_conjunction_naturality :
    independentMapping.functor.map (NativePredicates.operations (C := Bool)).conjunction ≫
        completeComparison.hom.app (NativePredicates.operations (C := Bool)).proposition =
      completeComparison.hom.app
          ((NativePredicates.operations (C := Bool)).proposition ⊗ (NativePredicates.operations (C := Bool)).proposition) ≫
        (ModelReadout.diagram base lastMeaning lastLaws).map (NativePredicates.operations (C := Bool)).conjunction :=
  completeComparison.hom.naturality (NativePredicates.operations (C := Bool)).conjunction

theorem local_isomorphism_admission_is_inhabited_and_unique :
    Nonempty (Unique {candidate : independentMapping.functor ≅
      (ModelReadout.model base lastMeaning lastLaws).diagram //
        Universal.CellAdmission base lastMeaning independentMapping baseComparison lastLaws candidate.hom}) :=
  ⟨Universal.admittedIsoUnique base lastMeaning independentMapping baseComparison lastLaws⟩

theorem retaining_the_old_truth_rejects_the_same_comparison :
    ¬ firstMeaning.truth ≫ completePropositionComparison =
      CartesianMonoidalCategory.toUnit (𝟙_ Type) ≫ firstMeaning.truth := by
  rw [complete_proposition_comparison]
  exact RelativeClosedConjunctiveMapControls.same_truth_rejects_negation

end Mettapedia.GSLT.Core.RelativeClosedConjunctiveUniversalControls
