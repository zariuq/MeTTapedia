import Mettapedia.CategoryTheory.RelativeClosedConjunctiveInterpretation
import Mettapedia.CategoryTheory.RelativeClosedConjunctiveNativePredicates
import Mettapedia.CategoryTheory.InternalConjunctiveObjectMaps
import Mettapedia.CategoryTheory.RelativeClosedSyntaxBaseExtensionCoherent

/-!
# Coherent extension from independently supplied conjunctive declarations

A candidate finite-limit closed functor is admitted by its actual base
comparison, proposition comparison, and the two finite operation squares.
Those squares earn the complete normalized truth and conjunction readings.
The native inverse equations determine all added base comparisons, and the
independent structural evaluator then gives the complete natural isomorphism.

Uniqueness uses only the base and fresh-proposition components of the cell.
No primitive-arrow reconstruction, whole-expression compatibility or
universal property is supplied as an admission field. This is the relative
conjunctive layer; the full modal/structural free-forgetful construction is
a separate extension.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedConjunctive.Universal

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open RelativeClosedSyntax GeneratedCategory FunctorNormalization

universe k w

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) [PreservesFiniteLimits base] [MonoidalClosedFunctor base]
variable (meaning : InternalConjunctiveObject.Operations D)

abbrev oldMeanings := Interpretation.lawfulAssignment base meaning

instance oldMeanings_lex : PreservesFiniteLimits (oldMeanings base meaning).base := by
  change PreservesFiniteLimits base
  infer_instance

instance oldMeanings_closed : MonoidalClosedFunctor (oldMeanings base meaning).base := by
  change MonoidalClosedFunctor base
  infer_instance

variable (mapping : InternalConjunctiveObject.Map (NativePredicates.operations (C := C)) meaning)
variable [PreservesFiniteLimits mapping.functor] [MonoidalClosedFunctor mapping.functor]
variable (baseComparison : baseFunctor (nativeSignature (C := C)) ⋙ mapping.functor ≅ base)

def primitiveImages : AtomicPresentation.PrimitiveImages (signature := nativeSignature (C := C)) mapping.functor
    (BaseExtension.WeakExtension.assignment (oldMeanings base meaning)) where
  base := baseComparison
  object origin := by
    cases origin with
    | up origin =>
      cases origin with
      | up origin =>
        cases origin
        exact mapping.proposition

abbrev selected := AtomicPresentation.functor (signature := nativeSignature (C := C)) mapping.functor
  (BaseExtension.WeakExtension.assignment (oldMeanings base meaning))
  (primitiveImages base meaning mapping baseComparison)

theorem truth_read :
    (BaseExtension.Coherent.extracted (oldMeanings base meaning) lawfulHeaders mapping.functor
      (primitiveImages base meaning mapping baseComparison)).arrow (BaseExtension.originalArrows (ULift.up Operation.truth)) =
        (oldMeanings base meaning).arrow (ULift.up Operation.truth) := by
  change (FunctorNormalization.assignment (signature := nativeSignature (C := C))
    (selected base meaning mapping baseComparison) nativeHeaders).arrow
    (BaseExtension.originalArrows (ULift.up Operation.truth)) = _
  rw [FunctorNormalization.assignment_arrow]
  change _ = (⟨𝟙_ D, meaning.proposition, meaning.truth⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D)
  have sourceChoice : objectImage (selected base meaning mapping baseComparison)
      (headerSource nativeHeaders (BaseExtension.originalArrows (ULift.up Operation.truth))) =
        ⟨𝟙_ D, asIso (CartesianMonoidalCategory.terminalComparison
          (selected base meaning mapping baseComparison))⟩ :=
    objectImage_terminal (selected base meaning mapping baseComparison)
  have targetChoice : objectImage (selected base meaning mapping baseComparison)
      (headerTarget nativeHeaders (BaseExtension.originalArrows (ULift.up Operation.truth))) =
        ⟨(selected base meaning mapping baseComparison).obj
          (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ()))), Iso.refl _⟩ :=
    objectImage_named (selected base meaning mapping baseComparison) (ULift.up (ULift.up ()))
  rw [sourceChoice, targetChoice]
  change (⟨𝟙_ D, meaning.proposition,
    (asIso (CartesianMonoidalCategory.terminalComparison (selected base meaning mapping baseComparison))).inv ≫
      (𝟙 _ ≫ mapping.functor.map (NativePredicates.operations (C := C)).truth ≫ mapping.proposition.hom) ≫ 𝟙 _⟩ :
        RelativeClosedSyntax.Interpretation.ArrowValue D) = ⟨𝟙_ D, meaning.proposition, meaning.truth⟩
  apply congrArg (fun arrow : 𝟙_ D ⟶ meaning.proposition =>
    (⟨𝟙_ D, meaning.proposition, arrow⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D))
  rw [Category.id_comp, Category.comp_id, mapping.truth]
  change (asIso (CartesianMonoidalCategory.terminalComparison
    (selected base meaning mapping baseComparison))).inv ≫
      (asIso (CartesianMonoidalCategory.terminalComparison
        (selected base meaning mapping baseComparison))).hom ≫ meaning.truth = meaning.truth
  exact Iso.inv_hom_id_assoc (asIso
    (CartesianMonoidalCategory.terminalComparison (selected base meaning mapping baseComparison))) meaning.truth

theorem conjunction_read :
    (BaseExtension.Coherent.extracted (oldMeanings base meaning) lawfulHeaders mapping.functor
      (primitiveImages base meaning mapping baseComparison)).arrow (BaseExtension.originalArrows (ULift.up Operation.conjunction)) =
        (oldMeanings base meaning).arrow (ULift.up Operation.conjunction) := by
  change (FunctorNormalization.assignment (signature := nativeSignature (C := C))
    (selected base meaning mapping baseComparison) nativeHeaders).arrow
    (BaseExtension.originalArrows (ULift.up Operation.conjunction)) = _
  rw [FunctorNormalization.assignment_arrow]
  change _ = (⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩ :
    RelativeClosedSyntax.Interpretation.ArrowValue D)
  have sourceChoice : objectImage (selected base meaning mapping baseComparison)
      (headerSource nativeHeaders (BaseExtension.originalArrows (ULift.up Operation.conjunction))) =
        ⟨(objectImage (selected base meaning mapping baseComparison)
            (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))).value ⊗
          (objectImage (selected base meaning mapping baseComparison)
            (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))).value,
          asIso (CartesianMonoidalCategory.prodComparison
            (selected base meaning mapping baseComparison)
            (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))
            (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))) ≪≫
          tensorIso (objectImage (selected base meaning mapping baseComparison)
            (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))).comparison
            (objectImage (selected base meaning mapping baseComparison)
              (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))).comparison⟩ :=
    objectImage_product (selected base meaning mapping baseComparison)
      (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))
      (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ())))
  have targetChoice : objectImage (selected base meaning mapping baseComparison)
      (headerTarget nativeHeaders (BaseExtension.originalArrows (ULift.up Operation.conjunction))) =
        ⟨(selected base meaning mapping baseComparison).obj
          (namedObject (signature := nativeSignature (C := C)) (ULift.up (ULift.up ()))), Iso.refl _⟩ :=
    objectImage_named (selected base meaning mapping baseComparison) (ULift.up (ULift.up ()))
  rw [sourceChoice, targetChoice, objectImage_named]
  change (⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition,
    (asIso (CartesianMonoidalCategory.prodComparison (selected base meaning mapping baseComparison)
      (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≪≫
        tensorIso (Iso.refl meaning.proposition) (Iso.refl meaning.proposition)).inv ≫
      (𝟙 _ ≫ mapping.functor.map (NativePredicates.operations (C := C)).conjunction ≫ mapping.proposition.hom) ≫ 𝟙 _⟩ :
        RelativeClosedSyntax.Interpretation.ArrowValue D) =
      ⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, meaning.conjunction⟩
  apply congrArg (fun arrow : meaning.proposition ⊗ meaning.proposition ⟶ meaning.proposition =>
    (⟨meaning.proposition ⊗ meaning.proposition, meaning.proposition, arrow⟩ : RelativeClosedSyntax.Interpretation.ArrowValue D))
  have identities : tensorIso (Iso.refl meaning.proposition) (Iso.refl meaning.proposition) =
      Iso.refl (meaning.proposition ⊗ meaning.proposition) := by
    apply Iso.ext
    exact id_tensorHom_id _ _
  rw [identities]
  change (𝟙 _ ≫ (asIso (CartesianMonoidalCategory.prodComparison
    (selected base meaning mapping baseComparison)
    (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition)).inv) ≫
    (𝟙 _ ≫ mapping.functor.map (NativePredicates.operations (C := C)).conjunction ≫
      mapping.proposition.hom) ≫ 𝟙 _ = meaning.conjunction
  simp only [Category.id_comp, Category.comp_id]
  rw [mapping.conjunction]
  have selectedProduct : CartesianMonoidalCategory.prodComparison
      (selected base meaning mapping baseComparison)
      (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition =
        CartesianMonoidalCategory.lift
          (mapping.functor.map (CartesianMonoidalCategory.fst
            (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≫
              mapping.proposition.hom)
          (mapping.functor.map (CartesianMonoidalCategory.snd
            (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition) ≫
              mapping.proposition.hom) := by
    change CartesianMonoidalCategory.lift (𝟙 _ ≫ _ ≫ _) (𝟙 _ ≫ _ ≫ _) = _
    simp only [Category.id_comp]
    rfl
  rw [← selectedProduct]
  change (asIso (CartesianMonoidalCategory.prodComparison (selected base meaning mapping baseComparison)
      (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition)).inv ≫
    (asIso (CartesianMonoidalCategory.prodComparison (selected base meaning mapping baseComparison)
      (NativePredicates.operations (C := C)).proposition (NativePredicates.operations (C := C)).proposition)).hom ≫
        meaning.conjunction = meaning.conjunction
  exact Iso.inv_hom_id_assoc _ meaning.conjunction

theorem oldArrowImages : BaseExtension.Coherent.OldArrowImages (oldMeanings base meaning) lawfulHeaders mapping.functor
    (primitiveImages base meaning mapping baseComparison) where
  arrow origin := by
    cases origin with
    | up origin =>
      cases origin with
      | truth => exact truth_read base meaning mapping baseComparison
      | conjunction => exact conjunction_read base meaning mapping baseComparison

variable (laws : meaning.Laws)

def comparison : mapping.functor ≅ (Interpretation.nativeModel base meaning laws).diagram :=
  BaseExtension.Coherent.comparison (oldMeanings base meaning) (Interpretation.lawful_realization base meaning laws)
    lawfulHeaders mapping.functor (primitiveImages base meaning mapping baseComparison)
      (oldArrowImages base meaning mapping baseComparison)

abbrev CellAdmission := BaseExtension.Coherent.CellAdmission (oldMeanings base meaning)
  (Interpretation.lawful_realization base meaning laws) mapping.functor (primitiveImages base meaning mapping baseComparison)

theorem comparison_admitted : CellAdmission base meaning mapping baseComparison laws
    (comparison base meaning mapping baseComparison laws).hom :=
  BaseExtension.Coherent.comparison_admitted (oldMeanings base meaning) (Interpretation.lawful_realization base meaning laws)
    lawfulHeaders mapping.functor (primitiveImages base meaning mapping baseComparison)
      (oldArrowImages base meaning mapping baseComparison)

theorem admitted_cell_unique (candidate : mapping.functor ⟶ (Interpretation.nativeModel base meaning laws).diagram)
    (localReadings : CellAdmission base meaning mapping baseComparison laws candidate) :
    candidate = (comparison base meaning mapping baseComparison laws).hom :=
  BaseExtension.Coherent.admitted_cell_unique (oldMeanings base meaning) (Interpretation.lawful_realization base meaning laws)
    lawfulHeaders mapping.functor (primitiveImages base meaning mapping baseComparison)
      (oldArrowImages base meaning mapping baseComparison) candidate localReadings

@[instance_reducible] def admittedIsoUnique :
    Unique {candidate : mapping.functor ≅ (Interpretation.nativeModel base meaning laws).diagram //
      CellAdmission base meaning mapping baseComparison laws candidate.hom} :=
  BaseExtension.Coherent.admittedIsoUnique (oldMeanings base meaning) (Interpretation.lawful_realization base meaning laws)
    lawfulHeaders mapping.functor (primitiveImages base meaning mapping baseComparison)
      (oldArrowImages base meaning mapping baseComparison)

end Mettapedia.CategoryTheory.RelativeClosedConjunctive.Universal
