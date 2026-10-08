import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorCellUniqueness

/-!
# Intrinsic local admission for the reconstructed comparison

Admission compares the embedded base and fresh object components with the
independent evaluator's actual primitive meanings. It does not mention the
chosen natural isomorphism. Its complete readings establish canonical
admission, and the earned constructor propagation determines every admitted
natural cell and isomorphism uniquely while retaining all raw source objects.

The comparison concerns an actual closed functor and its reconstructed
assignment. The free-extension category and biadjunction are separate
constructions.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (headers : HeaderFormation signature)

theorem reconstructed_base_object (object : C) :
    (reconstructedFunctor mapping headers).obj (baseObject signature object) =
      mapping.obj (baseObject signature object) :=
  (reconstructed_object mapping headers (baseObject signature object)).trans
    (congrArg ObjectImage.value (objectImage_base mapping object))

theorem reconstructed_named_object (origin : symbols.ObjectName) :
    (reconstructedFunctor mapping headers).obj (namedObject origin) = mapping.obj (namedObject origin) :=
  (reconstructed_object mapping headers (namedObject origin)).trans
    (congrArg ObjectImage.value (objectImage_named mapping origin))

theorem parserComparison_hom_component (object : Object signature) :
    (parserComparison mapping headers).hom.app object =
      (objectImage mapping object).comparison.hom ≫
        eqToHom (reconstructed_object mapping headers object).symm := by
  change (objectImage mapping object).comparison.hom ≫
    (eqToHom (reconstructed_functor_equal mapping headers).symm).app object = _
  rw [eqToHom_app]

theorem primitive_comparison_eqToHom (object : Object signature)
    (same : objectImage mapping object = ⟨mapping.obj object, Iso.refl _⟩) :
    (objectImage mapping object).comparison.hom = eqToHom (congrArg ObjectImage.value same).symm := by
  apply (cancel_mono (eqToHom (congrArg ObjectImage.value same))).mp
  rw [comparison_transport mapping same, eqToHom_trans, eqToHom_refl]
  rfl

theorem parserComparison_hom_base (object : C) :
    (parserComparison mapping headers).hom.app (baseObject signature object) =
      eqToHom (reconstructed_base_object mapping headers object).symm := by
  rw [parserComparison_hom_component, primitive_comparison_eqToHom mapping _ (objectImage_base mapping object),
    eqToHom_trans]

theorem parserComparison_hom_name (origin : symbols.ObjectName) :
    (parserComparison mapping headers).hom.app (namedObject origin) =
      eqToHom (reconstructed_named_object mapping headers origin).symm := by
  rw [parserComparison_hom_component, primitive_comparison_eqToHom mapping _ (objectImage_named mapping origin),
    eqToHom_trans]

structure ParserCellAdmission (cell : mapping ⟶ reconstructedFunctor mapping headers) : Prop where
  base (object : C) : cell.app (baseObject signature object) =
    eqToHom (reconstructed_base_object mapping headers object).symm
  object (origin : symbols.ObjectName) : cell.app (namedObject origin) =
    eqToHom (reconstructed_named_object mapping headers origin).symm

theorem parserComparison_admitted : ParserCellAdmission mapping headers (parserComparison mapping headers).hom where
  base := parserComparison_hom_base mapping headers
  object := parserComparison_hom_name mapping headers

theorem admitted_cell_unique (cell : mapping ⟶ reconstructedFunctor mapping headers)
    (admitted : ParserCellAdmission mapping headers cell) : cell = (parserComparison mapping headers).hom :=
  FunctorCellUniqueness.cells_equal_of_generators (parserComparison mapping headers) cell
    (fun object => (admitted.base object).trans (parserComparison_hom_base mapping headers object).symm)
    (fun origin => (admitted.object origin).trans (parserComparison_hom_name mapping headers origin).symm)

abbrev AdmittedParserCell := {cell : mapping ⟶ reconstructedFunctor mapping headers //
  ParserCellAdmission mapping headers cell}

instance admittedParserCellUnique : Unique (AdmittedParserCell mapping headers) where
  default := ⟨(parserComparison mapping headers).hom, parserComparison_admitted mapping headers⟩
  uniq cell := Subtype.ext (admitted_cell_unique mapping headers cell.val cell.property)

abbrev AdmittedParserIso := {comparison : mapping ≅ reconstructedFunctor mapping headers //
  ParserCellAdmission mapping headers comparison.hom}

instance admittedParserIsoUnique : Unique (AdmittedParserIso mapping headers) where
  default := ⟨parserComparison mapping headers, parserComparison_admitted mapping headers⟩
  uniq comparison := Subtype.ext (Iso.ext (admitted_cell_unique mapping headers comparison.val.hom comparison.property))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
