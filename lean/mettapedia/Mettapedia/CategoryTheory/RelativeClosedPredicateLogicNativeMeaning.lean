import Mettapedia.CategoryTheory.RelativeClosedPredicateLogicRealization
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateQuantifier
import Mettapedia.CategoryTheory.HigherOrderInternalPredicateImplication

/-!
# Native higher-order meanings realize the authored logical diagrams

The primitive meanings use the actual classifier, fibre quantifiers and
implication of a higher-order predicate doctrine. Their previously earned
finite diagrams admit the independently authored declarations. The quotient
diagram is then constructed by the structural evaluator and generated-rule
soundness, with complete original-arrow readouts.

Target object and hom universes remain independent. The common-hom-universe
semantic-model bundle is not needed for this actual interpretation functor.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.NativeMeaning

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open RelativeClosedSyntax GeneratedCategory

universe k w z p
variable {C : Type k} [Category.{k} C]
variable {D : Type w} [Category.{z} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (base : C ⥤ D) (doctrine : PredicateDoctrine.HigherOrder.{w,z,p} D)

def meaning : Interpretation.Meaning base where
  predicates := HigherOrderInternalPredicateObject.operations doctrine
  implication := HigherOrderInternalPredicateImplication.operation doctrine
  universal route := HigherOrderInternalPredicateQuantifier.forallOperation doctrine (base.map route)
  existential route := HigherOrderInternalPredicateQuantifier.existsOperation doctrine (base.map route)

theorem admitted : Interpretation.Admission base (meaning base doctrine) where
  conjunction := HigherOrderInternalPredicateObject.laws doctrine
  implicationMonotonicity := (HigherOrderInternalPredicateImplication.qualification doctrine).monotonicity
  implicationUnit := (HigherOrderInternalPredicateImplication.qualification doctrine).unit
  implicationCounit := (HigherOrderInternalPredicateImplication.qualification doctrine).counit
  universalMonotonicity route :=
    (HigherOrderInternalPredicateQuantifier.forallQualification doctrine (base.map route)).monotonicity
  universalUnit route :=
    (HigherOrderInternalPredicateQuantifier.forallQualification doctrine (base.map route)).unit
  universalCounit route :=
    (HigherOrderInternalPredicateQuantifier.forallQualification doctrine (base.map route)).counit
  existentialMonotonicity route :=
    (HigherOrderInternalPredicateQuantifier.existsQualification doctrine (base.map route)).monotonicity
  existentialUnit route :=
    (HigherOrderInternalPredicateQuantifier.existsQualification doctrine (base.map route)).unit
  existentialCounit route :=
    (HigherOrderInternalPredicateQuantifier.existsQualification doctrine (base.map route)).counit

theorem realized : RelativeClosedSyntax.Interpretation.Realization (lawfulSignature (C := C))
    (Interpretation.lawfulAssignment base (meaning base doctrine)) :=
  Interpretation.lawful_realization base (meaning base doctrine) (admitted base doctrine)

def diagram : Object (lawfulSignature (C := C)) ⥤ D :=
  RelativeClosedSyntax.Interpretation.functor
    (Interpretation.lawfulAssignment base (meaning base doctrine)) (realized base doctrine)

theorem original_object (object : Object (signature (C := C))) (value : D)
    (read : RawInterpretation.ObjectReads (Interpretation.assignment base (meaning base doctrine)) object value) :
    (diagram base doctrine).obj (equationInclusion.object object) = value :=
  RelativeClosedSyntax.Interpretation.objectValue_unique
    (Interpretation.lawfulAssignment base (meaning base doctrine)) (realized base doctrine)
    (equationInclusion.object object) value
    ((EquationExtension.evaluate_object_original (signature (C := C)) declaration
      (Interpretation.assignment base (meaning base doctrine)) object.code).trans read)

theorem original_image {source target : Object (signature (C := C))}
    (raw : RawHom source target) {before after : D} (arrow : before ⟶ after)
    (read : RawInterpretation.Reads (Interpretation.assignment base (meaning base doctrine)) raw arrow) :
    HEq ((diagram base doctrine).map (classOf (equationInclusion.rawArrow raw))) arrow :=
  RelativeClosedSyntax.Interpretation.functor_map_heq
    (Interpretation.lawfulAssignment base (meaning base doctrine)) (realized base doctrine)
    (equationInclusion.rawArrow raw) arrow
    ((EquationExtension.evaluate_arrow_original (signature (C := C)) declaration
      (Interpretation.assignment base (meaning base doctrine)) raw.code).trans read)

def imageAt {source target : Object (signature (C := C))}
    (raw : RawHom source target) {before after : D}
    (sourceRead : RawInterpretation.ObjectReads (Interpretation.assignment base (meaning base doctrine)) source before)
    (targetRead : RawInterpretation.ObjectReads (Interpretation.assignment base (meaning base doctrine)) target after) :
    before ⟶ after :=
  eqToHom (original_object base doctrine source before sourceRead).symm ≫
    (diagram base doctrine).map (classOf (equationInclusion.rawArrow raw)) ≫
      eqToHom (original_object base doctrine target after targetRead)

theorem imageAt_readout {source target : Object (signature (C := C))}
    (raw : RawHom source target) {before after : D}
    (sourceRead : RawInterpretation.ObjectReads (Interpretation.assignment base (meaning base doctrine)) source before)
    (targetRead : RawInterpretation.ObjectReads (Interpretation.assignment base (meaning base doctrine)) target after)
    (arrow : before ⟶ after)
    (read : RawInterpretation.Reads (Interpretation.assignment base (meaning base doctrine)) raw arrow) :
    imageAt base doctrine raw sourceRead targetRead = arrow := by
  have complete := (conj_eqToHom_iff_heq
    ((diagram base doctrine).map (classOf (equationInclusion.rawArrow raw))) arrow
    (original_object base doctrine source before sourceRead)
    (original_object base doctrine target after targetRead)).mpr
      (original_image base doctrine raw arrow read)
  simp only [imageAt, complete, ← Category.assoc, eqToHom_trans, eqToHom_refl,
    Category.id_comp]
  rw [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]

theorem universal_image {source target : C} (route : source ⟶ target) :
    HEq ((diagram base doctrine).map (classOf (equationInclusion.rawArrow (universalRaw route))))
      (HigherOrderInternalPredicateQuantifier.forallOperation doctrine (base.map route)) :=
  original_image base doctrine (universalRaw route) _ rfl

theorem existential_image {source target : C} (route : source ⟶ target) :
    HEq ((diagram base doctrine).map (classOf (equationInclusion.rawArrow (existentialRaw route))))
      (HigherOrderInternalPredicateQuantifier.existsOperation doctrine (base.map route)) :=
  original_image base doctrine (existentialRaw route) _ rfl

theorem implication_image :
    HEq ((diagram base doctrine).map (classOf
      (equationInclusion.rawArrow (implicationRaw (C := C)))))
      (HigherOrderInternalPredicateImplication.operation doctrine) :=
  original_image base doctrine implicationRaw _ rfl

end Mettapedia.CategoryTheory.RelativeClosedPredicateLogic.NativeMeaning
