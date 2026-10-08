import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationClosed
import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationEqualizers

/-!
# Independent expression readouts from an actual closed functor

The target evaluator and the functor on generated arrow classes are separate
constructions. These local readouts compare their complete object and arrow
values through the earned native-choice comparisons. In particular, transport
retains a supplied arrow, its two endpoints, and its equalizer candidate.

No declaration realization or whole-expression evaluation law is supplied.
The simultaneous generated-rule reconstruction is assembled separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory Interpretation

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping] (headers : HeaderFormation signature)

def ObjectRead (object : Object signature) : Prop :=
  (assignment mapping headers).evaluateObject object.code =
    some ((normalizedFunctor mapping).obj object)

def ArrowRead {source target : Object signature} (raw : RawHom source target) : Prop :=
  (assignment mapping headers).evaluateArrow raw.code =
    some ⟨(normalizedFunctor mapping).obj source, (normalizedFunctor mapping).obj target,
      (normalizedFunctor mapping).map (classOf raw)⟩

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D] in
theorem arrowValue_transport {source target before after : D} (arrow : source ⟶ target)
    (sourceSame : source = before) (targetSame : target = after) :
    (⟨source, target, arrow⟩ : ArrowValue D) =
      ⟨before, after, eqToHom sourceSame.symm ≫ arrow ≫ eqToHom targetSame⟩ := by
  cases sourceSame
  cases targetSame
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

theorem arrow_read_transport {source target : Object signature} (raw : RawHom source target)
    {before after : D} (arrow : before ⟶ after)
    (sourceSame : before = (normalizedFunctor mapping).obj source)
    (targetSame : after = (normalizedFunctor mapping).obj target)
    (read : (assignment mapping headers).evaluateArrow raw.code = some ⟨before, after, arrow⟩)
    (mapped : (normalizedFunctor mapping).map (classOf raw) =
      eqToHom sourceSame.symm ≫ arrow ≫ eqToHom targetSame) : ArrowRead mapping headers raw :=
  read.trans ((congrArg some (arrowValue_transport arrow sourceSame targetSame)).trans
    (congrArg (fun value => some (⟨(normalizedFunctor mapping).obj source,
      (normalizedFunctor mapping).obj target, value⟩ : ArrowValue D)) mapped.symm))

theorem object_read_base (object : C) : ObjectRead mapping headers (baseObject signature object) :=
  ((assignment mapping headers).evaluate_base_object object).trans
    (congrArg some (congrArg ObjectImage.value (objectImage_base mapping object)).symm)

theorem object_read_name (origin : symbols.ObjectName) :
    ObjectRead mapping headers (namedObject origin) :=
  ((assignment mapping headers).evaluate_object_name origin).trans
    (congrArg some (congrArg ObjectImage.value (objectImage_named mapping origin)).symm)

theorem object_read_terminal : ObjectRead mapping headers (terminal signature) :=
  ((assignment mapping headers).evaluate_terminal_object).trans
    (congrArg some (normalized_terminal_object mapping).symm)

theorem object_read_product (first second : Object signature)
    (firstRead : ObjectRead mapping headers first) (secondRead : ObjectRead mapping headers second) :
    ObjectRead mapping headers (product first second) :=
  ((assignment mapping headers).evaluate_product firstRead secondRead).trans
    (congrArg some (normalized_product_object mapping first second).symm)

theorem object_read_exponential (argument result : Object signature)
    (argumentRead : ObjectRead mapping headers argument) (resultRead : ObjectRead mapping headers result) :
    ObjectRead mapping headers (exponentialObject argument result) :=
  ((assignment mapping headers).evaluate_exponential argumentRead resultRead).trans
    (congrArg some (normalized_exponential_object mapping argument result).symm)

theorem object_read_equalizer {source target : Object signature} (first second : RawHom source target)
    (sourceRead : ObjectRead mapping headers source) (targetRead : ObjectRead mapping headers target)
    (firstRead : ArrowRead mapping headers first) (secondRead : ArrowRead mapping headers second) :
    ObjectRead mapping headers (PresentedEqualizer.object first second) :=
  ((assignment mapping headers).evaluate_equalizer _ _ sourceRead targetRead firstRead secondRead).trans
    (congrArg some (normalized_equalizer_object mapping first second).symm)

theorem arrow_read_base {source target : C} (arrow : source ⟶ target) :
    ArrowRead mapping headers
      (⟨.base arrow, ⟨.baseArrow arrow⟩⟩ : RawHom (baseObject signature source) (baseObject signature target)) := by
  change some (⟨mapping.obj (baseObject signature source), mapping.obj (baseObject signature target),
      mapping.map (baseArrow arrow)⟩ : ArrowValue D) =
    some ⟨(objectImage mapping (baseObject signature source)).value,
      (objectImage mapping (baseObject signature target)).value,
      (objectImage mapping (baseObject signature source)).comparison.inv ≫
        mapping.map (baseArrow arrow) ≫ (objectImage mapping (baseObject signature target)).comparison.hom⟩
  rw [objectImage_base, objectImage_base]
  simp only [Iso.refl_inv, Iso.refl_hom, Category.id_comp, Category.comp_id]

theorem arrow_read_name (origin : symbols.ArrowName) :
    ArrowRead mapping headers (namedArrow headers origin) := rfl

theorem arrow_read_identity (object : Object signature) (read : ObjectRead mapping headers object) :
    ArrowRead mapping headers (RawHom.identity object) := by
  change (assignment mapping headers).evaluateArrow (.identity object.code) =
    some ⟨(normalizedFunctor mapping).obj object, (normalizedFunctor mapping).obj object,
      (normalizedFunctor mapping).map (𝟙 object)⟩
  rw [(normalizedFunctor mapping).map_id]
  exact (assignment mapping headers).evaluate_identity read

theorem arrow_read_compose {source middle target : Object signature}
    (first : RawHom source middle) (second : RawHom middle target)
    (firstRead : ArrowRead mapping headers first) (secondRead : ArrowRead mapping headers second) :
    ArrowRead mapping headers (RawHom.compose first second) := by
  change (assignment mapping headers).evaluateArrow (.compose first.code second.code) =
    some ⟨(normalizedFunctor mapping).obj source, (normalizedFunctor mapping).obj target,
      (normalizedFunctor mapping).map (classOf first ≫ classOf second)⟩
  rw [(normalizedFunctor mapping).map_comp]
  exact (assignment mapping headers).evaluate_compose _ _ firstRead secondRead

theorem arrow_read_terminal (source : Object signature) (read : ObjectRead mapping headers source) :
    ArrowRead mapping headers
      (⟨.terminal source.code, ⟨.terminalArrow source.formed.some⟩⟩ : RawHom source (terminal signature)) := by
  apply arrow_read_transport mapping headers _ _ rfl (normalized_terminal_object mapping).symm
    ((assignment mapping headers).evaluate_terminal_arrow read)
  simpa only [GeneratedCategory.toTerminal, eqToHom_refl, Category.id_comp] using
    normalized_terminal_arrow mapping source

theorem arrow_read_first (first second : Object signature)
    (firstRead : ObjectRead mapping headers first) (secondRead : ObjectRead mapping headers second) :
    ArrowRead mapping headers
      (⟨.first first.code second.code, ⟨.first first.formed.some second.formed.some⟩⟩ :
        RawHom (product first second) first) := by
  apply arrow_read_transport mapping headers _ _ (normalized_product_object mapping first second).symm rfl
    ((assignment mapping headers).evaluate_first firstRead secondRead)
  simpa only [GeneratedCategory.first, eqToHom_refl, Category.comp_id] using
    normalized_first mapping first second

theorem arrow_read_second (first second : Object signature)
    (firstRead : ObjectRead mapping headers first) (secondRead : ObjectRead mapping headers second) :
    ArrowRead mapping headers
      (⟨.second first.code second.code, ⟨.second first.formed.some second.formed.some⟩⟩ :
        RawHom (product first second) second) := by
  apply arrow_read_transport mapping headers _ _ (normalized_product_object mapping first second).symm rfl
    ((assignment mapping headers).evaluate_second firstRead secondRead)
  simpa only [GeneratedCategory.second, eqToHom_refl, Category.comp_id] using
    normalized_second mapping first second

theorem arrow_read_pair {source first second : Object signature}
    (before : RawHom source first) (after : RawHom source second)
    (beforeRead : ArrowRead mapping headers before) (afterRead : ArrowRead mapping headers after) :
    ArrowRead mapping headers
      (⟨.pair before.code after.code, ⟨.pair before.admitted.some after.admitted.some⟩⟩ :
        RawHom source (product first second)) := by
  apply arrow_read_transport mapping headers _ _ rfl (normalized_product_object mapping first second).symm
    ((assignment mapping headers).evaluate_pair _ _ beforeRead afterRead)
  simpa only [GeneratedCategory.pairing, classOf, Quotient.map₂_mk, eqToHom_refl, Category.id_comp] using
    normalized_pairing mapping (classOf before) (classOf after)

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
