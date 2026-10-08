import Mettapedia.CategoryTheory.InternalConjunctiveObject

/-!
# Declaration-preserving maps of internal conjunctive objects

An actual functor, an independently supplied proposition-object isomorphism,
and two finite operation squares determine the complete predicate action.
The action preserves meet, truth, order and substitution. Every guarded
source arrow then has its actual target equalizer factor, with the complete
forget square and uniqueness. Identity and composition are constructed from
these local readings, retaining the original functors and object comparisons.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.InternalConjunctiveObject

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory

universe u v w k l m

variable {C : Type u} [Category.{k} C] [CartesianMonoidalCategory C]
variable {D : Type v} [Category.{l} D] [CartesianMonoidalCategory D]
variable {E : Type w} [Category.{m} E] [CartesianMonoidalCategory E]

structure Map (source : Operations C) (target : Operations D) where
  functor : C ⥤ D
  proposition : functor.obj source.proposition ≅ target.proposition
  truth : functor.map source.truth ≫ proposition.hom =
    CartesianMonoidalCategory.toUnit (functor.obj (𝟙_ C)) ≫ target.truth
  conjunction : functor.map source.conjunction ≫ proposition.hom =
    CartesianMonoidalCategory.lift
      (functor.map (CartesianMonoidalCategory.fst source.proposition source.proposition) ≫ proposition.hom)
      (functor.map (CartesianMonoidalCategory.snd source.proposition source.proposition) ≫ proposition.hom) ≫
        target.conjunction

namespace Map

variable {source : Operations C} {target : Operations D} {last : Operations E}
variable (mapping : Map source target)

def image {context : C} (predicate : source.Fiber context) : target.Fiber (mapping.functor.obj context) :=
  mapping.functor.map predicate ≫ mapping.proposition.hom

theorem image_reindex {context before : C} (substitution : context ⟶ before)
    (predicate : source.Fiber before) :
    mapping.image (source.reindex substitution predicate) =
      target.reindex (mapping.functor.map substitution) (mapping.image predicate) := by
  change mapping.functor.map (substitution ≫ predicate) ≫ mapping.proposition.hom =
    mapping.functor.map substitution ≫ (mapping.functor.map predicate ≫ mapping.proposition.hom)
  exact (congrArg (fun arrow => arrow ≫ mapping.proposition.hom)
    (mapping.functor.map_comp substitution predicate)).trans (Category.assoc _ _ _)

theorem image_top (context : C) :
    mapping.image (source.top context) = target.top (mapping.functor.obj context) := by
  change mapping.functor.map (CartesianMonoidalCategory.toUnit context ≫ source.truth) ≫
      mapping.proposition.hom = CartesianMonoidalCategory.toUnit (mapping.functor.obj context) ≫ target.truth
  rw [mapping.functor.map_comp, Category.assoc, mapping.truth, ← Category.assoc]
  exact congrArg (fun arrow => arrow ≫ target.truth)
    (CartesianMonoidalCategory.map_toUnit_comp_terminalComparison mapping.functor context)

theorem image_meet {context : C} (first second : source.Fiber context) :
    mapping.image (source.meet first second) = target.meet (mapping.image first) (mapping.image second) := by
  change mapping.functor.map (CartesianMonoidalCategory.lift first second ≫ source.conjunction) ≫
      mapping.proposition.hom = CartesianMonoidalCategory.lift
        (mapping.functor.map first ≫ mapping.proposition.hom)
        (mapping.functor.map second ≫ mapping.proposition.hom) ≫ target.conjunction
  rw [mapping.functor.map_comp, Category.assoc, mapping.conjunction, ← Category.assoc,
    CartesianMonoidalCategory.comp_lift]
  have firstRead : mapping.functor.map (CartesianMonoidalCategory.lift first second) ≫
      (mapping.functor.map (CartesianMonoidalCategory.fst _ _) ≫ mapping.proposition.hom) =
        mapping.functor.map first ≫ mapping.proposition.hom := by
    rw [← Category.assoc, ← mapping.functor.map_comp, CartesianMonoidalCategory.lift_fst]
  have secondRead : mapping.functor.map (CartesianMonoidalCategory.lift first second) ≫
      (mapping.functor.map (CartesianMonoidalCategory.snd _ _) ≫ mapping.proposition.hom) =
        mapping.functor.map second ≫ mapping.proposition.hom := by
    rw [← Category.assoc, ← mapping.functor.map_comp, CartesianMonoidalCategory.lift_snd]
  exact congrArg (fun arrow => arrow ≫ target.conjunction)
    (congrArg₂ CartesianMonoidalCategory.lift firstRead secondRead)

def orderHom (sourceLaws : source.Laws) (targetLaws : target.Laws) (context : C) :
    letI := Operations.semilattice sourceLaws context
    letI := Operations.semilattice targetLaws (mapping.functor.obj context)
    source.Fiber context →o target.Fiber (mapping.functor.obj context) := by
  letI := Operations.semilattice sourceLaws context
  letI := Operations.semilattice targetLaws (mapping.functor.obj context)
  refine ⟨mapping.image, ?_⟩
  intro first second ordered
  change source.meet second first = first at ordered
  change target.meet (mapping.image second) (mapping.image first) = mapping.image first
  exact (mapping.image_meet second first).symm.trans (congrArg mapping.image ordered)

def identity (source : Operations C) : Map source source where
  functor := 𝟭 C
  proposition := Iso.refl _
  truth := by
    change source.truth ≫ 𝟙 _ = CartesianMonoidalCategory.toUnit (𝟙_ C) ≫ source.truth
    rw [Category.comp_id, CartesianMonoidalCategory.toUnit_unit, Category.id_comp]
  conjunction := by
    change source.conjunction ≫ 𝟙 _ = CartesianMonoidalCategory.lift
      (CartesianMonoidalCategory.fst _ _ ≫ 𝟙 _) (CartesianMonoidalCategory.snd _ _ ≫ 𝟙 _) ≫ source.conjunction
    rw [Category.comp_id, Category.comp_id, Category.comp_id,
      CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]

theorem identity_image {context : C} (predicate : source.Fiber context) :
    (identity source).image predicate = predicate := Category.comp_id predicate

def comp (before : Map source target) (after : Map target last) : Map source last where
  functor := before.functor ⋙ after.functor
  proposition := after.functor.mapIso before.proposition ≪≫ after.proposition
  truth := by
    change after.functor.map (before.functor.map source.truth) ≫
        (after.functor.map before.proposition.hom ≫ after.proposition.hom) =
      CartesianMonoidalCategory.toUnit (after.functor.obj (before.functor.obj (𝟙_ C))) ≫ last.truth
    rw [← Category.assoc, ← after.functor.map_comp, before.truth, after.functor.map_comp,
      Category.assoc, after.truth, ← Category.assoc]
    exact congrArg (fun arrow => arrow ≫ last.truth)
      (CartesianMonoidalCategory.map_toUnit_comp_terminalComparison after.functor
        (before.functor.obj (𝟙_ C)))
  conjunction := by
    have first := congrArg after.image (before.image_meet
      (CartesianMonoidalCategory.fst source.proposition source.proposition)
      (CartesianMonoidalCategory.snd source.proposition source.proposition))
    have second := after.image_meet
      (before.image (CartesianMonoidalCategory.fst source.proposition source.proposition))
      (before.image (CartesianMonoidalCategory.snd source.proposition source.proposition))
    have complete := first.trans second
    have original : source.meet (CartesianMonoidalCategory.fst source.proposition source.proposition)
        (CartesianMonoidalCategory.snd source.proposition source.proposition) = source.conjunction := by
      change CartesianMonoidalCategory.lift (CartesianMonoidalCategory.fst _ _)
        (CartesianMonoidalCategory.snd _ _) ≫ source.conjunction = source.conjunction
      rw [CartesianMonoidalCategory.lift_fst_snd, Category.id_comp]
    rw [original] at complete
    change after.functor.map (before.functor.map source.conjunction) ≫
        (after.functor.map before.proposition.hom ≫ after.proposition.hom) =
      CartesianMonoidalCategory.lift
        (after.functor.map (before.functor.map (CartesianMonoidalCategory.fst _ _)) ≫
          (after.functor.map before.proposition.hom ≫ after.proposition.hom))
        (after.functor.map (before.functor.map (CartesianMonoidalCategory.snd _ _)) ≫
          (after.functor.map before.proposition.hom ≫ after.proposition.hom)) ≫ last.conjunction
    simpa only [image, Operations.meet, Functor.map_comp, Category.assoc] using complete

theorem comp_functor (before : Map source target) (after : Map target last) :
    (comp before after).functor = before.functor ⋙ after.functor := rfl

theorem comp_proposition (before : Map source target) (after : Map target last) :
    (comp before after).proposition.hom = after.functor.map before.proposition.hom ≫ after.proposition.hom := rfl

theorem comp_image (before : Map source target) (after : Map target last)
    {context : C} (predicate : source.Fiber context) :
    (comp before after).image predicate = after.image (before.image predicate) := by
  change after.functor.map (before.functor.map predicate) ≫
      (after.functor.map before.proposition.hom ≫ after.proposition.hom) =
    after.functor.map (before.functor.map predicate ≫ before.proposition.hom) ≫ after.proposition.hom
  rw [after.functor.map_comp, Category.assoc]

variable [HasEqualizers C] [HasEqualizers D]

def satisfyingMap {context : C} (predicate : source.Fiber context) :
    mapping.functor.obj (source.satisfying predicate) ⟶ target.satisfying (mapping.image predicate) :=
  target.factor (mapping.image predicate) (mapping.functor.map (source.inclusion predicate))
    ((mapping.image_reindex (source.inclusion predicate) predicate).symm.trans
      ((congrArg mapping.image (source.inclusion_satisfies predicate)).trans
        (mapping.image_top (source.satisfying predicate))))

theorem satisfyingMap_inclusion {context : C} (predicate : source.Fiber context) :
    mapping.satisfyingMap predicate ≫ target.inclusion (mapping.image predicate) =
      mapping.functor.map (source.inclusion predicate) := target.factor_inclusion _ _ _

theorem satisfyingMap_unique {context : C} (predicate : source.Fiber context)
    (candidate : mapping.functor.obj (source.satisfying predicate) ⟶ target.satisfying (mapping.image predicate))
    (square : candidate ≫ target.inclusion (mapping.image predicate) =
      mapping.functor.map (source.inclusion predicate)) : candidate = mapping.satisfyingMap predicate :=
  (cancel_mono (target.inclusion (mapping.image predicate))).mp
    (square.trans (mapping.satisfyingMap_inclusion predicate).symm)

omit [HasEqualizers C] [HasEqualizers D] in
theorem guarded_image {context before : C} (predicate : source.Fiber before) (arrow : context ⟶ before)
    (guard : source.reindex arrow predicate = source.top context) :
    target.reindex (mapping.functor.map arrow) (mapping.image predicate) =
      target.top (mapping.functor.obj context) :=
  (mapping.image_reindex arrow predicate).symm.trans
    ((congrArg mapping.image guard).trans (mapping.image_top context))

theorem factor_image {context before : C} (predicate : source.Fiber before) (arrow : context ⟶ before)
    (guard : source.reindex arrow predicate = source.top context) :
    mapping.functor.map (source.factor predicate arrow guard) ≫ mapping.satisfyingMap predicate =
      target.factor (mapping.image predicate) (mapping.functor.map arrow) (mapping.guarded_image predicate arrow guard) := by
  apply (cancel_mono (target.inclusion (mapping.image predicate))).mp
  rw [Category.assoc, mapping.satisfyingMap_inclusion, ← mapping.functor.map_comp,
    source.factor_inclusion, target.factor_inclusion]

end Map

end Mettapedia.CategoryTheory.InternalConjunctiveObject
