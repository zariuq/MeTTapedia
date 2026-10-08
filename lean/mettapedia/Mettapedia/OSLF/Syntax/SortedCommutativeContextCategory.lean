import Mettapedia.OSLF.Syntax.SortedCommutativeContextReconstruction
import Mettapedia.GSLT.Logic.RelativePushoutFunctor

/-!
# The independently formed sorted equation/context category

Actual raw composition and filling descend through their local generated
equations. Closed arrows retain the independently formed term classes. The
normalization functor is full, faithful and onto objects by the proved context
reconstruction, while its complete closed-value action is preserved.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedCommutative

open _root_.CategoryTheory
open Mettapedia.OSLF.SortedConstructors

universe u v

variable {signature : Signature.{u,v}} {Parallel : signature.Srt → Prop}

namespace ContextClass

def identity (sort : signature.Srt) : ContextClass signature Parallel sort sort := contextClassOf .hole

def comp {source middle target : signature.Srt}
    (inner : ContextClass signature Parallel source middle) (outer : ContextClass signature Parallel middle target) :
    ContextClass signature Parallel source target :=
  Quotient.map₂ (RawContext.comp (signature := signature) (Parallel := Parallel))
    (fun first second (innerEquation : ContextEquation first second) before after
      (outerEquation : ContextEquation before after) => innerEquation.comp outerEquation) inner outer

def fill {source target : signature.Srt} (context : ContextClass signature Parallel source target)
    (supplied : Class signature Parallel source) : Class signature Parallel target :=
  Quotient.map₂ (fun context supplied => context.fill supplied)
    (fun _first second equation before _ valueEquation =>
      (equation.fill before).trans (second.fill_equation valueEquation)) context supplied

theorem identity_comp {source target : signature.Srt} (context : ContextClass signature Parallel source target) :
    (identity source).comp context = context :=
  Quotient.inductionOn context (fun raw => congrArg contextClassOf (RawContext.identity_comp raw))

theorem comp_identity {source target : signature.Srt} (context : ContextClass signature Parallel source target) :
    context.comp (identity target) = context := Quotient.inductionOn context (fun _ => rfl)

theorem comp_assoc {first second third fourth : signature.Srt}
    (before : ContextClass signature Parallel first second) (middle : ContextClass signature Parallel second third)
    (after : ContextClass signature Parallel third fourth) :
    (before.comp middle).comp after = before.comp (middle.comp after) :=
  Quotient.inductionOn₃ before middle after
    (fun first second third => congrArg contextClassOf (RawContext.comp_assoc first second third))

theorem fill_identity {sort : signature.Srt} (supplied : Class signature Parallel sort) :
    (identity sort).fill supplied = supplied := Quotient.inductionOn supplied (fun _ => rfl)

theorem fill_comp {source middle target : signature.Srt}
    (inner : ContextClass signature Parallel source middle) (outer : ContextClass signature Parallel middle target)
    (supplied : Class signature Parallel source) :
    (inner.comp outer).fill supplied = outer.fill (inner.fill supplied) :=
  Quotient.inductionOn₃ inner outer supplied
    (fun inner outer supplied => congrArg classOf (RawContext.fill_comp inner outer supplied))

theorem normalize_comp {source middle target : signature.Srt}
    (inner : ContextClass signature Parallel source middle) (outer : ContextClass signature Parallel middle target) :
    normalizeContext (inner.comp outer) = (normalizeContext inner).comp (normalizeContext outer) :=
  Quotient.inductionOn₂ inner outer RawContext.normalize_comp

theorem normalize_filling {source target : signature.Srt}
    (context : ContextClass signature Parallel source target) (supplied : Class signature Parallel source) :
    (mixedAction signature Parallel).read (normalizeContext context) supplied = context.fill supplied :=
  Quotient.inductionOn₂ context supplied RawContext.normalize_filling

end ContextClass

inductive RawObject (signature : Signature.{u,v}) (Parallel : signature.Srt → Prop) where
  | origin
  | interface (sort : signature.Srt)

inductive RawArrow : RawObject signature Parallel → RawObject signature Parallel → Type (max u v) where
  | identity : RawArrow .origin .origin
  | value {sort : signature.Srt} (supplied : Class signature Parallel sort) : RawArrow .origin (.interface sort)
  | context {source target : signature.Srt} (supplied : ContextClass signature Parallel source target) :
      RawArrow (.interface source) (.interface target)

namespace RawArrow

def id : (object : RawObject signature Parallel) → RawArrow object object
  | .origin => .identity
  | .interface sort => .context (ContextClass.identity sort)

def comp : {source middle target : RawObject signature Parallel} → RawArrow source middle →
    RawArrow middle target → RawArrow source target
  | _, _, _, .identity, second => second
  | _, _, _, .value supplied, .context suppliedContext => .value (suppliedContext.fill supplied)
  | _, _, _, .context first, .context second => .context (first.comp second)

theorem id_comp {source target : RawObject signature Parallel} (arrow : RawArrow source target) :
    comp (id source) arrow = arrow := by
  cases arrow with
  | identity => rfl
  | value => rfl
  | context supplied => exact congrArg context (ContextClass.identity_comp supplied)

theorem comp_id {source target : RawObject signature Parallel} (arrow : RawArrow source target) :
    comp arrow (id target) = arrow := by
  cases arrow with
  | identity => rfl
  | value supplied => exact congrArg value (ContextClass.fill_identity supplied)
  | context supplied => exact congrArg context (ContextClass.comp_identity supplied)

theorem assoc {first second third fourth : RawObject signature Parallel}
    (before : RawArrow first second) (middle : RawArrow second third) (after : RawArrow third fourth) :
    comp (comp before middle) after = comp before (comp middle after) := by
  cases before with
  | identity => rfl
  | value supplied =>
    cases middle with
    | context inner =>
      cases after with
      | context outer => exact congrArg value (ContextClass.fill_comp inner outer supplied).symm
  | context first =>
    cases middle with
    | context second =>
      cases after with
      | context third => exact congrArg context (ContextClass.comp_assoc first second third)

end RawArrow

instance rawCategory : Category.{max u v} (RawObject signature Parallel) where
  Hom := RawArrow
  id := RawArrow.id
  comp := RawArrow.comp
  id_comp := RawArrow.id_comp
  comp_id := RawArrow.comp_id
  assoc := RawArrow.assoc

def normalizeObject : RawObject signature Parallel → MixedObject signature Parallel
  | .origin => .origin
  | .interface sort => .interface ⟨sort⟩

def normalizeArrow {source target : RawObject signature Parallel} (arrow : source ⟶ target) :
    normalizeObject source ⟶ normalizeObject target :=
  match arrow with
  | .identity => .identity
  | .value supplied => .value supplied
  | .context supplied => .context (normalizeContext supplied)

def normalizeFunctor : RawObject signature Parallel ⥤ MixedObject signature Parallel where
  obj := normalizeObject
  map := normalizeArrow
  map_id object := by cases object <;> rfl
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | @context source target suppliedContext =>
        exact congrArg (Mettapedia.CategoryTheory.MixedResidue.Arrow.value
            (action := mixedAction signature Parallel) (target := ⟨target⟩))
          (ContextClass.normalize_filling suppliedContext supplied).symm
    | context inner =>
      cases second with
      | context outer =>
        exact congrArg Mettapedia.CategoryTheory.MixedResidue.Arrow.context (ContextClass.normalize_comp inner outer)

instance normalizeFunctor_faithful : (normalizeFunctor (signature := signature) (Parallel := Parallel)).Faithful where
  map_injective := by
    intro source target first second same
    cases first with
    | identity => cases second; rfl
    | value supplied =>
      cases second with
      | value other =>
        exact congrArg RawArrow.value (Mettapedia.CategoryTheory.MixedResidue.Arrow.value.inj same)
    | context supplied =>
      cases second with
      | context other =>
        exact congrArg RawArrow.context ((contextEquiv _ _).injective
          (Mettapedia.CategoryTheory.MixedResidue.Arrow.context.inj same))

instance normalizeFunctor_full : (normalizeFunctor (signature := signature) (Parallel := Parallel)).Full where
  map_surjective := by
    intro source target arrow
    cases source with
    | origin =>
      cases target with
      | origin => cases arrow; exact ⟨.identity, rfl⟩
      | interface sort => cases arrow with
        | value supplied => exact ⟨.value supplied, rfl⟩
    | interface source =>
      cases target with
      | origin => cases arrow
      | interface target => cases arrow with
        | context supplied =>
          exact ⟨.context ((contextEquiv source target).symm supplied),
            congrArg Mettapedia.CategoryTheory.MixedResidue.Arrow.context
              ((contextEquiv source target).apply_symm_apply supplied)⟩

theorem normalizeObject_surjective : Function.Surjective (normalizeObject (signature := signature) (Parallel := Parallel)) := by
  intro object
  cases object with
  | origin => exact ⟨.origin, rfl⟩
  | interface vertex => exact ⟨.interface vertex.sort, rfl⟩

end Mettapedia.OSLF.SortedCommutative
