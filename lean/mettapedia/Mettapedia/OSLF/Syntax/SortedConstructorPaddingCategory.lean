import Mettapedia.OSLF.Syntax.SortedConstructorPaddingContexts

/-!
# The actual term-and-context quotient for unary padding equations

The origin, argument sorts and probe sorts remain separate objects. Arrows out
of the origin are authored term classes; arrows between interfaces are authored
context classes. Composition descends actual filling and path concatenation.
The independently earned normalization bijections give a based equivalence
with the original sorted constructor/context category.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.SortedConstructors.Padding

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.GroundPath

universe u v

variable (signature : Signature.{u,v}) (paddingSort : signature.Srt)

inductive EquationObject (paddingSort : signature.Srt) where
  | origin
  | interface (sort : signature.Srt)

inductive EquationArrow : EquationObject signature paddingSort → EquationObject signature paddingSort → Type (max u v) where
  | identity : EquationArrow .origin .origin
  | value {sort : signature.Srt} (supplied : Class signature paddingSort sort) :
      EquationArrow .origin (.interface sort)
  | context {source target : signature.Srt}
      (supplied : ContextClass signature paddingSort source target) :
      EquationArrow (.interface source) (.interface target)

variable {signature paddingSort}

theorem fill_respects_equations {source target : signature.Srt}
    {first second : RawTerm signature paddingSort source}
    {left right : Context (extended signature paddingSort) source target}
    (terms : Equation signature paddingSort first second)
    (contexts : ContextEquation signature paddingSort left right) :
    Equation signature paddingSort
      ((action (extended signature paddingSort)).path left first)
      ((action (extended signature paddingSort)).path right second) := by
  apply (equation_iff_normalizes _ _).mpr
  exact (normalize_fillContext signature paddingSort left first).trans
    ((congrArg₂ (fun path term => (action signature).path path term)
      (contextEquation_normalizes contexts) (equation_normalizes terms)).trans
      (normalize_fillContext signature paddingSort right second).symm)

def classFill {source target : signature.Srt}
    (term : Class signature paddingSort source)
    (context : ContextClass signature paddingSort source target) : Class signature paddingSort target :=
  Quotient.liftOn₂ term context
    (fun supplied path => classOf ((action (extended signature paddingSort)).path path supplied))
    (fun _ _ _ _ terms contexts => Quotient.sound (fill_respects_equations terms contexts))

def classCompose {source middle target : signature.Srt}
    (first : ContextClass signature paddingSort source middle)
    (second : ContextClass signature paddingSort middle target) :
    ContextClass signature paddingSort source target :=
  Quotient.liftOn₂ first second (fun left right => contextClassOf (left.comp right))
    (fun _ _ _ _ left right => Quotient.sound (ContextEquation.comp left right))

namespace EquationArrow

def id : (object : EquationObject signature paddingSort) → EquationArrow signature paddingSort object object
  | .origin => .identity
  | .interface _ => .context (contextClassOf .nil)

def comp : {first middle target : EquationObject signature paddingSort} →
    EquationArrow signature paddingSort first middle →
    EquationArrow signature paddingSort middle target → EquationArrow signature paddingSort first target
  | _, _, _, .identity, second => second
  | _, _, _, .value supplied, .context path => .value (classFill supplied path)
  | _, _, _, .context left, .context right => .context (classCompose left right)

def normalObject (object : EquationObject signature paddingSort) : ContextObject signature :=
  match object with
  | .origin => .origin
  | .interface sort => .interface sort

def down {source target : EquationObject signature paddingSort}
    (arrow : EquationArrow signature paddingSort source target) :
    normalObject source ⟶ normalObject target :=
  match arrow with
  | .identity => .identity
  | .value supplied => .value (Padding.value signature paddingSort supplied)
  | .context supplied => .context (contextValue signature paddingSort supplied)

def up {source target : EquationObject signature paddingSort}
    (arrow : normalObject source ⟶ normalObject target) :
    EquationArrow signature paddingSort source target := by
  cases source <;> cases target
  · cases arrow
    exact .identity
  · cases arrow with
    | value supplied => exact .value (classOf (embed signature paddingSort supplied))
  · cases arrow
  · cases arrow with
    | context supplied => exact .context (contextClassOf (embedContext signature paddingSort supplied))

theorem up_down {source target : EquationObject signature paddingSort}
    (arrow : EquationArrow signature paddingSort source target) : up (down arrow) = arrow := by
  cases arrow with
  | identity => rfl
  | value supplied => exact congrArg EquationArrow.value ((termEquiv signature paddingSort _).left_inv supplied)
  | context supplied =>
    exact congrArg EquationArrow.context ((contextEquiv signature paddingSort _ _).left_inv supplied)

theorem down_up {source target : EquationObject signature paddingSort}
    (arrow : normalObject source ⟶ normalObject target) : down (up arrow) = arrow := by
  cases source <;> cases target
  · cases arrow; rfl
  · cases arrow with
    | value supplied => exact congrArg Arrow.value (normalize_embed signature paddingSort supplied)
  · cases arrow
  · cases arrow with
    | context supplied => exact congrArg Arrow.context (normalize_embedContext signature paddingSort supplied)

theorem down_injective {source target : EquationObject signature paddingSort} :
    Function.Injective (down (signature := signature) (paddingSort := paddingSort)
      (source := source) (target := target)) :=
  Function.LeftInverse.injective up_down

theorem down_id (object : EquationObject signature paddingSort) :
    down (id (paddingSort := paddingSort) object) = 𝟙 (normalObject object) := by
  cases object <;> rfl

theorem down_comp {source middle target : EquationObject signature paddingSort}
    (first : EquationArrow signature paddingSort source middle)
    (second : EquationArrow signature paddingSort middle target) :
    down (comp first second) = down first ≫ down second := by
  cases first with
  | identity => rfl
  | value supplied =>
    cases second with
    | context path =>
      induction supplied using Quotient.inductionOn with
      | _ term =>
        induction path using Quotient.inductionOn with
        | _ context => exact congrArg Arrow.value (normalize_fillContext signature paddingSort context term)
  | context left =>
    cases second with
    | context right =>
      induction left using Quotient.inductionOn with
      | _ first =>
        induction right using Quotient.inductionOn with
        | _ second => exact congrArg Arrow.context (normalizeContext_comp signature paddingSort first second)

theorem id_comp {source target : EquationObject signature paddingSort}
    (arrow : EquationArrow signature paddingSort source target) : comp (id source) arrow = arrow := by
  apply down_injective
  rw [down_comp, down_id, Category.id_comp]

theorem comp_id {source target : EquationObject signature paddingSort}
    (arrow : EquationArrow signature paddingSort source target) : comp arrow (id target) = arrow := by
  apply down_injective
  rw [down_comp, down_id, Category.comp_id]

theorem comp_assoc {first second third fourth : EquationObject signature paddingSort}
    (f : EquationArrow signature paddingSort first second)
    (g : EquationArrow signature paddingSort second third)
    (h : EquationArrow signature paddingSort third fourth) : comp (comp f g) h = comp f (comp g h) := by
  apply down_injective
  rw [down_comp, down_comp, down_comp, down_comp, Category.assoc]

end EquationArrow

instance equationCategory : Category.{max u v} (EquationObject signature paddingSort) where
  Hom := EquationArrow signature paddingSort
  id := EquationArrow.id
  comp := EquationArrow.comp
  id_comp := EquationArrow.id_comp
  comp_id := EquationArrow.comp_id
  assoc := EquationArrow.comp_assoc

def normalizationFunctor (signature : Signature.{u,v}) (paddingSort : signature.Srt) :
    @Functor (EquationObject signature paddingSort) (equationCategory (paddingSort := paddingSort))
      (ContextObject signature) inferInstance where
  obj := EquationArrow.normalObject
  map := EquationArrow.down
  map_id := EquationArrow.down_id
  map_comp := EquationArrow.down_comp

def rawObject (object : EquationObject signature paddingSort) : ContextObject (extended signature paddingSort) :=
  match object with
  | .origin => .origin
  | .interface sort => .interface sort

def quotientArrow {source target : EquationObject signature paddingSort}
    (arrow : rawObject (paddingSort := paddingSort) source ⟶ rawObject (paddingSort := paddingSort) target) :
    EquationArrow signature paddingSort source target := by
  cases source <;> cases target
  · cases arrow; exact .identity
  · cases arrow with
    | value supplied => exact .value (classOf supplied)
  · cases arrow
  · cases arrow with
    | context supplied => exact .context (contextClassOf supplied)

theorem quotientArrow_comp {source middle target : EquationObject signature paddingSort}
    (first : rawObject (paddingSort := paddingSort) source ⟶ rawObject (paddingSort := paddingSort) middle)
    (second : rawObject (paddingSort := paddingSort) middle ⟶ rawObject (paddingSort := paddingSort) target) :
    quotientArrow (first ≫ second) = EquationArrow.comp (quotientArrow first) (quotientArrow second) := by
  cases source <;> cases middle <;> cases target <;> cases first <;> cases second <;> rfl

/-- Term and context normalization recover every hom, with both actual
quotient roundtrips. In particular no original constructor is erased. -/
def normalizationHomEquiv (source target : EquationObject signature paddingSort) :
    EquationArrow signature paddingSort source target ≃
      (EquationArrow.normalObject source ⟶ EquationArrow.normalObject target) where
  toFun := EquationArrow.down
  invFun := EquationArrow.up
  left_inv := EquationArrow.up_down
  right_inv := EquationArrow.down_up

end Mettapedia.OSLF.SortedConstructors.Padding
