import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.Algebra.Group.Action.Basic

/-!
# A monoid of contexts acting on closed values

The closed-term origin is distinct from the term interface. Its only
endomorphism is identity, no context returns to the origin, and the actual
context monoid acts on closed values. A map of these local actions earns a
functor; independent bijections on contexts and values earn full faithfulness.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundMonoidAction

open _root_.CategoryTheory

universe u v u' v'

inductive Object (M : Type u) (V : Type v) where
  | origin
  | interface

inductive Arrow (M : Type u) (V : Type v) : Object M V → Object M V → Type (max u v) where
  | identity : Arrow M V .origin .origin
  | value (supplied : V) : Arrow M V .origin .interface
  | context (supplied : M) : Arrow M V .interface .interface

variable {M : Type u} {V : Type v} [Monoid M] [MulAction M V]

namespace Arrow

def id : (object : Object M V) → Arrow M V object object
  | .origin => .identity
  | .interface => .context 1

def comp : {source middle target : Object M V} → Arrow M V source middle →
    Arrow M V middle target → Arrow M V source target
  | _, _, _, .identity, second => second
  | _, _, _, .value supplied, .context suppliedContext => .value (suppliedContext • supplied)
  | _, _, _, .context first, .context second => .context (second * first)

theorem id_comp {source target : Object M V} (arrow : Arrow M V source target) :
    comp (id source) arrow = arrow := by
  cases arrow with
  | identity => rfl
  | value => rfl
  | context supplied => exact congrArg context (mul_one supplied)

theorem comp_id {source target : Object M V} (arrow : Arrow M V source target) :
    comp arrow (id target) = arrow := by
  cases arrow with
  | identity => rfl
  | value supplied => exact congrArg value (one_smul M supplied)
  | context supplied => exact congrArg context (one_mul supplied)

theorem assoc {first second third fourth : Object M V}
    (f : Arrow M V first second) (g : Arrow M V second third)
    (h : Arrow M V third fourth) : comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | identity => rfl
  | value supplied =>
    cases g with
    | context inner =>
      cases h with
      | context outer => exact congrArg value (mul_smul outer inner supplied).symm
  | context first =>
    cases g with
    | context second =>
      cases h with
      | context third => exact congrArg context (mul_assoc third second first).symm

end Arrow

instance category : Category.{max u v} (Object M V) where
  Hom := Arrow M V
  id := Arrow.id
  comp := Arrow.comp
  id_comp := Arrow.id_comp
  comp_id := Arrow.comp_id
  assoc := Arrow.assoc

def valueArrow (value : V) : (.origin : Object M V) ⟶ .interface := .value value

def contextArrow (context : M) : (.interface : Object M V) ⟶ .interface := .context context

@[simp] theorem context_comp (first second : M) :
    contextArrow (V := V) first ≫ contextArrow second = contextArrow (second * first) := rfl

@[simp] theorem value_comp (value : V) (context : M) :
    valueArrow (M := M) value ≫ contextArrow context = valueArrow (context • value) := rfl

theorem no_interface_origin (arrow : (.interface : Object M V) ⟶ .origin) : False := by
  cases arrow

variable {N : Type u'} {W : Type v'} [Monoid N] [MulAction N W]

def map (contexts : M →* N) (values : V → W)
    (action : ∀ context value, values (context • value) = contexts context • values value) :
    Object M V ⥤ Object N W where
  obj
    | .origin => .origin
    | .interface => .interface
  map
    | .identity => .identity
    | .value supplied => .value (values supplied)
    | .context supplied => .context (contexts supplied)
  map_id object := by
    cases object with
    | origin => rfl
    | interface => exact congrArg Arrow.context contexts.map_one
  map_comp first second := by
    cases first with
    | identity => rfl
    | value supplied =>
      cases second with
      | context context => exact congrArg Arrow.value (action context supplied)
    | context first =>
      cases second with
      | context second => exact congrArg Arrow.context (contexts.map_mul second first)

theorem map_objects_surjective (contexts : M →* N) (values : V → W)
    (action : ∀ context value, values (context • value) = contexts context • values value) :
    Function.Surjective (map contexts values action).obj := by
  intro object
  cases object
  · exact ⟨.origin, rfl⟩
  · exact ⟨.interface, rfl⟩

theorem map_faithful (contexts : M →* N) (values : V → W)
    (action : ∀ context value, values (context • value) = contexts context • values value)
    (contextInjective : Function.Injective contexts) (valueInjective : Function.Injective values) :
    (map contexts values action).Faithful where
  map_injective := by
    intro source target first second same
    cases first with
    | identity => cases second; rfl
    | value first =>
      cases second with
      | value second => exact congrArg Arrow.value (valueInjective (Arrow.value.inj same))
    | context first =>
      cases second with
      | context second => exact congrArg Arrow.context (contextInjective (Arrow.context.inj same))

theorem map_full (contexts : M →* N) (values : V → W)
    (action : ∀ context value, values (context • value) = contexts context • values value)
    (contextSurjective : Function.Surjective contexts) (valueSurjective : Function.Surjective values) :
    (map contexts values action).Full where
  map_surjective := by
    intro source target arrow
    cases source <;> cases target
    · cases arrow; exact ⟨.identity, rfl⟩
    · cases arrow with
      | value supplied =>
        obtain ⟨value, rfl⟩ := valueSurjective supplied
        exact ⟨.value value, rfl⟩
    · cases arrow
    · cases arrow with
      | context supplied =>
        obtain ⟨context, rfl⟩ := contextSurjective supplied
        exact ⟨.context context, rfl⟩

end Mettapedia.CategoryTheory.GroundMonoidAction
