import Mathlib.CategoryTheory.PathCategory.Basic

/-!
# Closed values and paths of linear context frames

An independently supplied frame acts on a closed value. Iterating those local
actions earns a path action and an actual category: the distinguished origin
has closed values as arrows, while arrows between interfaces are frame paths.
The action may identify different values or paths; no faithfulness assumption
is part of this construction.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.GroundPath

open _root_.CategoryTheory

universe u v w

variable {V : Type u} [Quiver.{v} V]

/-- The local data of a closed-value action, one actual frame at a time. -/
structure Action (V : Type u) [Quiver.{v} V] where
  Value : V → Type w
  frame : {source target : V} → (source ⟶ target) → Value source → Value target

namespace Action

variable (action : Action.{u,v,w} V)

def path (action : Action.{u,v,w} V) {source target : V}
    (suppliedPath : Quiver.Path source target) : action.Value source → action.Value target :=
  @Quiver.Path.rec V _ source
    (fun target _ => action.Value source → action.Value target)
    (fun value => value)
    (fun _ suppliedFrame inductionHypothesis value => action.frame suppliedFrame (inductionHypothesis value))
    target suppliedPath

@[simp]
theorem path_nil {source : V} (value : action.Value source) :
    action.path (Quiver.Path.nil : Quiver.Path source source) value = value := rfl

@[simp]
theorem path_cons {source middle target : V} (previous : Quiver.Path source middle)
    (frame : middle ⟶ target) (value : action.Value source) :
    action.path (previous.cons frame) value = action.frame frame (action.path previous value) := rfl

theorem path_comp {source middle target : V} (first : Quiver.Path source middle)
    (second : Quiver.Path middle target) (value : action.Value source) :
    action.path (first.comp second) value = action.path second (action.path first value) := by
  induction second with
  | nil => rfl
  | cons previous frame inductionHypothesis =>
    exact congrArg (action.frame frame) inductionHypothesis

end Action

/-- The origin of a closed term and the actual sorted interfaces are distinct. -/
inductive Object (action : Action.{u,v,w} V) where
  | origin
  | interface (vertex : V)

inductive Arrow (action : Action.{u,v,w} V) : Object action → Object action → Type (max u v w) where
  | identity : Arrow action .origin .origin
  | value {target : V} (supplied : action.Value target) : Arrow action .origin (.interface target)
  | context {source target : V} (supplied : Quiver.Path source target) :
      Arrow action (.interface source) (.interface target)

namespace Arrow

variable {action : Action.{u,v,w} V}

def id : (object : Object action) → Arrow action object object
  | .origin => .identity
  | .interface _ => .context .nil

def comp : {source middle target : Object action} → Arrow action source middle →
    Arrow action middle target → Arrow action source target
  | _, _, _, .identity, second => second
  | _, _, _, .value supplied, .context suppliedPath => .value (action.path suppliedPath supplied)
  | _, _, _, .context first, .context second => .context (first.comp second)

theorem id_comp {source target : Object action} (arrow : Arrow action source target) :
    comp (id source) arrow = arrow := by
  cases arrow with
  | identity => rfl
  | value => rfl
  | context supplied => exact congrArg context (Quiver.Path.nil_comp supplied)

theorem comp_id {source target : Object action} (arrow : Arrow action source target) :
    comp arrow (id target) = arrow := by
  cases arrow with
  | identity => rfl
  | value => rfl
  | context supplied => rfl

theorem comp_assoc {first second third fourth : Object action}
    (f : Arrow action first second) (g : Arrow action second third)
    (h : Arrow action third fourth) : comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | identity => rfl
  | value supplied =>
    cases g with
    | context first =>
      cases h with
      | context second => exact congrArg value (action.path_comp first second supplied).symm
  | context first =>
    cases g with
    | context second =>
      cases h with
      | context third => exact congrArg context (Quiver.Path.comp_assoc first second third)

end Arrow

instance category (action : Action.{u,v,w} V) : Category.{max u v w} (Object action) where
  Hom := Arrow action
  id := Arrow.id
  comp := Arrow.comp
  id_comp := Arrow.id_comp
  comp_id := Arrow.comp_id
  assoc := Arrow.comp_assoc

variable (action : Action.{u,v,w} V)

def contextArrow {source target : V} (supplied : Quiver.Path source target) :
    (.interface source : Object action) ⟶ .interface target := .context supplied

def valueArrow {target : V} (supplied : action.Value target) :
    (.origin : Object action) ⟶ .interface target := .value supplied

@[simp]
theorem context_comp {source middle target : V}
    (first : Quiver.Path source middle) (second : Quiver.Path middle target) :
    contextArrow action first ≫ contextArrow action second = contextArrow action (first.comp second) := rfl

@[simp]
theorem value_comp {source target : V} (supplied : action.Value source)
    (context : Quiver.Path source target) :
    valueArrow action supplied ≫ contextArrow action context = valueArrow action (action.path context supplied) := rfl

theorem no_interface_origin {source : V}
    (arrow : Arrow action (.interface source) .origin) : False := by cases arrow

end Mettapedia.CategoryTheory.GroundPath
