import Mettapedia.CategoryTheory.MixedResidueContexts

/-!
# Actual closed-value categories for mixed residue contexts

Local parallel addition and genuine typed frame actions independently determine
the complete context action. Their local composition laws earn the category
with closed values at the distinguished origin. Local cancellation, when
available, earns injectivity of every complete context action.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.MixedResidue

open _root_.CategoryTheory

universe u v w z

variable {Vertex : Type u} [Quiver.{v} Vertex] (Payload : Vertex → Type w)

structure Action where
  Value : Vertex → Type z
  residue : {sort : Vertex} → Multiset (Payload sort) → Value sort → Value sort
  residue_zero : {sort : Vertex} → (value : Value sort) → residue 0 value = value
  residue_add : {sort : Vertex} → (first second : Multiset (Payload sort)) →
    (value : Value sort) → residue (first + second) value = residue first (residue second value)
  frame : {source target : Vertex} → (source ⟶ target) → Value source → Value target

namespace Action

variable {Payload} (action : Action.{u,v,w,z} Payload)

def read (action : Action.{u,v,w,z} Payload) {source target : Vertex} :
    Context Payload source target → action.Value source → action.Value target
  | .parallel residue => action.residue residue
  | .frame residue edge inner => fun value =>
      action.residue residue (action.frame edge (action.read inner value))

theorem read_addOuter {source target : Vertex}
    (residue : Multiset (Payload target)) (context : Context Payload source target)
    (value : action.Value source) :
    action.read (context.addOuter residue) value = action.residue residue (action.read context value) := by
  cases context with
  | parallel previous => exact action.residue_add residue previous value
  | frame previous edge inner =>
    exact action.residue_add residue previous (action.frame edge (action.read inner value))

theorem read_comp {source middle target : Vertex}
    (inner : Context Payload source middle) (outer : Context Payload middle target)
    (value : action.Value source) :
    action.read (inner.comp outer) value = action.read outer (action.read inner value) := by
  induction outer with
  | parallel residue => exact action.read_addOuter residue inner value
  | frame residue edge outer inductionHypothesis =>
    exact congrArg (fun supplied => action.residue residue (action.frame edge supplied)) inductionHypothesis

theorem read_identity {sort : Vertex} (value : action.Value sort) :
    action.read (.parallel 0) value = value := action.residue_zero value

/-- Only local cancellation is required; no whole-context cancellation is a field. -/
structure Cancellative : Prop where
  residue_injective : {sort : Vertex} → (residue : Multiset (Payload sort)) →
    Function.Injective (action.residue residue)
  frame_injective : {source target : Vertex} → (edge : source ⟶ target) →
    Function.Injective (action.frame edge)

theorem read_injective (qualified : action.Cancellative) {source target : Vertex}
    (context : Context Payload source target) : Function.Injective (action.read context) := by
  induction context with
  | parallel residue => exact qualified.residue_injective residue
  | frame residue edge inner inductionHypothesis =>
    exact (qualified.residue_injective residue).comp
      ((qualified.frame_injective edge).comp inductionHypothesis)

end Action

variable {Payload}

inductive Object (action : Action.{u,v,w,z} Payload) where
  | origin
  | interface (vertex : Vertex)

inductive Arrow (action : Action.{u,v,w,z} Payload) :
    Object action → Object action → Type (max u v w z) where
  | identity : Arrow action .origin .origin
  | value {target : Vertex} (supplied : action.Value target) : Arrow action .origin (.interface target)
  | context {source target : Vertex} (supplied : Context Payload source target) :
      Arrow action (.interface source) (.interface target)

namespace Arrow

variable {action : Action.{u,v,w,z} Payload}

def id : (object : Object action) → Arrow action object object
  | .origin => .identity
  | .interface _ => .context (.parallel 0)

def comp : {source middle target : Object action} → Arrow action source middle →
    Arrow action middle target → Arrow action source target
  | _, _, _, .identity, second => second
  | _, _, _, .value supplied, .context suppliedContext => .value (action.read suppliedContext supplied)
  | _, _, _, .context first, .context second => .context (first.comp second)

theorem id_comp {source target : Object action} (arrow : Arrow action source target) :
    comp (id source) arrow = arrow := by
  cases arrow with
  | identity => rfl
  | value => rfl
  | context supplied => exact congrArg context (Context.identity_comp supplied)

theorem comp_id {source target : Object action} (arrow : Arrow action source target) :
    comp arrow (id target) = arrow := by
  cases arrow with
  | identity => rfl
  | value supplied => exact congrArg value (action.read_identity supplied)
  | context supplied => exact congrArg context (Context.comp_identity supplied)

theorem comp_assoc {first second third fourth : Object action}
    (f : Arrow action first second) (g : Arrow action second third)
    (h : Arrow action third fourth) : comp (comp f g) h = comp f (comp g h) := by
  cases f with
  | identity => rfl
  | value supplied =>
    cases g with
    | context first =>
      cases h with
      | context second => exact congrArg value (action.read_comp first second supplied).symm
  | context first =>
    cases g with
    | context second =>
      cases h with
      | context third => exact congrArg context (Context.comp_assoc first second third)

end Arrow

instance category (action : Action.{u,v,w,z} Payload) : Category.{max u v w z} (Object action) where
  Hom := Arrow action
  id := Arrow.id
  comp := Arrow.comp
  id_comp := Arrow.id_comp
  comp_id := Arrow.comp_id
  assoc := Arrow.comp_assoc

variable (action : Action.{u,v,w,z} Payload)

def contextArrow {source target : Vertex} (supplied : Context Payload source target) :
    (.interface source : Object action) ⟶ .interface target := .context supplied

def valueArrow {target : Vertex} (supplied : action.Value target) :
    (.origin : Object action) ⟶ .interface target := .value supplied

@[simp] theorem context_comp {source middle target : Vertex}
    (first : Context Payload source middle) (second : Context Payload middle target) :
    contextArrow action first ≫ contextArrow action second = contextArrow action (first.comp second) := rfl

@[simp] theorem value_comp {source target : Vertex} (supplied : action.Value source)
    (context : Context Payload source target) :
    valueArrow action supplied ≫ contextArrow action context = valueArrow action (action.read context supplied) := rfl

theorem no_interface_origin {source : Vertex}
    (arrow : Arrow action (.interface source) .origin) : False := by cases arrow

end Mettapedia.CategoryTheory.MixedResidue
