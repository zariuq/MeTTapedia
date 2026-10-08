import Mettapedia.OSLF.Syntax.CommutativeCutEquations
import Mettapedia.CategoryTheory.GroundMonoidActionCategory

/-!
# Actual linear-context equations for the commutative Cut presentation

Contexts are independently authored trees with exactly one hole. Local AC1
equations generate their relation. They coincide with the original term
equations after marking that hole by a fresh variable. Complete context
inventories classify this quotient, and actual composition and filling descend
to give the context monoid and its action on the independent closed-term quotient.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CommutativeCut

universe u

inductive Context (Payload : Type u) where
  | hole
  | left (inner : Context Payload) (sibling : Term Payload)
  | right (sibling : Term Payload) (inner : Context Payload)

variable {Payload : Type u}

def Context.fill : Context Payload → Term Payload → Term Payload
  | .hole, term => term
  | .left inner sibling, term => .cut (inner.fill term) sibling
  | .right sibling inner, term => .cut sibling (inner.fill term)

def Context.compose : Context Payload → Context Payload → Context Payload
  | .hole, inner => inner
  | .left outer sibling, inner => .left (outer.compose inner) sibling
  | .right sibling outer, inner => .right sibling (outer.compose inner)

def contextInventory : Context Payload → Multiset Payload
  | .hole => 0
  | .left inner sibling => contextInventory inner + inventory sibling
  | .right sibling inner => inventory sibling + contextInventory inner

def Context.erase (context : Context Payload) : Term Payload := context.fill .zero

def Context.encode : Context Payload → Term (Option Payload)
  | .hole => .atom none
  | .left inner sibling => .cut inner.encode (sibling.map some)
  | .right sibling inner => .cut (sibling.map some) inner.encode

inductive ContextEquation : Context Payload → Context Payload → Prop where
  | refl (context) : ContextEquation context context
  | symm {first second} : ContextEquation first second → ContextEquation second first
  | trans {first second third} : ContextEquation first second → ContextEquation second third →
      ContextEquation first third
  | left {first first' sibling sibling'} : ContextEquation first first' → Equation sibling sibling' →
      ContextEquation (.left first sibling) (.left first' sibling')
  | right {sibling sibling' first first'} : Equation sibling sibling' → ContextEquation first first' →
      ContextEquation (.right sibling first) (.right sibling' first')
  | comm (context sibling) : ContextEquation (.left context sibling) (.right sibling context)
  | assocLeft (context first second) :
      ContextEquation (.left (.left context first) second) (.left context (.cut first second))
  | assocRight (first second context) :
      ContextEquation (.right first (.right second context)) (.right (.cut first second) context)
  | unit (context) : ContextEquation (.left context .zero) context

theorem ContextEquation.inventory {first second : Context Payload}
    (equation : ContextEquation first second) : contextInventory first = contextInventory second := by
  induction equation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | left _ second first => exact congrArg₂ (· + ·) first second.inventory
  | right first _ second => exact congrArg₂ (· + ·) first.inventory second
  | comm context sibling => exact add_comm _ _
  | assocLeft context first second => exact add_assoc _ _ _
  | assocRight first second context => exact (add_assoc _ _ _).symm
  | unit context => exact add_zero _

theorem fill_inventory (context : Context Payload) (term : Term Payload) :
    inventory (context.fill term) = inventory term + contextInventory context := by
  induction context with
  | hole => exact (add_zero _).symm
  | left inner sibling inductionHypothesis =>
    simp only [Context.fill, inventory, contextInventory, inductionHypothesis, add_assoc]
  | right sibling inner inductionHypothesis =>
    simp only [Context.fill, inventory, contextInventory, inductionHypothesis]
    ac_rfl

theorem erase_inventory (context : Context Payload) :
    inventory context.erase = contextInventory context := by
  rw [Context.erase, fill_inventory]
  exact zero_add _

theorem context_normal (context : Context Payload) :
    ContextEquation context (.right context.erase .hole) := by
  induction context with
  | hole => exact ((ContextEquation.comm .hole .zero).symm.trans (ContextEquation.unit .hole)).symm
  | left inner sibling inductionHypothesis =>
    refine (ContextEquation.left inductionHypothesis (Equation.refl sibling)).trans ?_
    refine (ContextEquation.comm (.right inner.erase .hole) sibling).trans ?_
    refine (ContextEquation.assocRight sibling inner.erase .hole).trans ?_
    exact ContextEquation.right (Equation.comm sibling inner.erase) (ContextEquation.refl .hole)
  | right sibling inner inductionHypothesis =>
    exact (ContextEquation.right (Equation.refl sibling) inductionHypothesis).trans
      (ContextEquation.assocRight sibling inner.erase .hole)

theorem contextEquation_iff_inventory (first second : Context Payload) :
    ContextEquation first second ↔ contextInventory first = contextInventory second := by
  refine ⟨ContextEquation.inventory, fun same => ?_⟩
  have erased : Equation first.erase second.erase :=
    (equation_iff_inventory _ _).mpr ((erase_inventory first).trans (same.trans (erase_inventory second).symm))
  exact (context_normal first).trans
    ((ContextEquation.right erased (ContextEquation.refl .hole)).trans (context_normal second).symm)

theorem encode_inventory (context : Context Payload) :
    inventory context.encode = {none} + (contextInventory context).map some := by
  induction context with
  | hole => exact (add_zero _).symm
  | left inner sibling inductionHypothesis =>
    simp only [Context.encode, inventory, inventory_map, inductionHypothesis, contextInventory, Multiset.map_add]
    ac_rfl
  | right sibling inner inductionHypothesis =>
    simp only [Context.encode, inventory, inventory_map, inductionHypothesis, contextInventory, Multiset.map_add]
    ac_rfl

/-- The context equations are exactly the original AC1 term equations at a
fresh, single-use hole; equality at one ground filling is insufficient. -/
theorem contextEquation_iff_openEquation (first second : Context Payload) :
    ContextEquation first second ↔ Equation first.encode second.encode := by
  rw [contextEquation_iff_inventory, equation_iff_inventory, encode_inventory, encode_inventory]
  constructor
  · intro same
    rw [same]
  · intro same
    exact Multiset.map_injective (fun _ _ equality => Option.some.inj equality) (add_left_cancel same)

theorem context_compose_inventory (outer inner : Context Payload) :
    contextInventory (outer.compose inner) = contextInventory outer + contextInventory inner := by
  induction outer with
  | hole => exact (zero_add _).symm
  | left outer sibling inductionHypothesis =>
    simp only [Context.compose, contextInventory, inductionHypothesis]
    ac_rfl
  | right sibling outer inductionHypothesis =>
    simp only [Context.compose, contextInventory, inductionHypothesis, add_assoc]

theorem ContextEquation.compose {outer outer' inner inner' : Context Payload}
    (first : ContextEquation outer outer') (second : ContextEquation inner inner') :
    ContextEquation (outer.compose inner) (outer'.compose inner') := by
  apply (contextEquation_iff_inventory _ _).mpr
  rw [context_compose_inventory, context_compose_inventory, first.inventory, second.inventory]

theorem ContextEquation.fill {first second : Context Payload} {value value' : Term Payload}
    (contextEquation : ContextEquation first second) (valueEquation : Equation value value') :
    Equation (first.fill value) (second.fill value') := by
  apply (equation_iff_inventory _ _).mpr
  rw [fill_inventory, fill_inventory, contextEquation.inventory, valueEquation.inventory]

def contextSetoid (Payload : Type u) : Setoid (Context Payload) where
  r := ContextEquation
  iseqv := ⟨ContextEquation.refl, ContextEquation.symm, ContextEquation.trans⟩

abbrev ContextClass (Payload : Type u) := Quotient (contextSetoid Payload)

def contextClassOf (context : Context Payload) : ContextClass Payload := Quotient.mk _ context

def contextInventoryQ : ContextClass Payload → Multiset Payload :=
  Quotient.lift contextInventory (fun _ _ equation => equation.inventory)

def contextFromTerm : Class Payload → ContextClass Payload :=
  Quotient.lift (fun term => contextClassOf (.right term .hole))
    (fun _ _ equation => Quotient.sound (ContextEquation.right equation (ContextEquation.refl .hole)))

theorem contextInventoryQ_fromTerm (value : Class Payload) :
    contextInventoryQ (contextFromTerm value) = inventoryQ value := by
  refine Quotient.inductionOn value ?_
  intro term
  exact add_zero _

def contextInventoryEquiv : ContextClass Payload ≃ Multiset Payload where
  toFun := contextInventoryQ
  invFun supplied := contextFromTerm (fromInventory supplied)
  left_inv context := by
    refine Quotient.inductionOn context ?_
    intro context
    have erased := erase_inventory context
    have same : contextFromTerm (fromInventory (contextInventory context)) =
        contextClassOf (.right context.erase .hole) := by
      rw [← erased, fromInventory_inventory]
      rfl
    exact same.trans (Quotient.sound (context_normal context)).symm
  right_inv supplied := by rw [contextInventoryQ_fromTerm, inventoryQ_fromInventory]

instance contextOne : One (ContextClass Payload) := ⟨contextClassOf .hole⟩

instance contextMul : Mul (ContextClass Payload) :=
  ⟨Quotient.map₂ Context.compose (fun _ _ first _ _ second => first.compose second)⟩

theorem compose_hole (context : Context Payload) : context.compose .hole = context := by
  induction context with
  | hole => rfl
  | left inner sibling inductionHypothesis => exact congrArg (fun inner => Context.left inner sibling) inductionHypothesis
  | right sibling inner inductionHypothesis => exact congrArg (Context.right sibling) inductionHypothesis

theorem compose_assoc (first second third : Context Payload) :
    (first.compose second).compose third = first.compose (second.compose third) := by
  induction first with
  | hole => rfl
  | left inner sibling inductionHypothesis => exact congrArg (fun inner => Context.left inner sibling) inductionHypothesis
  | right sibling inner inductionHypothesis => exact congrArg (Context.right sibling) inductionHypothesis

instance contextMonoid : Monoid (ContextClass Payload) where
  one_mul context := Quotient.inductionOn context (fun _ => rfl)
  mul_one context := Quotient.inductionOn context (fun context => congrArg contextClassOf (compose_hole context))
  mul_assoc first second third := Quotient.inductionOn₃ first second third
    (fun first second third => congrArg contextClassOf (compose_assoc first second third))
  npow := npowRec

theorem fill_compose (outer inner : Context Payload) (value : Term Payload) :
    (outer.compose inner).fill value = outer.fill (inner.fill value) := by
  induction outer with
  | hole => rfl
  | left outer sibling inductionHypothesis => exact congrArg (fun term => Term.cut term sibling) inductionHypothesis
  | right sibling outer inductionHypothesis => exact congrArg (Term.cut sibling) inductionHypothesis

instance contextAction : MulAction (ContextClass Payload) (Class Payload) where
  smul := Quotient.map₂ Context.fill (fun _ _ first _ _ second => first.fill second)
  one_smul value := Quotient.inductionOn value (fun _ => rfl)
  mul_smul outer inner value := Quotient.inductionOn₃ outer inner value
    (fun outer inner value => congrArg classOf (fill_compose outer inner value))

@[simp] theorem contextInventoryQ_one : contextInventoryQ (1 : ContextClass Payload) = 0 := rfl

@[simp] theorem contextInventoryQ_mul (outer inner : ContextClass Payload) :
    contextInventoryQ (outer * inner) = contextInventoryQ outer + contextInventoryQ inner :=
  Quotient.inductionOn₂ outer inner context_compose_inventory

theorem action_inventory (context : ContextClass Payload) (value : Class Payload) :
    inventoryQ (context • value) = inventoryQ value + contextInventoryQ context :=
  Quotient.inductionOn₂ context value fill_inventory

abbrev Category (Payload : Type u) :=
  Mettapedia.CategoryTheory.GroundMonoidAction.Object (ContextClass Payload) (Class Payload)

end Mettapedia.OSLF.CommutativeCut
