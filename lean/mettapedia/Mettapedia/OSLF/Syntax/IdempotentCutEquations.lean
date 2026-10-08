import Mettapedia.OSLF.Syntax.CommutativeCutContexts

/-!
# The independently extended idempotent Cut equations and their contexts

Adding idempotence changes the actual term and fresh-hole context quotients.
Local equations, rather than a Boolean definition of equality, generate the
relation. A separately computed presence model classifies the one-payload
closed quotient. Contexts remain exact linear trees, quotiented by the original
equations at a fresh hole; erasing that hole earns their normal-form comparison.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.CommutativeCut.Idempotent

universe u

variable {Payload : Type u}

inductive Equates : Term Payload → Term Payload → Prop where
  | base {first second} : Equation first second → Equates first second
  | symm {first second} : Equates first second → Equates second first
  | trans {first second third} : Equates first second → Equates second third → Equates first third
  | congr {first first' second second'} : Equates first first' → Equates second second' →
      Equates (.cut first second) (.cut first' second')
  | idem (term) : Equates (.cut term term) term

def setoid (Payload : Type u) : Setoid (Term Payload) where
  r := Equates
  iseqv := ⟨fun term => .base (.refl term), Equates.symm, Equates.trans⟩

abbrev Class (Payload : Type u) := Quotient (setoid Payload)

def classOf (term : Term Payload) : Class Payload := Quotient.mk _ term

instance classZero : Zero (Class Payload) := ⟨classOf .zero⟩
instance classAdd : Add (Class Payload) :=
  ⟨Quotient.map₂ Term.cut (fun _ _ first _ _ second => Equates.congr first second)⟩

instance classAddCommMonoid : AddCommMonoid (Class Payload) where
  add_assoc first second third := Quotient.inductionOn₃ first second third
    (fun first second third => Quotient.sound (Equates.base (Equation.assoc first second third)))
  zero_add value := Quotient.inductionOn value (fun term =>
    Quotient.sound (Equates.base ((Equation.comm .zero term).trans (Equation.unit term))))
  add_zero value := Quotient.inductionOn value (fun term => Quotient.sound (Equates.base (Equation.unit term)))
  add_comm first second := Quotient.inductionOn₂ first second
    (fun first second => Quotient.sound (Equates.base (Equation.comm first second)))
  nsmul := nsmulRec

theorem add_self (value : Class Payload) : value + value = value :=
  Quotient.inductionOn value (fun term => Quotient.sound (Equates.idem term))

def eval {Target : Type*} [AddCommMonoid Target] (values : Payload → Target) : Term Payload → Target
  | .zero => 0
  | .atom payload => values payload
  | .cut first second => eval values first + eval values second

theorem eval_base {Target : Type*} [AddCommMonoid Target] (values : Payload → Target)
    {first second : Term Payload} (equation : Equation first second) : eval values first = eval values second := by
  induction equation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | congr _ _ first second => exact congrArg₂ (· + ·) first second
  | assoc => exact add_assoc _ _ _
  | comm => exact add_comm _ _
  | unit => exact add_zero _

theorem Equates.eval {Target : Type*} [AddCommMonoid Target] (values : Payload → Target)
    (idempotent : ∀ value : Target, value + value = value)
    {first second : Term Payload} (equation : Equates first second) :
    Idempotent.eval values first = Idempotent.eval values second := by
  induction equation with
  | base equation => exact eval_base values equation
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | congr _ _ first second => exact congrArg₂ (· + ·) first second
  | idem term => exact idempotent _

theorem Equates.map {Target : Type*} (payload : Payload → Target)
    {first second : Term Payload} (equation : Equates first second) :
    Equates (first.map payload) (second.map payload) := by
  induction equation with
  | base equation =>
    apply Equates.base
    apply (equation_iff_inventory _ _).mpr
    rw [inventory_map, inventory_map, equation.inventory]
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | congr _ _ first second => exact Equates.congr first second
  | idem term => exact Equates.idem _

def presence : Term Payload → Bool
  | .zero => false
  | .atom _ => true
  | .cut first second => presence first || presence second

theorem presence_base {first second : Term Payload} (equation : Equation first second) :
    presence first = presence second := by
  induction equation with
  | refl => rfl
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | congr _ _ first second => exact congrArg₂ Bool.or first second
  | assoc => exact Bool.or_assoc _ _ _
  | comm => exact Bool.or_comm _ _
  | unit term => exact Bool.or_false _

theorem Equates.presence {first second : Term Payload} (equation : Equates first second) :
    presence first = presence second := by
  induction equation with
  | base equation => exact presence_base equation
  | symm _ inductionHypothesis => exact inductionHypothesis.symm
  | trans _ _ first second => exact first.trans second
  | congr _ _ first second => exact congrArg₂ Bool.or first second
  | idem term => exact Bool.or_self _

def presenceQ : Class Payload → Bool := Quotient.lift presence (fun _ _ equation => equation.presence)

@[simp] theorem presenceQ_zero : presenceQ (0 : Class Payload) = false := rfl
@[simp] theorem presenceQ_add (first second : Class Payload) :
    presenceQ (first + second) = (presenceQ first || presenceQ second) :=
  Quotient.inductionOn₂ first second (fun _ _ => rfl)

def represent : Bool → Term Unit
  | false => .zero
  | true => .atom ()

theorem represent_cut (first second : Bool) :
    Equates (.cut (represent first) (represent second)) (represent (first || second)) := by
  cases first <;> cases second
  · exact .base (.unit .zero)
  · exact .base ((Equation.comm .zero (.atom ())).trans (Equation.unit (.atom ())))
  · exact .base (.unit (.atom ()))
  · exact .idem (.atom ())

theorem normalize_presence (term : Term Unit) : Equates term (represent (presence term)) := by
  induction term with
  | zero => exact .base (.refl _)
  | atom payload => cases payload; exact .base (.refl _)
  | cut first second firstIH secondIH => exact (firstIH.congr secondIH).trans (represent_cut _ _)

def presenceEquiv : Class Unit ≃ Bool where
  toFun := presenceQ
  invFun present := classOf (represent present)
  left_inv value := Quotient.inductionOn value (fun term => Quotient.sound (normalize_presence term).symm)
  right_inv present := by cases present <;> rfl

def holeValues : Option Payload → Class Payload
  | none => 0
  | some payload => classOf (.atom payload)

theorem eval_map_some (term : Term Payload) : eval holeValues (term.map some) = classOf term := by
  induction term with
  | zero => rfl
  | atom => rfl
  | cut first second firstIH secondIH => exact congrArg₂ (· + ·) firstIH secondIH

theorem eval_encode (supplied : Context Payload) : eval holeValues supplied.encode = classOf supplied.erase := by
  induction supplied with
  | hole => rfl
  | left inner sibling inductionHypothesis =>
    exact congrArg₂ (· + ·) inductionHypothesis (eval_map_some sibling)
  | right sibling inner inductionHypothesis =>
    exact congrArg₂ (· + ·) (eval_map_some sibling) inductionHypothesis

/-- Literal equation equality at a fresh variable is classified by actual
closed erasures; the erasure proof uses the independently earned local model. -/
theorem open_equates_iff_erase (first second : Context Payload) :
    Equates first.encode second.encode ↔ Equates first.erase second.erase := by
  constructor
  · intro equation
    have same := equation.eval holeValues add_self
    rw [eval_encode, eval_encode] at same
    exact Quotient.exact same
  · intro equation
    have firstNormal : Equates first.encode (Context.right first.erase .hole).encode :=
      .base ((contextEquation_iff_openEquation _ _).mp (context_normal first))
    have secondNormal : Equates second.encode (Context.right second.erase .hole).encode :=
      .base ((contextEquation_iff_openEquation _ _).mp (context_normal second))
    exact firstNormal.trans ((Equates.congr (equation.map some) (.base (.refl (.atom none)))).trans secondNormal.symm)

def contextSetoid (Payload : Type u) : Setoid (Context Payload) where
  r first second := Equates first.encode second.encode
  iseqv := ⟨fun supplied => .base (.refl supplied.encode), Equates.symm, Equates.trans⟩

abbrev ContextClass (Payload : Type u) := Quotient (contextSetoid Payload)

def contextClassOf (supplied : Context Payload) : ContextClass Payload := Quotient.mk _ supplied

theorem erase_compose (outer inner : Context Payload) :
    Equation (outer.compose inner).erase (.cut outer.erase inner.erase) := by
  apply (equation_iff_inventory _ _).mpr
  rw [inventory, erase_inventory, context_compose_inventory, erase_inventory, erase_inventory]

theorem fill_eq_erased_cut (supplied : Context Payload) (value : Term Payload) :
    Equation (supplied.fill value) (.cut supplied.erase value) := by
  apply (equation_iff_inventory _ _).mpr
  rw [fill_inventory, inventory, erase_inventory]
  exact add_comm _ _

theorem context_compose_equates {outer outer' inner inner' : Context Payload}
    (first : Equates outer.encode outer'.encode) (second : Equates inner.encode inner'.encode) :
    Equates (outer.compose inner).encode (outer'.compose inner').encode := by
  apply (open_equates_iff_erase _ _).mpr
  exact (Equates.base (erase_compose outer inner)).trans
    ((Equates.congr ((open_equates_iff_erase _ _).mp first) ((open_equates_iff_erase _ _).mp second)).trans
      (Equates.base (erase_compose outer' inner')).symm)

theorem context_fill_equates {first second : Context Payload} {value value' : Term Payload}
    (equation : Equates first.encode second.encode) (values : Equates value value') :
    Equates (first.fill value) (second.fill value') :=
  (Equates.base (fill_eq_erased_cut first value)).trans
    ((Equates.congr ((open_equates_iff_erase _ _).mp equation) values).trans
      (Equates.base (fill_eq_erased_cut second value')).symm)

def erasureQ : ContextClass Payload → Class Payload :=
  Quotient.lift (fun supplied => classOf supplied.erase)
    (fun _ _ equation => Quotient.sound ((open_equates_iff_erase _ _).mp equation))

def fromTerm : Class Payload → ContextClass Payload :=
  Quotient.lift (fun term => contextClassOf (.right term .hole)) (fun _ _ equation =>
    Quotient.sound ((open_equates_iff_erase _ _).mpr
      (Equates.congr equation (.base (.refl .zero)))))

def erasureEquiv : ContextClass Payload ≃ Class Payload where
  toFun := erasureQ
  invFun := fromTerm
  left_inv value := Quotient.inductionOn value (fun supplied =>
    Quotient.sound (Equates.base ((contextEquation_iff_openEquation _ _).mp (context_normal supplied))).symm)
  right_inv value := Quotient.inductionOn value (fun term => Quotient.sound (Equates.base (Equation.unit term)))

instance contextOne : One (ContextClass Payload) := ⟨contextClassOf .hole⟩
instance contextMul : Mul (ContextClass Payload) :=
  ⟨Quotient.map₂ Context.compose (fun _ _ first _ _ second => context_compose_equates first second)⟩

instance contextMonoid : Monoid (ContextClass Payload) where
  one_mul supplied := Quotient.inductionOn supplied (fun _ => rfl)
  mul_one supplied := Quotient.inductionOn supplied (fun supplied => congrArg contextClassOf (compose_hole supplied))
  mul_assoc first second third := Quotient.inductionOn₃ first second third
    (fun first second third => congrArg contextClassOf (compose_assoc first second third))
  npow := npowRec

instance contextAction : MulAction (ContextClass Payload) (Class Payload) where
  smul := Quotient.map₂ Context.fill (fun _ _ first _ _ second => context_fill_equates first second)
  one_smul value := Quotient.inductionOn value (fun _ => rfl)
  mul_smul first second value := Quotient.inductionOn₃ first second value
    (fun first second value => congrArg classOf (fill_compose first second value))

theorem erasureQ_mul (outer inner : ContextClass Payload) :
    erasureQ (outer * inner) = erasureQ outer + erasureQ inner :=
  Quotient.inductionOn₂ outer inner (fun outer inner => Quotient.sound (Equates.base (erase_compose outer inner)))

theorem action_readout (supplied : ContextClass Payload) (value : Class Payload) :
    supplied • value = erasureQ supplied + value :=
  Quotient.inductionOn₂ supplied value (fun supplied value => Quotient.sound (Equates.base (fill_eq_erased_cut supplied value)))

abbrev Category (Payload : Type u) :=
  Mettapedia.CategoryTheory.GroundMonoidAction.Object (ContextClass Payload) (Class Payload)

end Mettapedia.OSLF.CommutativeCut.Idempotent
