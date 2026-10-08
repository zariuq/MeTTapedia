import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalInterpretation
import Mathlib.Tactic.NormNum

/-!
# Complete constructor-domain and operational-admission controls

An independent binding-constructor model computes on distinct value and term
objects. Its full function arguments and ordered stored/active positions
have concrete discriminating readings. These are constructor-model controls;
the five-rule compiler is separately checked at its actual generated guest
and endpoint equations, with no guest numeric execution claim.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory RelativeClosedSyntax GeneratedCategory Interpretation
open Mettapedia.OSLF.Binding
open Mettapedia.Languages.LambdaCalculus

abbrev Value := Nat × Bool
abbrev Body := Nat ⟶ Value

def operations : ClosedPresentation.Operations NamePassing.Presentation.signature (Type) where
  sort
    | .nm => Nat
    | .tm => Value
  operation
    | .reference => ↾fun data => ((show PUnit ⟶ Nat from data.1) PUnit.unit + 100, false)
    | .abstraction => ↾fun data =>
        let value := (show (Nat × PUnit) ⟶ Value from data.1) (37, PUnit.unit)
        (value.1 + 10, value.2)
    | .application => ↾fun data =>
        let value := (show PUnit ⟶ Value from data.1) PUnit.unit
        (2 * value.1 + (show PUnit ⟶ Nat from data.2.1) PUnit.unit + 200, value.2)
    | .definition => ↾fun data =>
        let stored := (show PUnit ⟶ Value from data.1) PUnit.unit
        let body := (show (Nat × PUnit) ⟶ Value from data.2.1) (stored.1, PUnit.unit)
        (stored.1 + body.1 + 300, stored.2 != body.2)
    | .carrier => ↾fun data =>
        let name := (show PUnit ⟶ Nat from data.1) PUnit.unit
        let stored := (show PUnit ⟶ Value from data.2.1) PUnit.unit
        let active := (show PUnit ⟶ Value from data.2.2.1) PUnit.unit
        (1000 * name + 10 * stored.1 + active.1, stored.2 && active.2)

def image (operator : NamePassing.Presentation.Operator .tm) : ArrowValue (Type) :=
  ⟨operations.interpretation.functor.obj (NamePassingBindingClosedConstructorExpressions.domain operator),
    operations.interpretation.functor.obj NamePassingBindingClosedConstructorExpressions.terms,
    operations.interpretation.functor.map
      (classOf (NamePassingBindingClosedConstructorExpressions.expression operator))⟩

def read (operator : NamePassing.Presentation.Operator .tm) (inputType : Type) (input : inputType) : Option Value :=
  (ArrowValue.readAt (some (image operator)) inputType Value).map (fun arrow => arrow input)

theorem reference_readout (name : Nat) : read .reference Nat name = some (name + 100, false) := by
  rw [read, image, NamePassingBindingClosedConstructorReadout.complete_readout]
  change Option.map (fun arrow : Nat ⟶ Value => arrow name)
    (ArrowValue.readAt (some (⟨Nat, Value, NamePassingBindingPrimitiveOperations.reference operations⟩ : ArrowValue (Type)))
      Nat Value) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem abstraction_readout (body : Body) : read .abstraction Body body =
    some ((body 37).1 + 10, (body 37).2) := by
  rw [read, image, NamePassingBindingClosedConstructorReadout.complete_readout]
  change Option.map (fun arrow : Body ⟶ Value => arrow body)
    (ArrowValue.readAt (some (⟨Body, Value, NamePassingBindingPrimitiveOperations.abstraction operations⟩ : ArrowValue (Type)))
      Body Value) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem application_readout (term : Value) (name : Nat) : read .application (Value × Nat) (term,name) =
    some (2 * term.1 + name + 200, term.2) := by
  rw [read, image, NamePassingBindingClosedConstructorReadout.complete_readout]
  change Option.map (fun arrow : (Value × Nat) ⟶ Value => arrow (term,name))
    (ArrowValue.readAt (some (⟨Value × Nat, Value, NamePassingBindingPrimitiveOperations.application operations⟩ : ArrowValue (Type)))
      (Value × Nat) Value) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem definition_readout (stored : Value) (body : Body) : read .definition (Value × Body) (stored,body) =
    some (stored.1 + (body stored.1).1 + 300, stored.2 != (body stored.1).2) := by
  rw [read, image, NamePassingBindingClosedConstructorReadout.complete_readout]
  change Option.map (fun arrow : (Value × Body) ⟶ Value => arrow (stored,body))
    (ArrowValue.readAt (some (⟨Value × Body, Value, NamePassingBindingPrimitiveOperations.definition operations⟩ : ArrowValue (Type)))
      (Value × Body) Value) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem carrier_readout (name : Nat) (stored active : Value) :
    read .carrier (Nat × (Value × Value)) (name,(stored,active)) =
      some (1000 * name + 10 * stored.1 + active.1, stored.2 && active.2) := by
  rw [read, image, NamePassingBindingClosedConstructorReadout.complete_readout]
  change Option.map (fun arrow : (Nat × (Value × Value)) ⟶ Value => arrow (name,(stored,active)))
    (ArrowValue.readAt (some (⟨Nat × (Value × Value), Value, NamePassingBindingPrimitiveOperations.carrier operations⟩ : ArrowValue (Type)))
      (Nat × (Value × Value)) Value) = _
  rw [ArrowValue.readAt_supplied]
  rfl

def firstBody : Body := ↾fun name => (name,false)
def changedBody : Body := ↾fun name => (if name = 37 then name + 1 else name,false)

theorem bodies_agree_at_one_argument : firstBody 0 = changedBody 0 := rfl

theorem complete_body_readings_differ : read .abstraction Body firstBody = some (47,false) ∧
    read .abstraction Body changedBody = some (48,false) := by
  rw [abstraction_readout, abstraction_readout]
  constructor <;> rfl

theorem one_argument_cannot_determine_constructor : ¬
    (∃ decoder : Value → Option Value, ∀ body : Body, decoder (body 0) = read .abstraction Body body) := by
  rintro ⟨decoder, recover⟩
  have first := recover firstBody
  have second := recover changedBody
  rw [← bodies_agree_at_one_argument] at second
  have same := first.symm.trans second
  rw [complete_body_readings_differ.1, complete_body_readings_differ.2] at same
  cases same

theorem definition_retains_full_body_and_stored_value :
    read .definition (Value × Body) ((37,false),firstBody) = some (374,false) ∧
    read .definition (Value × Body) ((37,false),changedBody) = some (375,false) := by
  rw [definition_readout, definition_readout]
  constructor <;> rfl

theorem carrier_positions_differ :
    read .carrier (Nat × (Value × Value)) (3,((5,true),(7,false))) = some (3057,false) ∧
    read .carrier (Nat × (Value × Value)) (3,((7,false),(5,true))) = some (3075,false) := by
  rw [carrier_readout, carrier_readout]
  constructor <;> rfl

theorem carrier_has_no_exchanged_position_decoder : ¬
    (∀ name stored active, read .carrier (Nat × (Value × Value)) (name,(stored,active)) =
      read .carrier (Nat × (Value × Value)) (name,(active,stored))) := by
  intro exchange
  have same := exchange 3 (5,true) (7,false)
  rw [carrier_positions_differ.1, carrier_positions_differ.2] at same
  cases same

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingGeneratedOperationalControls
