import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorClassifying
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorInterpretation
import Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorUniversal
import Mathlib.CategoryTheory.Monoidal.Closed.Types
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Complete continuation-constructor readouts

An independent higher-order tree algebra retains the bodies of unary and
binary receivers and fresh-name binding. The actual classifying functor's
constructor images are read at independently supplied arguments and returns.
The controls distinguish the argument and return positions, the suspended
stored value and active body, and a changed return channel.

This algebra tests the constructor interpretation. It does not supply the
structural equations or communication dynamics of a pi process model.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorControls

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Mettapedia.CategoryTheory.RelativeClosedSyntax.Interpretation
open NamePassingContinuationOperations NamePassingConstructorClassifying
open Mettapedia.OSLF.Binding Mettapedia.Languages.LambdaCalculus

inductive ProcessTree where
  | empty
  | parallel (first second : ProcessTree)
  | output (channel datum : Nat)
  | send (channel argument result : Nat)
  | input (channel : Nat) (body : Nat → ProcessTree)
  | receive (channel : Nat) (body : Nat × Nat → ProcessTree)
  | fresh (body : Nat → ProcessTree)
  | replication (body : ProcessTree)

def operations : Operations (Type) where
  names := Nat
  processes := ProcessTree
  empty := ↾fun _ => .empty
  parallel := ↾fun pair => .parallel pair.1 pair.2
  output := ↾fun pair => .output pair.1 pair.2
  send := ↾fun data => .send data.1 data.2.1 data.2.2
  input := ↾fun data => .input data.1 (fun name => (show Nat ⟶ ProcessTree from data.2) name)
  receive := ↾fun data => .receive data.1 (fun pair => (show (Nat × Nat) ⟶ ProcessTree from data.2) pair)
  fresh := ↾fun body => .fresh (fun name => (show Nat ⟶ ProcessTree from body) name)
  replication := ↾ProcessTree.replication

abbrev Program := Nat ⟶ ProcessTree
abbrev BoundBody := Nat ⟶ Program

def value : Program := ↾fun result => .output 31 result
def body : BoundBody := ↾fun reference => ↾fun result => .send 47 reference result

def actualImage (constructor : Constructor) : ArrowValue (Type) :=
  ⟨(constructorMap operations).functor.obj (constructorDomain constructor),
    (constructorMap operations).functor.obj termObject,
    (constructorMap operations).functor.map
      (Mettapedia.CategoryTheory.RelativeClosedSyntax.GeneratedCategory.classOf
        (constructorArrow constructor))⟩

def read (constructor : Constructor) (source : Type) (input : source) (result : Nat) :
    Option ProcessTree :=
  (ArrowValue.readAt (some (actualImage constructor)) source Program).map
    (fun arrow => arrow input result)

theorem reference_readout (name result : Nat) :
    read .reference Nat name result = some (.output name result) := by
  rw [read, actualImage, complete_constructor_readout]
  change Option.map (fun arrow : (Nat) ⟶ Program => arrow name result)
    (ArrowValue.readAt (some (⟨Nat, Program, operations.reference⟩ : ArrowValue (Type)))
      (Nat) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem abstraction_readout (result : Nat) :
    read .abstraction BoundBody body result =
      some (.receive result (fun pair => .send 47 pair.1 pair.2)) := by
  rw [read, actualImage, complete_constructor_readout]
  change Option.map (fun arrow : (BoundBody) ⟶ Program => arrow body result)
    (ArrowValue.readAt (some (⟨BoundBody, Program, operations.abstraction⟩ : ArrowValue (Type)))
      (BoundBody) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem application_readout (argument result : Nat) :
    read .application (Program × Nat) (value, argument) result =
      some (.fresh (fun privateName =>
        .parallel (.output 31 privateName) (.send privateName argument result))) := by
  rw [read, actualImage, complete_constructor_readout]
  change Option.map (fun arrow : (Program × Nat) ⟶ Program => arrow (value, argument) result)
    (ArrowValue.readAt (some (⟨Program × Nat, Program, operations.application⟩ : ArrowValue (Type)))
      (Program × Nat) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem definition_readout (result : Nat) :
    read .definition (Program × BoundBody) (value, body) result =
      some (.fresh (fun reference =>
        .parallel (.send 47 reference result)
          (.replication (.input reference (fun reply => .output 31 reply))))) := by
  rw [read, actualImage, complete_constructor_readout]
  change Option.map (fun arrow : (Program × BoundBody) ⟶ Program => arrow (value, body) result)
    (ArrowValue.readAt (some (⟨Program × BoundBody, Program, operations.definition⟩ : ArrowValue (Type)))
      (Program × BoundBody) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem carrier_readout (name result : Nat) :
    read .carrier (Nat × (Program × Program))
        (name, (value, ↾fun reply => .send 47 19 reply)) result =
      some (.parallel (.send 47 19 result) (.input name (fun reply => .output 31 reply))) := by
  rw [read, actualImage, complete_constructor_readout]
  change Option.map (fun arrow : (Nat × (Program × Program)) ⟶ Program => arrow (name, (value, ↾fun reply => .send 47 19 reply)) result)
    (ArrowValue.readAt (some (⟨Nat × (Program × Program), Program, operations.carrier⟩ : ArrowValue (Type)))
      (Nat × (Program × Program)) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem received_positions_distinct :
    (body 7) 11 ≠ (body 11) 7 := by
  intro same
  have changed := ProcessTree.send.inj same
  exact (by decide : (7 : Nat) ≠ 11) changed.2.1

theorem actual_return_changes :
    read .reference Nat 3 7 ≠ read .reference Nat 3 11 := by
  rw [reference_readout, reference_readout]
  intro same
  have changed := ProcessTree.output.inj (Option.some.inj same)
  exact (by decide : (7 : Nat) ≠ 11) changed.2

theorem application_retains_external_return :
    (.send 5 7 11 : ProcessTree) ≠ .send 5 11 7 := by
  intro same
  have changed := ProcessTree.send.inj same
  exact (by decide : (7 : Nat) ≠ 11) changed.2.1

def sourceScope : Ctx NamePassing.Presentation.signature := [.tm, .nm]

def innerCall : NamePassing.Presentation.Program (.nm :: sourceScope) :=
  NamePassing.Presentation.application (.var (.succ .zero)) (.var .zero)

def caller : NamePassing.Presentation.Program sourceScope :=
  NamePassing.Presentation.application (NamePassing.Presentation.abstraction innerCall) (.var (.succ .zero))

def instantiatedCall : NamePassing.Presentation.Program sourceScope :=
  NamePassing.Presentation.application (.var .zero) (.var (.succ .zero))

theorem instantiated_call : inst innerCall (Term.var (.succ .zero)) = instantiatedCall := rfl

def actualOpenImage {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context) : ArrowValue (Type) :=
  ⟨(constructorMap operations).functor.obj (NamePassingConstructorSyntax.contextObject context),
    (constructorMap operations).functor.obj termObject,
    (constructorMap operations).functor.map (NamePassingConstructorSyntax.arrow term)⟩

def readOpen {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context)
    (input : NamePassingConstructorInterpretation.contextValue operations context)
    (result : Nat) : Option ProcessTree :=
  (ArrowValue.readAt (some (actualOpenImage term))
    (NamePassingConstructorInterpretation.contextValue operations context) Program).map
      (fun arrow => arrow input result)

theorem readOpen_semantics {context : Ctx NamePassing.Presentation.signature}
    (term : NamePassing.Presentation.Program context)
    (input : NamePassingConstructorInterpretation.contextValue operations context) (result : Nat) :
    readOpen term input result =
      some ((show Program from NamePassingConstructorInterpretation.meaning operations term input) result) := by
  rw [readOpen, actualOpenImage, NamePassingConstructorInterpretation.complete_open_term_readout]
  change Option.map _
    (ArrowValue.readAt (some (⟨NamePassingConstructorInterpretation.contextValue operations context,
      Program, NamePassingConstructorInterpretation.meaning operations term⟩ : ArrowValue (Type)))
      (NamePassingConstructorInterpretation.contextValue operations context) Program) = _
  rw [ArrowValue.readAt_supplied]
  rfl

theorem whole_bound_caller_readout (argument result : Nat) :
    readOpen caller (value, argument, PUnit.unit) result =
      some (.fresh (fun callName =>
        .parallel
          (.receive callName (fun pair =>
            .fresh (fun privateName =>
              .parallel (.output 31 privateName) (.send privateName pair.1 pair.2))))
          (.send callName argument result))) := by
  rw [readOpen_semantics]
  simp only [caller, innerCall, NamePassing.Presentation.application, NamePassing.Presentation.abstraction,
    NamePassingConstructorInterpretation.meaning]
  rfl

theorem whole_instantiated_readout (argument result : Nat) :
    readOpen instantiatedCall (value, argument, PUnit.unit) result =
      some (.fresh (fun privateName =>
        .parallel (.output 31 privateName) (.send privateName argument result))) := by
  rw [readOpen_semantics]
  simp only [instantiatedCall, NamePassing.Presentation.application, NamePassingConstructorInterpretation.meaning]
  rfl

/-- The constructor completion admits this independently supplied algebra,
but does not silently equate an operational redex with its contractum. -/
theorem constructor_completion_does_not_supply_beta_equality :
    readOpen caller (value, (17 : Nat), PUnit.unit) 23 ≠
      readOpen instantiatedCall (value, (17 : Nat), PUnit.unit) 23 := by
  rw [whole_bound_caller_readout, whole_instantiated_readout]
  intro same
  have roots := ProcessTree.fresh.inj (Option.some.inj same)
  have atName := congrArg (fun function : Nat → ProcessTree => function 5) roots
  have firstSame := (ProcessTree.parallel.inj atName).1
  cases firstSame

end Mettapedia.Languages.ProcessCalculi.PolyadicPi.Bridges.NamePassingConstructorControls
