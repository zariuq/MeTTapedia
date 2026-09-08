import Mathlib.CategoryTheory.Monad.Limits
import Mathlib.CategoryTheory.Limits.Types.Products
import Mettapedia.TypeTheory.ContextualKleisliAdjunction

/-!
# Products of contextual computation algebras

The existing contextual adjunction induces the monad used here. Its
Eilenberg--Moore algebras have value-indexed products, with literal dependent
function carriers and pointwise algebra action. The limiting cone and its
universal property are Mathlib's construction of limits created by the
forgetful functor, applied to the explicit product cone in `Type`.

Constant families provide powers; the empty product is terminal. A product
of free returners still contains the original contextual programs at every
index. Neither the terminal algebra nor pointwise evaluation identifies those
programs modulo their effects. These interfaces do not supply arbitrary
dependent sequencing or select a full dependent CBPV profile.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualComputationAlgebraProducts

open CategoryTheory CategoryTheory.Limits
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe u

/-- Use the existing induced monad directly. -/
abbrev Computation (State Intent : Type u) :=
  CategoryTheory.Monad.Algebra (ContextualKleisliAdjunction.inducedMonad State Intent)

variable {State Intent Index : Type u}

private def carrierDiagramIso (family : Index → Computation State Intent) :=
  Discrete.compNatIsoDiscrete family
    (CategoryTheory.Monad.forget (ContextualKleisliAdjunction.inducedMonad State Intent))

def carrierCone (family : Index → Computation State Intent) :
    Cone (Discrete.functor family ⋙
      CategoryTheory.Monad.forget (ContextualKleisliAdjunction.inducedMonad State Intent)) :=
  (Cone.postcompose (carrierDiagramIso family).inv).obj
    (Types.productLimitCone (fun index => (family index).A)).cone

def carrierIsLimit (family : Index → Computation State Intent) :
    IsLimit (carrierCone family) :=
  (IsLimit.postcomposeInvEquiv (carrierDiagramIso family)
    (Types.productLimitCone (fun index => (family index).A)).cone).symm
      (Types.productLimitCone (fun index => (family index).A)).isLimit

/-- The concrete computation product is the limit algebra constructed by
Mathlib, not merely a type equipped with projection functions. -/
def product (family : Index → Computation State Intent) : Computation State Intent :=
  CategoryTheory.Monad.ForgetCreatesLimits.conePoint (Discrete.functor family)
    (carrierCone family) (carrierIsLimit family)

def productCone (family : Index → Computation State Intent) : Fan family :=
  CategoryTheory.Monad.ForgetCreatesLimits.liftedCone (Discrete.functor family)
    (carrierCone family) (carrierIsLimit family)

/-- Creation of limits supplies the actual universal property. -/
def productIsLimit (family : Index → Computation State Intent) :
    IsLimit (productCone family) :=
  CategoryTheory.Monad.ForgetCreatesLimits.liftedConeIsLimit (Discrete.functor family)
    (carrierCone family) (carrierIsLimit family)

@[simp] theorem product_carrier (family : Index → Computation State Intent) :
    (product family).A = ((index : Index) → (family index).A) := rfl

/-- Evaluating one value index distributes through the actual monad action.
The family of computation carriers may vary with that index. -/
@[simp] theorem product_action_apply (family : Index → Computation State Intent)
    (program : Program State ((index : Index) → (family index).A) Intent) (index : Index) :
    (product family).a program index =
      (family index).a (Program.map (fun values => values index) program) := rfl

def projection (family : Index → Computation State Intent) (index : Index) :
    product family ⟶ family index :=
  (productCone family).π.app ⟨index⟩

@[simp] theorem projection_apply (family : Index → Computation State Intent)
    (index : Index) (values : (product family).A) :
    (projection family index).f values = values index := rfl

def lift {source : Computation State Intent} {family : Index → Computation State Intent}
    (arrows : (index : Index) → source ⟶ family index) : source ⟶ product family :=
  (productIsLimit family).lift (Fan.mk source arrows)

@[simp] theorem lift_apply {source : Computation State Intent}
    {family : Index → Computation State Intent}
    (arrows : (index : Index) → source ⟶ family index) (value : source.A) (index : Index) :
    (lift arrows).f value index = (arrows index).f value := rfl

@[simp] theorem lift_projection {source : Computation State Intent}
    {family : Index → Computation State Intent}
    (arrows : (index : Index) → source ⟶ family index) (index : Index) :
    lift arrows ≫ projection family index = arrows index :=
  (productIsLimit family).fac (Fan.mk source arrows) ⟨index⟩

theorem product_hom_ext {source : Computation State Intent}
    {family : Index → Computation State Intent} {first second : source ⟶ product family}
    (equal : ∀ index, first ≫ projection family index = second ≫ projection family index) :
    first = second := by
  apply (productIsLimit family).hom_ext
  intro index
  exact equal index.as

/-- Maps into a computation product are exactly index-wise algebra maps. -/
def productHomEquiv (source : Computation State Intent)
    (family : Index → Computation State Intent) :
    (source ⟶ product family) ≃ ((index : Index) → source ⟶ family index) where
  toFun arrow index := arrow ≫ projection family index
  invFun := lift
  left_inv arrow := product_hom_ext (fun index =>
    lift_projection (fun selected => arrow ≫ projection family selected) index)
  right_inv arrows := funext (fun index => lift_projection arrows index)

/-- A power is the constant-family case, with a value-to-computation carrier. -/
def power (Index : Type u) (target : Computation State Intent) : Computation State Intent :=
  product (fun _ : Index => target)

@[simp] theorem power_carrier (Index : Type u) (target : Computation State Intent) :
    (power Index target).A = (Index → target.A) := rfl

def powerHomEquiv (source target : Computation State Intent) (Index : Type u) :
    (source ⟶ power Index target) ≃ (Index → (source ⟶ target)) :=
  productHomEquiv source (fun _ : Index => target)

def emptyFamily (State Intent : Type u) : PEmpty.{u + 1} → Computation State Intent :=
  fun index => index.elim

def terminal (State Intent : Type u) : Computation State Intent :=
  product (emptyFamily State Intent)

/-- Terminality is the universal property of this genuine empty limit. -/
noncomputable def terminalIsTerminal (State Intent : Type u) : IsTerminal (terminal State Intent) :=
  (isLimitEquivIsTerminalOfIsEmpty (Computation State Intent)
    (productCone (emptyFamily State Intent)))
    (productIsLimit (emptyFamily State Intent))

namespace Controls

/-- The computation family genuinely varies with its value index. -/
def Answer : Bool → Type
  | false => Nat
  | true => Bool

def freeFamily (index : Bool) : Computation Bool Nat :=
  (CategoryTheory.Monad.free (ContextualKleisliAdjunction.inducedMonad Bool Nat)).obj (Answer index)

def firstRow : (index : Bool) → (freeFamily index).A
  | false => .pure (3 : Nat)
  | true => .pure false

def secondRow : (index : Bool) → (freeFamily index).A
  | false => .intent 7 (.write true (.pure (8 : Nat)))
  | true => .choose (.pure true) (.pure false)

/-- Choice of a row precedes the requested value-index projection. -/
def rows : Program Bool ((index : Bool) → (freeFamily index).A) Nat :=
  .choose (.pure firstRow) (.pure secondRow)

def selected : (product freeFamily).A := (product freeFamily).a rows

theorem false_projection :
    (projection freeFamily false).f selected =
      Program.choose (.pure (3 : Nat)) (.intent 7 (.write true (.pure (8 : Nat)))) := rfl

theorem true_projection :
    (projection freeFamily true).f selected =
      Program.choose (.pure false) (.choose (.pure true) (.pure false)) := rfl

/-- Projection retains the authored branches, private state and deferred
intent at this selected index; it does not run or merge other components. -/
theorem false_projection_worlds :
    runWorlds ((projection freeFamily false).f selected) false =
      [{ branch := [false], answer := (3 : Nat), state := false, intents := [] },
       { branch := [true], answer := (8 : Nat), state := true, intents := [7] }] := rfl

theorem true_projection_worlds :
    runWorlds ((projection freeFamily true).f selected) false =
      [{ branch := [false], answer := false, state := false, intents := [] },
       { branch := [false, true], answer := true, state := false, intents := [] },
       { branch := [true, true], answer := false, state := false, intents := [] }] := rfl

/-- The product action does not select just one row. -/
theorem selected_is_not_first_row : selected ≠ firstRow := by
  intro equal
  have atFalse := congrArg (fun values => values false) equal
  change Program.choose (.pure (3 : Nat)) (.intent 7 (.write true (.pure (8 : Nat)))) =
    Program.pure (3 : Nat) at atFalse
  cases atFalse

def unitReturner : Computation Bool Nat :=
  (CategoryTheory.Monad.free (ContextualKleisliAdjunction.inducedMonad Bool Nat)).obj Unit

/-- Free extension of a real effectful computation, using the monad's
existing free-forgetful adjunction. -/
def addUnitIntent : unitReturner ⟶ unitReturner :=
  ((CategoryTheory.Monad.adj (ContextualKleisliAdjunction.inducedMonad Bool Nat)).homEquiv
    Unit unitReturner).symm (TypeCat.ofHom (fun _ => Program.intent 7 (Program.pure ())))

theorem addUnitIntent_pure :
    addUnitIntent.f (Program.pure ()) = Program.intent 7 (Program.pure ()) := rfl

/-- Returning `Unit` is not the terminal computation object: two algebra
endomorphisms already distinguish pure return from appending an intent. -/
theorem free_unit_is_not_terminal : ¬ Nonempty (IsTerminal unitReturner) := by
  rintro ⟨terminalProof⟩
  have equal := terminalProof.hom_ext (𝟙 unitReturner) addUnitIntent
  have impossible := congrArg (fun arrow => arrow.f (Program.pure ())) equal
  change Program.pure () = Program.intent 7 (Program.pure ()) at impossible
  cases impossible

theorem unit_effect_observations_differ :
    runWorlds (Program.pure () : Program Bool Unit Nat) false ≠
      runWorlds (Program.intent 7 (Program.pure ())) false := by
  intro equal
  have intents := congrArg (List.map WorldResult.intents) equal
  change [[]] = ([[7]] : List (List Nat)) at intents
  cases intents

/-- This is a value-indexed computation, not a program returning a pure
function. The requested argument controls whether an intent is emitted. -/
def argumentEffect (index : Bool) : Program Bool Unit Nat :=
  if index then .intent 7 (.pure ()) else .pure ()

/-- Evaluating a computed pure function at an argument cannot acquire an
argument-dependent outer effect that was absent from the computation. -/
theorem argument_effect_not_computed_pure_function :
    ¬ ∃ program : Program Bool (Bool → Unit) Nat,
      (fun index => Program.map (fun function => function index) program) = argumentEffect := by
  rintro ⟨program, equal⟩
  have atFalse := congrFun equal false
  have atTrue := congrFun equal true
  cases program <;> simp only [Program.map, Program.bind, argumentEffect,
    Bool.false_eq_true, ↓reduceIte] at atFalse atTrue
  all_goals cases atFalse
  all_goals cases atTrue

end Controls

#print axioms productIsLimit
#print axioms product_action_apply
#print axioms lift_projection
#print axioms product_hom_ext
#print axioms productHomEquiv
#print axioms powerHomEquiv
#print axioms terminalIsTerminal
#print axioms Controls.false_projection
#print axioms Controls.true_projection
#print axioms Controls.false_projection_worlds
#print axioms Controls.true_projection_worlds
#print axioms Controls.selected_is_not_first_row
#print axioms Controls.addUnitIntent_pure
#print axioms Controls.free_unit_is_not_terminal
#print axioms Controls.unit_effect_observations_differ
#print axioms Controls.argument_effect_not_computed_pure_function

end Mettapedia.TypeTheory.ContextualComputationAlgebraProducts
