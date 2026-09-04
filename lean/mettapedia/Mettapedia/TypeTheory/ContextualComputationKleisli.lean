import Mathlib.CategoryTheory.Category.Basic
import Mettapedia.GSLT.Dynamics.ContextualEffectHandlers
import Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-!
# Kleisli category of contextual computations

For fixed state and deferred-intent types, contextual programs are a monad in
their answer type.  The laws follow structurally from the free syntax and do
not choose an evaluator for choice or state.  Value types are therefore the
objects of a Kleisli category, while a computation from `A` to `B` maps an
`A` value to a contextual program returning `B`.

The construction separates values from computations without asserting that
choice is commutative, that alternatives share state, that intents execute
immediately, or that a computation has only one result.  The separating
examples exhibit computations which are not pure value maps.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.ContextualComputationKleisli

open CategoryTheory
open Mettapedia.GSLT.Dynamics.ContextualEffectHandlers

universe u

namespace Program

variable {State Answer OtherAnswer LastAnswer Intent : Type u}

@[simp] theorem read_bind
    (next : State → Program State Answer Intent)
    (later : Answer → Program State OtherAnswer Intent) :
    Program.bind (.read next) later =
      .read (fun state => Program.bind (next state) later) :=
  rfl

@[simp] theorem write_bind (state : State)
    (next : Program State Answer Intent)
    (later : Answer → Program State OtherAnswer Intent) :
    Program.bind (.write state next) later =
      .write state (Program.bind next later) :=
  rfl

@[simp] theorem intent_bind (request : Intent)
    (next : Program State Answer Intent)
    (later : Answer → Program State OtherAnswer Intent) :
    Program.bind (.intent request next) later =
      .intent request (Program.bind next later) :=
  rfl

/-- Returning every answer unchanged is a right identity for sequencing. -/
@[simp] theorem bind_pure (program : Program State Answer Intent) :
    Program.bind program (fun answer => .pure answer) = program := by
  induction program with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program.choose_bind]
      rw [leftIH, rightIH]
  | read next nextIH =>
      simp only [read_bind]
      congr 1
      funext state
      exact nextIH state
  | write state next nextIH =>
      simp only [write_bind]
      rw [nextIH]
  | intent request next nextIH =>
      simp only [intent_bind]
      rw [nextIH]

/-- Sequencing is associative. -/
theorem bind_assoc (program : Program State Answer Intent)
    (next : Answer → Program State OtherAnswer Intent)
    (later : OtherAnswer → Program State LastAnswer Intent) :
    Program.bind (Program.bind program next) later =
      Program.bind program
        (fun answer => Program.bind (next answer) later) := by
  induction program with
  | pure answer => rfl
  | choose left right leftIH rightIH =>
      simp only [Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program.choose_bind]
      rw [leftIH, rightIH]
  | read continuation continuationIH =>
      simp only [read_bind]
      congr 1
      funext state
      exact continuationIH state
  | write state continuation continuationIH =>
      simp only [write_bind]
      rw [continuationIH]
  | intent request continuation continuationIH =>
      simp only [intent_bind]
      rw [continuationIH]

/-- Mapping by the identity function changes no contextual computation. -/
@[simp] theorem map_id (program : Program State Answer Intent) :
    Program.map (fun answer => answer) program = program := by
  exact bind_pure program

/-- Contextual mapping respects function composition. -/
theorem map_comp (first : Answer → OtherAnswer)
    (second : OtherAnswer → LastAnswer)
    (program : Program State Answer Intent) :
    Program.map second (Program.map first program) =
      Program.map (fun answer => second (first answer)) program := by
  unfold Mettapedia.GSLT.Dynamics.ContextualEffectHandlers.Program.map
  rw [bind_assoc]
  rfl

/-! ## Witness-retaining dependent sequencing -/

/-- Sequence an index-dependent contextual continuation while retaining the
selected index in the answer.  This is the always-sound dependent target;
hiding the index requires additional fibre-uniformity evidence. -/
def bindSigma {Index : Type u} {Family : Index → Type u}
    (indices : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent) :
    Program State (Sigma Family) Intent :=
  Program.bind indices fun index =>
    Program.map (Sigma.mk index) (next index)

@[simp] theorem bindSigma_pure {Index : Type u} {Family : Index → Type u}
    (index : Index)
    (next : (index : Index) → Program State (Family index) Intent) :
    bindSigma (.pure index) next =
      Program.map (Sigma.mk index) (next index) :=
  rfl

@[simp] theorem bindSigma_choose {Index : Type u}
    {Family : Index → Type u}
    (left right : Program State Index Intent)
    (next : (index : Index) → Program State (Family index) Intent) :
    bindSigma (.choose left right) next =
      .choose (bindSigma left next) (bindSigma right next) :=
  rfl

end Program

/-! ## The Kleisli category -/

/-- A value type, with the fixed state and intent parameters retained in the
object type so each Kleisli category has its own type-class instance. -/
structure Object (State Intent : Type u) where
  Carrier : Type u

namespace Object

variable {State Intent : Type u}

/-- A Kleisli arrow maps a value to an effectful contextual computation. -/
@[ext]
structure Hom (source target : Object State Intent) where
  toFun : source.Carrier → Program State target.Carrier Intent

instance {source target : Object State Intent} :
    CoeFun (Hom source target)
      (fun _ => source.Carrier → Program State target.Carrier Intent) :=
  ⟨Hom.toFun⟩

/-- A pure value map, regarded as a contextual computation. -/
def Hom.ofFunction {source target : Object State Intent}
    (function : source.Carrier → target.Carrier) : Hom source target where
  toFun := fun value => .pure (function value)

/-- Identity returns its input without effects. -/
def Hom.id (object : Object State Intent) : Hom object object :=
  Hom.ofFunction (fun value => value)

/-- Kleisli composition sequences the first contextual program into the
second. -/
def Hom.comp {first middle last : Object State Intent}
    (earlier : Hom first middle) (later : Hom middle last) : Hom first last where
  toFun := fun value => Program.bind (earlier value) later

instance : Category.{u} (Object State Intent) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp := by
    intro first second arrow
    apply Hom.ext
    funext value
    rfl
  comp_id := by
    intro first second arrow
    apply Hom.ext
    funext value
    exact Program.bind_pure (arrow value)
  assoc := by
    intro first second third fourth earlier middle later
    apply Hom.ext
    funext value
    exact Program.bind_assoc (earlier value) middle later

/-- Pure functions embed functorially into contextual computations. -/
@[simp] theorem ofFunction_id (object : Object State Intent) :
    Hom.ofFunction (fun value : object.Carrier => value) = 𝟙 object :=
  rfl

theorem ofFunction_comp {first middle last : Object State Intent}
    (earlier : first.Carrier → middle.Carrier)
    (later : middle.Carrier → last.Carrier) :
    Hom.comp (Hom.ofFunction earlier) (Hom.ofFunction later) =
      Hom.ofFunction (fun value => later (earlier value)) :=
  rfl

/-! ## Separating controls -/

abbrev UnitValue : Object Bool Unit := ⟨Unit⟩
abbrev BoolValue : Object Bool Unit := ⟨Bool⟩

/-- One computation retains two alternatives. -/
def chooseBool : UnitValue ⟶ BoolValue where
  toFun := fun _ => .choose (.pure false) (.pure true)

/-- A pure computation returning `false`. -/
def pureFalse : UnitValue ⟶ BoolValue :=
  Hom.ofFunction (fun _ => false)

/-- A pure computation returning `true`. -/
def pureTrue : UnitValue ⟶ BoolValue :=
  Hom.ofFunction (fun _ => true)

/-- Contextual choice is not silently identified with either pure branch. -/
theorem chooseBool_ne_pureFalse : chooseBool ≠ pureFalse := by
  intro equalArrows
  have programsEqual := congrArg (fun arrow => arrow.toFun ()) equalArrows
  cases programsEqual

theorem chooseBool_ne_pureTrue : chooseBool ≠ pureTrue := by
  intro equalArrows
  have programsEqual := congrArg (fun arrow => arrow.toFun ()) equalArrows
  cases programsEqual

/-- A state-reading Kleisli arrow cannot be represented by a constant pure
Boolean return. -/
def readState : UnitValue ⟶ BoolValue where
  toFun := fun _ => .read (fun state => .pure state)

theorem readState_ne_pureFalse : readState ≠ pureFalse := by
  intro equalArrows
  have programsEqual := congrArg (fun arrow => arrow.toFun ()) equalArrows
  cases programsEqual

/-- The Kleisli category therefore strictly contains its displayed pure
value maps. -/
theorem effectful_arrows_strictly_extend_pure_maps :
    chooseBool ≠ pureFalse ∧ chooseBool ≠ pureTrue ∧
      readState ≠ pureFalse :=
  ⟨chooseBool_ne_pureFalse, chooseBool_ne_pureTrue,
    readState_ne_pureFalse⟩

/-! ## Dependent sequencing control -/

open Mettapedia.TypeTheory.DependencyExtensionalityOrthogonality

/-- A choice of Boolean index followed by a genuinely index-dependent
continuation. -/
def varyingContinuation :
    (index : Bool) → Program Unit (varyingBoolFamily index) Unit
  | false => .pure PUnit.unit
  | true => .choose (.pure false) (.pure true)

def varyingDependentProgram :
    Program Unit (Sigma varyingBoolFamily) Unit :=
  Program.bindSigma
    (.choose (.pure false) (.pure true)) varyingContinuation

/-- The selected index survives dependent sequencing beside every result. -/
theorem varyingDependentProgram_indices :
    (runWorlds varyingDependentProgram ()).map
        (fun result => result.answer.1) = [false, true, true] :=
  rfl

/-- The result family is genuinely varying, so this witness retention is not
just a restatement of ordinary nondependent sequencing. -/
theorem varyingDependentProgram_is_genuinely_dependent :
    ¬ ∃ Constant : Type,
      ∀ index, Nonempty (varyingBoolFamily index ≃ Constant) :=
  varyingBoolFamily_not_constant

/-! ## Axiom audit -/

#print axioms Program.bind_pure
#print axioms Program.bind_assoc
#print axioms Program.map_comp
#print axioms Program.bindSigma_choose
#print axioms Object.instCategory
#print axioms chooseBool_ne_pureFalse
#print axioms chooseBool_ne_pureTrue
#print axioms readState_ne_pureFalse
#print axioms effectful_arrows_strictly_extend_pure_maps
#print axioms varyingDependentProgram_indices
#print axioms varyingDependentProgram_is_genuinely_dependent

end Object

end Mettapedia.TypeTheory.ContextualComputationKleisli
