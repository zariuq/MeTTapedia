import Mathlib.CategoryTheory.SingleObj
import Mettapedia.CategoryTheory.ParameterizedMonad
import Mettapedia.CategoryTheory.WriterActionTransport

/-!
# Runs with results, and their accounts

The arrows of a category are runs between states.  A run paired with a
returned value is an execution.  Executions form a parameterized monad: the
empty run returns, and bind runs one execution after the other, which is
possible exactly when the first ends in the state where the second starts.

An account assigns an element of a monoid to every run: the unit to the empty
run, and to a composite the product of the two accounts, first run first.
Reading the account of an execution lands in the writer monad of that monoid
and preserves return, mapping and bind.  That writer monad is the monad of the
free and forgetful functors for monoid actions.  Its multiplication is not
injective (`WriterActionAdjunction.multiplication_not_injective`): reading a
bind forgets where the first run ended.

Accounts change along monoid homomorphisms, pair up, and restrict along
functors.  An account is the same thing as a functor to the one-object
category of the opposite monoid; the opposite appears because that category
composes its arrows in the order opposite to running.
-/

open CategoryTheory

namespace Mettapedia.Effects

set_option autoImplicit false

universe u v w x y

/-- A run of a category from one state to another, with a returned value. -/
@[ext]
structure Execution (C : Type u) [Category.{v} C] (source target : C)
    (Result : Type w) where
  /-- The run. -/
  transition : source ⟶ target
  /-- The value it returns. -/
  result : Result

namespace Execution

variable {C : Type u} [Category.{v} C] {Result NextResult FinalResult : Type w}

/-- Return a value without running: the empty run. -/
def pure (state : C) (result : Result) : Execution C state state Result :=
  ⟨𝟙 state, result⟩

/-- Run one execution, then the one its result selects. -/
def bind {source middle target : C} (first : Execution C source middle Result)
    (next : Result → Execution C middle target NextResult) :
    Execution C source target NextResult :=
  ⟨first.transition ≫ (next first.result).transition, (next first.result).result⟩

/-- Change the returned value; the run stays. -/
def map {source target : C} (function : Result → NextResult)
    (execution : Execution C source target Result) :
    Execution C source target NextResult :=
  ⟨execution.transition, function execution.result⟩

@[simp] theorem pure_transition (state : C) (result : Result) :
    (pure state result).transition = 𝟙 state := rfl

@[simp] theorem pure_result (state : C) (result : Result) :
    (pure state result).result = result := rfl

@[simp] theorem bind_transition {source middle target : C}
    (first : Execution C source middle Result)
    (next : Result → Execution C middle target NextResult) :
    (first.bind next).transition =
      first.transition ≫ (next first.result).transition := rfl

@[simp] theorem bind_result {source middle target : C}
    (first : Execution C source middle Result)
    (next : Result → Execution C middle target NextResult) :
    (first.bind next).result = (next first.result).result := rfl

@[simp] theorem map_transition {source target : C} (function : Result → NextResult)
    (execution : Execution C source target Result) :
    (execution.map function).transition = execution.transition := rfl

@[simp] theorem map_result {source target : C} (function : Result → NextResult)
    (execution : Execution C source target Result) :
    (execution.map function).result = function execution.result := rfl

/-- Left unit of bind. -/
@[simp] theorem pure_bind {source target : C} (result : Result)
    (next : Result → Execution C source target NextResult) :
    (pure source result).bind next = next result := by
  ext <;> simp

/-- Right unit of bind. -/
@[simp] theorem bind_pure {source target : C}
    (execution : Execution C source target Result) :
    execution.bind (pure target) = execution := by
  ext <;> simp

/-- Associativity of bind: associativity of running one after the other. -/
theorem bind_assoc {firstState secondState thirdState fourthState : C}
    (first : Execution C firstState secondState Result)
    (second : Result → Execution C secondState thirdState NextResult)
    (third : NextResult → Execution C thirdState fourthState FinalResult) :
    (first.bind second).bind third =
      first.bind fun result => (second result).bind third := by
  ext <;> simp

@[simp] theorem map_id {source target : C}
    (execution : Execution C source target Result) :
    execution.map id = execution := rfl

@[simp] theorem map_comp {source target : C} (first : Result → NextResult)
    (second : NextResult → FinalResult)
    (execution : Execution C source target Result) :
    (execution.map first).map second = execution.map (second ∘ first) := rfl

/-- Mapping is binding with a return. -/
theorem map_eq_bind {source target : C} (function : Result → NextResult)
    (execution : Execution C source target Result) :
    execution.map function =
      execution.bind fun result => pure target (function result) := by
  ext <;> simp

end Execution

/-- The executions of any category form a parameterized monad. -/
def executionParameterizedMonad (C : Type u) [Category.{v} C] :
    ParameterizedMonad.{u, w, max v w} C
      (fun source target Result => Execution C source target Result) where
  pure := Execution.pure
  bind := Execution.bind
  pure_bind := Execution.pure_bind
  bind_pure := Execution.bind_pure
  bind_assoc := Execution.bind_assoc

/-- An account of the runs of a category in a monoid: the empty run has the
unit account, and a composite run has the product of the two accounts, first
run first. -/
@[ext]
structure RunAccount (C : Type u) [Category.{v} C] (M : Type w) [Monoid M] where
  /-- The account of one run. -/
  of : {source target : C} → (source ⟶ target) → M
  of_id : ∀ state : C, of (𝟙 state) = 1
  of_comp : ∀ {source middle target : C}
    (first : source ⟶ middle) (second : middle ⟶ target),
    of (first ≫ second) = of first * of second

namespace RunAccount

open Mettapedia.CategoryTheory.WriterActionAdjunction

variable {C : Type u} [Category.{v} C] {M N : Type w} [Monoid M] [Monoid N]

attribute [simp] of_id of_comp

/-- Change the account monoid along a homomorphism. -/
def map (account : RunAccount C M) (change : M →* N) : RunAccount C N where
  of run := change (account.of run)
  of_id state := by rw [account.of_id, change.map_one]
  of_comp first second := by rw [account.of_comp, change.map_mul]

@[simp] theorem map_of (account : RunAccount C M) (change : M →* N)
    {source target : C} (run : source ⟶ target) :
    (account.map change).of run = change (account.of run) := rfl

/-- Keep two accounts side by side. -/
def prod (first : RunAccount C M) (second : RunAccount C N) :
    RunAccount C (M × N) where
  of run := (first.of run, second.of run)
  of_id state := by rw [first.of_id, second.of_id]; rfl
  of_comp left right := by rw [first.of_comp, second.of_comp]; rfl

/-- Read an account along a functor into the category it accounts for. -/
def comap {D : Type x} [Category.{y} D] (account : RunAccount C M)
    (functor : D ⥤ C) : RunAccount D M where
  of run := account.of (functor.map run)
  of_id state := by rw [functor.map_id, account.of_id]
  of_comp first second := by rw [functor.map_comp, account.of_comp]

@[simp] theorem comap_of {D : Type x} [Category.{y} D] (account : RunAccount C M)
    (functor : D ⥤ C) {source target : D} (run : source ⟶ target) :
    (account.comap functor).of run = account.of (functor.map run) := rfl

/-- The account that records nothing. -/
def trivial (C : Type u) [Category.{v} C] (M : Type w) [Monoid M] :
    RunAccount C M where
  of _ := 1
  of_id _ := rfl
  of_comp _ _ := (one_mul 1).symm

/-! ## Accounts are functors to a one-object category -/

/-- An account as a functor.  The one-object category of a monoid composes
its arrows in the order opposite to running, so the target is the opposite
monoid. -/
def toFunctor (account : RunAccount C M) : C ⥤ SingleObj Mᵐᵒᵖ where
  obj _ := SingleObj.star _
  map run := MulOpposite.op (account.of run)
  map_id state := by
    change MulOpposite.op (account.of (𝟙 state)) = 1
    rw [account.of_id]
    rfl
  map_comp first second := by
    change MulOpposite.op (account.of (first ≫ second)) =
      MulOpposite.op (account.of second) * MulOpposite.op (account.of first)
    rw [account.of_comp]
    rfl

/-- A functor to the one-object category of the opposite monoid is an
account. -/
def ofFunctor (functor : C ⥤ SingleObj Mᵐᵒᵖ) : RunAccount C M where
  of run := MulOpposite.unop (functor.map run)
  of_id state := by
    rw [functor.map_id]
    rfl
  of_comp first second := by
    rw [functor.map_comp]
    rfl

@[simp] theorem ofFunctor_toFunctor (account : RunAccount C M) :
    ofFunctor account.toFunctor = account := rfl

/-- In a commutative monoid the order of the product does not matter, and an
account is a functor to the one-object category of the monoid itself. -/
def toCommFunctor {M : Type w} [CommMonoid M] (account : RunAccount C M) :
    C ⥤ SingleObj M where
  obj _ := SingleObj.star _
  map run := account.of run
  map_id state := account.of_id state
  map_comp first second := by
    change account.of (first ≫ second) = account.of second * account.of first
    rw [account.of_comp, mul_comm]

/-! ## Reading the account of an execution -/

/-- Read the account of an execution: the account of its run, and its
result. -/
def read (account : RunAccount C M) {source target : C} {Result : Type w}
    (execution : Execution C source target Result) : (writerMonad M).obj Result :=
  (account.of execution.transition, execution.result)

variable (account : RunAccount C M) {Result NextResult : Type w}

/-- Returning has the unit account. -/
theorem read_pure (state : C) (result : Result) :
    account.read (Execution.pure state result) =
      (writerMonad M).η.app Result result := by
  change (account.of (𝟙 state), result) = (1, result)
  rw [account.of_id]

/-- Changing the returned value keeps the account. -/
theorem read_map {source target : C} (function : Result → NextResult)
    (execution : Execution C source target Result) :
    account.read (execution.map function) =
      (writerMonad M).map (TypeCat.ofHom function) (account.read execution) := rfl

/-- Binding multiplies the accounts, in the order of running. -/
theorem read_bind {source middle target : C}
    (first : Execution C source middle Result)
    (next : Result → Execution C middle target NextResult) :
    account.read (first.bind next) =
      (writerMonad M).μ.app NextResult
        ((writerMonad M).map
          (TypeCat.ofHom fun result => account.read (next result))
          (account.read first)) := by
  change (account.of (first.transition ≫ (next first.result).transition),
      (next first.result).result) =
    (account.of first.transition * account.of (next first.result).transition,
      (next first.result).result)
  rw [account.of_comp]

/-- Changing the account monoid after reading is reading the changed
account. -/
theorem read_map_account (change : M →* N) {source target : C}
    (execution : Execution C source target Result) :
    (account.map change).read execution =
      (Mettapedia.CategoryTheory.WriterActionTransport.freeMap change id).hom
        (account.read execution) := rfl

/-! ## Controls -/

/-- The account that records nothing reads every execution as a return. -/
theorem trivial_read {source target : C}
    (execution : Execution C source target Result) :
    (trivial C M).read execution =
      (writerMonad M).η.app Result execution.result := rfl

/-- No account charges the empty run: whatever is charged for doing nothing is
the unit. -/
theorem not_charges_empty_run (state : C) {charge : M} (nonunit : charge ≠ 1) :
    ¬ ∃ account : RunAccount C M, account.of (𝟙 state) = charge := by
  rintro ⟨account, charged⟩
  exact nonunit (charged.symm.trans (account.of_id state))

end RunAccount

end Mettapedia.Effects
