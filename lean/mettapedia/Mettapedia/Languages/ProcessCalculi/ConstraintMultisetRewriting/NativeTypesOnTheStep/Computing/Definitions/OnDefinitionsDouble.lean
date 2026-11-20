import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.OnDefinitions

/-!
# Definitions on definitions: doubling a vector, over the append of step two

**Step three.** `double app A n xs = app A n n xs xs`, at `vec A (add n n)`, takes the append of step
two as its first parameter `app`, at append's declared type, and uses the exported addition by rows in
its own type. A later definition that uses an earlier one only through its declared type takes it as a
parameter: the row checker and the validation then see a variable, not the earlier compiled body.

* **The verdict** (`double_verdict`): a closed function, at budget 32, by kernel evaluation.
* **The function on the append of step two** is the application `doubleOnAppend = doubleTerm
  appendRTerm`: typed at `Π (A : U0) (n : num). vec A n → vec A (add n n)` by one application
  (`doubleOnAppend_typed`), and its row holds there as a conversion, at every instance, by the generic
  theorem at the instance `app := appendRTerm` (`doubleOnAppend_row`):
  `double A n xs ≡ append A n n xs xs`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)

/-- **Doubling over append is a closed function.** -/
theorem double_verdict : qualify 32 doubleDef = .function true := by decide +kernel

/-- Its compiled term is the abstraction of its row, typed at its declared type. -/
theorem doubleTerm_typed : Typed pkg .nil doubleTerm (liftClosed doubleDef.type) := by
  obtain ⟨c, checked⟩ := qualify_closed double_verdict
  obtain rfl : c = doubleTerm := Option.some.inj (checked.compiled.symm.trans double_compiles)
  exact checked.guarantee.1

/-- `Π (A : U0) (n : num). vec A n → vec A (add n n)`. -/
def doubleType : Tower.Tm 0 :=
  .pi U0 (.pi numC (.pi (vecC (.var 1) (.var 0)) (vecC (.var 2) (spine (liftClosed addExport) [.var 1, .var 1]))))

/-- **Doubling the append of step two.** -/
def doubleOnAppend : Tower.Tm 0 := .app doubleTerm appendRTerm

/-- **It is typed at `Π (A : U0) (n : num). vec A n → vec A (add n n)`**: one application of the
checked function to the checked append. -/
theorem doubleOnAppend_typed : Typed pkg .nil doubleOnAppend doubleType := by
  have typed : Typed pkg .nil doubleTerm (.pi (liftClosed appendRDef.type) (Presentation.rename wk doubleType)) :=
    doubleTerm_typed
  have applied := Derivable.appElim typed appendRTerm_typed
  have same : inst0 appendRTerm (Presentation.rename wk doubleType) = doubleType := by decide +kernel
  rw [same] at applied
  exact applied

/-- The row of `double`, its slots, and its two sides, by evaluation. -/
theorem double_shapes :
    shapesOf doubleDef = some [(doubleRow, false, [.param 0, .param 1, .param 2, .param 3])] := rfl

/-- The left side of `double`'s row: the compiled function applied to `app, A, n, xs`. -/
abbrev doubleLeft : Tower.Tm 4 := spine (Presentation.rename (shiftBase 0 4) doubleTerm) [.var 3, .var 2, .var 1, .var 0]

/-- The right side of `double`'s row: `app A n n xs xs`. -/
abbrev doubleRight : Tower.Tm 4 := spine (.var 3) [.var 2, .var 1, .var 1, .var 0, .var 0]

theorem double_lhs : lhs 0 doubleTerm doubleRow [.param 0, .param 1, .param 2, .param 3] false = some doubleLeft :=
  rfl

theorem double_rhs : rhs 0 doubleTerm doubleRow [.param 0, .param 1, .param 2, .param 3] false = doubleRight :=
  rfl

/-- **The row at every instance**, from the generic theorem: for every instance of `app, A, n, xs`,
`double app A n xs ≡ app A n n xs xs`. -/
theorem double_row {m : Nat} (σ : Sub Tower.Head 4 m) :
    Conv pkg.headEq (subst σ doubleLeft) (subst σ doubleRight) pkg.computation := by
  obtain ⟨c, checked⟩ := qualify_closed double_verdict
  obtain rfl : c = doubleTerm := Option.some.inj (checked.compiled.symm.trans double_compiles)
  obtain ⟨-, ⟨shapes, found, -, rows⟩, -⟩ := checked.guarantee
  rw [double_shapes] at found
  obtain rfl := Option.some.inj found
  obtain ⟨l, hl, conv⟩ := rows _ (List.mem_singleton_self _)
  rw [double_lhs] at hl
  obtain rfl := Option.some.inj hl
  have := conv σ
  rw [double_rhs] at this
  exact this

/-- The instance `app := appendRTerm`, the other variables kept. -/
def appendInstance : Sub Tower.Head 4 3 :=
  fun x => if h : x.val < 3 then .var ⟨x.val, h⟩ else liftClosed appendRTerm

/-- At the instance, the right side is `appendRTerm A n n xs xs`. -/
theorem appendInstance_right :
    subst appendInstance doubleRight = spine (liftClosed appendRTerm) [.var 2, .var 1, .var 1, .var 0, .var 0] := by
  decide +kernel

/-- **The row of doubling the append of step two**: over `A, n, xs`,
`doubleOnAppend A n xs ≡ appendRTerm A n n xs xs`, at every further instance. -/
theorem doubleOnAppend_row {m : Nat} (σ : Sub Tower.Head 3 m) :
    Conv pkg.headEq (subst σ (subst appendInstance doubleLeft))
      (subst σ (spine (liftClosed appendRTerm) [.var 2, .var 1, .var 1, .var 0, .var 0])) pkg.computation := by
  have base := double_row (fun x => subst σ (appendInstance x))
  rw [← subst_comp σ appendInstance, ← subst_comp σ appendInstance, appendInstance_right] at base
  exact base

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.double_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.doubleTerm_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.doubleOnAppend_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.double_shapes
#print axioms NativeTypesOnTheStep.Computing.Definitions.double_lhs
#print axioms NativeTypesOnTheStep.Computing.Definitions.double_rhs
#print axioms NativeTypesOnTheStep.Computing.Definitions.double_row
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendInstance_right
#print axioms NativeTypesOnTheStep.Computing.Definitions.doubleOnAppend_row

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
