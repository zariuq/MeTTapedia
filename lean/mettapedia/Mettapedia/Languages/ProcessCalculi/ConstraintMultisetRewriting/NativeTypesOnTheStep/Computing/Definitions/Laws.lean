import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Acceptance

/-!
# The laws of a definition by rows, each with its smallest counterexample

A definition by rows must give a term of its declared type, its rows as conversions, an unchanged
package, answers of ground calls at their types, and something later definitions can use. Each
condition of the class is needed for one of these; dropping it, the smallest counterexample:

* **Disjoint rows** (one row per case). `add zero m = m` beside `add zero m = zero`: **no term at all**
  meets both rows at the instance `m := 1`, because `1` and `zero` are distinct normal forms of a
  Church–Rosser conversion (`overlap_no_function`). The compiled addition meets the first
  (`addTerm_zero_row`).
* **Recursion on the predecessor.** `loop zero m = m` with `loop (succ k) m = loop (succ k) m`: the
  rows **do not determine the function**. The compiled addition and `λ n m. m` both meet both rows at
  every instance, and their calls at `1, zero` answer `1` and `zero` (`loop_rows_underdetermined`).
* **Rows typed after their match.** `append xs ys = xs` is refused by the row checker for every settler
  (`keep_refused_by_rows`). Compiled anyway, its ground call `append num 0 1 [] [3]` answers `[]`, which
  is not of the call's declared type `vec num (add 0 1)` (`keep_compiled_breaks`).
* **Covering rows.** `head` without a `nil` row, at the type `Π (A : U0) (n : num). vec A n → A`: a
  closed term of that type gives a closed term of the empty type, `h void zero nil`
  (`partial_head_inhabits_void`). So a definition whose rows do not cover is compiled over its own name,
  the uncovered calls left as they are, never closed by inventing an answer.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC voidC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one three single)
open Vectors (vecNormalize vecNormalize_sound const_normal succ_normal pair_normal)

/-! ## Disjoint rows -/

/-- `1` and `zero` are not convertible: distinct normal forms of a Church–Rosser conversion. -/
theorem one_not_zero : ¬ Conv pkg.headEq (one : Tower.Tm 0) zeroC pkg.computation := fun conversion => by
  have same := Vectors.vectors_eq_of_normal level1 (succ_normal level1 (const_normal level1 (by decide)))
    (const_normal level1 (by decide)) conversion
  cases same

/-- **Overlapping rows with different answers have no function**: no closed term converts, at the
call `zero, 1`, both to `1` (the first row) and to `zero` (the second). -/
theorem overlap_no_function (c : Tower.Tm 0)
    (first : Conv pkg.headEq (spine c [zeroC, one]) one pkg.computation)
    (second : Conv pkg.headEq (spine c [zeroC, one]) zeroC pkg.computation) : False :=
  one_not_zero (.trans _ _ _ (.symm _ _ first) second)

/-- **The positive control**: the compiled addition meets the first row at `zero, 1`. -/
theorem addTerm_zero_row : Conv pkg.headEq (spine addTerm [zeroC, one]) one pkg.computation :=
  joins_conv (fuel := 16) (by decide +kernel)

/-! ## Recursion on the predecessor -/

/-- `λ n m. m`. -/
def second : Tower.Tm 0 := .lam (.lam (.var 0))

/-- **Rows with a recursive call not on the predecessor do not determine the function**: the compiled
addition and `λ n m. m` both meet `loop zero m = m` at every instance (over `m`) and trivially
`loop (succ k) m = loop (succ k) m`, yet their calls at `1, zero` are not convertible. -/
theorem loop_rows_underdetermined :
    (∀ {k : Nat} (σ : Sub Tower.Head 1 k),
      Conv pkg.headEq (subst σ (spine (liftClosed addTerm) [zeroC, .var 0])) (subst σ (.var 0)) pkg.computation ∧
      Conv pkg.headEq (subst σ (spine (liftClosed second) [zeroC, .var 0])) (subst σ (.var 0)) pkg.computation) ∧
    (∀ {k : Nat} (t : Tower.Tm k), Conv pkg.headEq t t pkg.computation) ∧
    ¬ Conv pkg.headEq (spine addTerm [one, zeroC]) (spine second [one, zeroC]) pkg.computation := by
  refine ⟨fun σ => ⟨Conv.substitute σ (joins_conv (fuel := 16) (by decide +kernel)),
    Conv.substitute σ (joins_conv (fuel := 16) (by decide +kernel))⟩, fun t => .refl _, fun conversion => ?_⟩
  have toOne : Conv pkg.headEq (spine addTerm [one, zeroC]) one pkg.computation :=
    conv_of_stepStar (vecNormalize_sound level1 (fuel := 16) (by decide +kernel))
  have toZero : Conv pkg.headEq (spine second [one, zeroC]) zeroC pkg.computation :=
    conv_of_stepStar (vecNormalize_sound level1 (fuel := 16) (by decide +kernel))
  exact one_not_zero (.trans _ _ _ (.symm _ _ toOne) (.trans _ _ _ conversion toZero))

/-! ## Rows typed after their match -/

/-- The compiled `append xs ys = xs`: `λ A n m xs ys. xs`. -/
def keepTerm : Tower.Tm 0 := .lam (.lam (.lam (.lam (.lam (.var 1)))))

/-- **Compiled anyway, the row that is not typed after its match breaks the declared type**: its ground
call `append num 0 1 [] [3]` has the unique answer `[]`, the call's declared type is
`vec num (add 0 1)`, and `[]` is not of that type. -/
theorem keep_compiled_breaks :
    compile 0 Vectors.Checker.keepDef = some keepTerm ∧
      Answer pkg (spine keepTerm [numC, zeroC, one, ttC, single three]) ttC ∧
      subst (fun x : Fin 5 => ([numC, zeroC, one, ttC, single three] : List (Tower.Tm 0)).getD (4 - x.val) zeroC)
          Vectors.Checker.keepDef.result = vecC numC (addC zeroC one) ∧
      ¬ Typed pkg .nil ttC (vecC numC (addC zeroC one)) :=
  ⟨by decide +kernel, ⟨vecNormalize_sound level1 (fuel := 16) (by decide +kernel), const_normal level1 (by decide)⟩,
    by decide +kernel, Vectors.Checker.nil_not_length_one⟩

/-! ## Covering rows -/

/-- `Π (A : U0) (n : num). vec A n → A`. -/
def headPartialType : Tower.Tm 0 := .pi U0 (.pi numC (.pi (vecC (.var 1) (.var 0)) (.var 2)))

theorem void_typed : Typed pkg .nil voidC U0 := D.tower.small (by decide)

/-- **A partial definition cannot always be closed**: a closed term of `Π (A : U0) (n : num). vec A n →
A`, the type of `head` without its `nil` row, gives a closed term of the empty type. -/
theorem partial_head_inhabits_void {h : Tower.Tm 0} (typed : Typed pkg .nil h headPartialType) :
    Typed pkg .nil (spine h [voidC, zeroC, ttC]) voidC :=
  .appElim (.appElim (.appElim typed void_typed) D.zero_typed) (D.nil_typed void_typed)

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.one_not_zero
#print axioms NativeTypesOnTheStep.Computing.Definitions.overlap_no_function
#print axioms NativeTypesOnTheStep.Computing.Definitions.addTerm_zero_row
#print axioms NativeTypesOnTheStep.Computing.Definitions.loop_rows_underdetermined
#print axioms NativeTypesOnTheStep.Computing.Definitions.keep_compiled_breaks
#print axioms NativeTypesOnTheStep.Computing.Definitions.void_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.partial_head_inhabits_void

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
