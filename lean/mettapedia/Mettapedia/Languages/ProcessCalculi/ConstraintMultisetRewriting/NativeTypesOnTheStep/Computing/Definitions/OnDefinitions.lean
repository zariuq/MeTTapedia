import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Acceptance

/-!
# Definitions on definitions: append on the addition by rows

A checked function is a term of the package, so the checker runs over a later definition that uses it
with nothing generalized: the package, the row checker and the validation are the same.

* **Step one**: addition by rows is a closed function (`add_verdict`), exported as `addExport`.
* **Step two**: `append`, its declared type `vec A (add n m)` written with the exported addition, is a
  closed function (`appendR_checked`). Its `cons` row is typed because addition's own `succ` row
  computes in the type: `vec A (add (succ k) m)` and `Σ A (vec A (add k m))` convert
  (`appendR_type_computes`).
* **Step three**, `double` on this `append`, is in `OnDefinitionsDouble`.

Steps two and three are checked **component by component** (`Checked`), one kernel evaluation per
component, each with its own budget: one evaluation of a whole verdict exceeds the memory the gate
allows. The guarantee is the same generic theorem (`Checked.guarantee`).

| definition | rows admitted | compiled | typed | rows convert |
|---|---|---|---|---|
| `append` on addition by rows | budget 32 | `appendR_compiles` | budget 40 | budget 24 |
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)

theorem appendR_rows_admitted : Vectors.Checker.checkDefinition 32 appendRDef = .admitted := by
  decide +kernel

theorem appendR_typed_certified :
    (typed? 40 (baseCtx appendRDef 0) appendRTerm (liftClosed appendRDef.type)).isSome = true := by
  decide +kernel

theorem appendR_rows_convert : rowsConvert 24 0 appendRDef appendRTerm = true := by decide +kernel

theorem appendR_stuck : stuckConvert 0 0 appendRDef appendRTerm = true := by decide +kernel

/-- **`append` on the addition by rows is a closed checked function.** -/
theorem appendR_checked : Checked appendRDef 0 appendRTerm :=
  ⟨appendR_covers.symm, ⟨32, appendR_rows_admitted⟩, appendR_compiles, ⟨40, appendR_typed_certified⟩,
    ⟨24, appendR_rows_convert⟩, ⟨0, appendR_stuck⟩⟩

/-- **Its compiled term is typed at its declared type**, which mentions the addition by rows. -/
theorem appendRTerm_typed : Typed pkg .nil appendRTerm (liftClosed appendRDef.type) :=
  appendR_checked.guarantee.1

/-- **The addition by rows computes in the type of `append`'s `cons` row**:
`vec A (add (succ k) m)` and `Σ A (vec A (add k m))` convert, over `A, k, m`. -/
theorem appendR_type_computes :
    Conv pkg.headEq
      (vecC (.var 2) (spine (liftClosed addExport) [succC (.var 1), .var 0]) : Tower.Tm 3)
      (.sigma (.var 2) (vecC (.var 3) (spine (liftClosed addExport) [.var 2, .var 1]))) pkg.computation :=
  joins_conv (fuel := 24) (by decide +kernel)

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_rows_admitted
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_typed_certified
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_rows_convert
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_stuck
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendRTerm_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.appendR_type_computes

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
