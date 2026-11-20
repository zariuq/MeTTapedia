import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Source

/-!
# The definitions of the acceptance table, in the source form

* **`append`** (`appendDef`): `append : Π (A : U0) (n m : num). vec A n → vec A m → vec A (add n m)`,
  with the nil row `append A n m nil ys = ys` and the cons row
  `append A n m (cons a v) ys = pair a (append A k m v ys)`, `k` the implicit length of `cons`.
* **The shape real HE lets through** (`keepDef`): `append A n m xs ys = xs`.
* **The nil row answering nil** (`nilNilDef`): `append A n m nil ys = nil`, beside the cons row.
* **The cons row answering its first argument** (`consFirstDef`): `append A n m (cons a v) ys = cons a v`,
  beside the nil row; and **the nil row answering a pair** (`nilPairDef`): `append A n m nil ys = cons 0 nil`.
* **`head` on a successor length** (`headDef`): `head : Π (A : U0) (n : num). vec A n →
  below-step (λ _. A) n`, one row `head A n (cons a w) = a`.
* **The interpreter's literal row** (`evalDef`): `eval : Π (code : num). num → val code`, the row
  `eval zero x = x`, `val` computed by the recursor of the numbers at level one.
* **A body outside the synthesized class** (`konstDef`): `konst : Π (A : U0) (a : A). A → A`, the row
  `konst A a = λ _. a`: an abstraction carries no domain, so its type is not synthesized.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC belowStepC)

/-- The function applied to five arguments. -/
abbrev call5 {n : Nat} (f a b c d e : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app f a) b) c) d) e

/-! ## `append` -/

/-- The declared result type of append, `vec A (add n m)`, over `A, n, m, xs, ys`. -/
abbrev appendResult : Tower.Tm 5 := vecC (.var 4) (addC (.var 3) (.var 2))

/-- **The nil row**: `append A n m nil ys = ys`. Pattern variables `A, n, m, ys`. -/
def nilRow : Row := ⟨[.var, .var, .var, .nil, .var], 4, .var 0⟩

/-- **The cons row**: `append A n m (cons a v) ys = pair a (append A k m v ys)`. Pattern variables
`A, n, m, k, a, v, ys`; the function is variable 7. -/
def consRow : Row :=
  ⟨[.var, .var, .var, .cons .var .var, .var], 7,
    .pair (.var 2) (call5 (.var 7) (.var 6) (.var 3) (.var 4) (.var 1) (.var 0))⟩

/-- **The shape HE lets through**: `append A n m xs ys = xs`. -/
def keepRow : Row := ⟨[.var, .var, .var, .var, .var], 5, .var 1⟩

/-- **The nil row answering nil**: `append A n m nil ys = nil`. -/
def nilNilRow : Row := ⟨[.var, .var, .var, .nil, .var], 4, ttC⟩

/-- **The cons row answering its first argument**: `append A n m (cons a v) ys = cons a v`. -/
def consFirstRow : Row := ⟨[.var, .var, .var, .cons .var .var, .var], 7, .pair (.var 2) (.var 1)⟩

/-- **The nil row answering a pair**: `append A n m nil ys = cons 0 nil`. -/
def nilPairRow : Row := ⟨[.var, .var, .var, .nil, .var], 4, .pair zeroC ttC⟩

/-- **append**, two rows. -/
def appendDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx, appendResult, [nilRow, consRow]⟩

/-- `append` declared with the row HE lets through. -/
def keepDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx, appendResult, [keepRow]⟩

/-- `append` with the nil row answering nil, beside the cons row. -/
def nilNilDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx, appendResult, [nilNilRow, consRow]⟩

/-- `append` with the cons row answering its first argument, beside the nil row. -/
def consFirstDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx, appendResult, [nilRow, consFirstRow]⟩

/-- `append` with the nil row answering a pair, beside the cons row. -/
def nilPairDef : Definition :=
  ⟨"append", 5, TowerVectorsPrograms.appendCtx, appendResult, [nilPairRow, consRow]⟩

/-- The declared type of append is the type of the eliminator program of the tree. -/
theorem appendDef_type : appendDef.type = TowerVectorsPrograms.appendProgramType := rfl

/-! ## `head` -/

/-- The telescope `A : U0, n : num, v : vec A n`. -/
abbrev headTelescope : Ctx Tower.Head 3 := .snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))

/-- **head's cons row**: `head A n (cons a w) = a`. Pattern variables `A, n, k, a, w`. -/
def headRow : Row := ⟨[.var, .var, .cons .var .var], 5, .var 1⟩

/-- **head**, at the motive `below-step (λ _. A) n` of the call's length. -/
def headDef : Definition := ⟨"head", 3, headTelescope, belowStepC (.lam (.var 3)) (.var 1), [headRow]⟩

/-! ## The interpreter's literal row -/

/-- **The literal row**: `eval zero x = x`. Pattern variable `x`. -/
def litRow : Row := ⟨[.zero, .var], 1, .var 0⟩

/-- **eval**, at the value type `val code`. -/
def evalDef : Definition := ⟨"eval", 2, .snoc (.snoc .nil numC) numC, valC (.var 1), [litRow]⟩

/-! ## A body outside the synthesized class -/

/-- **konst's row**: `konst A a = λ _. a`. -/
def konstRow : Row := ⟨[.var, .var], 2, .lam (.var 1)⟩

/-- **konst**, at `A → A`. -/
def konstDef : Definition := ⟨"konst", 2, .snoc (.snoc .nil U0) (.var 0), .pi (.var 1) (.var 2), [konstRow]⟩

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.appendDef_type

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
