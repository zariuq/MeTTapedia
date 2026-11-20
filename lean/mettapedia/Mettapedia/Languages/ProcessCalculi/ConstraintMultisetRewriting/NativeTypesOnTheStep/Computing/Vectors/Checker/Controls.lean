import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Acceptance

/-!
# Controls of elaboration and synthesis

**Elaboration agrees with today's hand-written rows.** The nil row of `append`, head's row and the
interpreter's literal row elaborate to the frames, made rows and declared types written by hand for the
audit (`RowsAfterMatch`, `ValueTypeRow`), with the function added as the oldest variable: every code is
today's, read one variable wider (`nil_agrees`, `head_agrees`, `lit_agrees`). The cons row's frame
binds the implicit length `k` after `m`, where today's binds it before; its codes differ by that order.

**Synthesis, shown** (`cons_synthesized`, `nil_synthesized`, `head_synthesized`, `lit_synthesized`): the
cons row's body `pair a (append A k m v ys)` gets `Σ A (vec A (add k m))`, its recursive call typed by
the function's declared type; the nil row's `ys` gets `vec A m`; head's `a` gets `A`; the literal row's `x`
gets `num`.

**Outside the elaborated class, not decided, never refused** (`pairHeads_undecided`,
`nested_undecided`, `sameLength_undecided`): two call indices, a nested `cons` pattern, and a frame
variable whose type mentions the call index. The elaboration does not build their frames, so the
checker does not decide them.

**Outside the refuted class, not decided, never admitted** (`swap_undecided`): the cons row with the
recursive call's vectors swapped. Its body is not synthesized, and the refutation reads variables,
constants and pairs, not applications.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC belowStepC)

/-! ## Agreement with today's rows -/

/-- An elaborated row's frame arity, raw frame, declared type and made code. -/
def shape {n : Nat} (e : Elaborated n) : Σ k : Nat, Ctx Tower.Head k × Tower.Tm k × Tower.Tm k :=
  ⟨e.frame.arity, e.frame.raw, e.made.type.code, e.made.code⟩

/-- **The nil row**: today's frame `A, m, ys, n` under the function, today's declared type and code. -/
theorem nil_agrees : (elaborate 16 appendDef nilRow).map shape =
    some ⟨5, .snoc (.snoc (.snoc (.snoc (.snoc .nil appendDef.type) U0) numC) (vecC (.var 1) (.var 0))) numC,
      rename Fin.castSucc Vectors.nilRow.type.code, rename Fin.castSucc Vectors.nilRow.code⟩ := by
  decide +kernel

/-- **head's row**: today's frame `A, k, a, w, n` under the function, today's declared type and code. -/
theorem head_agrees : (elaborate 16 headDef headRow).map shape =
    some ⟨6, .snoc (.snoc (.snoc (.snoc (.snoc (.snoc .nil headDef.type) U0) numC) (.var 1)) (vecC (.var 2) (.var 1)))
        numC,
      rename Fin.castSucc Vectors.headRow.type.code, rename Fin.castSucc Vectors.headRow.code⟩ := by
  decide +kernel

/-- **The literal row**: today's frame `x, code` under the function, today's declared type and code. -/
theorem lit_agrees : (elaborate 16 evalDef litRow).map shape =
    some ⟨3, .snoc (.snoc (.snoc .nil evalDef.type) numC) numC,
      rename Fin.castSucc Vectors.valRow.type.code, rename Fin.castSucc Vectors.valRow.code⟩ := by
  decide +kernel

/-! ## Synthesis, shown -/

/-- The synthesized type of an elaborated row's body, with the frame's arity. -/
def synthesizedType (fuel : Nat) (d : Definition) (r : Row) : Option (Σ k : Nat, Tower.Tm k) :=
  (elaborate fuel d r).bind fun e =>
    (synthesize fuel e.frame e.made.code).map fun s => ⟨e.frame.arity, s.1.code⟩

/-- **The cons row's body gets `Σ A (vec A (add k m))`**, in the frame `f, A, m, k, a, v, ys, n`. -/
theorem cons_synthesized :
    synthesizedType 16 appendDef consRow = some ⟨8, .sigma (.var 6) (vecC (.var 7) (addC (.var 5) (.var 6)))⟩ := by
  decide +kernel

/-- **The nil row's body gets `vec A m`.** -/
theorem nil_synthesized : synthesizedType 16 appendDef nilRow = some ⟨5, vecC (.var 3) (.var 2)⟩ := by
  decide +kernel

/-- **head's body gets `A`.** -/
theorem head_synthesized : synthesizedType 16 headDef headRow = some ⟨6, .var 4⟩ := by decide +kernel

/-- **The literal row's body gets `num`.** -/
theorem lit_synthesized : synthesizedType 16 evalDef litRow = some ⟨3, numC⟩ := by decide +kernel

/-- **konst's body gets nothing**: an abstraction. -/
theorem konst_not_synthesized : synthesizedType 16 konstDef konstRow = none := by decide +kernel

/-! ## Outside the elaborated class -/

/-- `pairHeads A n m (cons a v) (cons b w) = pair a b`: two call indices. -/
def pairHeadsDef : Definition :=
  ⟨"pairHeads", 5, TowerVectorsPrograms.appendCtx, .sigma (.var 4) (.var 5),
    [⟨[.var, .var, .var, .cons .var .var, .cons .var .var], 9, .pair (.var 4) (.var 1)⟩]⟩

/-- `second A n (cons a (cons b w)) = b`: a nested pattern. -/
def nestedDef : Definition :=
  ⟨"second", 3, headTelescope, .var 2, [⟨[.var, .var, .cons .var (.cons .var .var)], 7, .var 1⟩]⟩

/-- `rest A n (cons a v) ys = ys` with `ys : vec A n`: a frame type mentioning the call index. -/
def sameLengthDef : Definition :=
  ⟨"rest", 4, .snoc (.snoc (.snoc (.snoc .nil U0) numC) (vecC (.var 1) (.var 0))) (vecC (.var 2) (.var 1)),
    vecC (.var 3) (.var 2), [⟨[.var, .var, .cons .var .var, .var], 6, .var 0⟩]⟩

theorem pairHeads_unelaborated : rawPass pairHeadsDef (pairHeadsDef.rows.headD keepRow) = none := by decide +kernel
theorem nested_unelaborated : rawPass nestedDef (nestedDef.rows.headD keepRow) = none := by decide +kernel
theorem sameLength_unelaborated : rawPass sameLengthDef (sameLengthDef.rows.headD keepRow) = none := by decide +kernel

theorem pairHeads_undecided : checkDefinition 16 pairHeadsDef = .undecided := by decide +kernel
theorem nested_undecided : checkDefinition 16 nestedDef = .undecided := by decide +kernel
theorem sameLength_undecided : checkDefinition 16 sameLengthDef = .undecided := by decide +kernel

/-! ## Outside the refuted class -/

/-- The cons row with the recursive call's two vectors swapped:
`append A n m (cons a v) ys = pair a (append A k m ys v)`. -/
def swapRow : Row :=
  ⟨[.var, .var, .var, .cons .var .var, .var], 7,
    .pair (.var 2) (call5 (.var 7) (.var 6) (.var 3) (.var 4) (.var 0) (.var 1))⟩

def swapDef : Definition := ⟨"append", 5, TowerVectorsPrograms.appendCtx, appendResult, [nilRow, swapRow]⟩

/-- **The swapped call is not synthesized** (its arguments do not check against the declared type of the
function), and the refutation does not reach inside applications: **not decided**, and never admitted. -/
theorem swap_not_synthesized : synthesizedType 16 swapDef swapRow = none := by decide +kernel
theorem swap_undecided : checkDefinition 16 swapDef = .undecided := by decide +kernel

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nil_agrees
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_agrees
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.lit_agrees
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.cons_synthesized
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nil_synthesized
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_synthesized
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.lit_synthesized
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_not_synthesized
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.pairHeads_unelaborated
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nested_unelaborated
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.sameLength_unelaborated
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.pairHeads_undecided
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nested_undecided
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.sameLength_undecided
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.swap_not_synthesized
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.swap_undecided

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
