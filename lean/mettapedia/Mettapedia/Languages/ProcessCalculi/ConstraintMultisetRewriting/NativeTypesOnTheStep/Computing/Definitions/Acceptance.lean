import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Definitions.Development

/-!
# The acceptance table, by kernel evaluation and the generic theorem

Each verdict is a theorem by `decide +kernel`, at the budget written beside it; what it means is the
generic theorem (`qualify_function`, `qualify_closed`, `qualify_open`, `Checked.guarantee`) applied
to it, with no proof about the particular definition.

| definition | budget | verdict | meaning |
|---|---|---|---|
| addition by rows (`addDef`) | 16 | function, closed | `addTerm` typed at `num → num → num`, both rows conversions |
| `append` on the package's addition (`appendDef`) | 24 | function, closed | its compiled term typed at its type, both rows conversions |
| `head` on a successor length (`headDef`) | 16 | function, open | typed over its own name; the cons row a conversion; at length zero the call is the stuck call |
| the interpreter's literal row (`evalDef`) | 24 | function, open | typed over its own name; the literal row a conversion; at `succ k` the call is the stuck call |
| `map` with a function argument (`mapDef`) | 24 | function, closed | typed, both rows conversions |
| `append xs ys = xs` (`keepDef`) | 16 | refused, row 0 | the row checker's proved refusal, for every settler |
| two rows for `zero` (`overlapDef`) | 16 | not decided: outside the class | rows typed, but no one method per case |
| recursion not on the predecessor (`loopDef`) | 16 | not decided: outside the class | the call is no call of the hypothesis |
| a type that mentions the vector (`selfDef`) | 32 | not decided: rows | the naive compilation is not certified either (`self_naive_not_certified`) |
| addition by rows at budget 0 | 0 | not decided: rows | a budget that runs out decides nothing |

The two-step development (addition by rows, `append` on it, `concat3` on both) is in
`OnDefinitions`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Definitions

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (pkg)
open Vectors.Checker (appendDef headDef evalDef keepDef)

/-! ## The verdicts -/

/-- **Addition by rows is a closed function.** -/
theorem add_verdict : qualify 16 addDef = .function true := by decide +kernel

/-- **`append` is a closed function.** -/
theorem append_verdict : qualify 24 appendDef = .function true := by decide +kernel

/-- **`head` is a function over its own name**: its rows do not cover. -/
theorem head_verdict : qualify 16 headDef = .function false := by decide +kernel

/-- **The interpreter's literal row is a function over its own name.** -/
theorem eval_verdict : qualify 24 evalDef = .function false := by decide +kernel

/-- **`map` is a closed function.** -/
theorem map_verdict : qualify 24 mapDef = .function true := by decide +kernel

/-- **The shape HE lets through is refused**, at its only row. -/
theorem keep_verdict : qualify 16 keepDef = .refused 0 := by decide +kernel

/-- **Overlapping rows are outside the class.** -/
theorem overlap_verdict : qualify 16 overlapDef = .undecided .outside := by decide +kernel

/-- **Recursion not on the predecessor is outside the class.** -/
theorem loop_verdict : qualify 16 loopDef = .undecided .outside := by decide +kernel

/-- **A declared type mentioning the vector is not decided by the rows.** -/
theorem self_verdict : qualify 32 selfDef = .undecided .rows := by decide +kernel

/-- **A budget that runs out decides nothing.** -/
theorem add_budget : qualify 0 addDef = .undecided .rows := by decide +kernel

/-- **The naive compilation of `self` is not certified**: its `nil` method answers `refl nil` where the
vector is a variable of `vec A zero`, and the checker finds no typing at budget 64. -/
theorem self_naive_not_certified :
    (compile 0 selfDef).map (fun c => (typed? 64 .nil c (liftClosed selfDef.type)).isSome) = some false := by
  decide +kernel

/-! ## What the verdicts mean, by the generic theorem -/

/-- **The compiled addition is typed at addition's declared type.** -/
theorem addTerm_typed : Typed pkg .nil addTerm (liftClosed addDef.type) := by
  obtain ⟨c, checked⟩ := qualify_closed add_verdict
  obtain rfl : c = addTerm := Option.some.inj (checked.compiled.symm.trans add_compiles)
  exact checked.guarantee.1

/-- **Addition's rows hold as conversions at every instance**, by the generic theorem. -/
theorem add_rows : ∃ c, compile 0 addDef = some c ∧ Checked addDef 0 c := by
  obtain ⟨c, checked⟩ := qualify_closed add_verdict
  exact ⟨c, checked.compiled, checked⟩

/-- **`append`, `map`: closed checked functions.** -/
theorem append_checked : ∃ c, Checked appendDef 0 c := qualify_closed append_verdict

theorem map_checked : ∃ c, Checked mapDef 0 c := qualify_closed map_verdict

/-- **`head`, the literal row: checked functions over their own name.** -/
theorem head_checked : ∃ c, Checked headDef 1 c := qualify_open head_verdict

theorem eval_checked : ∃ c, Checked evalDef 1 c := qualify_open eval_verdict

/-- **The refusal is the row checker's.** -/
theorem keep_refused_by_rows : Vectors.Checker.checkDefinition 16 keepDef = .refused 0 :=
  qualify_refused keep_verdict

end NativeTypesOnTheStep.Computing.Definitions

#print axioms NativeTypesOnTheStep.Computing.Definitions.add_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.append_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.head_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.eval_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.map_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.keep_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.overlap_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.loop_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.self_verdict
#print axioms NativeTypesOnTheStep.Computing.Definitions.add_budget
#print axioms NativeTypesOnTheStep.Computing.Definitions.self_naive_not_certified
#print axioms NativeTypesOnTheStep.Computing.Definitions.addTerm_typed
#print axioms NativeTypesOnTheStep.Computing.Definitions.add_rows
#print axioms NativeTypesOnTheStep.Computing.Definitions.append_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.map_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.head_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.eval_checked
#print axioms NativeTypesOnTheStep.Computing.Definitions.keep_refused_by_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
