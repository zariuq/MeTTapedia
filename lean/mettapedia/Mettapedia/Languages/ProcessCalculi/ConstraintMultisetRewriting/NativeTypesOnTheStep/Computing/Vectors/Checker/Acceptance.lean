import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Laws

/-!
# The acceptance table, by kernel evaluation

The checker's verdicts at budget 16, each a theorem by `decide +kernel`:

| definition | verdict | why |
|---|---|---|
| `append`, nil and cons rows (`appendDef`) | admitted | `n ≐ zero` gives `vec A (add zero m) ≡ vec A m`; `n ≐ succ k` gives `vec A (add (succ k) m) ≡ Σ A (vec A (add k m))`, the pair's synthesized type, the recursive call typed by the function's declared type |
| `append xs ys = xs` (`keepDef`) | refused, row 0 | `vec A n` and `vec A (add n m)` are neutral with last arguments of different heads |
| nil row answering nil (`nilNilDef`) | refused, row 0 | at `n ↦ zero` the type is `vec A m`, neutral; `nil : unit` is an inductive type |
| cons row answering its first argument (`consFirstDef`) | refused, row 1 | componentwise against `Σ A (vec A (add k m))`: `v : vec A k` |
| nil row answering a pair (`nilPairDef`) | refused, row 0 | a pair has no type at the stuck `vec A m` |
| `head` on a successor length (`headDef`) | admitted | `below-step (λ _. A) (succ k) ≡ A` |
| the interpreter's literal row (`evalDef`) | admitted | `val zero ≡ num`, a large elimination |
| `konst A a = λ _. a` (`konstDef`) | not decided | an abstraction has no synthesized type |

**Each verdict means what the soundness theorems say**: the admitted rows are admitted by the computable
converting step and typed after their match (`append_rows`, `head_rows`, `eval_rows`); the refused rows
are refused for every settler (`keep_every_settler`, `nilNil_every_settler`); the procedure gives the
same verdicts from budget 16 on (`append_procedure`, ...). **Not decided is honest**: konst's row is typed
in its own frame, so every settler's converting step admits it (`konst_every_settler`); a refusal would be
false. **A budget that runs out decides nothing** (`append_budget`).

The shapes are those of the three definitions measured on real HE today, which accepts `append xs ys =
xs`, refuses the correct cons row, and refuses the nil row answering nil. The Lean object is the
checker over this package, not a model of HE.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open _root_.CategoryTheory Interface
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization TypedContextual
open ContextualDependentEta
open Interface.DependentFull (Make State Firing enabled_iff)
open UnificationWithLevels.TreeFibre.Budgets (Procedure Decider)
open TowerVectorsModel (U0)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)

/-! ## The verdicts -/

/-- **`append` is admitted.** -/
theorem append_admitted : checkDefinition 16 appendDef = .admitted := by decide +kernel

/-- **The shape HE lets through is refused**, at its only row. -/
theorem keep_refused : checkDefinition 16 keepDef = .refused 0 := by decide +kernel

/-- **The nil row answering nil is refused**, at row 0. -/
theorem nilNil_refused : checkDefinition 16 nilNilDef = .refused 0 := by decide +kernel

/-- **The cons row answering its first argument is refused**, at row 1: componentwise, `v : vec A k` is
not of `vec A (add k m)`. -/
theorem consFirst_refused : checkDefinition 16 consFirstDef = .refused 1 := by decide +kernel

/-- **The nil row answering a pair is refused**, at row 0: at `n ↦ zero` the type is `vec A m`, stuck. -/
theorem nilPair_refused : checkDefinition 16 nilPairDef = .refused 0 := by decide +kernel

/-- **`head` on a successor length is admitted.** -/
theorem head_admitted : checkDefinition 16 headDef = .admitted := by decide +kernel

/-- **The interpreter's literal row is admitted.** -/
theorem eval_admitted : checkDefinition 16 evalDef = .admitted := by decide +kernel

/-- **A body outside the synthesized class is not decided.** -/
theorem konst_undecided : checkDefinition 16 konstDef = .undecided := by decide +kernel

/-- **A budget that runs out decides nothing.** -/
theorem append_budget : checkDefinition 0 appendDef = .undecided := by decide +kernel

/-! ## What the verdicts mean -/

/-- **append's rows are admitted by the computable converting step and typed after their match.** -/
theorem append_rows : ∀ r ∈ appendDef.rows, ∃ e, elaborate 16 appendDef r = some e ∧
    (convertingStep vecS.levels Nat (vecSettler 16 16)).Admits e.firing ∧
      TypedAfterMatch vecS.levels e.tells e.made :=
  checkDefinition_admitted append_admitted

theorem head_rows : ∀ r ∈ headDef.rows, ∃ e, elaborate 16 headDef r = some e ∧
    (convertingStep vecS.levels Nat (vecSettler 16 16)).Admits e.firing ∧
      TypedAfterMatch vecS.levels e.tells e.made :=
  checkDefinition_admitted head_admitted

theorem eval_rows : ∀ r ∈ evalDef.rows, ∃ e, elaborate 16 evalDef r = some e ∧
    (convertingStep vecS.levels Nat (vecSettler 16 16)).Admits e.firing ∧
      TypedAfterMatch vecS.levels e.tells e.made :=
  checkDefinition_admitted eval_admitted

/-- **The row HE lets through is refused for every settler.** -/
theorem keep_every_settler : ∃ r, keepDef.rows[0]? = some r ∧ ∃ e, elaborate 16 keepDef r = some e ∧
    ∀ settler : Settler vecS.levels, ¬ (convertingStep vecS.levels Nat settler).Admits e.firing :=
  checkDefinition_refused keep_refused

/-- **The nil row answering nil is refused for every settler.** -/
theorem nilNil_every_settler : ∃ r, nilNilDef.rows[0]? = some r ∧ ∃ e, elaborate 16 nilNilDef r = some e ∧
    ∀ settler : Settler vecS.levels, ¬ (convertingStep vecS.levels Nat settler).Admits e.firing :=
  checkDefinition_refused nilNil_refused

theorem consFirst_every_settler : ∃ r, consFirstDef.rows[1]? = some r ∧ ∃ e, elaborate 16 consFirstDef r = some e ∧
    ∀ settler : Settler vecS.levels, ¬ (convertingStep vecS.levels Nat settler).Admits e.firing :=
  checkDefinition_refused consFirst_refused

theorem nilPair_every_settler : ∃ r, nilPairDef.rows[0]? = some r ∧ ∃ e, elaborate 16 nilPairDef r = some e ∧
    ∀ settler : Settler vecS.levels, ¬ (convertingStep vecS.levels Nat settler).Admits e.firing :=
  checkDefinition_refused nilPair_refused

/-- **The procedure's verdicts, from budget 16 on.** -/
theorem append_procedure : ∀ k, 16 ≤ k → procedure.verdict k appendDef = .equal :=
  procedure_of_admitted append_admitted

theorem keep_procedure : ∀ k, 16 ≤ k → procedure.verdict k keepDef = .different :=
  procedure_of_refused keep_refused

theorem nilNil_procedure : ∀ k, 16 ≤ k → procedure.verdict k nilNilDef = .different :=
  procedure_of_refused nilNil_refused

theorem head_procedure : ∀ k, 16 ≤ k → procedure.verdict k headDef = .equal :=
  procedure_of_admitted head_admitted

theorem eval_procedure : ∀ k, 16 ≤ k → procedure.verdict k evalDef = .equal :=
  procedure_of_admitted eval_admitted

/-! ## Not decided is honest: konst's row is typed in its own frame -/

/-- The raw pass of konst's row: the function, `A : U0`, `a : A`; no call index. -/
def konstAcc : Acc :=
  ⟨3, .snoc (.snoc (.snoc .nil konstDef.type) U0) (.var 0), [some (.var 0), some (.var 1)],
    [some 0, some 1], none⟩

theorem konst_raw : rawPass konstDef konstRow = some konstAcc := by decide

/-- **konst's row is typed in its frame**, at every budget it elaborates. -/
theorem konst_typed_in_frame {fuel : Nat} {e : Elaborated konstDef.arity}
    (elaborated : elaborate fuel konstDef konstRow = some e) : e.made.WellTyped := by
  obtain ⟨pos, formed, l, rfl⟩ := elaborate_plain elaborated konst_raw rfl
  show Typed pkg (.snoc (.snoc (.snoc .nil konstDef.type) U0) (.var 0) : Ctx Tower.Head 3) (.lam (.var 1))
    (.pi (.var 1) (.var 2))
  exact .lamIntro (D.tower.pi_small (Derivable.var 1) (Derivable.var 2)) (D.tower.isUniverse _) (Derivable.var 1)

/-- **So the present step admits it**, and with it every settler's converting step. -/
theorem konst_present {fuel : Nat} {e : Elaborated konstDef.arity}
    (elaborated : elaborate fuel konstDef konstRow = some e) : (DependentFull.step vecS.levels Nat).Admits e.firing := by
  have typed := konst_typed_in_frame elaborated
  obtain ⟨pos, formed, l, rfl⟩ := elaborate_plain elaborated konst_raw rfl
  refine ⟨⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, fun m member => ?_⟩,
    (enabled_iff _).mpr ⟨fun _ member => absurd member List.not_mem_nil,
      fun _ member => absurd member List.not_mem_nil, fun _ member => absurd member List.not_mem_nil,
      fun o _ inside => Finset.notMem_empty o inside⟩,
    ⟨_, 𝟙 _, Frames.models_nil _⟩, fun _ _ _ => ⟨Frames.models_nil _, fun _ member => absurd member List.not_mem_nil⟩⟩
  obtain rfl := List.mem_singleton.mp member
  exact typed

theorem konst_every_settler {fuel : Nat} {e : Elaborated konstDef.arity}
    (elaborated : elaborate fuel konstDef konstRow = some e) (settler : Settler vecS.levels) :
    (convertingStep vecS.levels Nat settler).Admits e.firing :=
  converting_admits_of_admits vecS.levels settler (konst_present elaborated)

/-- **konst's row elaborates at budget 16**, so the honesty control is not vacuous. -/
theorem konst_elaborates : (elaborate 16 konstDef konstRow).isSome = true := by decide +kernel

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keep_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nilNil_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.consFirst_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nilPair_refused
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.consFirst_every_settler
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nilPair_every_settler
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.eval_admitted
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_undecided
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_budget
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_rows
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_rows
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.eval_rows
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keep_every_settler
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nilNil_every_settler
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_procedure
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.keep_procedure
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nilNil_procedure
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.head_procedure
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.eval_procedure
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_raw
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_typed_in_frame
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_present
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_every_settler
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.konst_elaborates

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
