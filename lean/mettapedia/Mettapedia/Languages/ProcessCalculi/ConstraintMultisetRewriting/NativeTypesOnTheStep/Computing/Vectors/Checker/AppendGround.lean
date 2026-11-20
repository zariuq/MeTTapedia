import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NativeTypesOnTheStep.Computing.Vectors.Checker.Guarantee

/-!
# Every ground call of `append` answers, by induction

For every element type `A : U0` and all written-out vectors `xs`, `ys` of normal elements of `A`
(`written`, of the lengths `numeral |xs|`, `numeral |ys|`), the call `append A |xs| |ys| xs ys` of the
package's append (the eliminator program `appendTm`) **has exactly one answer, the written-out
`xs ++ ys`, typed at `vec A (add |xs| |ys|)` and typed-equal to the call there** (`append_ground`).

The proof is an induction on `xs`, not an evaluation:

* the nil case is two root steps of the package (`nil_reduces`): the eliminator at `zero`, then the
  unit recursor at `tt`;
* the cons case is the recursive equation of the program as a reduction (`cons_reduces`): the tree's
  reduction sequence of the cons equation in the context of its variables (`cons_reduces_open`),
  instantiated at closed terms (reduction is stable under substitution), then the induction hypothesis
  under the pair;
* the answer is normal because its elements are; it is the only one because the package is qualified,
  hence Church–Rosser; it is typed because reduction preserves typing on the qualified package.

The written-out call of today's witness is an instance (`append_ground_example`), and so is its
negative control (`append_ground_not_swapped`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace NativeTypesOnTheStep.Computing.Vectors.Checker

open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation TypedEquality TypedEquality.Normalization
open ConversionCoherence (StepStar)
open TowerVectorsModel (U0 numC zeroC succC ttC vecC addC)
open TowerVectorsPrograms (appendTm appendMotive appendMethod)
open ProgrammingOnTheStep.IndexedFamilies.Eliminator (level1 pkg D)
open ProgrammingOnTheStep.IndexedFamilies.ClosedCalls (one two three single twoThree)

/-! ## Written-out vectors -/

/-- A numeral of the numbers. -/
def numeral : Nat → Tower.Tm 0
  | 0 => zeroC
  | k + 1 => succC (numeral k)

/-- **A written-out vector**: `[]` is `tt`, `a :: rest` is `pair a rest`. -/
def written : List (Tower.Tm 0) → Tower.Tm 0
  | [] => ttC
  | a :: rest => .pair a (written rest)

/-- **The ground call** `append A |xs| |ys| xs ys`. -/
abbrev appendCall (A : Tower.Tm 0) (xs ys : List (Tower.Tm 0)) : Tower.Tm 0 :=
  appendTm A (numeral xs.length) (numeral ys.length) (written xs) (written ys)

theorem numeral_typed (k : Nat) : Typed pkg .nil (numeral k) numC := by
  induction k with
  | zero => exact D.zero_typed
  | succ k ih => exact D.succ_typed ih

theorem written_typed {A : Tower.Tm 0} (tA : Typed pkg .nil A U0) :
    ∀ {xs : List (Tower.Tm 0)}, (∀ a ∈ xs, Typed pkg .nil a A) →
      Typed pkg .nil (written xs) (vecC A (numeral xs.length))
  | [], _ => D.nil_typed tA
  | a :: rest, typed =>
      D.cons_typed tA (numeral_typed rest.length) (typed a (List.mem_cons_self ..))
        (written_typed tA fun b member => typed b (List.mem_cons_of_mem _ member))

theorem written_normal : ∀ {xs : List (Tower.Tm 0)}, (∀ a ∈ xs, ConstructorSystem.Normal pkg a) →
    ConstructorSystem.Normal pkg (written xs)
  | [], _ => const_normal level1 (by decide)
  | a :: rest, normal =>
      pair_normal level1 (normal a (List.mem_cons_self ..))
        (written_normal fun b member => normal b (List.mem_cons_of_mem _ member))

/-! ## The two equations of append as reductions -/

/-- **The nil equation**: `append A zero m tt ys` reaches `ys`, by two root steps. -/
theorem nil_reduces (A m ys : Tower.Tm 0) : Reduces pkg (appendTm A zeroC m ttC ys) ys :=
  .tail (.single (.root (TowerVectorsModel.elim_zero_step level1 A (appendMotive A m) ys appendMethod ttC)))
    (.root (TowerVectorsModel.unit_iota_step level1 _ _))

/-- **The cons equation, in the context of its variables**: the eliminator at `succ k`, four β-steps and
the two projections. -/
theorem cons_reduces_open : Reduces pkg TowerVectorsPrograms.consCall TowerVectorsPrograms.consResult := by
  refine .head (.root (TowerVectorsModel.elim_succ_step level1 (.var 5) (appendMotive (.var 5) (.var 3)) (.var 0)
    appendMethod (.var 4) (.pair (.var 2) (.var 1)))) ?_
  refine .head (.congAppFun (.congAppFun (.congAppFun (.betaPi _ _)))) ?_
  refine .head (.congAppFun (.congAppFun (.betaPi _ _))) ?_
  refine .head (.congAppFun (.betaPi _ _)) ?_
  refine .head (.betaPi _ _) ?_
  refine .head (.congPairFst (.betaSigmaFst _ _)) ?_
  refine .head (.congPairSnd (.congAppArg (.betaSigmaSnd _ _))) ?_
  exact .refl

/-- **The cons equation at closed terms**: `append A (succ k) m (pair a v) ys` reaches
`pair a (append A k m v ys)`. -/
theorem cons_reduces (A k m a v ys : Tower.Tm 0) :
    Reduces pkg (appendTm A (succC k) m (.pair a v) ys) (.pair a (appendTm A k m v ys)) :=
  Reduces.substitute (R := pkg) cons_reduces_open
    (consSub ys (consSub v (consSub a (consSub m (consSub k (consSub A fun i => Fin.elim0 i))))))

/-- **Every ground call reaches the written-out concatenation**, by induction on the first vector. -/
theorem append_reduces (A : Tower.Tm 0) :
    ∀ (xs ys : List (Tower.Tm 0)), Reduces pkg (appendCall A xs ys) (written (xs ++ ys))
  | [], _ => nil_reduces A _ _
  | a :: rest, ys =>
      (cons_reduces A _ _ a (written rest) (written ys)).trans
        (Reduces.congr (f := Tm.pair a) (fun step => .congPairSnd step) (append_reduces A rest ys))

/-! ## The answer -/

/-- The call is typed at its declared type `vec A (add |xs| |ys|)`. -/
theorem appendCall_typed {A : Tower.Tm 0} (tA : Typed pkg .nil A U0) {xs ys : List (Tower.Tm 0)}
    (typedXs : ∀ a ∈ xs, Typed pkg .nil a A) (typedYs : ∀ a ∈ ys, Typed pkg .nil a A) :
    Typed pkg .nil (appendCall A xs ys) (vecC A (addC (numeral xs.length) (numeral ys.length))) := by
  have m₀ : SubstMor pkg (.nil : Ctx Tower.Head 0) .nil fun i => Fin.elim0 i := fun i => Fin.elim0 i
  exact (TowerVectorsPrograms.append_typed level1).substitute
    (Normalization.SubstMor.cons (Normalization.SubstMor.cons (Normalization.SubstMor.cons
      (Normalization.SubstMor.cons (Normalization.SubstMor.cons m₀ tA) (numeral_typed xs.length))
      (numeral_typed ys.length)) (written_typed tA typedXs)) (written_typed tA typedYs))

/-- **Every ground call of `append` answers**: for all written-out vectors of normal elements of `A`,
the call has exactly one answer, the written-out concatenation, typed at `vec A (add |xs| |ys|)` and
typed-equal to the call there. -/
theorem append_ground {A : Tower.Tm 0} (tA : Typed pkg .nil A U0) {xs ys : List (Tower.Tm 0)}
    (typedXs : ∀ a ∈ xs, Typed pkg .nil a A) (typedYs : ∀ a ∈ ys, Typed pkg .nil a A)
    (normalXs : ∀ a ∈ xs, ConstructorSystem.Normal pkg a) (normalYs : ∀ a ∈ ys, ConstructorSystem.Normal pkg a) :
    Answer pkg (appendCall A xs ys) (written (xs ++ ys)) ∧
      (∀ v, Answer pkg (appendCall A xs ys) v ↔ v = written (xs ++ ys)) ∧
      Typed pkg .nil (written (xs ++ ys)) (vecC A (addC (numeral xs.length) (numeral ys.length))) ∧
      Equal pkg .nil (appendCall A xs ys) (written (xs ++ ys))
        (vecC A (addC (numeral xs.length) (numeral ys.length))) := by
  have normal : ∀ a ∈ xs ++ ys, ConstructorSystem.Normal pkg a := by
    intro a member
    rcases List.mem_append.mp member with inXs | inYs
    · exact normalXs a inXs
    · exact normalYs a inYs
  have answer : Answer pkg (appendCall A xs ys) (written (xs ++ ys)) :=
    ⟨append_reduces A xs ys, written_normal normal⟩
  obtain ⟨typed, equal⟩ := vectors_answer_typed level1 .nil (appendCall_typed tA typedXs typedYs) answer
  exact ⟨answer, fun v => ⟨fun other => vectors_answer_unique level1 other answer, fun same => same ▸ answer⟩,
    typed, equal⟩

/-! ## Controls -/

/-- **Today's witness is an instance**: `append num 1 1 [2] [3]` answers `[2, 3]`. -/
theorem append_ground_example : Answer pkg (appendCall numC [two] [three]) twoThree :=
  (append_ground D.num_typed (xs := [two]) (ys := [three])
    (fun a member => by
      obtain rfl := List.mem_singleton.mp member
      exact D.succ_typed (D.succ_typed D.zero_typed))
    (fun a member => by
      obtain rfl := List.mem_singleton.mp member
      exact D.succ_typed (D.succ_typed (D.succ_typed D.zero_typed)))
    (fun a member => by
      obtain rfl := List.mem_singleton.mp member
      exact succ_normal level1 (succ_normal level1 (const_normal level1 (by decide))))
    (fun a member => by
      obtain rfl := List.mem_singleton.mp member
      exact succ_normal level1 (succ_normal level1 (succ_normal level1 (const_normal level1 (by decide)))))).1

/-- **Negative control**: the swapped concatenation `[3, 2]` is not an answer. -/
theorem append_ground_not_swapped : ¬ Answer pkg (appendCall numC [two] [three]) (written [three, two]) := by
  intro answer
  have same := vectors_answer_unique level1 answer append_ground_example
  exact absurd same (by decide)

end NativeTypesOnTheStep.Computing.Vectors.Checker

#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.numeral_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.written_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.written_normal
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.nil_reduces
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.cons_reduces_open
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.cons_reduces
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_reduces
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.appendCall_typed
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_ground
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_ground_example
#print axioms NativeTypesOnTheStep.Computing.Vectors.Checker.append_ground_not_swapped

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
