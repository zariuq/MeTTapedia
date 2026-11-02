import Mettapedia.OSLF.NativeTypes.GeneratedLogic.DependentJudgments
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.JudgmentControls

/-!
# Controls: dependent and parametric types on the coins

On the language of coins (sides `H` and `T`, `Toss ⇒ H`, `Toss ⇒ T`, `Show(s) ⇒ s`), each verdict from the front door
for dependent judgments (`askDep`) over the complete fibre of sides:

- **A refinement that mentions an earlier variable**: `x : Side, y : Side refined by is x ⊢ y : is x` is proved at
  four candidate valuations (`second_is_first`); without the refinement it is refuted at `y = T`
  (`second_not_first`). With `y` refined by `¬ is x`, `y : ¬ is x` is proved (`second_other`) and `y : is x`
  refuted (`second_other_not_first`).
- **A type that depends on a value**: `x : Side ⊢ Show(x) : ◇(is x)` is proved (`show_dependent`), while the fixed
  type `◇(is H)` is refuted at `Show(T)` (`show_not_heads`).
- **Π introduction from a judgment**: `x : Side ⊢ Toss : ◇(is x)` gives `Π x : Side. ◇(is x)` at `Toss`
  (`toss_pi_intro`), the product the front door's Π over the fibre also proves (`toss_each_dependent`); `Σ` likewise
  (`toss_some_dependent`), and `H` is not each side (`heads_not_each_dependent`).
- **Π elimination at a value**: from the product, `Toss` steps to `H` (`toss_steps_to_heads`).
- **Parametric types over the sides** (`askSortParam`), the parameter read with both polarities: determinism,
  `∀X ≤ Side. □X ∨ □¬X`, holds of `Show(H)` and of the stuck `H` at all four predicates (`show_heads_deterministic`,
  `heads_deterministic`) and fails of `Toss` at `X = {H}` (`toss_not_deterministic`), although its instances at
  `X = ∅` and `X = Side` both hold of `Toss` (`toss_extremes_hold`); eliminated at `is H` (`show_heads_at_heads`).
- **Covariant parametric types**, decided at their least instance (`askCovariantParam`): `□X` holds of `H` for every
  `X` (`heads_box_parametric`), and in particular `□(is T)` (`heads_box_tails`); `◇X` does not at `Toss`
  (`toss_diamond_not_parametric`), and `◇X ∨ ◇(is H)` does (`toss_either_parametric`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.DependentJudgmentControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open JudgmentControls (coins Coins fibres side heads tails toss showing stepsTo toss_each toss_some heads_not_each
  heads_value)

/-- The variables the families range over. -/
def first : Pattern := .fvar "x"
def second : Pattern := .fvar "y"

/-- The dependent judgment at the front door, four rounds. -/
def judge (context : DepContext) (formula : Formula 0) (term : Pattern) : JudgmentAnswer :=
  askDep RelationEnv.empty [] coins 2 none none 4 fibres context formula term

/-! ## Refinements that mention earlier variables -/

theorem second_is_first_answer :
    judge [("x", side, .top), ("y", side, .is first)] (.is first) second = .proved (.instances 4) := by
  decide +kernel

/-- **`x : Side, y : Side refined by is x ⊢ y : is x`.** -/
theorem second_is_first : DepHolds Coins [("x", side, .top), ("y", side, .is first)] (.is first) second :=
  askDep_proved second_is_first_answer

theorem second_not_first_answer :
    judge [("x", side, .top), ("y", side, .top)] (.is first) second = .refuted (.atInstance tails (.closedRegion 4)) := by
  decide +kernel

/-- **Without the refinement, `y : is x` fails**, at `x = H, y = T`. -/
theorem second_not_first : ¬ DepHolds Coins [("x", side, .top), ("y", side, .top)] (.is first) second :=
  askDep_refuted second_not_first_answer

theorem second_other_answer :
    judge [("x", side, .top), ("y", side, .isNot first)] (.isNot first) second = .proved (.instances 4) := by
  decide +kernel

/-- **`x : Side, y : Side refined by ¬ is x ⊢ y : ¬ is x`.** -/
theorem second_other : DepHolds Coins [("x", side, .top), ("y", side, .isNot first)] (.isNot first) second :=
  askDep_proved second_other_answer

theorem second_other_not_first_answer :
    judge [("x", side, .top), ("y", side, .isNot first)] (.is first) second =
      .refuted (.atInstance tails (.closedRegion 4)) := by
  decide +kernel

/-- **The other side is not the first.** -/
theorem second_other_not_first : ¬ DepHolds Coins [("x", side, .top), ("y", side, .isNot first)] (.is first) second :=
  askDep_refuted second_other_not_first_answer

/-! ## A type that depends on a value -/

theorem show_dependent_answer :
    judge [("x", side, .top)] (.possibly .any (.is first)) (showing first) = .proved (.instances 2) := by
  decide +kernel

/-- **`x : Side ⊢ Show(x) : ◇(is x)`**: what `Show(x)` steps to depends on `x`. -/
theorem show_dependent : DepHolds Coins [("x", side, .top)] (.possibly .any (.is first)) (showing first) :=
  askDep_proved show_dependent_answer

theorem show_not_heads_answer :
    judge [("x", side, .top)] (.possibly .any (.is heads)) (showing first) =
      .refuted (.atInstance (showing tails) (.closedRegion 4)) := by
  decide +kernel

/-- **The fixed type `◇(is H)` fails**, at `Show(T)`. -/
theorem show_not_heads : ¬ DepHolds Coins [("x", side, .top)] (.possibly .any (.is heads)) (showing first) :=
  askDep_refuted show_not_heads_answer

/-! ## Dependent products and sums -/

theorem stepsTo_at (value : Pattern) : (Formula.possibly .any (.is first)).«at» "x" value = stepsTo value := by
  simp [Formula.«at», Formula.substTerms, freeSubst, first, single, stepsTo]

theorem is_at (value : Pattern) : (Formula.is first).«at» "x" value = .is value := by
  simp [Formula.«at», Formula.substTerms, freeSubst, first, single]

theorem toss_judged_answer : judge [("x", side, .top)] (.possibly .any (.is first)) toss = .proved (.instances 2) := by
  decide +kernel

/-- **Π introduction**: `x : Side ⊢ Toss : ◇(is x)` gives `Π x : Side. ◇(is x)` at `Toss`. -/
theorem toss_pi_intro : DepPi Coins [] "x" side .top (.possibly .any (.is first)) toss :=
  depPi_intro (by simp [DepContext.names]) (fun _ member => nomatch member) rfl (by decide)
    (askDep_proved toss_judged_answer)

/-- **The same product from the front door's Π over the fibre.** -/
theorem toss_each_dependent : DepPi Coins [] "x" side .top (.possibly .any (.is first)) toss := by
  rw [depPi_nil_iff]
  simpa only [stepsTo_at] using toss_each

/-- **`Toss` steps to some side**, as a dependent sum. -/
theorem toss_some_dependent : DepSigma Coins [] "x" side .top (.possibly .any (.is first)) toss := by
  rw [depSigma_nil_iff]
  simpa only [stepsTo_at] using toss_some

/-- **`H` is not each side.** -/
theorem heads_not_each_dependent : ¬ DepPi Coins [] "x" side .top (.is first) heads := by
  rw [depPi_nil_iff]
  simpa only [is_at] using heads_not_each

/-- **Π elimination**: from the product, `Toss` steps to `H`. -/
theorem toss_steps_to_heads : Coins.sat Env.closed (stepsTo heads) toss := by
  have holds := depPi_elim (argument := heads) toss_pi_intro fun assignment valuation => by
    obtain rfl := (depValuation_nil_iff assignment).mp valuation
    simp only [freeSubst_fvar]
    exact ⟨heads_value.1, heads_value.2, trivial⟩
  have instance' := holds Pattern.fvar ((depValuation_nil_iff _).mpr rfl)
  rwa [stepsTo_at, freeSubst_fvar] at instance'

/-! ## Parametric types -/

/-- The discrete fibres of the constant sorts. -/
abbrev discreteFibres : (type : TypeExpr) → Option (DiscreteFibre Coins type) :=
  constantDiscreteFibres RelationEnv.empty coins (formsReading none)

/-- **`∀X ≤ Side. □X ∨ □¬X`**: every successor is in `X`, or every successor is outside it. -/
def deterministic : Formula 2 := .or (.necessarily .any (.var 0)) (.necessarily .any (.var 1))

/-- A parametric type over the sides at the front door, four rounds. -/
def judgeSides (formula : Formula 2) (term : Pattern) : JudgmentAnswer :=
  askSortParam RelationEnv.empty [] coins 2 none none 4 discreteFibres side formula term

theorem show_heads_deterministic_answer : judgeSides deterministic (showing heads) = .proved (.instances 4) := by
  decide +kernel

/-- **`Show(H)` is deterministic over the sides**: its one successor is in `X` or outside it, for each of the four
predicates. -/
theorem show_heads_deterministic : SortParamHolds Coins side deterministic (showing heads) :=
  askSortParam_proved show_heads_deterministic_answer

theorem heads_deterministic_answer : judgeSides deterministic heads = .proved (.instances 4) := by
  decide +kernel

/-- **`H` is deterministic**, having no successor. -/
theorem heads_deterministic : SortParamHolds Coins side deterministic heads :=
  askSortParam_proved heads_deterministic_answer

theorem toss_not_deterministic_answer :
    judgeSides deterministic toss = .refuted (.atPredicate [heads] (.closedRegion 4)) := by
  decide +kernel

/-- **`Toss` is not deterministic**, refuted at `X = {H}`. -/
theorem toss_not_deterministic : ¬ SortParamHolds Coins side deterministic toss :=
  askSortParam_refuted toss_not_deterministic_answer

theorem toss_least_answer :
    ask RelationEnv.empty [] coins 2 (deterministic.subst (polarSubst .bot)) toss none 4 none = .proved (.closedRegion 4) := by
  decide +kernel

theorem toss_greatest_answer :
    ask RelationEnv.empty [] coins 2 (deterministic.subst (polarSubst (.typed side))) toss none 4 none =
      .proved (.closedRegion 4) := by
  decide +kernel

/-- **The extreme instances do not decide it**: at `X = ∅` and at `X = Side` the type holds of `Toss`, which is not
deterministic. -/
theorem toss_extremes_hold :
    Coins.sat Env.closed (deterministic.subst (polarSubst .bot)) toss ∧
      Coins.sat Env.closed (deterministic.subst (polarSubst (.typed side))) toss :=
  ⟨ask_proved toss_least_answer, ask_proved toss_greatest_answer⟩

/-- **Elimination at a type of the sort**: `Show(H)` steps only into `is H`, or only outside it. -/
theorem show_heads_at_heads :
    Coins.sat Env.closed (deterministic.subst (polarSubst (.is heads))) (showing heads) :=
  sortParamHolds_instantiate show_heads_deterministic _ fun value named => by
    simp only [NativeStructure.sat] at named
    obtain rfl := (objectEquivalent_iff_eq_of_isEquationFree (by decide)).mp named.2
    exact heads_value

/-! ## Covariant parametric types -/

/-- A covariant parametric type at the front door, four rounds. -/
def judgeCovariant (formula : Formula 1) (term : Pattern) : Answer :=
  askCovariantParam RelationEnv.empty [] coins 2 none none 4 formula term

theorem heads_box_answer : judgeCovariant (.necessarily .any (.var 0)) heads = .proved (.closedRegion 4) := by
  decide +kernel

/-- **`□X` holds at `H` for every `X`**: it has no step. -/
theorem heads_box_parametric : CovariantParamHolds Coins (.necessarily .any (.var 0)) heads :=
  askCovariantParam_proved heads_box_answer

/-- **Its instance at `is T`.** -/
theorem heads_box_tails : Coins.sat Env.closed (.necessarily .any (.is tails)) heads :=
  covariantParamHolds_instantiate heads_box_parametric (.is tails)

theorem toss_diamond_answer : judgeCovariant (.possibly .any (.var 0)) toss = .refuted (.closedRegion 4) := by
  decide +kernel

/-- **`◇X` does not hold at `Toss` for every `X`**: no successor lies in the empty predicate. -/
theorem toss_diamond_not_parametric : ¬ CovariantParamHolds Coins (.possibly .any (.var 0)) toss :=
  askCovariantParam_refuted toss_diamond_answer

theorem toss_either_answer :
    judgeCovariant (.or (.possibly .any (.var 0)) (.possibly .any (.is heads))) toss = .proved (.exploration 4) := by
  decide +kernel

/-- **`◇X ∨ ◇(is H)` holds at `Toss` for every `X`**, through its second disjunct. -/
theorem toss_either_parametric :
    CovariantParamHolds Coins (.or (.possibly .any (.var 0)) (.possibly .any (.is heads))) toss :=
  askCovariantParam_proved toss_either_answer

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.DependentJudgmentControls
