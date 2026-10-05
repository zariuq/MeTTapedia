import Mettapedia.GSLT.Distinction.ProductionLicences
import Mettapedia.GSLT.Distinction.ProductiveBlocks
import Mettapedia.GSLT.Dynamics.WeightedResumptionControls
import Mathlib.Algebra.Tropical.Basic
import Mathlib.Data.ZMod.Defs

/-!
# Controls for production licences

* **`AA/BB` against the spurious `AB/BA` of resampling** (`aa_bb_control`).
  Sharing two productions `A` and `B` used twice gives `AA` and `BB`, each with
  one factor; resampling adds `AB` and `BA` and squares the coefficients.  With
  matrix coefficients `AB` and `BA` even differ from each other, while with
  counts they agree (`ab_ba_matrix_order`).
* **A single pure answer** (`single_answer_control`).  The ordered law licenses
  resampling it; the ledgers differ (one production against two); Boolean
  coefficients license it on coefficients, counts and tropical costs do not.
* **An unused effect or fault** (`unused_effect_control`,
  `unused_fault_control`, `unused_zero_annihilates`).  Eager evaluation of an
  unused computation commits its effect or fault and charges its production;
  lazy evaluation does neither.  An unused zero production annihilates the
  eager count.
* **Zero and equal values** (`zero_retains_occurrence`,
  `equal_values_distinct_factors`).  A zero coefficient keeps its occurrence and
  its factor, where a value-indexed aggregate cannot tell it from absence; two
  productions of the same value with different identities are two factors.
* **Resumed pending production under nested scopes**
  (`resumed_production_nested_scopes`, `restart_charges_twice`).  A production
  pending at a pause completes inside a nested scope after resumption: the
  inner scope claims it, the outer scope sees the earlier production, and each
  is charged once.  Restarting instead of resuming charges the first production
  twice and is refused by the ledger.
* **Noncommutative coefficients** (`movesPast_positive`, `movesPast_negative`).
  An upper triangular production moves past its own square: eager and lazy
  agree; it does not move past a lower triangular factor.
* **Coefficients are not weights** (`coefficient_not_a_weight`,
  `bag_is_unit_count`).  Two coefficient draws with the same erasure are at the
  same weighted distance under every choice of weights, while their count
  aggregates differ; at unit coefficients the aggregate is the bag count.
-/

set_option autoImplicit false
-- Deciding equality of traces of uses needs a larger instance search.
set_option synthInstance.maxSize 1024

namespace Mettapedia.GSLT.Distinction.ProductionLicences.Controls

open Mettapedia.GSLT.Dynamics.OrderedDemand
open Mettapedia.Algebra.SharedCoefficientLedger (Factor Ledger Valid denote identities Scoped)
open Mettapedia.GSLT.Distinction.ProductionLicences

/-- Two values. -/
inductive Letter where
  | A
  | B
  deriving DecidableEq

/-- A production with identity, value and coefficient. -/
def produce {V : Type} (identity : ℕ) (letter : Letter) (coefficient : V) : Factor ℕ Letter V :=
  ⟨identity, letter, coefficient⟩

/-! ## `AA/BB` against `AB/BA` -/

/-- The bound computation answers `A` (coefficient `a`) and `B` (coefficient `b`). -/
def twoProductions {V : Type} (a b : V) : Trace (Factor ℕ Letter V) Unit Unit :=
  [.answer (produce 1 .A a), .answer (produce 2 .B b)]

/-- **`AA/BB` against the spurious `AB/BA`.** -/
theorem aa_bb_control :
    (answers (lazyUses 2 (twoProductions (2 : ℕ) 3))).map Prod.fst = [[.A, .A], [.B, .B]] ∧
      (answers (resampledUses 2 (twoProductions (2 : ℕ) 3))).map Prod.fst =
        [[.A, .A], [.A, .B], [.B, .A], [.B, .B]] ∧
      answers (coefficients (lazyUses 2 (twoProductions (2 : ℕ) 3))) = [([.A, .A], 2), ([.B, .B], 3)] ∧
      answers (coefficients (resampledUses 2 (twoProductions (2 : ℕ) 3))) =
        [([.A, .A], 4), ([.A, .B], 6), ([.B, .A], 6), ([.B, .B], 9)] ∧
      (answers (lazyUses 2 (twoProductions (2 : ℕ) 3))).map (fun use => use.2.length) = [1, 1] ∧
      (answers (resampledUses 2 (twoProductions (2 : ℕ) 3))).map (fun use => use.2.length) =
        [2, 2, 2, 2] := by
  decide

open Mettapedia.GSLT.Dynamics.WeightedResumptionControls (TwoByTwo upper lower
  matrix_composition_is_ordered)

/-- **Under resampling, `AB` and `BA` carry the coefficients in their order**:
with matrices they differ. -/
theorem ab_ba_matrix_order :
    (answers (coefficients (resampledUses 2 (twoProductions upper lower)))).map Prod.snd =
        [upper * upper, upper * lower, lower * upper, lower * lower] ∧
      upper * lower ≠ lower * upper := by
  refine ⟨?_, matrix_composition_is_ordered⟩
  simp [resampledUses, resampledFrom, twoProductions, coefficients, answers, Event.bind,
    Event.mapAnswer, Event.answer?, denote, drawnAt, produce]

/-! ## A single pure answer -/

/-- One production of `A`. -/
def single {V : Type} (c : V) : Trace (Factor ℕ Letter V) Unit Unit := [.answer (produce 1 .A c)]

/-- **The ordered law licenses resampling one pure answer; the ledgers do not.**
Boolean coefficients (the multiplicative monoid of `ZMod 2`) license it on
coefficients; counts and tropical costs do not. -/
theorem single_answer_control :
    lazyTrace 2 (values (single (2 : ℕ))) = resampledTrace 2 (values (single (2 : ℕ))) ∧
      lazyUses 2 (single (2 : ℕ)) ≠ resampledUses 2 (single (2 : ℕ)) ∧
      coefficients (lazyUses 2 (single (1 : ZMod 2))) =
        coefficients (resampledUses 2 (single (1 : ZMod 2))) ∧
      coefficients (lazyUses 2 (single (2 : ℕ))) ≠ coefficients (resampledUses 2 (single (2 : ℕ))) ∧
      coefficients (lazyUses 2 (single (Tropical.trop (3 : WithTop ℕ)))) ≠
        coefficients (resampledUses 2 (single (Tropical.trop (3 : WithTop ℕ)))) := by
  refine ⟨by decide, ?_, ?_, ?_, ?_⟩
  · rw [Ne, lazyUses_eq_resampledUses_iff]
    simp [single, answers, Event.answer?]
  · exact (coefficients_lazy_eq_resampled_iff 2 _).mpr (Or.inr (Or.inr ⟨_, rfl, by decide⟩))
  · rw [Ne, coefficients_lazy_eq_resampled_iff]
    rintro (few | none | ⟨production, same, power⟩)
    · omega
    · simp [single, answers, Event.answer?] at none
    · simp only [single, List.cons.injEq, Event.answer.injEq, and_true] at same
      subst same
      simp [produce] at power
  · rw [Ne, coefficients_lazy_eq_resampled_iff]
    rintro (few | none | ⟨production, same, power⟩)
    · omega
    · simp [single, answers, Event.answer?] at none
    · simp only [single, List.cons.injEq, Event.answer.injEq, and_true] at same
      subst same
      revert power
      decide

/-! ## Unused effects and faults -/

/-- **An unused effect**: eager evaluation commits it and charges the
production; lazy evaluation does neither. -/
theorem unused_effect_control :
    eagerUses 0 ([.effect (), .answer (produce 1 .A (2 : ℕ))] : Trace (Factor ℕ Letter ℕ) Unit Unit) =
        [.effect (), .answer ([], [drawnAt [] (produce 1 .A 2)])] ∧
      lazyUses 0 ([.effect (), .answer (produce 1 .A (2 : ℕ))] : Trace (Factor ℕ Letter ℕ) Unit Unit) =
        [.answer ([], [])] := by
  decide

/-- **An unused fault**, likewise. -/
theorem unused_fault_control :
    eagerUses 0 ([.fault (), .answer (produce 1 .A (2 : ℕ))] : Trace (Factor ℕ Letter ℕ) Unit Unit) =
        [.fault (), .answer ([], [drawnAt [] (produce 1 .A 2)])] ∧
      lazyUses 0 ([.fault (), .answer (produce 1 .A (2 : ℕ))] : Trace (Factor ℕ Letter ℕ) Unit Unit) =
        [.answer ([], [])] := by
  decide

/-- **An unused zero production annihilates the eager count**, and an unused
unit production is discardable on coefficients. -/
theorem unused_zero_annihilates :
    coefficients (eagerUses 0 (single (0 : ℕ))) = [.answer ([], 0)] ∧
      coefficients (lazyUses 0 (single (0 : ℕ))) = [.answer ([], 1)] ∧
      coefficients (eagerUses 0 (single (1 : ℕ))) = coefficients (lazyUses 0 (single (1 : ℕ))) :=
  ⟨by decide, by decide, (coefficients_eager_eq_lazy_zero_iff _).mpr ⟨_, rfl, rfl⟩⟩

/-! ## Zero and equal values -/

/-- The coefficient of a value: the sum over its occurrences. -/
def valueAggregate (trace : Trace (List Letter × ℕ) Unit Unit) (tuple : List Letter) : ℕ :=
  (((answers trace).filter fun occurrence => occurrence.1 = tuple).map Prod.snd).sum

/-- **A zero coefficient retains its occurrence and its factor**; the value
aggregate cannot tell it from absence. -/
theorem zero_retains_occurrence :
    answers (lazyUses 1 (single (0 : ℕ))) = [([.A], [drawnAt [] (produce 1 .A 0)])] ∧
      valueAggregate (coefficients (lazyUses 1 (single (0 : ℕ)))) [.A] =
        valueAggregate (coefficients (lazyUses 1 ([] : Trace (Factor ℕ Letter ℕ) Unit Unit))) [.A] ∧
      lazyUses 1 (single (0 : ℕ)) ≠ lazyUses 1 [] := by
  decide

/-- **Equal values with different identities keep different factors.** -/
theorem equal_values_distinct_factors :
    runLedger (lazyUses 2 ([.answer (produce 1 .A (3 : ℕ)), .answer (produce 2 .A 3)] :
        Trace (Factor ℕ Letter ℕ) Unit Unit)) =
      [drawnAt [] (produce 1 .A 3), drawnAt [] (produce 2 .A 3)] ∧
      Valid (runLedger (lazyUses 2 ([.answer (produce 1 .A (3 : ℕ)), .answer (produce 2 .A 3)] :
        Trace (Factor ℕ Letter ℕ) Unit Unit))) ∧
      denote (runLedger (lazyUses 2 ([.answer (produce 1 .A (3 : ℕ)), .answer (produce 2 .A 3)] :
        Trace (Factor ℕ Letter ℕ) Unit Unit))) = 9 := by
  decide

/-! ## Resumed pending production under nested scopes -/

open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Producer phases: the second production is pending at `pending`. -/
inductive Stage where
  | first
  | pending
  | second
  | done
  deriving DecidableEq

abbrev ProductionEvent := Event (Factor ℕ Letter ℕ) Unit Unit

/-- Produce `A` (coefficient 2), start the production of `B` (pending), produce
it (coefficient 3), finish. -/
def producer : Machine Stage ProductionEvent Unit Empty where
  step
    | .first => some (.publish [.answer (produce 1 .A 2)] .pending)
    | .pending => some (.silent .second)
    | .second => some (.publish [.answer (produce 2 .B 3)] .done)
    | .done => some (.finish ())

/-- The paused run: `A` produced, `B` pending at the residual. -/
theorem paused : producer.run 1 .first = ([.answer (produce 1 .A 2)], .exhausted .pending) :=
  rfl

/-- The productions of the resumed run: the established ones, then the pending
one completed after resumption. -/
def resumedProductions : Ledger ℕ Letter ℕ :=
  answers ((producer.run 1 .first).1 ++ (producer.run 3 .pending).1)

/-- The shared world: both productions, nothing claimed. -/
def world : Scoped ℕ Letter ℕ String :=
  ⟨resumedProductions, fun _ => none⟩

/-- The nested scope entered after the first production claims what follows. -/
def innerHandled : Scoped ℕ Letter ℕ String :=
  Scoped.handle 1 "inner" world

/-- **Resumed pending production under nested scopes.**  Resumption produces
each production once, exactly as the uninterrupted run; the inner scope
observes the resumed production `B`, the outer scope then observes `A` alone,
and each coefficient is charged once. -/
theorem resumed_production_nested_scopes :
    (producer.run 1 .first).1 ++ (producer.run 3 .pending).1 = (producer.run 4 .first).1 ∧
      resumedProductions = [produce 1 .A 2, produce 2 .B 3] ∧ Valid resumedProductions ∧
      Scoped.selected 1 world = [produce 2 .B 3] ∧
      Scoped.selected 0 innerHandled = [produce 1 .A 2] ∧
      denote (Scoped.selected 1 world) * denote (Scoped.selected 0 innerHandled) =
        denote resumedProductions := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide⟩
  have resumed := producer.established_and_pending 1 3 .first .pending _ paused
  rw [show 1 + 3 = 4 from rfl] at resumed
  rw [resumed]
  rfl

/-- **Restarting instead of resuming charges the first production twice** and
is refused by the ledger. -/
theorem restart_charges_twice :
    answers ((producer.run 1 .first).1 ++ (producer.run 4 .first).1) =
        [produce 1 .A 2, produce 1 .A 2, produce 2 .B 3] ∧
      ¬ Valid (answers ((producer.run 1 .first).1 ++ (producer.run 4 .first).1)) ∧
      denote (answers ((producer.run 1 .first).1 ++ (producer.run 4 .first).1)) = 12 := by
  decide

/-! ## Noncommutative coefficients -/

/-- **Positive**: an upper triangular production moves past its square. -/
theorem movesPast_positive :
    MovesPast (produce 1 .A upper) [drawnAt [] (produce 2 .B (upper * upper))] ∧
      denote (eagerLedger (produce 1 .A upper) [drawnAt [] (produce 2 .B (upper * upper))]) =
        denote (lazyLedger (produce 1 .A upper) [drawnAt [] (produce 2 .B (upper * upper))]) := by
  have lawful : MovesPast (produce 1 .A upper) [drawnAt [] (produce 2 .B (upper * upper))] := by
    intro factor member
    simp only [List.mem_singleton] at member
    subst member
    exact (Commute.refl upper).mul_right (Commute.refl upper)
  exact ⟨lawful, eager_eq_lazy_of_movesPast lawful⟩

/-- **Negative**: it does not move past a lower triangular factor. -/
theorem movesPast_negative :
    denote (eagerLedger (produce 1 .A upper) [drawnAt [] (produce 2 .B lower)]) ≠
      denote (lazyLedger (produce 1 .A upper) [drawnAt [] (produce 2 .B lower)]) := by
  rw [Ne, eager_eq_lazy_single_iff]
  exact matrix_composition_is_ordered

/-! ## Coefficients are not weights -/

open Mettapedia.GSLT.Distinction.DemandStrategies (Strategy Program Weights answerDistance bagReading)

/-- One computation: a fair coin. -/
inductive Coin where
  | coin
  deriving DecidableEq

/-- The coin with unit coefficients. -/
def unitCoin : Coin → Multiset (Option Bool × ℕ) := fun _ => {(some true, 1), (some false, 1)}

/-- The coin with coefficients `0` and `5`. -/
def skewedCoin : Coin → Multiset (Option Bool × ℕ) := fun _ => {(some true, 0), (some false, 5)}

/-- **Coefficients are not a weight.**  The two coin draws have the same erasure,
so every weighted observer puts any two programs at the same distance under
both; their count aggregates differ. -/
theorem coefficient_not_a_weight :
    erasedDraw unitCoin = erasedDraw skewedCoin ∧
      (∀ (weights : Weights) (strategy : Strategy) (left right : Program Coin),
        answerDistance (erasedDraw unitCoin) weights strategy left right =
          answerDistance (erasedDraw skewedCoin) weights strategy left right) ∧
      aggregate (coefficientAnswers unitCoin .eager (.forceThen .coin)) (some []) = 2 ∧
      aggregate (coefficientAnswers skewedCoin .eager (.forceThen .coin)) (some []) = 5 := by
  have same : erasedDraw unitCoin = erasedDraw skewedCoin := by
    funext computation
    simp [erasedDraw, unitCoin, skewedCoin]
  exact ⟨same, fun weights strategy left right =>
    answerDistance_of_erasure unitCoin skewedCoin same weights strategy left right, by decide, by decide⟩

/-- **At unit coefficients the aggregate is the bag count**: the bag reading
counts two outcomes `a` of forcing the coin. -/
theorem bag_is_unit_count :
    (bagReading (erasedDraw unitCoin) .eager (.forceThen .coin)).count (some []) = 2 := by
  rw [count_eq_unit_aggregate]
  decide

end Mettapedia.GSLT.Distinction.ProductionLicences.Controls
