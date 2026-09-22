import Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision
import Mettapedia.TypeTheory.Authority

/-!
# Bounded comparison without a fallback decision

The existing intrinsically typed beta stepper supplies a bounded normalizer.
A completed run retains its reduction path, normality proof, and unspent
allowance. Comparison passes that allowance to the second operand instead of
restarting the bound. Two completed runs decide beta conversion; an unfinished
run decides neither polarity. Increasing the bound preserves completed
decisions, and strong normalization gives eventual completion for every pair
of simple terms.

This is an executable Lean reference for the simple beta fragment, not a
verification of a C normalizer or of declaration-specific computation rules.
The bound counts calls of the reduction stepper, not machine instructions.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BoundedConversion

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT
open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.Normalization Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.ConversionDecision
open Mettapedia.TypeTheory.AuthorityTheory

variable {Γ : List Ty} {A : Ty}

def normalizeWithin : Nat → (t : Term Γ A) → Option (Mettapedia.Logic.Relation.NormalizationResult BetaStep t × Nat)
  | 0, _ => none
  | fuel + 1, t =>
      match selected : reduceOnce? t with
      | none => some (⟨t, .refl, (reduceOnce_eq_none_iff t).1 selected⟩, fuel)
      | some next => (normalizeWithin fuel next.1).map fun result =>
          (⟨result.1.normalForm, .head next.2 result.1.reduces,
            result.1.irreducible⟩, result.2)

theorem normalizeWithin_succ_none (fuel : Nat) (t : Term Γ A)
    (selected : reduceOnce? t = none) :
    normalizeWithin (fuel + 1) t =
      some (⟨t, .refl, (reduceOnce_eq_none_iff t).1 selected⟩, fuel) := by
  unfold normalizeWithin
  split <;> simp_all

theorem normalizeWithin_succ_some (fuel : Nat) (t : Term Γ A)
    (next : {u : Term Γ A // BetaStep t u})
    (selected : reduceOnce? t = some next) :
    normalizeWithin (fuel + 1) t = (normalizeWithin fuel next.1).map
      (fun result => (⟨result.1.normalForm, .head next.2 result.1.reduces,
        result.1.irreducible⟩, result.2)) := by
  rw [normalizeWithin]
  split
  · simp_all
  · rename_i other chosen
    have equal : other = next := Option.some.inj (chosen.symm.trans selected)
    subst other
    rfl

theorem normalizeWithin_add {fuel remaining : Nat} {t : Term Γ A} {result : Mettapedia.Logic.Relation.NormalizationResult BetaStep t}
    (completed : normalizeWithin fuel t = some (result, remaining)) (extra : Nat) :
    normalizeWithin (fuel + extra) t = some (result, remaining + extra) := by
  induction fuel generalizing t with
  | zero => simp [normalizeWithin] at completed
  | succ fuel ih =>
      cases selected : reduceOnce? t with
      | none =>
          rw [normalizeWithin_succ_none fuel t selected] at completed
          rw [Nat.succ_add, normalizeWithin_succ_none _ t selected]
          exact congrArg some
            (congrArg (fun pair : Mettapedia.Logic.Relation.NormalizationResult BetaStep t × Nat => (pair.1, pair.2 + extra))
              (Option.some.inj completed))
      | some next =>
          rw [normalizeWithin_succ_some fuel t next selected] at completed
          obtain ⟨⟨inner, rest⟩, ran, equal⟩ := Option.map_eq_some_iff.mp completed
          cases equal
          rw [Nat.succ_add, normalizeWithin_succ_some _ t next selected, ih ran]
          rfl

/-- Every successful run consumes a stepper call, including the final
normality check, and returns strictly less than its incoming allowance. -/
theorem normalizeWithin_remaining_lt {fuel remaining : Nat} {t : Term Γ A}
    {result : Mettapedia.Logic.Relation.NormalizationResult BetaStep t}
    (completed : normalizeWithin fuel t = some (result, remaining)) :
    remaining < fuel := by
  induction fuel generalizing t remaining with
  | zero => simp [normalizeWithin] at completed
  | succ fuel ih =>
      cases selected : reduceOnce? t with
      | none =>
          rw [normalizeWithin_succ_none fuel t selected] at completed
          have equal := congrArg (fun value => value.map Prod.snd) completed
          simp only [Option.map_some, Option.some.injEq] at equal
          omega
      | some next =>
          rw [normalizeWithin_succ_some fuel t next selected] at completed
          obtain ⟨⟨inner, rest⟩, ran, equal⟩ := Option.map_eq_some_iff.mp completed
          have remainingEqual := congrArg Prod.snd equal
          have bound := ih ran
          simp only at remainingEqual
          omega

theorem normalizeWithin_eventually (t : Term Γ A) :
    ∃ fuel result remaining, normalizeWithin fuel t = some (result, remaining) := by
  induction strong_normalization t with
  | intro t _ ih =>
      cases selected : reduceOnce? t with
      | none => exact ⟨1, _, 0, normalizeWithin_succ_none 0 t selected⟩
      | some next =>
          obtain ⟨fuel, result, remaining, completed⟩ := ih next.1 next.2
          refine ⟨fuel + 1,
            ⟨result.normalForm, .head next.2 result.reduces, result.irreducible⟩,
            remaining, ?_⟩
          rw [normalizeWithin_succ_some fuel t next selected, completed]
          rfl

theorem result_eq_normalize {t : Term Γ A} (result : Mettapedia.Logic.Relation.NormalizationResult BetaStep t) :
    result.normalForm = (normalize t).normalForm := by
  apply Normal.eq_of_towerConv
    (Normal.iff_no_betaStep.mpr result.irreducible)
    (normalize_normal t)
  have conversion : BetaConv result.normalForm (normalize t).normalForm :=
    .trans _ _ _ (.symm _ _ (steps_convert result.reduces)) (normalize_convert t)
  exact conversion.erase

def compareWithin (fuel : Nat) (left right : Term Γ A) : Option Bool :=
  match normalizeWithin fuel left with
  | none => none
  | some (l, remaining) =>
      match normalizeWithin remaining right with
      | none => none
      | some (r, _) =>
          some (decide (TowerDTT.eraseTerm l.normalForm = TowerDTT.eraseTerm r.normalForm))

/-- The displayed work of the two actual runs adds to their total work.
The second run cannot recover the allowance consumed by the first. -/
theorem comparison_spent_add {fuel afterLeft remaining : Nat}
    {left right : Term Γ A} {l : Mettapedia.Logic.Relation.NormalizationResult BetaStep left} {r : Mettapedia.Logic.Relation.NormalizationResult BetaStep right}
    (leftCompleted : normalizeWithin fuel left = some (l, afterLeft))
    (rightCompleted : normalizeWithin afterLeft right = some (r, remaining)) :
    (fuel - afterLeft) + (afterLeft - remaining) = fuel - remaining ∧
      remaining < afterLeft ∧ afterLeft < fuel := by
  have hl := normalizeWithin_remaining_lt leftCompleted
  have hr := normalizeWithin_remaining_lt rightCompleted
  exact ⟨by omega, hr, hl⟩

theorem compareWithin_eq_decision {fuel : Nat} {left right : Term Γ A} {answer : Bool}
    (completed : compareWithin fuel left right = some answer) :
    answer = decideConversion left right := by
  unfold compareWithin at completed
  cases hl : normalizeWithin fuel left with
  | none => simp [hl] at completed
  | some pair =>
      rcases pair with ⟨l, remaining⟩
      cases hr : normalizeWithin remaining right with
      | none => simp [hl, hr] at completed
      | some pair =>
          rcases pair with ⟨r, rest⟩
          simp only [hl, hr, Option.some.injEq] at completed
          rw [result_eq_normalize l, result_eq_normalize r] at completed
          exact completed.symm

theorem compareWithin_established {fuel : Nat} {left right : Term Γ A}
    (completed : compareWithin fuel left right = some true) : BetaConv left right :=
  (decideConversion_correct left right).1 (compareWithin_eq_decision completed).symm

theorem compareWithin_refuted {fuel : Nat} {left right : Term Γ A}
    (completed : compareWithin fuel left right = some false) : ¬ BetaConv left right := by
  intro converts
  have equal := compareWithin_eq_decision completed
  rw [(decideConversion_correct left right).2 converts] at equal
  cases equal

theorem compareWithin_add {fuel : Nat} {left right : Term Γ A} {answer : Bool}
    (completed : compareWithin fuel left right = some answer) (extra : Nat) :
    compareWithin (fuel + extra) left right = some answer := by
  cases hl : normalizeWithin fuel left with
  | none => simp [compareWithin, hl] at completed
  | some pair =>
      rcases pair with ⟨l, remaining⟩
      cases hr : normalizeWithin remaining right with
      | none => simp [compareWithin, hl, hr] at completed
      | some pair =>
          rcases pair with ⟨r, rest⟩
          simpa [compareWithin, normalizeWithin_add hl extra, normalizeWithin_add hr extra, hl, hr]
            using completed

theorem compareWithin_eventually (left right : Term Γ A) :
    ∃ fuel, compareWithin fuel left right = some (decideConversion left right) := by
  obtain ⟨fl, l, rl, hl⟩ := normalizeWithin_eventually left
  obtain ⟨fr, r, rr, hr⟩ := normalizeWithin_eventually right
  have hl' := normalizeWithin_add hl fr
  have hr' := normalizeWithin_add hr rl
  rw [Nat.add_comm fr rl] at hr'
  refine ⟨fl + fr, ?_⟩
  simp [compareWithin, hl', hr', result_eq_normalize, decideConversion]

/-- Outcomes use the existing evidence-bearing authority sum. No result is
not a negative answer, and no second decision procedure is invoked. -/
def outcome (fuel : Nat) (left right : Term Γ A) :
    Outcome (BetaConv left right) (¬ BetaConv left right) Empty Nat :=
  match completed : compareWithin fuel left right with
  | some true => .established (compareWithin_established completed)
  | some false => .refuted (compareWithin_refuted completed)
  | none => .incomplete fuel

theorem outcome_asBool (fuel : Nat) (left right : Term Γ A) :
    (outcome fuel left right).asBool = compareWithin fuel left right := by
  unfold outcome
  split <;> simp_all [Outcome.asBool]

theorem exhausted_is_incomplete {fuel : Nat} {left right : Term Γ A}
    (exhausted : compareWithin fuel left right = none) :
    (outcome fuel left right).publicStatus = .incomplete := by
  unfold outcome
  split <;> simp_all [Outcome.publicStatus]

theorem outcome_budgetRefines (fuel extra : Nat) (left right : Term Γ A) :
    Outcome.BudgetRefines (outcome fuel left right)
      (outcome (fuel + extra) left right) := by
  unfold outcome
  split
  · rename_i completed
    have later := compareWithin_add completed extra
    split <;> simp_all
    constructor
  · rename_i completed
    have later := compareWithin_add completed extra
    split <;> simp_all
    constructor
  · split <;> constructor

/-- Substitution preserves a positive conversion judgment, but may increase
the reduction work; no reuse of the old fuel bound is asserted. -/
theorem substituted_established {Δ : List Ty} {fuel : Nat} {left right : Term Γ A}
    (completed : compareWithin fuel left right = some true)
    (σ : Substitution Γ Δ) :
    ∃ laterFuel, compareWithin laterFuel (left.substitute σ) (right.substitute σ) = some true := by
  have conversion := BetaConv.substitute (compareWithin_established completed) σ
  obtain ⟨laterFuel, later⟩ := compareWithin_eventually (left.substitute σ) (right.substitute σ)
  rw [(decideConversion_correct _ _).2 conversion] at later
  exact ⟨laterFuel, later⟩

def identity : Term [] (.arr .atom .atom) := .lam (.var .zero)
def redex : Term [] (.arr .atom .atom) := .app (.lam (.var .zero)) identity

theorem open_distinct_variables_refuted :
    compareWithin 2 (.var .zero : Term [.atom, .atom] .atom)
      (.var (.succ .zero)) = some false := by decide

theorem beta_redex_completed : compareWithin 3 redex identity = some true := by decide

theorem unfinished_convertible_pair :
    compareWithin 2 redex identity = none ∧ BetaConv redex identity := by
  exact ⟨by decide, compareWithin_established beta_redex_completed⟩

/-- Two normal operands still require two normality checks. Giving the
second operand the original one-call allowance would fabricate completion. -/
theorem second_operand_cannot_restart_budget :
    (∃ result remaining, normalizeWithin 1 identity = some (result, remaining)) ∧
      compareWithin 1 identity identity = none ∧
      compareWithin 2 identity identity = some true := by
  exact ⟨⟨_, 0, normalizeWithin_succ_none 0 identity (by decide)⟩,
    by decide, by decide⟩

theorem unfinished_nonconvertible_pair :
    compareWithin 0 etaVariable etaExpansion = none ∧
      ¬ BetaConv etaVariable etaExpansion :=
  ⟨rfl, eta_not_betaConvertible⟩

/-- Stopping at a residual and comparing its syntax would incorrectly
refute this pair, even though one beta step joins it. -/
theorem residual_inequality_does_not_refute :
    TowerDTT.eraseTerm redex ≠ TowerDTT.eraseTerm identity ∧
      BetaConv redex identity := by
  exact ⟨by decide, unfinished_convertible_pair.2⟩

def identifyVariables : Substitution [.atom, .atom] [.atom] :=
  fun {_} v => match v with
    | .zero => .var .zero
    | .succ .zero => .var .zero
    | .succ (.succ impossible) => nomatch impossible

/-- A checked negative result is about its original open context. An
arbitrary substitution may identify the variables that made it negative. -/
theorem refutation_not_preserved_by_substitution :
    compareWithin 2 (.var .zero : Term [.atom, .atom] .atom)
        (.var (.succ .zero)) = some false ∧
      compareWithin 2 ((.var .zero : Term [.atom, .atom] .atom).substitute identifyVariables)
        ((.var (.succ .zero) : Term [.atom, .atom] .atom).substitute identifyVariables) = some true := by
  constructor <;> decide

#print axioms normalizeWithin_eventually
#print axioms normalizeWithin_remaining_lt
#print axioms comparison_spent_add
#print axioms second_operand_cannot_restart_budget
#print axioms compareWithin_established
#print axioms compareWithin_refuted
#print axioms compareWithin_add
#print axioms compareWithin_eventually
#print axioms unfinished_convertible_pair
#print axioms residual_inequality_does_not_refute
#print axioms outcome_budgetRefines
#print axioms substituted_established
#print axioms refutation_not_preserved_by_substitution

end Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.BoundedConversion
