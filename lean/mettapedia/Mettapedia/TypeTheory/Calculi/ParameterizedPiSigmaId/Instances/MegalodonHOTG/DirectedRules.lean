import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.MegalodonHOTG.Queries
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.DirectedRules

/-!
# Directed rules, read in the sets

A directed rule `l ⟶ r` says that the answers of `r` are among the answers of `l`.
Running a call by stored rules returns those answers, one copy for each rule
(`Queries.answersCallEquiv`). The rule type itself speaks of values, not of counts
(`Queries.rule_sound`).

Admitting the fork `c ⟶ 5`, `c ⟶ 6` as equations makes any reading of the root steps
send `5` and `6` to the same set. The numerals `5` and `6` are distinct, so that
reading is impossible. The pair `c ⟶ 5`, `d ⟶ 5` does not: a reading that sends
`6` to the numeral `6` and every other constant to the numeral `5` respects its
root steps, and still separates `5` from `6`.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
namespace MegalodonHOTG
namespace DirectedRules

open Presentation Presentation.TypedEquality Presentation.TypedEquality.Annotated
open DirectedRule
open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.Logic.HOL.Embedding
open ZFSetTraceProducts (traceApp)

universe u

variable {L : Type} [LevelOrder L]

section Calls

variable {heads : Head L → ZFSet.{u}} {consts : DeclName → ZFSet.{u}} {n : Nat}

omit [LevelOrder L] in
/-- **A run's answer is an answer of the call.** One matching rule and one answer
of its right side are one element of the set the call denotes. -/
theorem run_answer_mem_call {Rl K lhs c Ans : CTm (Head L) n} {ρ : Env.{u} n}
    {rule answer : ZFSet.{u}}
    (matched : Queries.Matching (heads := heads) (consts := consts) Rl lhs c ρ rule)
    (returned : answer ∈ traceApp (ev heads consts Ans ρ) rule) :
    ((Queries.answersCallEquiv (heads := heads) (consts := consts) Rl K lhs c Ans ρ).symm
        ⟨(rule, answer), matched, returned⟩).1 ∈
      ev heads consts (Queries.cCall Rl K lhs c Ans) ρ := by
  let e := Queries.answersCallEquiv (heads := heads) (consts := consts) Rl K lhs c Ans ρ
  exact (e.symm ⟨(rule, answer), matched, returned⟩).2

omit [LevelOrder L] in
/-- **Distinct rule occurrences stay distinct as answers of the call.** The
correspondence keeps the pair of the rule and the answer it returned, so two
different occurrences are two elements. -/
theorem distinct_rule_answers_distinct_call_answers {Rl K lhs c Ans : CTm (Head L) n}
    {ρ : Env.{u} n}
    {p q : {p : ZFSet.{u} × ZFSet.{u} //
      Queries.Matching (heads := heads) (consts := consts) Rl lhs c ρ p.1 ∧
        p.2 ∈ traceApp (ev heads consts Ans ρ) p.1}}
    (ne : p.1 ≠ q.1) :
    ((Queries.answersCallEquiv (heads := heads) (consts := consts) Rl K lhs c Ans ρ).symm p).1 ≠
      ((Queries.answersCallEquiv (heads := heads) (consts := consts) Rl K lhs c Ans ρ).symm
        q).1 := by
  intro same
  let e := Queries.answersCallEquiv (heads := heads) (consts := consts) Rl K lhs c Ans ρ
  exact ne (congrArg Subtype.val (e.symm.injective (Subtype.ext same)))

omit [LevelOrder L] in
/-- **The answers of the right side are answers of the left side.** This is the
inclusion a directed rule reads as. Counts are the call, above. -/
theorem value_of_right_is_value_of_left {T I v J w : CTm (Head L) n} {ρ : Env.{u} n}
    {m : ZFSet.{u}} (hm : m ∈ ev heads consts (Queries.cRule T I v J w) ρ)
    {j : ZFSet.{u}} (hj : j ∈ ev heads consts J ρ) :
    ∃ i ∈ ev heads consts I ρ,
      traceApp (ev heads consts v ρ) i = traceApp (ev heads consts w ρ) j :=
  Queries.rule_sound hm hj

end Calls

/-! ## The fork and the pair, read as numerals -/

/-- A reading of constants that sends `6` to the numeral `6` and every other
constant to the numeral `5`. -/
def answerReading {Head : Type} {n : Nat} : Tm Head n → ZFSet.{u}
  | .const name => if name = `six then numeral 6 else numeral 5
  | _ => numeral 5

/-- **The promoted fork cannot be read by the numerals.** A reading that respects
the admitted root steps and sends `5` and `6` to the numerals `5` and `6` is
impossible: both steps pass through `c`. -/
theorem promoted_fork_refutes_numerals {Head : Type}
    (reading : {n : Nat} → Tm Head n → ZFSet.{u})
    (respects : ∀ {n : Nat} {t u : Tm Head n},
      (forkPromoted Head).equationRoot.step t u → reading t = reading u)
    (five : reading (.const `five : Tm Head 0) = numeral 5)
    (six : reading (.const `six : Tm Head 0) = numeral 6) : False := by
  have atFive := respects (fork_equation_to_five (Head := Head) (n := 0))
  have atSix := respects (fork_equation_to_six (Head := Head) (n := 0))
  have nums : numeral.{u} 5 = numeral.{u} 6 :=
    five.symm.trans (atFive.symm.trans (atSix.trans six))
  exact absurd (numeral_injective nums) (by decide : (5 : ℕ) ≠ 6)

/-- **The admitted pair keeps this reading.** Both root steps land on `5`, which
this reading already gives to `c` and to `d`. -/
theorem pair_keeps_numeral_reading {Head : Type} {n : Nat} {t u : Tm Head n}
    (step : (Normalization.RootComputation.union (quiet Head).computation
        (erasedComputation (pairRules.map promote))).step t u) :
    answerReading t = answerReading u := by
  rcases pair_equation_step step with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simp only [answerReading, if_neg (by decide : (`c : DeclName) ≠ `six),
      if_neg (by decide : (`five : DeclName) ≠ `six)]
  · simp only [answerReading, if_neg (by decide : (`d : DeclName) ≠ `six),
      if_neg (by decide : (`five : DeclName) ≠ `six)]

/-- Under that reading, `c` and `d` answer `5`, and `5` stays apart from `6`. -/
theorem pair_reading_answers {Head : Type} {n : Nat} :
    answerReading (.const `c : Tm Head n) = numeral.{u} 5 ∧
      answerReading (.const `d : Tm Head n) = numeral.{u} 5 ∧
      answerReading (.const `five : Tm Head n) = numeral.{u} 5 ∧
      answerReading (.const `six : Tm Head n) = numeral.{u} 6 ∧
      answerReading (.const `five : Tm Head n) ≠
        answerReading (.const `six : Tm Head n) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp only [answerReading, if_neg (by decide : (`c : DeclName) ≠ `six)]
  · simp only [answerReading, if_neg (by decide : (`d : DeclName) ≠ `six)]
  · simp only [answerReading, if_neg (by decide : (`five : DeclName) ≠ `six)]
  · simp only [answerReading, if_true]
  · intro same
    simp only [answerReading, if_neg (by decide : (`five : DeclName) ≠ `six), if_true] at same
    exact absurd (numeral_injective same) (by decide : (5 : ℕ) ≠ 6)

/-! ## Axioms -/

#print axioms run_answer_mem_call
#print axioms distinct_rule_answers_distinct_call_answers
#print axioms value_of_right_is_value_of_left
#print axioms promoted_fork_refutes_numerals
#print axioms pair_keeps_numeral_reading
#print axioms pair_reading_answers

end DirectedRules
end MegalodonHOTG
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation
