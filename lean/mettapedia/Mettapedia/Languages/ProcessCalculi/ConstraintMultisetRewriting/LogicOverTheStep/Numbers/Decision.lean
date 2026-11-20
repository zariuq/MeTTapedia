import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.OnTheStep

/-!
# The knowledge's equality is decided by one evaluation, exactly under the value law

The knowledge of the step with a grounded table identifies two terms when every instance of them
evaluates to terms of equal value (`OnTheStep.Identified`), a statement about all substitutions.
This module shows when one evaluation decides it.

* **Evaluation commutes with substitution** (`eval_subst`, with `eval_idem`), for every table:
  evaluating an instance is evaluating the instance of the evaluated term.
* **Under the value law the knowledge's equality is "evaluate, then compare values"**
  (`identified_iff_of_respects`): with a table that respects the value lens, two terms are
  identified exactly when their evaluations are storage variants. So it is decidable
  (`decideIdentified`), by one evaluation of each side and one comparison of terms over the
  rationals; no cost is claimed.
* **Control: without the value law "evaluate, then compare" is not the knowledge's equality, and not
  even stable under substitution** (`naive_fails`): with the storage-dependent division,
  `(/ $x 2)` and `(/ $x 2.0)` evaluate to storage variants, and at `$x = 5` they evaluate to `2`
  and `5/2`. This is why the knowledge is defined over all instances: it is a lawful substitution
  action for every table, and it agrees with the one-evaluation test exactly where the table
  respects the value lens.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Decision

open Distinctions.NumberLens OnTheStep

deriving instance DecidableEq for NTerm

theorem evalOp_none {G : Table} {o : OpName} {L R : NTerm Stored} (refused : answer G o L R = none) :
    evalOp G o L R = .op o L R := by
  simp only [evalOp, refused]

theorem evalOp_some {G : Table} {o : OpName} {L R : NTerm Stored} {c : Stored}
    (answered : answer G o L R = some c) : evalOp G o L R = .num c := by
  simp only [evalOp, answered]

theorem nums_of_answer {G : Table} {o : OpName} {L R : NTerm Stored} {c : Stored}
    (answered : answer G o L R = some c) : ∃ a b, L.asNum = some a ∧ R.asNum = some b := by
  unfold answer at answered
  rcases hl : L.asNum with _ | a
  · rw [hl] at answered
    simp at answered
  · rcases hr : R.asNum with _ | b
    · rw [hl, hr] at answered
      simp at answered
    · exact ⟨a, b, rfl, rfl⟩

/-- **Evaluation is idempotent.** -/
theorem eval_idem (G : Table) (t : NTerm Stored) : eval G (eval G t) = eval G t := by
  induction t with
  | num n => rfl
  | var x => rfl
  | sym c => rfl
  | app f a ihf iha =>
      show NTerm.app (eval G (eval G f)) (eval G (eval G a)) = NTerm.app (eval G f) (eval G a)
      rw [ihf, iha]
  | op o l r ihl ihr =>
      show eval G (evalOp G o (eval G l) (eval G r)) = evalOp G o (eval G l) (eval G r)
      rcases hanswer : answer G o (eval G l) (eval G r) with _ | c
      · rw [evalOp_none hanswer]
        show evalOp G o (eval G (eval G l)) (eval G (eval G r)) = NTerm.op o (eval G l) (eval G r)
        rw [ihl, ihr, evalOp_none hanswer]
      · rw [evalOp_some hanswer]
        rfl

/-- A numeral is fixed by every substitution. -/
theorem subst_num (σ : ℕ → NTerm Stored) {t : NTerm Stored} {a : Stored} (numeral : t.asNum = some a) :
    t.subst σ = t := by
  cases t <;> first | rfl | cases numeral

/-- **Evaluation commutes with substitution**, for every table. -/
theorem eval_subst (G : Table) (σ : ℕ → NTerm Stored) (s : NTerm Stored) :
    eval G ((eval G s).subst fun x => eval G (σ x)) = eval G (s.subst σ) := by
  induction s with
  | num n => rfl
  | var x => exact eval_idem G (σ x)
  | sym c => rfl
  | app f a ihf iha =>
      show NTerm.app (eval G ((eval G f).subst fun x => eval G (σ x)))
          (eval G ((eval G a).subst fun x => eval G (σ x))) =
        NTerm.app (eval G (f.subst σ)) (eval G (a.subst σ))
      rw [ihf, iha]
  | op o l r ihl ihr =>
      show eval G ((evalOp G o (eval G l) (eval G r)).subst fun x => eval G (σ x)) =
        evalOp G o (eval G (l.subst σ)) (eval G (r.subst σ))
      rw [← ihl, ← ihr]
      rcases hanswer : answer G o (eval G l) (eval G r) with _ | c
      · rw [evalOp_none hanswer]
        rfl
      · obtain ⟨a, b, hl, hr⟩ := nums_of_answer hanswer
        rw [evalOp_some hanswer, subst_num _ hl, subst_num _ hr, eval_idem, eval_idem,
          evalOp_some hanswer]
        rfl

/-- **Under the value law the knowledge's equality is "evaluate, then compare values".** -/
theorem identified_iff_of_respects {G : Table} (respects : TableRespects G) (s t : NTerm Stored) :
    Identified G s t ↔ Variant (eval G s) (eval G t) := by
  constructor
  · intro identified
    have atIdentity := identified NTerm.var
    rw [NTerm.subst_var, NTerm.subst_var] at atIdentity
    exact atIdentity
  · intro same σ
    rw [← eval_subst G σ s, ← eval_subst G σ t]
    exact eval_variant respects (subst_variant same _)

/-- **So the knowledge's equality is decidable** for a table that respects the value lens. -/
def decideIdentified {G : Table} (respects : TableRespects G) (s t : NTerm Stored) :
    Decidable (Identified G s t) :=
  decidable_of_iff ((eval G s).map value = (eval G t).map value)
    (identified_iff_of_respects respects s t).symm

/-- `(/ $x 2)`. -/
def halfInt : NTerm Stored := .op .divide (.var 0) (.num (.int 2))

/-- `(/ $x 2.0)`. -/
def halfFrac : NTerm Stored := .op .divide (.var 0) (.num (.frac 2))

/-- **Control: without the value law, "evaluate, then compare" is not the knowledge's equality**:
`(/ $x 2)` and `(/ $x 2.0)` evaluate to storage variants, yet they are not identified: at `$x = 5`
they evaluate to `2` and `5/2`. -/
theorem naive_fails :
    Variant (eval storedDivTable halfInt) (eval storedDivTable halfFrac) ∧
      ¬ Identified storedDivTable halfInt halfFrac := by
  constructor
  · show NTerm.map value (NTerm.op .divide (.var 0) (.num (.int 2))) =
      NTerm.map value (NTerm.op .divide (.var 0) (.num (.frac 2)))
    simp [NTerm.map, value]
  · intro identified
    have atFive := identified fun _ => .num (.int 5)
    have nonzeroInt : ¬ value (Stored.int 2) = 0 := by norm_num [value]
    have nonzeroFrac : ¬ value (Stored.frac 2) = 0 := by norm_num [value]
    have left : eval storedDivTable (halfInt.subst fun _ => .num (.int 5)) =
        .num (storedDiv (.int 5) (.int 2)) := by
      show evalOp storedDivTable .divide (.num (.int 5)) (.num (.int 2)) = _
      rw [evalOp_some (c := storedDiv (.int 5) (.int 2))]
      show (if value (Stored.int 2) = 0 then none else some (storedDiv (.int 5) (.int 2))) =
        some (storedDiv (.int 5) (.int 2))
      exact if_neg nonzeroInt
    have right : eval storedDivTable (halfFrac.subst fun _ => .num (.int 5)) =
        .num (storedDiv (.int 5) (.frac 2)) := by
      show evalOp storedDivTable .divide (.num (.int 5)) (.num (.frac 2)) = _
      rw [evalOp_some (c := storedDiv (.int 5) (.frac 2))]
      show (if value (Stored.frac 2) = 0 then none else some (storedDiv (.int 5) (.frac 2))) =
        some (storedDiv (.int 5) (.frac 2))
      exact if_neg nonzeroFrac
    rw [left, right] at atFive
    simp only [NTerm.map, NTerm.num.injEq] at atFive
    have quotient : Int.tdiv 5 2 = 2 := by decide
    have two : value (storedDiv (.int 5) (.int 2)) = 2 := by
      show ((Int.tdiv 5 2 : ℤ) : ℚ) = 2
      rw [quotient]
      norm_num
    have half : value (storedDiv (.int 5) (.frac 2)) = 5 / 2 := by
      show ((5 : ℤ) : ℚ) / 2 = 5 / 2
      norm_num
    rw [two, half] at atFive
    norm_num at atFive

#print axioms evalOp_none
#print axioms evalOp_some
#print axioms eval_idem
#print axioms eval_subst
#print axioms identified_iff_of_respects
#print axioms decideIdentified
#print axioms naive_fails

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Numbers.Decision
