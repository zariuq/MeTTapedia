import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterJoinCalls

/-!
# Controls for the two-way interpreter join

* **An open call binds the caller** (`open_call_interpreted`): with `(= (f (s $z)) $z)`, the call
  `(f $y)` beside the row `(out $y)` is answered by the interpreter with a variable `a`, and the
  caller's row becomes `(out (s a))`: the store's unification binds the caller's variable, as the
  compiled firing does, up to the name of the fresh variable.
* **Unrestricted equations are answered** (`unrestricted_interpreted`): `(= g $y)` answers `g` with a
  variable. The matching interpreter of `ProgramCompiledInterpreter` reaches no answer for it
  (`ProgramCompiled.unrestricted_mismatch`); this one allocates the slot.
* **Ground calls are answered exactly** (`ground_interpreted`): with `(= (f $x) (g $x))`, the call
  `(f a)` is answered `(g a)` itself; a renaming fixes ground answers, so the join is exact there.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin.Controls

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

/-- **Binding a variable to a term without it is a most general unifier.** -/
theorem single_isMGU {s : Tm} {v : ℕ × ℕ} (fresh : v ∉ s.freeVars) :
    IsMGU [(s, .var v)] (Subst.single (σ := rows) v s) := by
  have fixS : (Subst.single (σ := rows) v s).applyTerm s = s :=
    Subst.applyTerm_eq_self fun w hw => Subst.single_ne (σ := rows) _ fun h => fresh (h ▸ hw)
  refine ⟨?_, fun δ unifies => ⟨δ, fun x => ?_⟩, ?_⟩
  · rw [unifies_single, fixS, Subst.applyTerm_var, Subst.single_eq (σ := rows)]
  · rw [unifies_single, Subst.applyTerm_var] at unifies
    by_cases h : x = v
    · rw [h, Subst.single_eq (σ := rows), unifies]
    · rw [Subst.single_ne (σ := rows) _ h, Subst.applyTerm_var]
  · have vars : eqVars [(s, .var v)] = s.freeVars ∪ {v} := by
      simp [eqVars, Term.freeVars]
    rw [vars]
    refine ⟨fun x notIn => ?_, fun x _ => ?_, fun x w hw => ?_⟩
    · rw [Subst.single_ne (σ := rows) _ fun h => notIn (by simp [h])]
    · by_cases h : x = v
      · rw [h, Subst.single_eq (σ := rows)]
        exact Finset.subset_union_left
      · rw [Subst.single_ne (σ := rows) _ h]
        intro w hw
        rw [Term.mem_freeVars_var (σ := rows)] at hw
        subst hw
        assumption
    · by_cases h : x = v
      · rw [h, Subst.single_eq (σ := rows)] at hw
        rw [Subst.single_ne (σ := rows) _ fun h' : w = v => fresh (by rw [← h']; exact hw)]
      · rw [Subst.single_ne (σ := rows) _ h, Term.mem_freeVars_var (σ := rows)] at hw
        rw [hw, Subst.single_ne (σ := rows) _ h]

/-! ## An open call binds the caller -/

/-- `(= (f (s $z)) $z)`. -/
def eqS : ProgramEquations.Equation := ⟨ptag 50 (ptag 51 (.var 0)), .var 0⟩

/-- The caller's variable `$y`. -/
def vy : Tm := .var (0, 0)

/-- `(out $y)`. -/
def outRow (t : Tm) : Tm := tagged 70 t

/-- The compiled unifier: `$y := (s $z)`, with `$z` at scope `1`. -/
def bindY : Subst rows := Subst.single (0, 0) (tagged 51 (.var (1, 0)))

theorem bindY_isMGU : IsMGU [(eqS.lhs.at 1, tagged 50 vy)] bindY := by
  have base := single_isMGU (s := tagged 51 (.var (1, 0))) (v := (0, 0)) (by
    rw [freeVars_tagged, Term.mem_freeVars_var (σ := rows)]
    decide)
  have same : ∀ δ : Subst rows, Unifies δ [(tagged 51 (.var (1, 0)), .var (0, 0))] ↔
      Unifies δ [(eqS.lhs.at 1, tagged 50 vy)] := by
    intro δ
    show _ ↔ Unifies δ [(tagged 50 (tagged 51 (.var (1, 0))), tagged 50 vy)]
    rw [unifies_tagged_iff]
    rfl
  refine base.congr same ?_
  show eqVars [(tagged 51 (.var (1, 0)), .var (0, 0))] = eqVars [(tagged 50 (tagged 51 (.var (1, 0))), tagged 50 vy)]
  simp [eqVars, freeVars_tagged, vy]

/-- **The interpreter answers the open call with a variable `a`, and the caller's row becomes
`(out (s a))`.** -/
theorem open_call_interpreted :
    ∃ m a F', Relation.ReflTransGen (EqStep joinMeta)
        (thread (ttup 160 [embed (progData [eqS]), tagged 50 vy]) ::ₘ {outRow vy}, 1)
        (thread (ttup 173 [a]) ::ₘ F', m) ∧
      (∃ x, a = .var x) ∧ F' = {outRow (tagged 51 a)} := by
  have tB : Bounded 1 (tagged 50 vy) := fun w hw => by
    rw [freeVars_tagged, vy, Term.mem_freeVars_var (σ := rows)] at hw
    rw [hw]
    decide
  have FB : ∀ f ∈ ({outRow vy} : Multiset Tm), Bounded 1 f := by
    intro f member
    rw [Multiset.mem_singleton] at member
    rw [member]
    intro w hw
    rw [outRow, freeVars_tagged, vy, Term.mem_freeVars_var (σ := rows)] at hw
    rw [hw]
    decide
  obtain ⟨m, a, F', run, κ, ren, answer, rowsEq⟩ :=
    interpreter_answers (prog := [eqS]) ⟨0, by decide⟩ tB FB bindY_isMGU
  have compiled : bindY.applyTerm (([eqS].get ⟨0, by decide⟩).rhs.at 1) = .var (1, 0) := by
    show Subst.single (σ := rows) (0, 0) (tagged 51 (.var (1, 0))) (1, 0) = _
    rw [Subst.single_ne (σ := rows) _ (by decide)]
  rw [compiled] at answer
  obtain ⟨x, hx⟩ := ren (1, 0)
  refine ⟨m, a, F', run, ⟨x, by rw [answer, Subst.applyTerm_var, hx]⟩, ?_⟩
  rw [rowsEq, Multiset.map_singleton, Multiset.map_singleton]
  congr 1
  show κ.applyTerm (bindY.applyTerm (tagged 70 vy)) = tagged 70 (tagged 51 a)
  rw [apply_tagged, apply_tagged, vy, Subst.applyTerm_var]
  show tagged 70 (κ.applyTerm (Subst.single (σ := rows) (0, 0) (tagged 51 (.var (1, 0))) (0, 0))) = _
  rw [Subst.single_eq (σ := rows), apply_tagged, Subst.applyTerm_var, answer, Subst.applyTerm_var]

/-! ## Unrestricted equations are answered -/

/-- `(= g $y)`: the right-hand side's variable is not on the left. -/
def eqG : ProgramEquations.Equation := ⟨ptag 52 (.sym 0), .var 0⟩

/-- The call `g`. -/
def gCall : Tm := tagged 52 (.const 0)

theorem gCall_bounded : Bounded 1 gCall := fun w hw => by
  simp [gCall, freeVars_tagged, Term.freeVars] at hw

/-- **`(= g $y)` answers `g` with a variable.** -/
theorem unrestricted_interpreted :
    ∃ m a F', Relation.ReflTransGen (EqStep joinMeta)
        (thread (ttup 160 [embed (progData [eqG]), gCall]) ::ₘ 0, 1) (thread (ttup 173 [a]) ::ₘ F', m) ∧
      ∃ x, a = .var x := by
  have mgu : IsMGU [(eqG.lhs.at 1, gCall)] (Subst.id rows) :=
    ProgramNested.isMGU_id_of_eq fun e member => by
      rw [List.mem_singleton] at member
      rw [member]
      rfl
  obtain ⟨m, a, F', run, κ, ren, answer, -⟩ :=
    interpreter_answers (prog := [eqG]) (F := 0) ⟨0, by decide⟩ gCall_bounded (by simp) mgu
  obtain ⟨x, hx⟩ := ren (1, 0)
  refine ⟨m, a, F', run, x, ?_⟩
  rw [answer]
  show κ.applyTerm ((Subst.id rows).applyTerm (.var (1, 0))) = _
  rw [Subst.applyTerm_id, Subst.applyTerm_var, hx]

/-! ## Ground calls are answered exactly -/

/-- `(= (f $x) (g $x))`. -/
def eqFG : ProgramEquations.Equation := ⟨ptag 50 (.var 0), ptag 53 (.var 0)⟩

/-- The call `(f a)`. -/
def faCall : Tm := tagged 50 (.const 60)

theorem fa_mgu : IsMGU [(eqFG.lhs.at 1, faCall)] (Subst.single (σ := rows) (1, 0) (.const 60)) := by
  have base := single_isMGU (s := (.const 60 : Tm)) (v := (1, 0)) (by simp [Term.freeVars])
  refine base.congr (fun δ => ?_) ?_
  · show Unifies δ [(.const 60, .var (1, 0))] ↔ Unifies δ [(tagged 50 (.var (1, 0)), tagged 50 (.const 60))]
    rw [unifies_tagged_iff, unifies_single, unifies_single]
    exact eq_comm
  · show eqVars [((.const 60 : Tm), .var (1, 0))] = eqVars [(tagged 50 (.var (1, 0)), tagged 50 (.const 60))]
    simp [eqVars, freeVars_tagged, Term.freeVars, Finset.union_comm]

/-- **The ground call `(f a)` is answered `(g a)` itself.** -/
theorem ground_interpreted :
    ∃ m F', Relation.ReflTransGen (EqStep joinMeta)
        (thread (ttup 160 [embed (progData [eqFG]), faCall]) ::ₘ 0, 1)
        (thread (ttup 173 [tagged 53 (.const 60)]) ::ₘ F', m) := by
  have tB : Bounded 1 faCall := fun w hw => by simp [faCall, freeVars_tagged, Term.freeVars] at hw
  obtain ⟨m, a, F', run, κ, -, answer, -⟩ :=
    interpreter_answers (prog := [eqFG]) (F := 0) ⟨0, by decide⟩ tB (by simp) fa_mgu
  have ground : a = tagged 53 (.const 60) := by
    rw [answer]
    show κ.applyTerm ((Subst.single (σ := rows) (1, 0) (.const 60)).applyTerm (tagged 53 (.var (1, 0)))) = _
    rw [apply_tagged, Subst.applyTerm_var, Subst.single_eq (σ := rows), apply_tagged]
    rfl
  rw [ground] at run
  exact ⟨m, F', run⟩

#print axioms single_isMGU
#print axioms bindY_isMGU
#print axioms open_call_interpreted
#print axioms unrestricted_interpreted
#print axioms fa_mgu
#print axioms ground_interpreted

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin.Controls
