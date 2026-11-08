import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedControls
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedComplete

/-!
# Two nested calls multiply their answers: exactly four

`ProgramNested.Controls.answers_multiply` shows that `((c) (c))`, with `(= (c) x)` and `(= (c) y)`,
reaches each of `(x x)`, `(x y)`, `(y x)`, `(y y)`. Here no other value is reachable.

* **In evaluation contexts** (`reach_closed`, `reference_values`): every reference run from the
  expression stays among the configurations of `Reach`, by unique decomposition (only the left call,
  then only the right call, then only the build can fire) and because a unifier of a ground call
  moves no variable. So every value it reaches is one of the four.
* **On the machine** (`machine_values`): through `halted_is_value`, every machine run that returns
  a value to the empty stack returns one of the four. With `answers_multiply` the answers are
  exactly the four.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.Controls

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

/-! ## Inverting a reference step -/

/-- Rows that are not threads. -/
def NoThread (G : Multiset Tm) : Prop := ∀ r ∈ G, ∀ s, r ≠ thread s

theorem cstep_inv {defs : Defs} {X : Ex} {G : Multiset Tm} {n : ℕ} {s' : Multiset Tm × ℕ}
    (noThread : NoThread G) (step : CStep defs (thread (encE X) ::ₘ G, n) s') :
    (∃ (E : ECtx) (v w : Tm), X = E.fill (.pair (.val v) (.val w)) ∧
      s'.1 = thread (encE (E.fill (.val (node v w)))) ::ₘ G) ∨
    (∃ (u : ℕ) (j : Fin (defs u).length) (E : ECtx) (w : Tm) (m : ℕ) (θ : Subst rows) (F : Multiset Tm),
      IsMGU [(((defs u).get j).lhs.at m, w)] θ ∧ X = E.fill (.call (.val w)) ∧ G = ver u ::ₘ F ∧
      s'.1 = thread (encE ((E.fill (((defs u).get j).rhs.at m)).subst θ)) ::ₘ cite u ::ₘ ver u ::ₘ
        F.map θ.applyTerm) := by
  generalize hs : (thread (encE X) ::ₘ G, n) = start at step
  cases step with
  | build E v w F n' =>
      obtain ⟨eqW, -⟩ := Prod.mk.inj hs
      rcases Multiset.cons_eq_cons.mp eqW with ⟨same, rfl⟩ | ⟨-, cs, hG, -⟩
      · exact .inl ⟨E, v, w, encE_inj (thread_inj same), rfl⟩
      · exact absurd rfl (noThread _ (by rw [hG]; exact Multiset.mem_cons_self _ _) _)
  | apply u j E w F n' m fresh θ mgu =>
      obtain ⟨eqW, -⟩ := Prod.mk.inj hs
      rcases Multiset.cons_eq_cons.mp eqW with ⟨same, rfl⟩ | ⟨-, cs, hG, -⟩
      · exact .inr ⟨u, j, E, w, m, θ, F, mgu, encE_inj (thread_inj same), rfl, rfl⟩
      · exact absurd rfl (noThread _ (by rw [hG]; exact Multiset.mem_cons_self _ _) _)
  | redefine u u' F n' =>
      obtain ⟨eqW, -⟩ := Prod.mk.inj hs
      rcases Multiset.cons_eq_cons.mp eqW with ⟨same, -⟩ | ⟨-, cs, hG, -⟩
      · have inner := thread_inj same
        cases X <;> simp [encE, redefTo, tagged_inj] at inner
      · exact absurd rfl (noThread _ (by rw [hG]; exact Multiset.mem_cons_self _ _) _)

theorem cite_not_thread (u : ℕ) (s : Tm) : cite u ≠ thread s := fun h => by
  have := (tagged_inj.mp h).1
  omega

theorem ver_not_thread (u : ℕ) (s : Tm) : ver u ≠ thread s := fun h => by
  have := (tagged_inj.mp h).1
  omega

theorem noThread0 : NoThread (ver 1 ::ₘ 0) := by
  intro r member s
  rw [Multiset.mem_cons] at member
  rcases member with rfl | member
  · exact ver_not_thread 1 s
  · exact absurd member (Multiset.notMem_zero _)

theorem noThread_cite {G : Multiset Tm} (h : NoThread G) : NoThread (cite 1 ::ₘ G) := by
  intro r member s
  rw [Multiset.mem_cons] at member
  rcases member with rfl | member
  · exact cite_not_thread 1 s
  · exact h r member s

theorem noThread1 : NoThread (cite 1 ::ₘ ver 1 ::ₘ 0) := noThread_cite noThread0
theorem noThread2 : NoThread (cite 1 ::ₘ cite 1 ::ₘ ver 1 ::ₘ 0) := noThread_cite noThread1

/-! ## The decompositions of the four shapes -/

theorem start_decomp {E : ECtx} {r : Ex} (redex : Redex r) (h : twoCalls = E.fill r) :
    E = .pairL .hole cCall ∧ r = .call (.val (embed scc)) :=
  decomposition_unique redex (.inr ⟨_, rfl⟩) E (.pairL .hole cCall) h.symm

theorem first_decomp (a : Sx) {E : ECtx} {r : Ex} (redex : Redex r) (h : Ex.pair (gv a) cCall = E.fill r) :
    E = .pairR (embed a) .hole ∧ r = .call (.val (embed scc)) :=
  decomposition_unique redex (.inr ⟨_, rfl⟩) E (.pairR (embed a) .hole) h.symm

theorem second_decomp (a b : Sx) {E : ECtx} {r : Ex} (redex : Redex r)
    (h : Ex.pair (gv a) (gv b) = E.fill r) : E = .hole ∧ r = .pair (.val (embed a)) (.val (embed b)) :=
  decomposition_unique redex (.inl ⟨_, _, rfl⟩) E .hole h.symm

theorem built_decomp (s : Sx) {E : ECtx} {r : Ex} (redex : Redex r) (h : gv s = E.fill r) : False :=
  fill_redex_not_value redex E ⟨_, h.symm⟩

/-! ## Ground calls move no variable -/

theorem ground_mgu_fixes {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) (ground : eqVars P = ∅)
    (v : ℕ × ℕ) : θ v = .var v :=
  mgu.relevant.fixes v (by rw [ground]; exact Finset.notMem_empty v)

theorem ground_mgu_term {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) (ground : eqVars P = ∅)
    (t : Tm) : θ.applyTerm t = t :=
  Subst.applyTerm_eq_self fun v _ => ground_mgu_fixes mgu ground v

theorem ground_mgu_ex {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) (ground : eqVars P = ∅)
    (e : Ex) : e.subst θ = e := by
  rw [Ex.subst_congr (θ' := Subst.id rows) (fun v => ground_mgu_fixes mgu ground v) e, Ex.subst_id]

theorem ground_rows {P : List (Tm × Tm)} {θ : Subst rows} (mgu : IsMGU P θ) (ground : eqVars P = ∅)
    (F : Multiset Tm) : F.map θ.applyTerm = F :=
  (Multiset.map_congr rfl fun t _ => ground_mgu_term mgu ground t).trans (Multiset.map_id' F)

/-- The equations of version `1`: `(= (c) x)` or `(= (c) y)`. -/
theorem defsC_get (j : Fin (defsC 1).length) :
    ∃ a : Fin 2, ((defsC 1).get j).lhs = .sym 156 ∧ ∀ m, ((defsC 1).get j).rhs.at m = gv (pick a) := by
  rcases j with ⟨_ | _ | jv, jlt⟩
  · exact ⟨0, rfl, fun _ => rfl⟩
  · exact ⟨1, rfl, fun _ => rfl⟩
  · exact absurd jlt (by simp [defsC])

theorem call_problem_ground (m : ℕ) : eqVars [((Pat.sym 156).at m, embed scc)] = ∅ := by
  simp [eqVars, Pat.at, embed, scc, Term.freeVars]

theorem version_split {u : ℕ} {F C : Multiset Tm} (noVer : ∀ r ∈ C, ∀ u', r ≠ ver u')
    (h : C + (ver 1 ::ₘ 0) = ver u ::ₘ F) : u = 1 ∧ F = C := by
  have mem : ver u ∈ C + (ver 1 ::ₘ 0) := by rw [h]; exact Multiset.mem_cons_self _ _
  rcases Multiset.mem_add.mp mem with mem | mem
  · exact absurd rfl (noVer _ mem u)
  · rcases Multiset.mem_cons.mp mem with mem | mem
    swap
    · exact absurd mem (Multiset.notMem_zero _)
    have hu : u = 1 := by
      have := (tagged_inj.mp mem).2
      cases this
      rfl
    subst hu
    refine ⟨rfl, ?_⟩
    rw [add_comm, Multiset.cons_add, zero_add] at h
    exact ((Multiset.cons_inj_right _).mp h).symm

/-! ## The reachable configurations -/

/-- **The reference configurations reachable from `((c) (c))`.** -/
inductive Reach : Multiset Tm → Prop
  | start : Reach (thread (encE twoCalls) ::ₘ ver 1 ::ₘ 0)
  | first (a : Fin 2) : Reach (thread (encE (.pair (gv (pick a)) cCall)) ::ₘ cite 1 ::ₘ ver 1 ::ₘ 0)
  | second (a b : Fin 2) :
      Reach (thread (encE (.pair (gv (pick a)) (gv (pick b)))) ::ₘ cite 1 ::ₘ cite 1 ::ₘ ver 1 ::ₘ 0)
  | built (a b : Fin 2) :
      Reach (thread (encE (gv (.cell (pick a) (pick b)))) ::ₘ cite 1 ::ₘ cite 1 ::ₘ ver 1 ::ₘ 0)

/-- **Every reference step from a reachable configuration stays reachable.** -/
theorem reach_closed {W : Multiset Tm} (reach : Reach W) {n : ℕ} {s' : Multiset Tm × ℕ}
    (step : CStep defsC (W, n) s') : Reach s'.1 := by
  cases reach with
  | start =>
      rcases cstep_inv noThread0 step with ⟨E, v, w, hX, -⟩ | ⟨u, j, E, w, m, θ, F, mgu, hX, hG, result⟩
      · exact absurd (start_decomp (.inl ⟨v, w, rfl⟩) hX).2 (by intro h; cases h)
      · obtain ⟨hE, hr⟩ := start_decomp (.inr ⟨w, rfl⟩) hX
        simp only [Ex.call.injEq, Ex.val.injEq] at hr
        subst hE hr
        obtain ⟨rfl, rfl⟩ := version_split (C := 0) (u := u) (F := F) (by simp) (by rw [zero_add]; exact hG)
        obtain ⟨a, hl, hrhs⟩ := defsC_get j
        rw [hl] at mgu
        rw [hrhs m] at result
        have ground := call_problem_ground m
        rw [result, ground_mgu_ex mgu ground, ground_rows mgu ground]
        exact .first a
  | first a =>
      rcases cstep_inv noThread1 step with ⟨E, v, w, hX, -⟩ | ⟨u, j, E, w, m, θ, F, mgu, hX, hG, result⟩
      · exact absurd (first_decomp _ (.inl ⟨v, w, rfl⟩) hX).2 (by intro h; cases h)
      · obtain ⟨hE, hr⟩ := first_decomp _ (.inr ⟨w, rfl⟩) hX
        simp only [Ex.call.injEq, Ex.val.injEq] at hr
        subst hE hr
        obtain ⟨rfl, rfl⟩ := version_split (C := cite 1 ::ₘ 0) (u := u) (F := F)
          (by
            intro r member u' same
            rcases Multiset.mem_cons.mp member with rfl | member
            · have := (tagged_inj.mp same).1
              omega
            · exact absurd member (Multiset.notMem_zero _))
          (by rw [Multiset.cons_add, zero_add]; exact hG)
        obtain ⟨b, hl, hrhs⟩ := defsC_get j
        rw [hl] at mgu
        rw [hrhs m] at result
        have ground := call_problem_ground m
        rw [result, ground_mgu_ex mgu ground, ground_rows mgu ground,
          Multiset.cons_swap (ver 1) (cite 1)]
        exact .second a b
  | second a b =>
      rcases cstep_inv noThread2 step with ⟨E, v, w, hX, result⟩ | ⟨u, j, E, w, m, θ, F, mgu, hX, hG, result⟩
      · obtain ⟨rfl, hr⟩ := second_decomp _ _ (.inl ⟨v, w, rfl⟩) hX
        simp only [Ex.pair.injEq, Ex.val.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        rw [result]
        exact .built a b
      · exact absurd (second_decomp _ _ (.inr ⟨w, rfl⟩) hX).2 (by intro h; cases h)
  | built a b =>
      rcases cstep_inv noThread2 step with ⟨E, v, w, hX, -⟩ | ⟨u, j, E, w, m, θ, F, -, hX, -, -⟩
      · exact (built_decomp _ (.inl ⟨v, w, rfl⟩) hX).elim
      · exact (built_decomp _ (.inr ⟨w, rfl⟩) hX).elim

theorem reach_runs {a b : Multiset Tm × ℕ} (run : Relation.ReflTransGen (CStep defsC) a b)
    (reach : Reach a.1) : Reach b.1 := by
  induction run with
  | refl => exact reach
  | @tail c d _ step ih =>
      obtain ⟨W, n⟩ := c
      exact reach_closed ih step

theorem reach_value {W : Multiset Tm} (reach : Reach W) {v : Tm} {F : Multiset Tm}
    (h : W = thread (encE (.val v)) ::ₘ F) : ∃ a b : Fin 2, v = node (embed (pick a)) (embed (pick b)) := by
  have head : ∀ {X : Ex} {G : Multiset Tm}, NoThread G →
      thread (encE X) ::ₘ G = thread (encE (.val v)) ::ₘ F → X = .val v := by
    intro X G noThread same
    rcases Multiset.cons_eq_cons.mp same with ⟨h₁, -⟩ | ⟨-, cs, hG, -⟩
    · exact encE_inj (thread_inj h₁)
    · exact absurd rfl (noThread _ (by rw [hG]; exact Multiset.mem_cons_self _ _) _)
  cases reach with
  | start => cases head noThread0 h
  | first a => cases head noThread1 h
  | second a b => cases head noThread2 h
  | built a b =>
      have same := head noThread2 h
      simp only [gv, Ex.val.injEq] at same
      exact ⟨a, b, same.symm⟩

/-- **In evaluation contexts, every value of `((c) (c))` is one of the four.** -/
theorem reference_values {n m : ℕ} {v : Tm} {F : Multiset Tm}
    (run : Relation.ReflTransGen (CStep defsC) (thread (encE twoCalls) ::ₘ ver 1 ::ₘ 0, n)
      (thread (encE (.val v)) ::ₘ F, m)) :
    ∃ a b : Fin 2, v = node (embed (pick a)) (embed (pick b)) :=
  reach_value (reach_runs run .start) rfl

/-- **On the machine, every value of `((c) (c))` is one of the four**; with `answers_multiply`, the
answers are exactly the four. -/
theorem machine_values {n' : ℕ} {v : Tm} {F' : Multiset SRow}
    (run : Relation.ReflTransGen (KStep defsC) (.ev twoCalls [] ::ₘ .version 1 ::ₘ 0, 1)
      (.ret v [] ::ₘ F', n')) :
    ∃ a b : Fin 2, v = node (embed (pick a)) (embed (pick b)) := by
  obtain ⟨m, -, reference⟩ := halted_is_value run
  rw [unloadAll_cons, show unloadAll (0 : Multiset SRow) = 0 from rfl] at reference
  exact reference_values reference

#print axioms cstep_inv
#print axioms version_split
#print axioms reach_closed
#print axioms reach_runs
#print axioms reference_values
#print axioms machine_values

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested.Controls
