import Mettapedia.Logic.ASP.Solver
import Mettapedia.Logic.ASP.CheckerControls

/-!
# Controls for nogoods and the solver transition system

Programs from `CheckerControls`.

## Nogoods

* `p :- not q. q :- not p.`: `{p}` solves the completion nogoods; `{p, q}` does
  not, and the violated nogood is the support nogood of `q`.
* `p :- p.`: `{p}` solves the completion nogoods but violates its loop nogood,
  `{T p}`.
* `p :- q. q :- p. r :- not p.`: `{p, q}` is unfounded before anything is
  assigned, and the reason for `F p` is the one-literal loop nogood `{T p}`.
* `p :- q. q :- p. p :- not r. r :- not p.`: `{p, q}` is not unfounded before
  anything is assigned; it becomes unfounded once the external body `not r` is
  false, that is once `T r`, the complement of its literal, is assigned, and the
  reason for `F p` is then `{T p, T r}`.

Every body here is a unit body, so the variables are the atoms alone.

## Runs

* `p :- not p.` (`liar_run`): `p` is a falsum atom, and the nogood of its rule,
  its body without `not p`, is empty; it is falsified at level 0, so `unsat` in one
  step. Soundness then refutes every stable model (`liar_no_stable_by_run`).
* `p :- not p. p :- q.` (`liarQ_run`), where `p` is no falsum atom: propagate
  `F q` (support); decide `T p`; the support nogood `{T p, T p, F q}` of `p` is
  falsified; conflict analysis resolves it with the reason `{T q}` of `F q` to the
  entailed nogood `{T p}` (`liarQ_learned_entailed`); backjump to `F p` at level 0;
  the rule's nogood `{F p, F p}` is falsified at level 0; `unsat`
  (`liarQ_no_stable_by_run`).
* `p :- not q.` (`onlyP_run`): propagate `F q` (support), then `T p` by the rule's
  nogood `{F q, F p}`; `succeed` with `{p}`, its loop guard decided by the reduct
  checker. The unit body `not q` is no variable (`onlyP_not_isVar_body`).
* A negative control (`selfSupport_no_succeed`): at the total trail `T p` of
  `p :- p.`, which violates no completion nogood, `succeed` cannot fire: the loop
  nogood `{T p}` is falsified.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.ASP.SolverControls

open CheckerControls CheckerControls.Atom Program Relation

/-! ## Completion and loop nogoods -/

theorem choice_p_solution : choice.CompletionSolution (canonical ↑({p} : Finset Atom)) := by
  rw [← finValuation_eq_canonical]
  decide

theorem choice_pq_not_solution : ¬ choice.CompletionSolution (canonical ↑({p, q} : Finset Atom)) := by
  rw [← finValuation_eq_canonical]
  decide

/-- The violated nogood: `q` is true, but its only body, `not p`, is false. -/
theorem choice_pq_support_violated :
    (choice.supportNogood q).Violated (canonical ↑({p, q} : Finset Atom)) := by
  rw [← finValuation_eq_canonical]
  decide

theorem selfSupport_p_loop :
    selfSupport.CompletionSolution (canonical ↑({p} : Finset Atom)) ∧
      (selfSupport.loopNogood {p} p).Violated (canonical ↑({p} : Finset Atom)) ∧
      (selfSupport.loopNogood {p} p).lits = [tAtom p] := by
  rw [← finValuation_eq_canonical]
  decide

theorem unsupportedLoop_unfounded : unsupportedLoop.UnfoundedBy [] {p, q} := by decide

theorem unsupportedLoop_reason : (unsupportedLoop.loopNogood {p, q} p).lits = [tAtom p] := by decide

theorem supportedLoop_not_unfounded : ¬ supportedLoop.UnfoundedBy [] {p, q} := by decide

theorem supportedLoop_unfounded_after : supportedLoop.UnfoundedBy [tAtom r] {p, q} := by decide

theorem supportedLoop_reason : (supportedLoop.loopNogood {p, q} p).lits = [tAtom p, tAtom r] := by
  decide

/-! ## `p :- not p.` is refuted at once -/

/-- The nogood of the liar's rule is empty: `p` is a falsum atom, and its rule has no other
literals. -/
theorem liar_constraint : constraintNogood (⟨p, [], [p]⟩ : Rule Atom) ∈ liar.completionNogoods ∧
    (constraintNogood (⟨p, [], [p]⟩ : Rule Atom)).lits = [] := by
  decide

theorem liar_run : liar.Reachable (.done .unsat) :=
  ReflTransGen.single (Step.fail (δ := constraintNogood ⟨p, [], [p]⟩) (Or.inl liar_constraint.1)
    (fun l hl => by rw [liar_constraint.2] at hl; cases hl) rfl)

/-- The run's verdict, read through soundness. -/
theorem liar_no_stable_by_run (S : Set Atom) : ¬ liar.Stable S := liar.unsat_sound liar_run S

/-! ## A run to `unsat` by conflict analysis: `p :- not p. p :- q.` -/

/-- With the rule `p :- q`, `p` is no falsum atom. -/
def liarQ : Program Atom := [⟨p, [], [p]⟩, ⟨p, [q], []⟩]

theorem liarQ_falsum : liarQ.falsum p = false ∧ liarQ.falsum q = false := by decide

/-- Both bodies are unit bodies, so the variables are the atoms alone: the nogood of `p :- not p` is
`{F p, F p}`, that of `p :- q` is `{T q, F p}`, and the support nogood of `p` is `{T p, T p, F q}`. -/
theorem liarQ_nogoods : liarQ.varFinset = {.atom p, .atom q} ∧
    (headNogood (⟨p, [], [p]⟩ : Rule Atom)).lits = [fAtom p, fAtom p] ∧
    (headNogood (⟨p, [q], []⟩ : Rule Atom)).lits = [tAtom q, fAtom p] ∧
    (liarQ.supportNogood p).lits = [tAtom p, tAtom p, fAtom q] := by
  decide

def liarLearned : Nogood Atom := ⟨[tAtom p], .learned 0⟩

def liarQ1 : State Atom := ⟨[⟨fAtom q, 0, some (liarQ.supportNogood q)⟩], [], 0⟩
def liarQ2 : State Atom := ⟨⟨tAtom p, 1, none⟩ :: liarQ1.trail, [], 0⟩
def liarQ3 : State Atom := ⟨⟨fAtom p, 0, some liarLearned⟩ :: liarQ1.trail, [], 0⟩

theorem liarQ_isVar_p : liarQ.IsVar (.atom p) := ⟨_, List.mem_cons_self, Or.inl rfl⟩
theorem liarQ_isVar_q : liarQ.IsVar (.atom q) := ⟨⟨p, [q], []⟩, by decide, Or.inr (Or.inl List.mem_cons_self)⟩

theorem liarQ_reach2 : liarQ.Reachable (.running liarQ2) := by
  have step1 : liarQ.Step (.running State.initial) (.running liarQ1) :=
    Step.propagate (δ := liarQ.supportNogood q) (l := tAtom q) (Or.inl (by decide))
      ⟨by decide, by decide, by simp [State.Assigned, State.initial]⟩ liarQ_isVar_q
  have step2 : liarQ.Step (.running liarQ1) (.running liarQ2) :=
    Step.decide (l := tAtom p) liarQ_isVar_p (by simp [State.Assigned, liarQ1, fAtom, tAtom])
  exact (ReflTransGen.single step1).tail step2

/-- **Conflict analysis, by resolution**: the falsified support nogood of `p`, resolved with the
reason `{T q}` of `F q` on the trail, gives `{T p, T p}`, which weakens to `{T p}`; no knowledge of the
stable models is used. -/
theorem liarQ_learned_entailed : liarQ.Entailed liarLearned.lits := by
  have inv := liarQ.reachable_inv liarQ_reach2
  have support : liarQ.Derived liarQ2 (liarQ.supportNogood p).lits := Derived.database (Or.inl (by decide))
  have reason : liarQ.Derived liarQ2 (liarQ.supportNogood q).lits :=
    Derived.reason (e := ⟨fAtom q, 0, some (liarQ.supportNogood q)⟩) (List.mem_cons_of_mem _ List.mem_cons_self)
      rfl
  have resolvent := (Derived.resolve (fAtom q) support reason).entailed liarQ inv
  exact Entailed.weaken liarQ resolvent (by decide)

theorem liarQ_run : liarQ.Reachable (.done .unsat) := by
  have step3 : liarQ.Step (.running liarQ2) (.running liarQ3) :=
    Step.backjump (δ := liarQ.supportNogood p) (ε := liarLearned) (l := tAtom p)
      (newer := []) (older := liarQ1.trail) (d := ⟨tAtom p, 1, none⟩)
      (Or.inl (by decide)) (by unfold State.Falsifies; decide) rfl rfl
      liarQ_learned_entailed (by decide) (by decide) (by decide) liarQ_isVar_p
  have step4 : liarQ.Step (.running liarQ3) (.done .unsat) :=
    Step.fail (δ := headNogood ⟨p, [], [p]⟩) (Or.inl (by decide)) (by unfold State.Falsifies; decide) rfl
  exact (liarQ_reach2.tail step3).tail step4

theorem liarQ_no_stable_by_run (S : Set Atom) : ¬ liarQ.Stable S := liarQ.unsat_sound liarQ_run S

/-! ## A run to `sat`: `p :- not q.` -/

def onlyP1 : State Atom := ⟨[⟨fAtom q, 0, some (onlyP.supportNogood q)⟩], [], 0⟩
def onlyP2 : State Atom :=
  ⟨[⟨tAtom p, 0, some (headNogood ⟨p, [], [q]⟩)⟩, ⟨fAtom q, 0, some (onlyP.supportNogood q)⟩], [], 0⟩

/-- The rule's nogood is `{F q, F p}`: its body `not q` is a unit body. -/
theorem onlyP_head : (headNogood (⟨p, [], [q]⟩ : Rule Atom)).lits = [fAtom q, fAtom p] := rfl

theorem onlyP_isVar_q : onlyP.IsVar (.atom q) := ⟨_, List.mem_cons_self, Or.inr (Or.inr List.mem_cons_self)⟩
theorem onlyP_isVar_p : onlyP.IsVar (.atom p) := ⟨_, List.mem_cons_self, Or.inl rfl⟩

/-- The unit body `not q` is no variable. -/
theorem onlyP_not_isVar_body : ¬ onlyP.IsVar (.body ⟨[], [q]⟩) := by
  rintro ⟨r, hr, -, hu, -⟩
  simp only [onlyP, List.mem_cons, List.not_mem_nil, or_false] at hr
  subst hr
  exact hu (by decide)

theorem onlyP_reach2 : onlyP.Reachable (.running onlyP2) := by
  have step1 : onlyP.Step (.running State.initial) (.running onlyP1) :=
    Step.propagate (δ := onlyP.supportNogood q) (l := tAtom q) (Or.inl (by decide))
      ⟨by decide, by decide, by simp [State.Assigned, State.initial]⟩ onlyP_isVar_q
  have step2 : onlyP.Step (.running onlyP1) (.running onlyP2) :=
    Step.propagate (δ := headNogood ⟨p, [], [q]⟩) (l := fAtom p) (Or.inl (by decide))
      ⟨by decide, by decide, by simp [State.Assigned, onlyP1, fAtom]⟩ onlyP_isVar_p
  exact (ReflTransGen.single step1).tail step2

theorem onlyP2_total : ∀ x, onlyP.IsVar x → onlyP2.Assigned x := by
  rintro (a | B) h
  · obtain ⟨r, hr, ha⟩ := h
    simp only [onlyP, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    simp only [List.mem_cons, List.not_mem_nil, or_false, false_or] at ha
    rcases ha with rfl | rfl
    · exact ⟨_, List.mem_cons_self, rfl⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩
  · obtain ⟨r, hr, -, hu, rfl⟩ := h
    simp only [onlyP, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact absurd (by decide) hu

theorem onlyP2_completion : ∀ δ ∈ onlyP.completionNogoods, ¬ onlyP2.Falsifies δ := by
  unfold State.Falsifies
  decide

theorem onlyP_trailModel : onlyP.trailModel onlyP2 = {p} := by decide

theorem onlyP_run : onlyP.Reachable (.done (.sat {p})) := by
  have inv := onlyP.reachable_inv onlyP_reach2
  have loops := (onlyP.loops_ok_iff_isStable inv onlyP2_total onlyP2_completion).mpr (by decide)
  have step := Step.succeed (P := onlyP) onlyP2_total onlyP2_completion loops
  rw [onlyP_trailModel] at step
  exact onlyP_reach2.tail step

/-! ## `succeed` needs the loop nogoods: `p :- p.` -/

/-- A total trail of `p :- p.` with `p` true, by a decision; the unit body `p` is no variable. -/
def selfTotal : State Atom := ⟨[⟨tAtom p, 1, none⟩], [], 0⟩

/-- The nogood of the rule and the support nogood of `p` are both `{T p, F p}`. -/
theorem selfSupport_nogoods : (headNogood (⟨p, [p], []⟩ : Rule Atom)).lits = [tAtom p, fAtom p] ∧
    (selfSupport.supportNogood p).lits = [tAtom p, fAtom p] := by
  decide

theorem selfTotal_completion : ∀ δ ∈ selfSupport.completionNogoods, ¬ selfTotal.Falsifies δ := by
  unfold State.Falsifies
  decide

theorem selfSupport_no_succeed :
    ¬ ∀ (U : Finset Atom), ∀ a ∈ U, ¬ selfTotal.Falsifies (selfSupport.loopNogood U a) := by
  intro loops
  apply loops {p} p (Finset.mem_singleton_self p)
  unfold State.Falsifies
  decide

end Mettapedia.Logic.ASP.SolverControls
