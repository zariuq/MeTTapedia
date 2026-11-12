import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.CodomainNarrowing

/-!
# Controls for narrowing

Over `X : Sort 0 ⟶ Sort 0` (unknown 0) and `Y : Sort 0 ⟶ Sort 1` (unknown 1), the store `X par ≐ arr (Y par) gnd`:

* **without narrowing it stops** (negative): the body `arr (Y par) gnd` is not a code of `Sort 0`
  (`no_direct_solve`), so the solver of `PatternSolver` has no rule and no refutation for it (`uniform_solver_stopped`);
* **with narrowing it is solved** (positive): `Y` is narrowed to `Sort 0 ⟶ Sort 0`, then `X` is instantiated; the run
  ends in the empty store and its answer is principal (`narrowed_run`, `narrowed_principal`).

The universe refutation (negative): `X par ≐ arr (sort 0) gnd` over `X : Sort 0 ⟶ Sort 0` is refuted with reason
`levels` (`misfit_refuted`), since `sort 0` is a code of `Sort 1` only.

**The domain condition, by counterexample** (`domain_needed`): over `X : Sort 0 ⟶ Sort 1` and `W : Sort 2 ⟶ Sort 2`,
`X par ≐ W par` is solved by sending both to the parameter, and that solution does not factor through narrowing `W`
to `Sort 2 ⟶ Sort 1`. So narrowing an unknown whose domain is above `X`'s is not exact.

**The domain condition is not the boundary of principality** (`domain_raising`): over `X : Sort 1 ⟶ Sort 2` and
`W : Sort 0 ⟶ Sort 2`, `X par ≐ arr (W par) gnd` is outside the fragment, the solver with narrowing stops on it,
and it has the principal answer `X := arr (W' par) gnd`, `W := W' par` with a new `W' : Sort 1 ⟶ Sort 2`. A rule
that raises a domain is missing.

**A level question** (`level_question`): over `X : Sort 0 ⟶ Sort a` and `Y : Sort 0 ⟶ Sort b`, the same store needs
narrowing where `a < b` and is instantiated directly where `b ≤ a`; the empty level store decides neither, and at every
valuation the store has a principal answer. Unlike the cross store, only the form of the answer depends on the levels.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

open Interface

namespace CumulativeCodes

namespace NarrowingControls

open Narrowing

/-! ## Narrowing, then instantiation -/

/-- `X : Sort 0 ⟶ Sort 0` (unknown 0) and `Y : Sort 0 ⟶ Sort 1` (unknown 1). -/
def ctx : Ctx := [⟨.const 0, .const 0⟩, ⟨.const 0, .const 1⟩]

/-- `X par`. -/
def X : Term ctx := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `arr (Y par) gnd`. -/
def body : Term ctx := ⟨.arr (.app 1 .par) .gnd, .arr (.app (by decide) .par) .gnd⟩

/-- **The store** `X par ≐ arr (Y par) gnd`. -/
def store : EquationStore (Term ctx) := [(X, body)]

theorem store_oneDomain (v : Nat → Nat) : OneDomain v ctx store := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · simp only [store, List.mem_singleton] at he
    subst he
    exact ⟨.app 0, .arr (.app 1) .gnd⟩
  · simp only [store, List.mem_singleton] at he
    subst he
    refine ⟨0, ?_, ?_⟩ <;> intro W hW d hd
    · simp only [X, Tm.unknowns, Finset.mem_insert, Finset.notMem_empty, or_false] at hW
      subst hW
      simp only [ctx, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rfl
    · simp only [body, Tm.unknowns, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
        at hW
      subst hW
      simp only [ctx, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rfl

/-- **Negative: `X` cannot be instantiated by `arr (Y par) gnd`**: that body is not a code of `Sort 0`, since `Y`'s
codomain is `Sort 1`. -/
theorem no_direct_solve (v : Nat → Nat) : ¬ TyA v ctx ctx (Function.update Tm.idA 0 body.1) := by
  intro typed
  have h := typed 0 ⟨.const 0, .const 0⟩ rfl
  rw [Function.update_self] at h
  obtain ⟨hY, _⟩ := Ty.arr_inv (show Ty v ctx 0 (.arr (.app 1 .par) .gnd) 0 from h)
  obtain ⟨d, hd, _, hc⟩ := Ty.app_inv hY
  simp only [ctx, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
  subst hd
  simp at hc

theorem no_direct_assign (v : Nat → Nat) (σ : Assign v ctx ctx) : σ.1 ≠ Function.update Tm.idA 0 body.1 :=
  fun h => no_direct_solve v (h ▸ σ.2)

/-- **Negative: the solver without narrowing stops on the store**, with the equation postponed: no rule of
`PatternSolver` and no refutation applies. -/
theorem uniform_solver_stopped (v : Nat → Nat) : (CumulativeCodes.solver v).Stopped store := by
  refine ⟨fun n τ R' r => ?_, fun reason r => ?_⟩
  · change Rule v store n τ R' at r
    cases r with
    | delete same => simp [X, body, Tm.lower] at same
    | decompose h _ _ _ _ _ => cases h
    | solveLeft hl _ hσ =>
        obtain ⟨hX, _⟩ := Tm.app.inj hl
        subst hX
        exact no_direct_assign v _ hσ
    | solveRight hr _ _ => cases hr
  · change Refutes v store reason at r
    cases r with
    | clash h₁ _ _ => cases h₁
    | levels h₁ _ _ => cases h₁
    | occursLeft hl _ hX _ =>
        obtain ⟨hX', _⟩ := Tm.app.inj hl
        subst hX'
        simp [body, Tm.unknowns] at hX
    | occursRight hr _ _ _ => cases hr

/-- `Y` narrowed to `Sort 0 ⟶ Sort 0`. -/
abbrev narrowed : Ctx := ctx.set 1 ⟨.const 0, .const 0⟩

/-- The narrowing morphism, the identity on codes. -/
def narrowing (v : Nat → Nat) : Assign v ctx narrowed :=
  narrowAssign v ⟨.const 0, .const 0⟩ (W := 1) (dW := ⟨.const 0, .const 1⟩) rfl rfl (Nat.zero_le _)

/-- The instantiation `X := arr (Y par) gnd`, typed at the narrowed context. -/
def solving (v : Nat → Nat) : Assign v narrowed narrowed :=
  ⟨Function.update Tm.idA 0 (Tm.act Tm.idA body.1),
    update_typed_of_ty (dX := ⟨.const 0, .const 0⟩) rfl (by
      rw [Tm.act_id]
      exact .arr (.app (d := ⟨.const 0, .const 0⟩) rfl (.par le_rfl) le_rfl) .gnd)⟩

/-- **Positive: narrowing, then instantiation, solves the store.** -/
theorem narrowed_run (v : Nat → Nat) :
    (Narrowing.solver v).Reaches store narrowed
      ((frames v).comp ((frames v).comp ((frames v).id narrowed) (solving v)) (narrowing v)) [] :=
  .step (NarrowStep.narrowLeft (X := 0) (W := 1) (dX := ⟨.const 0, .const 0⟩) (dW := ⟨.const 0, .const 1⟩)
      rfl (.arr (.app 1) .gnd) (by simp [body, Tm.unknowns]) rfl rfl le_rfl Nat.zero_lt_one rfl)
    (.step (NarrowStep.rule (Rule.solveLeft rfl rfl rfl)) (.refl []))

/-- **Positive: its answer is principal.** -/
theorem narrowed_principal (v : Nat → Nat) :
    (frames v).Principal store
      ((frames v).comp ((frames v).comp ((frames v).id narrowed) (solving v)) (narrowing v)) :=
  solved_principal (narrowed_run v)

/-! ## The universe refutation -/

/-- `X : Sort 0 ⟶ Sort 0`. -/
def ctx₀ : Ctx := [⟨.const 0, .const 0⟩]

/-- `X par`. -/
def X₀ : Term ctx₀ := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `arr (sort 0) gnd`, a code of `Sort 1` and not of `Sort 0`. -/
def large : Term ctx₀ := ⟨.arr (.sort (.const 0)) .gnd, .arr (.sort _) .gnd⟩

/-- **Negative: a universe that does not fit the codomain is refuted**, with reason `levels`. -/
theorem misfit_refuted (v : Nat → Nat) :
    NarrowRefutes v [(X₀, large)] .levels ∧ ¬ (frames v).Solvable [(X₀, large)] := by
  have r : NarrowRefutes v [(X₀, large)] .levels :=
    .misfitLeft (X := 0) (dX := ⟨.const 0, .const 0⟩) rfl rfl rfl
  exact ⟨r, r.sound⟩

/-! ## The domain condition, by counterexample -/

/-- `X : Sort 0 ⟶ Sort 1` (unknown 0) and `W : Sort 2 ⟶ Sort 2` (unknown 1): two domains. -/
def ctxD : Ctx := [⟨.const 0, .const 1⟩, ⟨.const 2, .const 2⟩]

/-- `X par`. -/
def XD : Term ctxD := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `W par`. -/
def WD : Term ctxD := ⟨.app 1 .par, .app (by decide) .par⟩

/-- `X par ≐ W par`. -/
def storeD : EquationStore (Term ctxD) := [(XD, WD)]

/-- The narrowing of `W` to `X`'s codomain with `W`'s domain: `W : Sort 2 ⟶ Sort 1`. -/
def narrowingD (v : Nat → Nat) : Assign v ctxD (ctxD.set 1 ⟨.const 2, .const 1⟩) :=
  narrowAssign v ⟨.const 2, .const 1⟩ (W := 1) (dW := ⟨.const 2, .const 2⟩) rfl rfl (by simp)

theorem both_typed (v : Nat → Nat) : TyA v ctxD [] (fun _ => .par) := by
  intro W d hW
  match W, hW with
  | 0, hW =>
      simp only [ctxD, List.getElem?_cons_zero, Option.some.injEq] at hW
      subst hW
      exact .par (by simp)
  | 1, hW =>
      simp only [ctxD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hW
      subst hW
      exact .par (by simp)
  | n + 2, hW => simp [ctxD] at hW

/-- The solution sending both unknowns to the parameter. -/
def both (v : Nat → Nat) : Assign v ctxD [] := ⟨fun _ => .par, both_typed v⟩

theorem both_solves (v : Nat → Nat) : (frames v).Models (both v) storeD := by
  intro e he
  simp only [storeD, List.mem_singleton] at he
  subst he
  rfl

/-- **Negative: without the domain condition narrowing is not exact.** The solution sending both unknowns to the
parameter does not factor through the narrowing of `W` to `Sort 2 ⟶ Sort 1`: the parameter of `Sort 2` is not a code
of `Sort 1`. -/
theorem domain_needed (v : Nat → Nat) :
    (frames v).Models (both v) storeD ∧
      ¬ Exact (frames v) storeD (narrowingD v) ((frames v).applyStore (narrowingD v) storeD) := by
  refine ⟨both_solves v, fun exact => ?_⟩
  obtain ⟨g, fg, _⟩ := (exact [] (both v)).mp (both_solves v)
  have h : Tm.lower v (Tm.act (fun _ => Tm.par) (.app 1 .par)) =
      Tm.lower v (Tm.act (Tm.compA g.1 Tm.idA) (.app 1 .par)) := fg WD
  rw [Tm.act_comp, Tm.act_id, act_app_par, act_app_par] at h
  have typed : Ty v [] (Level.value v (.const 2)) (g.1 1) (Level.value v (.const 1)) :=
    g.2 1 ⟨.const 2, .const 1⟩ rfl
  have lowered := typed.lower
  rw [← h] at lowered
  have := Ty.par_inv lowered
  simp at this

/-! ## Outside the fragment: a principal answer that needs a raised domain -/

/-- `X : Sort 1 ⟶ Sort 2` (unknown 0) and `W : Sort 0 ⟶ Sort 2` (unknown 1). -/
def ctxR : Ctx := [⟨.const 1, .const 2⟩, ⟨.const 0, .const 2⟩]

/-- `X par`. -/
def XR : Term ctxR := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `arr (W par) gnd`. -/
def bodyR : Term ctxR := ⟨.arr (.app 1 .par) .gnd, .arr (.app (by decide) .par) .gnd⟩

/-- `X par ≐ arr (W par) gnd`. -/
def storeR : EquationStore (Term ctxR) := [(XR, bodyR)]

/-- The context of the answer: one unknown `W' : Sort 1 ⟶ Sort 2`, with `W`'s codomain and `X`'s domain. -/
def answerCtxR : Ctx := [⟨.const 1, .const 2⟩]

theorem answerR_typed (v : Nat → Nat) :
    TyA v ctxR answerCtxR (fun W => if W = 0 then .arr (.app 0 .par) .gnd else .app 0 .par) := by
  intro W d hW
  match W, hW with
  | 0, hW =>
      simp only [ctxR, List.getElem?_cons_zero, Option.some.injEq] at hW
      subst hW
      exact .arr (.app (d := ⟨.const 1, .const 2⟩) rfl (.par le_rfl) le_rfl) .gnd
  | 1, hW =>
      simp only [ctxR, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hW
      subst hW
      exact .app (d := ⟨.const 1, .const 2⟩) rfl (.par (by simp)) le_rfl
  | n + 2, hW => simp [ctxR] at hW

/-- **The answer**: `X := arr (W' par) gnd` and `W := W' par`. -/
def answerR (v : Nat → Nat) : Assign v ctxR answerCtxR := ⟨_, answerR_typed v⟩

theorem answerR_solves (v : Nat → Nat) : (frames v).Models (answerR v) storeR := by
  intro e he
  simp only [storeR, List.mem_singleton] at he
  subst he
  rfl

/-- **The answer is principal**: every solution sends `W` to a code of `Sort 2` over a parameter of `Sort 1`, since
that code is part of `X`'s body, so it factors through `W'`. -/
theorem answerR_principal (v : Nat → Nat) : (frames v).Principal storeR (answerR v) := by
  refine ⟨answerR_solves v, fun Θ f solved => ?_⟩
  have same : Tm.lower v (f.1 0) = Tm.lower v (.arr (f.1 1) .gnd) := by
    have h : Tm.lower v (Tm.act f.1 (.app 0 .par)) = Tm.lower v (Tm.act f.1 (.arr (.app 1 .par) .gnd)) :=
      solves_head solved
    rw [act_app_par] at h
    simp only [Tm.act, Tm.inst_par_self] at h
    exact h
  have bodyX : Ty v Θ 1 (f.1 0) 2 := f.2 0 ⟨.const 1, .const 2⟩ rfl
  have bodyW : Ty v Θ 1 (f.1 1) 2 := (Ty.arr_inv (Ty.of_lower_eq same bodyX)).1
  have typed : TyA v answerCtxR Θ (fun _ => f.1 1) := by
    intro W d hW
    match W, hW with
    | 0, hW =>
        simp only [answerCtxR, List.getElem?_cons_zero, Option.some.injEq] at hW
        subst hW
        exact bodyW
    | n + 1, hW => simp [answerCtxR] at hW
  refine ⟨⟨fun _ => f.1 1, typed⟩, agree_of_unknowns fun W hW => ?_⟩
  match W, hW with
  | 0, _ =>
      show Tm.lower v (f.1 0) = Tm.lower v (Tm.act (fun _ => f.1 1) (.arr (.app 0 .par) .gnd))
      rw [same]
      simp only [Tm.act, Tm.inst_par_self]
  | 1, _ =>
      show Tm.lower v (f.1 1) = Tm.lower v (Tm.act (fun _ => f.1 1) (.app 0 .par))
      rw [act_app_par]
  | n + 2, h => simp [ctxR] at h

theorem no_direct_assignR (v : Nat → Nat) (σ : Assign v ctxR ctxR) :
    σ.1 ≠ Function.update Tm.idA 0 bodyR.1 := by
  intro hσ
  have typed := σ.2 0 ⟨.const 1, .const 2⟩ rfl
  rw [hσ, Function.update_self] at typed
  obtain ⟨hW, _⟩ := Ty.arr_inv (show Ty v ctxR 1 (.arr (.app 1 .par) .gnd) 2 from typed)
  obtain ⟨d, hd, hpar, _⟩ := Ty.app_inv hW
  simp only [ctxR, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
  subst hd
  have := Ty.par_inv hpar
  simp at this

/-- **Outside the fragment the rules here stop on a store with a principal answer.** `X par ≐ arr (W par) gnd`, with
`W`'s domain below `X`'s, has the principal answer `X := arr (W' par) gnd`, `W := W' par`, through a new unknown
`W' : Sort 1 ⟶ Sort 2`; yet the solver with narrowing has no transition and no refutation for it: the instantiation
of `X` passes `X`'s parameter, of `Sort 1`, to `W`, which takes `Sort 0`, and no codomain is too large. The domain
condition of `OneDomain` is a condition of these rules, not the boundary of principality. -/
theorem domain_raising (v : Nat → Nat) :
    (frames v).Principal storeR (answerR v) ∧ (Narrowing.solver v).Stopped storeR := by
  refine ⟨answerR_principal v, fun n τ R' st => ?_, fun reason r => ?_⟩
  · change NarrowStep v storeR n τ R' at st
    cases st with
    | rule r =>
        cases r with
        | delete same => simp [XR, bodyR, Tm.lower] at same
        | decompose h _ _ _ _ _ => cases h
        | solveLeft hl _ hσ =>
            obtain ⟨hX, _⟩ := Tm.app.inj hl
            subst hX
            exact no_direct_assignR v _ hσ
        | solveRight hr _ _ => cases hr
    | narrowLeft hl _ hW hX hdW _ lt _ =>
        obtain ⟨hX', _⟩ := Tm.app.inj hl
        subst hX'
        simp only [bodyR, Tm.unknowns, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty,
          or_false] at hW
        subst hW
        simp only [ctxR, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at hX hdW
        subst hX
        subst hdW
        simp at lt
    | narrowRight hr _ _ _ _ _ _ _ => cases hr
  · change NarrowRefutes v storeR reason at r
    cases r with
    | rule r =>
        cases r with
        | clash h₁ _ _ => cases h₁
        | levels h₁ _ _ => cases h₁
        | occursLeft hl _ hX _ =>
            obtain ⟨hX', _⟩ := Tm.app.inj hl
            subst hX'
            simp [bodyR, Tm.unknowns] at hX
        | occursRight hr _ _ _ => cases hr
    | misfitLeft hl hX misfit =>
        obtain ⟨hX', _⟩ := Tm.app.inj hl
        subst hX'
        simp only [ctxR, List.getElem?_cons_zero, Option.some.injEq] at hX
        subst hX
        simp [rigidFits, bodyR] at misfit
    | misfitRight hr _ _ => cases hr

/-! ## A level question -/

/-- `X : Sort 0 ⟶ Sort a` (unknown 0) and `Y : Sort 0 ⟶ Sort b` (unknown 1), with level variables `a` (index 0) and
`b` (index 1). -/
def ctxL : Ctx := [⟨.const 0, .param 0⟩, ⟨.const 0, .param 1⟩]

/-- `X par`. -/
def XL : Term ctxL := ⟨.app 0 .par, .app (by decide) .par⟩

/-- `arr (Y par) gnd`. -/
def bodyL : Term ctxL := ⟨.arr (.app 1 .par) .gnd, .arr (.app (by decide) .par) .gnd⟩

/-- `X par ≐ arr (Y par) gnd`. -/
def storeL : EquationStore (Term ctxL) := [(XL, bodyL)]

theorem storeL_oneDomain (v : Nat → Nat) : OneDomain v ctxL storeL := by
  refine ⟨fun e he => ?_, fun e he => ?_⟩
  · simp only [storeL, List.mem_singleton] at he
    subst he
    exact ⟨.app 0, .arr (.app 1) .gnd⟩
  · simp only [storeL, List.mem_singleton] at he
    subst he
    refine ⟨0, ?_, ?_⟩ <;> intro W hW d hd
    · simp only [XL, Tm.unknowns, Finset.mem_insert, Finset.notMem_empty, or_false] at hW
      subst hW
      simp only [ctxL, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rfl
    · simp only [bodyL, Tm.unknowns, Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false]
        at hW
      subst hW
      simp only [ctxL, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
      subst hd
      rfl

theorem constants_typed (v : Nat → Nat) :
    TyA v ctxL [] (fun W => if W = 0 then .arr .gnd .gnd else .gnd) := by
  intro W d hW
  match W, hW with
  | 0, _ => exact .arr .gnd .gnd
  | 1, _ => exact .gnd
  | n + 2, hW => simp [ctxL] at hW

theorem storeL_solvable (v : Nat → Nat) : (frames v).Solvable storeL := by
  refine ⟨[], ⟨_, constants_typed v⟩, fun e he => ?_⟩
  simp only [storeL, List.mem_singleton] at he
  subst he
  rfl

theorem direct_typed (v : Nat → Nat) (ba : v 1 ≤ v 0) :
    TyA v ctxL ctxL (Function.update Tm.idA 0 bodyL.1) :=
  update_typed_of_ty (dX := ⟨.const 0, .param 0⟩) rfl
    (.arr (.app (d := ⟨.const 0, .param 1⟩) rfl (.par le_rfl) ba) .gnd)

theorem direct_untyped (v : Nat → Nat) (ab : v 0 < v 1) :
    ¬ TyA v ctxL ctxL (Function.update Tm.idA 0 bodyL.1) := by
  intro typed
  have h := typed 0 ⟨.const 0, .param 0⟩ rfl
  rw [Function.update_self] at h
  obtain ⟨hY, _⟩ := Ty.arr_inv (show Ty v ctxL 0 (.arr (.app 1 .par) .gnd) (v 0) from h)
  obtain ⟨d, hd, _, hc⟩ := Ty.app_inv hY
  simp only [ctxL, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd
  subst hd
  have hc' : v 1 ≤ v 0 := hc
  omega

/-- **Which rule applies is a level question; principality is not.** Where `a < b`, `Y` is narrowed and the direct
instantiation is not typed; where `b ≤ a`, the direct instantiation is typed; the empty level store decides neither
`b ≤ a` nor `a + 1 ≤ b`; and at every valuation the store has a principal answer. -/
theorem level_question :
    (∀ v : Nat → Nat, v 0 < v 1 →
      ¬ TyA v ctxL ctxL (Function.update Tm.idA 0 bodyL.1) ∧
      ∃ σ : Assign v ctxL (ctxL.set 1 ⟨.const 0, .param 0⟩),
        NarrowStep v storeL (ctxL.set 1 ⟨.const 0, .param 0⟩) σ ((frames v).applyStore σ storeL)) ∧
    (∀ v : Nat → Nat, v 1 ≤ v 0 → TyA v ctxL ctxL (Function.update Tm.idA 0 bodyL.1)) ∧
    ¬ LevelStore.Entails [] ⟨.param 1, .param 0⟩ ∧ ¬ LevelStore.Entails [] ⟨.succ (.param 0), .param 1⟩ ∧
    ∀ v : Nat → Nat, ∃ (m : Ctx) (σ : Assign v ctxL m), (frames v).Principal storeL σ := by
  refine ⟨fun v ab => ⟨direct_untyped v ab, ?_⟩, direct_typed, by decide, by decide, fun v => ?_⟩
  · exact ⟨narrowAssign v ⟨.const 0, .param 0⟩ (W := 1) (dW := ⟨.const 0, .param 1⟩) rfl rfl (Nat.le_of_lt ab),
      .narrowLeft (X := 0) (W := 1) (dX := ⟨.const 0, .param 0⟩) (dW := ⟨.const 0, .param 1⟩)
        rfl (.arr (.app 1) .gnd) (by simp [bodyL, Tm.unknowns]) rfl rfl le_rfl ab rfl⟩
  · rcases Narrowing.principal_or_unsolvable storeL (storeL_oneDomain v) with principal | none
    · exact principal
    · exact absurd (storeL_solvable v) none

end NarrowingControls

end CumulativeCodes

#print axioms CumulativeCodes.NarrowingControls.no_direct_solve
#print axioms CumulativeCodes.NarrowingControls.uniform_solver_stopped
#print axioms CumulativeCodes.NarrowingControls.narrowed_run
#print axioms CumulativeCodes.NarrowingControls.narrowed_principal
#print axioms CumulativeCodes.NarrowingControls.misfit_refuted
#print axioms CumulativeCodes.NarrowingControls.domain_needed
#print axioms CumulativeCodes.NarrowingControls.level_question
#print axioms CumulativeCodes.NarrowingControls.answerR_principal
#print axioms CumulativeCodes.NarrowingControls.domain_raising

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
