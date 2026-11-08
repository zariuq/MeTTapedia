import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterConverseStages

/-!
# The interpreter-join converse: every step keeps the stage invariant

One lemma per stage of `joinMeta`, for every step under every most general unifier:

* `next_select`: from the stored program's suffix, the choice (`jTry`) and the skip (`jSkip`) both
  reach a stage; an empty suffix has no step;
* `next_chosen`: the allocation starts (`jInst`);
* `next_alloc`: one fresh variable is allocated (`jAlloc`), and it is distinct and apart from the
  caller's; with no slot left, the build starts (`jStart`);
* `next_build`, `next_read`: one instruction of the building code runs (`jSym`, `jCell`, `jVar`,
  `jRdSucc`, `jRdZero`), and the left-hand side's end starts the right-hand side (`jDoneL`), whose end
  hands both to the store (`jDoneR`);
* `next_store`: the store's firing (`jApply`) answers, by a renamed compiled answer.

`reached_step` gathers them.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem vals_bounded_of_fill)

theorem next_select {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    (copy : Copy ρ t F) (tB' : Bounded m (ρ.applyTerm t)) (FB' : ∀ f ∈ F.map ρ.applyTerm, Bounded m f)
    (free : ThreadFree (F.map ρ.applyTerm)) (i : ℕ)
    (sB : Bounded m (ttup 160 [embed (codeOf ((prog.map eqData).drop i)), ρ.applyTerm t]))
    {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 160 [embed (codeOf ((prog.map eqData).drop i)), ρ.applyTerm t]) ::ₘ
      F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  by_cases hi : i < prog.length
  · have split : (prog.map eqData).drop i =
        eqData (prog.get ⟨i, hi⟩) :: (prog.map eqData).drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using hi)]
      simp
    rw [split] at step sB
    obtain ⟨r, θ, clash, mgu, rfl⟩ := forced (q := jTry.lhs)
      (vals := [embed (eqData (prog.get ⟨i, hi⟩)), embed (codeOf ((prog.map eqData).drop (i + 1))),
        ρ.applyTerm t]) free step
    have only : ∀ r : Fin joinMeta.length, Clash (joinMeta.get r).lhs jTry.lhs = false →
        r = ⟨0, by decide⟩ ∨ r = ⟨1, by decide⟩ := by decide
    rcases only r clash with rfl | rfl
    · obtain ⟨κ, κ', ren, -, back, κB, newB, eq⟩ := renamed_by (e := jTry) (k := 3)
        (vals := [embed (eqData (prog.get ⟨i, hi⟩)), embed (codeOf ((prog.map eqData).drop (i + 1))),
          ρ.applyTerm t]) sB rfl (by decide) (by decide) FB' mgu
      refine .inl ⟨_, _, eq, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
      rw [target_k (p := jTry.rhs) (k := 3) rfl (by decide), fill_apply]
      simp only [List.map_cons, List.map_nil, apply_embed]
      exact Stage.chosen ⟨i, hi⟩
    · obtain ⟨κ, κ', ren, -, back, κB, newB, eq⟩ := renamed_by (e := jSkip) (k := 3)
        (vals := [embed (eqData (prog.get ⟨i, hi⟩)), embed (codeOf ((prog.map eqData).drop (i + 1))),
          ρ.applyTerm t]) sB rfl (by decide) (by decide) FB' mgu
      refine .inl ⟨_, _, eq, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
      rw [target_k (p := jSkip.rhs) (k := 3) rfl (by decide), fill_apply]
      simp only [List.map_cons, List.map_nil, apply_embed]
      exact Stage.select (i + 1)
  · have empty : (prog.map eqData).drop i = [] := List.drop_eq_nil_of_le (by simpa using hi)
    rw [empty] at step
    obtain ⟨r, -, clash, -, -⟩ := forced (q := ptup 160 [pnil, .var 0]) (vals := [ρ.applyTerm t]) free step
    have allClash : ∀ r : Fin joinMeta.length,
        Clash (joinMeta.get r).lhs (ptup 160 [pnil, .var 0]) = true := by
      decide
    rw [allClash r] at clash
    cases clash

theorem next_chosen {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    (copy : Copy ρ t F) (tB' : Bounded m (ρ.applyTerm t)) (FB' : ∀ f ∈ F.map ρ.applyTerm, Bounded m f)
    (free : ThreadFree (F.map ρ.applyTerm)) (j : Fin prog.length)
    (sB : Bounded m (ttup 162 [embed (eqData (prog.get j)), ρ.applyTerm t])) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 162 [embed (eqData (prog.get j)), ρ.applyTerm t]) ::ₘ
      F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jInst) (r := ⟨2, by decide⟩) rfl
    (by decide) (k := 4) (vals := [embed (nat (slots (prog.get j))), embed (codeOf (bcode (prog.get j).lhs)),
      embed (codeOf (bcode (prog.get j).rhs)), ρ.applyTerm t]) sB rfl (by decide) (by decide) FB' free step
  refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
  rw [target_k (p := jInst.rhs) (k := 4) rfl (by decide), fill_apply]
  simp only [List.map_cons, List.map_nil, apply_embed]
  exact Stage.alloc j (slots (prog.get j)) [] (by simp) (fresh_nil _ _)

theorem next_alloc {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    (copy : Copy ρ t F) (tB' : Bounded m (ρ.applyTerm t)) (FB' : ∀ f ∈ F.map ρ.applyTerm, Bounded m f)
    (free : ThreadFree (F.map ρ.applyTerm)) (j : Fin prog.length) (k : ℕ) (env : List Tm)
    (count : k + env.length = slots (prog.get j)) (fresh : FreshFor env (ρ.applyTerm t) (F.map ρ.applyTerm))
    (sB : Bounded m (ttup 164 [embed (nat k), tlist env, embed (codeOf (bcode (prog.get j).lhs)),
      embed (codeOf (bcode (prog.get j).rhs)), ρ.applyTerm t])) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 164 [embed (nat k), tlist env, embed (codeOf (bcode (prog.get j).lhs)),
      embed (codeOf (bcode (prog.get j).rhs)), ρ.applyTerm t]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  have envB : ∀ w ∈ env, Bounded m w := bounded_of_tlist (bounded_of_ttup sB _ (by simp))
  cases k with
  | zero =>
      obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jStart) (r := ⟨4, by decide⟩)
        rfl (by decide) (k := 4) (vals := [tlist env, embed (codeOf (bcode (prog.get j).lhs)),
          embed (codeOf (bcode (prog.get j).rhs)), ρ.applyTerm t]) sB rfl (by decide) (by decide) FB' free step
      refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
      rw [target_k (p := jStart.rhs) (k := 4) rfl (by decide), fill_apply]
      simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply]
      rw [bcode_eq (prog.get j).lhs]
      have len : (env.map κ.applyTerm).length = slots (prog.get j) := by
        rw [List.length_map]; omega
      exact Stage.build j false (env.map κ.applyTerm) (icode (prog.get j).lhs) [] len
        (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx))
        (runs_start (within_side (prog.get j) false len))
  | succ k =>
      obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jAlloc) (r := ⟨3, by decide⟩)
        rfl (by decide) (k := 5) (vals := [embed (nat k), tlist env, embed (codeOf (bcode (prog.get j).lhs)),
          embed (codeOf (bcode (prog.get j).rhs)), ρ.applyTerm t]) sB rfl (by decide) (by decide) FB' free step
      refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
      have fresh' : FreshFor ((Term.var (m, 5) :: env).map κ.applyTerm) (κ.applyTerm (ρ.applyTerm t))
          ((F.map ρ.applyTerm).map κ.applyTerm) := by
        refine fresh_map (Q := fun x : ℕ × ℕ => x.1 < m ∨ (x.1 = m ∧ 5 ≤ x.2))
          (fresh_cons fresh (fun w hw hx => lt_irrefl m (envB w hw _ hx)) ?_) ren ?_ ?_ back
        · rintro (hx | ⟨f, member, hx⟩)
          · exact lt_irrefl m (tB' _ hx)
          · exact lt_irrefl m (FB' f member _ hx)
        · intro w hw x hx
          rcases List.mem_cons.mp hw with rfl | hw
          · rw [Term.mem_freeVars_var (σ := rows)] at hx
            exact .inr ⟨by simp [hx], by simp [hx]⟩
          · exact .inl (envB w hw x hx)
        · rintro x (hx | ⟨f, member, hx⟩)
          · exact .inl (tB' x hx)
          · exact .inl (FB' f member x hx)
      have stage := Stage.alloc (prog := prog) j k ((Term.var (m, 5) :: env).map κ.applyTerm)
        (by rw [List.length_map, List.length_cons]; omega) fresh'
      rw [target_fresh_k (p := jAlloc.rhs) (k := 5) rfl (by decide), fill_apply]
      simp only [List.cons_append, List.nil_append, List.map_cons, List.map_nil, apply_embed, tlist_apply]
      exact stage

/-- The common hypotheses of a build stage. -/
structure BuildAt (prog : Program) (t : Tm) (F : Multiset Tm) (ρ : Subst rows) (m : ℕ) (j : Fin prog.length)
    (b : Bool) (env : List Tm) (C : List Ins) (S : List Tm) : Prop where
  copy : Copy ρ t F
  tB : Bounded m (ρ.applyTerm t)
  FB : ∀ f ∈ F.map ρ.applyTerm, Bounded m f
  free : ThreadFree (F.map ρ.applyTerm)
  len : env.length = slots (prog.get j)
  fresh : FreshFor env (ρ.applyTerm t) (F.map ρ.applyTerm)
  runs : exec env C S = some [Pat.fill env (side (prog.get j) b)]
  sB : Bounded m (ttup 165 [embed (codeOf (C.map Ins.enc)), tlist S, tlist env, cont (prog.get j) env (ρ.applyTerm t) b])

theorem BuildAt.envB {prog : Program} {t : Tm} {F : Multiset Tm} {ρ : Subst rows} {m : ℕ} {j : Fin prog.length}
    {b : Bool} {env : List Tm} {C : List Ins} {S : List Tm} (h : BuildAt prog t F ρ m j b env C S) :
    ∀ w ∈ env, Bounded m w :=
  bounded_of_tlist (bounded_of_ttup h.sB _ (by simp))

theorem BuildAt.len' {prog : Program} {t : Tm} {F : Multiset Tm} {ρ : Subst rows} {m : ℕ} {j : Fin prog.length}
    {b : Bool} {env : List Tm} {C : List Ins} {S : List Tm} (h : BuildAt prog t F ρ m j b env C S) (κ : Subst rows) :
    (env.map κ.applyTerm).length = slots (prog.get j) := by
  rw [List.length_map, h.len]

theorem next_build_done {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    {j : Fin prog.length} {b : Bool} {env : List Tm} {S : List Tm} (h : BuildAt prog t F ρ m j b env [] S)
    {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 165 [embed (codeOf (([] : List Ins).map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  have copy := h.copy
  have tB' := h.tB
  have FB' := h.FB
  have free := h.free
  have fresh := h.fresh
  have envB := h.envB
  have len' := h.len'
  have sB := h.sB
  have runs := h.runs
  have hS : S = [Pat.fill env (side (prog.get j) b)] := by
    rw [exec, Option.some.injEq] at runs
    exact runs
  subst hS
  cases b with
      | false =>
          obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jDoneL) (r := ⟨10, by decide⟩)
            rfl (by decide) (k := 4) (vals := [Pat.fill env (prog.get j).lhs, tlist env,
              embed (codeOf (bcode (prog.get j).rhs)), ρ.applyTerm t]) sB rfl (by decide) (by decide) FB'
            free step
          refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
          rw [target_k (p := jDoneL.rhs) (k := 4) rfl (by decide), fill_apply]
          simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply, fill_apply]
          rw [bcode_eq (prog.get j).rhs]
          exact Stage.build j true (env.map κ.applyTerm) (icode (prog.get j).rhs) [] (len' κ)
            (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx))
            (runs_start (within_side (prog.get j) true (len' κ)))
      | true =>
          obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jDoneR) (r := ⟨11, by decide⟩)
            rfl (by decide) (k := 4) (vals := [Pat.fill env (prog.get j).rhs, tlist env,
              Pat.fill env (prog.get j).lhs, ρ.applyTerm t]) sB rfl (by decide) (by decide) FB' free step
          refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
          rw [target_k (p := jDoneR.rhs) (k := 4) rfl (by decide), fill_apply]
          simp only [List.map_cons, List.map_nil, tlist_apply, fill_apply]
          exact Stage.store j (env.map κ.applyTerm) (len' κ)
            (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx))

theorem next_build_sym {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    {j : Fin prog.length} {b : Bool} {env : List Tm} {k : ℕ} {C : List Ins} {S : List Tm}
    (h : BuildAt prog t F ρ m j b env (.sym k :: C) S) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 165 [embed (codeOf ((Ins.sym k :: C).map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  have copy := h.copy
  have tB' := h.tB
  have FB' := h.FB
  have free := h.free
  have fresh := h.fresh
  have envB := h.envB
  have len' := h.len'
  have sB := h.sB
  have runs := h.runs
  rw [exec] at runs
  obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jSym) (r := ⟨5, by decide⟩)
    rfl (by decide) (k := 5) (vals := [.const k, embed (codeOf (C.map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b]) sB rfl (by decide) (by decide) FB' free step
  refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
  rw [target_k (p := jSym.rhs) (k := 5) rfl (by decide), fill_apply]
  simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply, cont_apply, Subst.applyTerm_const]
  have runs' := runs_next κ runs
  rw [List.map_cons, Subst.applyTerm_const] at runs'
  exact Stage.build j b (env.map κ.applyTerm) C (Term.const k :: S.map κ.applyTerm) (len' κ)
    (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx)) runs'

theorem next_build_var {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    {j : Fin prog.length} {b : Bool} {env : List Tm} {x : ℕ} {C : List Ins} {S : List Tm}
    (h : BuildAt prog t F ρ m j b env (.var x :: C) S) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 165 [embed (codeOf ((Ins.var x :: C).map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  have copy := h.copy
  have tB' := h.tB
  have FB' := h.FB
  have free := h.free
  have fresh := h.fresh
  have envB := h.envB
  have len' := h.len'
  have sB := h.sB
  have runs := h.runs
  by_cases lt : x < env.length
  · rw [exec, if_pos lt] at runs
    obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jVar) (r := ⟨7, by decide⟩)
      rfl (by decide) (k := 5) (vals := [embed (nat x), embed (codeOf (C.map Ins.enc)), tlist S, tlist env,
        cont (prog.get j) env (ρ.applyTerm t) b]) sB rfl (by decide) (by decide) FB' free step
    refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
    rw [target_k (p := jVar.rhs) (k := 5) rfl (by decide), fill_apply]
    simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply, cont_apply]
    have runs' := runs_next κ runs
    rw [List.map_cons] at runs'
    refine Stage.read j b (env.map κ.applyTerm) x (env.map κ.applyTerm) C (S.map κ.applyTerm) (len' κ)
      (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx))
      (by rw [List.length_map]; exact lt) ?_
    rw [getD_map_apply]
    exact runs'
  · rw [exec, if_neg lt] at runs
    cases runs

theorem next_build_cell {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    {j : Fin prog.length} {b : Bool} {env : List Tm} {C : List Ins} {S : List Tm}
    (h : BuildAt prog t F ρ m j b env (.cell :: C) S) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 165 [embed (codeOf ((Ins.cell :: C).map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  have copy := h.copy
  have tB' := h.tB
  have FB' := h.FB
  have free := h.free
  have fresh := h.fresh
  have envB := h.envB
  have len' := h.len'
  have sB := h.sB
  have runs := h.runs
  rcases S with _ | ⟨a, _ | ⟨a', S⟩⟩
  · rw [exec] at runs
    cases runs
  · rw [exec] at runs
    cases runs
  · rw [exec] at runs
    obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jCell)
      (r := ⟨6, by decide⟩) rfl (by decide) (k := 6) (vals := [embed (codeOf (C.map Ins.enc)), a, a',
        tlist S, tlist env, cont (prog.get j) env (ρ.applyTerm t) b]) sB rfl (by decide) (by decide)
      FB' free step
    refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
    rw [target_k (p := jCell.rhs) (k := 6) rfl (by decide), fill_apply]
    simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply, cont_apply]
    have runs' := runs_next κ runs
    rw [List.map_cons, apply_node] at runs'
    exact Stage.build j b (env.map κ.applyTerm) C
      (node (κ.applyTerm a') (κ.applyTerm a) :: S.map κ.applyTerm) (len' κ)
      (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx)) runs'

theorem next_build {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    {j : Fin prog.length} {b : Bool} {env : List Tm} {C : List Ins} {S : List Tm}
    (h : BuildAt prog t F ρ m j b env C S) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 165 [embed (codeOf (C.map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  rcases C with _ | ⟨c, C⟩
  · exact next_build_done h step
  · cases c with
    | sym k => exact next_build_sym h step
    | var x => exact next_build_var h step
    | cell => exact next_build_cell h step

theorem next_read {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} {ρ : Subst rows} {m : ℕ}
    (copy : Copy ρ t F) (tB' : Bounded m (ρ.applyTerm t)) (FB' : ∀ f ∈ F.map ρ.applyTerm, Bounded m f)
    (free : ThreadFree (F.map ρ.applyTerm)) (j : Fin prog.length) (b : Bool) (env : List Tm) (d : ℕ)
    (W : List Tm) (C : List Ins) (S : List Tm) (len : env.length = slots (prog.get j))
    (fresh : FreshFor env (ρ.applyTerm t) (F.map ρ.applyTerm)) (lt : d < W.length)
    (runs : exec env C (W.getD d (.const 0) :: S) = some [Pat.fill env (side (prog.get j) b)])
    (sB : Bounded m (ttup 166 [embed (nat d), tlist W, embed (codeOf (C.map Ins.enc)), tlist S, tlist env,
      cont (prog.get j) env (ρ.applyTerm t) b])) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 166 [embed (nat d), tlist W, embed (codeOf (C.map Ins.enc)), tlist S,
      tlist env, cont (prog.get j) env (ρ.applyTerm t) b]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  have envB : ∀ w ∈ env, Bounded m w := bounded_of_tlist (bounded_of_ttup sB _ (by simp))
  have len' : ∀ κ : Subst rows, (env.map κ.applyTerm).length = slots (prog.get j) := fun κ => by
    rw [List.length_map, len]
  cases W with
  | nil => exact absurd lt (Nat.not_lt_zero _)
  | cons w W =>
      cases d with
      | zero =>
          rw [List.getD_cons_zero] at runs
          obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jRdZero) (r := ⟨9, by decide⟩)
            rfl (by decide) (k := 6) (vals := [w, tlist W, embed (codeOf (C.map Ins.enc)), tlist S, tlist env,
              cont (prog.get j) env (ρ.applyTerm t) b]) sB rfl (by decide) (by decide) FB' free step
          refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
          rw [target_k (p := jRdZero.rhs) (k := 6) rfl (by decide), fill_apply]
          simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply, cont_apply]
          exact Stage.build j b (env.map κ.applyTerm) C ((w :: S).map κ.applyTerm) (len' κ)
            (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx)) (runs_next κ runs)
      | succ d =>
          rw [List.getD_cons_succ] at runs
          obtain ⟨κ, κ', ren, -, back, κB, newB, rfl⟩ := single_step (e := jRdSucc) (r := ⟨8, by decide⟩)
            rfl (by decide) (k := 7) (vals := [embed (nat d), w, tlist W, embed (codeOf (C.map Ins.enc)), tlist S,
              tlist env, cont (prog.get j) env (ρ.applyTerm t) b]) sB rfl (by decide) (by decide) FB' free step
          refine .inl ⟨_, _, rfl, reached_next copy tB' FB' ren (fun x hx => back x (.inl hx)) κB newB ?_⟩
          rw [target_k (p := jRdSucc.rhs) (k := 7) rfl (by decide), fill_apply]
          simp only [List.map_cons, List.map_nil, apply_embed, tlist_apply, cont_apply]
          have runs' := runs_next κ runs
          rw [List.map_cons] at runs'
          refine Stage.read j b (env.map κ.applyTerm) d (W.map κ.applyTerm) C (S.map κ.applyTerm) (len' κ)
            (fresh_next fresh envB tB' FB' ren fun x hx => back x (.inl hx))
            (by rw [List.length_map]; exact Nat.lt_of_succ_lt_succ lt) ?_
          rw [getD_map_apply]
          exact runs'

theorem next_store {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) (data : DataRows F) {ρ : Subst rows} {m : ℕ} (copy : Copy ρ t F)
    (FB' : ∀ f ∈ F.map ρ.applyTerm, Bounded m f) (j : Fin prog.length) (env : List Tm)
    (len : env.length = slots (prog.get j)) (fresh : FreshFor env (ρ.applyTerm t) (F.map ρ.applyTerm))
    (sB : Bounded m (ttup 169 [Pat.fill env (prog.get j).lhs, Pat.fill env (prog.get j).rhs, ρ.applyTerm t]))
    {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 169 [Pat.fill env (prog.get j).lhs, Pat.fill env (prog.get j).rhs,
      ρ.applyTerm t]) ::ₘ F.map ρ.applyTerm, m) target) :
    Next prog t F n m target := by
  obtain ⟨r, θ, clash, mgu, rfl⟩ := forced (q := ptup 169 [.var 0, .var 1, .var 2])
    (vals := [Pat.fill env (prog.get j).lhs, Pat.fill env (prog.get j).rhs, ρ.applyTerm t]) (data.map ρ).free step
  have only : ∀ r : Fin joinMeta.length, Clash (joinMeta.get r).lhs (ptup 169 [.var 0, .var 1, .var 2]) = false →
      r = ⟨12, by decide⟩ := by decide
  have same := only r clash
  subst same
  have mgu' : IsMGU [(jApply.lhs.at m, ttup 169 [Pat.fill env (prog.get j).lhs, Pat.fill env (prog.get j).rhs,
      ρ.applyTerm t])] θ := mgu
  have FBρ : ∀ f ∈ F, Bounded m (ρ.applyTerm f) := fun f member => FB' _ (Multiset.mem_map_of_mem _ member)
  obtain ⟨θc, mguc⟩ := store_unifiable_renamed tB len mgu'.unifies
  obtain ⟨κ, κ', ren, ren', ans, ans', rowsEq⟩ := store_renamed tB FB copy fresh len sB FBρ mguc mgu'
  refine .inr ⟨θ (m, 1), (F.map ρ.applyTerm).map θ.applyTerm, ?_, (data.map ρ).map θ, ?_⟩
  · show (thread (θ.applyTerm (jApply.rhs.at m)) ::ₘ _, m + 1) = _
    rw [store_rhs]
  · refine ⟨_, _, EqStep.call j t F n θc mguc, κ, κ', ren, ren', ans, ans', ?_, ?_⟩
    · rw [Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun f member => (rowsEq f member).1
    · rw [Multiset.map_map, Multiset.map_map]
      exact Multiset.map_congr rfl fun f member => (rowsEq f member).2

/-- **The stage invariant is kept by every step**, under every most general unifier; at the store's
stage the step answers, by a renamed compiled answer. -/
theorem reached_step {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) (data : DataRows F) {s : Tm} {F' : Multiset Tm} {m : ℕ}
    (reached : Reached prog t F s F' m) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread s ::ₘ F', m) target) : Next prog t F n m target := by
  obtain ⟨ρ, copy, rfl, tB', sB, FB', stage⟩ := reached
  have free : ThreadFree (F.map ρ.applyTerm) := (data.map ρ).free
  cases stage with
  | select i => exact next_select copy tB' FB' free i sB step
  | chosen j => exact next_chosen copy tB' FB' free j sB step
  | alloc j k env count fresh => exact next_alloc copy tB' FB' free j k env count fresh sB step
  | build j b env C S len fresh runs => exact next_build ⟨copy, tB', FB', free, len, fresh, runs, sB⟩ step
  | read j b env d W C S len fresh lt runs =>
      exact next_read copy tB' FB' free j b env d W C S len fresh lt runs sB step
  | store j env len fresh => exact next_store tB FB data copy FB' j env len fresh sB step

#print axioms next_select
#print axioms next_chosen
#print axioms next_alloc
#print axioms next_build_done
#print axioms next_build_sym
#print axioms next_build_var
#print axioms next_build_cell
#print axioms next_build
#print axioms next_read
#print axioms next_store
#print axioms reached_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
