import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterConverseSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterJoinControls

/-!
# The interpreter-join converse, and the join both ways

* **The converse** (`interpreter_join_converse`): every answer the interpreter `joinMeta` reaches
  from a stored program and a call, under any most general unifier at every firing, is a compiled
  answer (one firing of `EqStep` on the call) up to renaming both ways: a renaming takes the compiled
  answer and rows to the interpreted ones, and another takes them back. The proof follows the run
  through the stage invariant (`reached_step`), and the last firing is the store's
  (`store_renamed`).
* **The forward direction, both ways** (`interpreter_join_forward`): for every compiled answer the
  interpreter reaches an answer, and the two agree up to renaming both ways.
* **The two-way join** (`interpreter_join_iff`): interpreted and compiled answers agree up to
  renaming.
* **On the ordinary step** (`interpreter_join_converse_on_step`, `interpreter_join_forward_on_step`):
  through `equations_execution`, every run of translated firings of the compiled interpreter that
  has answered represents a renamed compiled answer, which one translated firing of the compiled
  program reaches, and conversely.

Hypotheses: the call and the other rows lie below the call's scope, and the other rows are data
rows (`DataRows`: tagged by a constant other than the thread's), so no unifier turns one into a
thread.

**Controls.**
* `open_call_answers_are_variables`: with `(= (f (s $z)) $z)`, every interpreted answer to `(f $y)`
  is a variable, under every run and every unifier.
* `unmatched_never_interpreted`: with `(= (f b) c)` alone, no run of the interpreter answers
  `(f a)`.
* `two_equations_answers`: with `(= (f a) b)` and `(= (f $x) c)`, every interpreted answer to
  `(f a)` is `b` or `c`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem)

/-! ## Following a run -/

theorem answer_eq {x y : Tm} {G H : Multiset Tm} (same : thread x ::ₘ G = thread y ::ₘ H)
    (free : ThreadFree G) : x = y ∧ G = H := by
  rcases Multiset.cons_eq_cons.mp same with ⟨heads, tails⟩ | ⟨_, cs, inG, _⟩
  · exact ⟨(tagged_inj.mp heads).2, tails⟩
  · exact absurd rfl (free (thread y) (by rw [inG]; exact Multiset.mem_cons.mpr (Or.inl rfl)) y)

theorem ttup_one_inj {k : ℕ} {a b : Tm} (same : ttup k [a] = ttup k [b]) : a = b := by
  simp only [ttup, tseq, node_inj] at same
  exact same.2.1

theorem reached_initial {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) : Reached prog t F (ttup 160 [embed (progData prog), t]) F n := by
  have rowsId : F = F.map (Subst.id rows).applyTerm :=
    ((Multiset.map_congr rfl fun f _ => Subst.applyTerm_id f).trans (Multiset.map_id' F)).symm
  refine ⟨Subst.id rows, copy_id t F, rowsId, by rw [Subst.applyTerm_id]; exact tB, ?_, FB, ?_⟩
  · exact bounded_ttup (by
      intro s member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact embed_bounded n _
      · exact tB)
  · rw [Subst.applyTerm_id]
    exact Stage.select 0

/-- **Every run from a reached state to an answer answers by a renamed compiled answer.** -/
theorem reached_answer {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) (data : DataRows F) {a' : Tm} {G' : Multiset Tm} {m' : ℕ} :
    ∀ {S : Multiset Tm × ℕ}, Relation.ReflTransGen (EqStep joinMeta) S (thread (ttup 173 [a']) ::ₘ G', m') →
      ∀ {s : Tm} {F' : Multiset Tm} {m : ℕ}, S = (thread s ::ₘ F', m) → Reached prog t F s F' m →
        CompiledAnswer prog t F n a' G' := by
  intro S run
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro s F' m hS reached
      obtain ⟨ρ, -, rfl, -, -, -, stage⟩ := reached
      obtain ⟨same, -⟩ := answer_eq (congrArg Prod.fst hS).symm (data.map ρ).free
      exact absurd same (stage_not_answer stage a')
  | head step rest ih =>
      intro s F' m hS reached
      subst hS
      rcases reached_step tB FB data reached step with ⟨s', F'', rfl, reached'⟩ |
        ⟨b', H', rfl, dataH, answer⟩
      · exact ih rfl reached'
      · rcases Relation.ReflTransGen.cases_head rest with same | ⟨c, first, -⟩
        · obtain ⟨hb, hH⟩ := answer_eq (congrArg Prod.fst same) dataH.free
          rw [ttup_one_inj hb, hH] at answer
          exact answer
        · exact absurd first (answer_is_final dataH.free c)

/-- **The interpreter-join converse.** Every answer the interpreter reaches from the stored program
and a call, under any most general unifier at every firing, is a compiled answer to the call up to
renaming both ways. -/
theorem interpreter_join_converse {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) (data : DataRows F) {m : ℕ} {a' : Tm} {G' : Multiset Tm}
    (run : Relation.ReflTransGen (EqStep joinMeta) (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n)
      (thread (ttup 173 [a']) ::ₘ G', m)) :
    ∃ a G, EqStep prog (thread t ::ₘ F, n) (thread a ::ₘ G, n + 1) ∧ RenamedAnswer a G a' G' :=
  reached_answer tB FB data run rfl (reached_initial tB FB)

/-! ## The forward direction, both ways -/

/-- **The administrative run to the store's firing**, with the copy named: R95's run of
`interpreter_join`, ending with the copy built from the allocation `freshVars n₀`. -/
theorem interpreter_reaches_store {prog : Program} (j : Fin prog.length) {t : Tm} {F : Multiset Tm} {n : ℕ}
    (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f) :
    ∃ n₀ m, n ≤ n₀ ∧ n₀ + slots (prog.get j) ≤ m ∧ Relation.ReflTransGen (EqStep joinMeta)
      (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n)
      (thread (ttup 169 [Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).lhs,
        Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).rhs, t]) ::ₘ F, m) := by
  have hlen : j.1 < (prog.map eqData).length := by simp
  have choose := select_run t F (prog.map eqData) ⟨j, hlen⟩ n tB FB
  rw [map_eqData_get] at choose
  have mono : ∀ {a b : ℕ} {s : Tm}, a ≤ b → Bounded a s → Bounded b s := fun le h => h.mono le
  have vbInst : ∀ s ∈ [embed (nat (slots (prog.get j))), embed (codeOf (bcode (prog.get j).lhs)),
      embed (codeOf (bcode (prog.get j).rhs)), t], Bounded (n + j + 1) s := by
    intro s m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · exact embed_bounded _ _
    · exact embed_bounded _ _
    · exact embed_bounded _ _
    · exact mono (by omega) tB
  have inst := meta_step (e := jInst) (k := 4) (by simp [joinMeta]) rfl (by decide) (by decide) vbInst
    (fun f m => mono (by omega) (FB f m))
    (row := ttup 162 [embed (eqData (prog.get j)), t])
    (row' := ttup 164 [embed (nat (slots (prog.get j))), tlist [], embed (codeOf (bcode (prog.get j).lhs)),
      embed (codeOf (bcode (prog.get j).rhs)), t]) rfl
    (by rw [target_k (p := jInst.rhs) (k := 4) rfl (by decide)]; rfl)
  have alloc := alloc_run (embed (codeOf (bcode (prog.get j).lhs))) (embed (codeOf (bcode (prog.get j).rhs)))
    t F (slots (prog.get j)) [] (n + j + 2) (by simp) (embed_bounded _ _) (embed_bounded _ _)
    (mono (by omega) tB) (fun f m => mono (by omega) (FB f m))
  rw [List.append_nil] at alloc
  have envB : ∀ s ∈ freshVars (n + j + 2) (slots (prog.get j)),
      Bounded (n + j + 2 + slots (prog.get j)) s := freshVars_bounded _ _
  have envLength : (freshVars (n + j + 2) (slots (prog.get j))).length = slots (prog.get j) :=
    freshVars_length _ _
  have withinL : ∀ x ∈ (prog.get j).lhs.vars, x < (freshVars (n + j + 2) (slots (prog.get j))).length :=
    fun x hx => by rw [envLength]; exact lt_slots (List.mem_append_left _ hx)
  have withinR : ∀ x ∈ (prog.get j).rhs.vars, x < (freshVars (n + j + 2) (slots (prog.get j))).length :=
    fun x hx => by rw [envLength]; exact lt_slots (List.mem_append_right _ hx)
  obtain ⟨a, ha⟩ : ∃ a, a = n + j + 2 + slots (prog.get j) := ⟨_, rfl⟩
  have aGe : n ≤ a := by omega
  have vbStart : ∀ s ∈ [tlist (freshVars (n + j + 2) (slots (prog.get j))), embed (codeOf (bcode (prog.get j).lhs)),
      embed (codeOf (bcode (prog.get j).rhs)), t], Bounded a s := by
    intro s m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · rw [ha]; exact bounded_tlist envB
    · exact embed_bounded _ _
    · exact embed_bounded _ _
    · exact mono aGe tB
  have start := meta_step (e := jStart) (k := 4) (n := a) (by simp [joinMeta]) rfl (by decide) (by decide)
    vbStart (fun f m => mono aGe (FB f m))
    (row := ttup 164 [embed (nat 0), tlist (freshVars (n + j + 2) (slots (prog.get j))),
      embed (codeOf (bcode (prog.get j).lhs)), embed (codeOf (bcode (prog.get j).rhs)), t])
    (row' := ttup 165 [embed (codeOf (bcode (prog.get j).lhs)), tnil,
      tlist (freshVars (n + j + 2) (slots (prog.get j))), ttup 167 [embed (codeOf (bcode (prog.get j).rhs)), t]])
    rfl (by rw [target_k (p := jStart.rhs) (k := 4) rfl (by decide)]; rfl)
  have KLB : Bounded (a + 1) (ttup 167 [embed (codeOf (bcode (prog.get j).rhs)), t]) :=
    bounded_ttup (by
      intro s m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact embed_bounded _ _
      · exact mono (by omega) tB)
  obtain ⟨i₁, buildL⟩ := build_run (freshVars (n + j + 2) (slots (prog.get j)))
    (ttup 167 [embed (codeOf (bcode (prog.get j).rhs)), t]) F (prog.get j).lhs withinL [] tnil (a + 1)
    (fun s m => mono (by omega) (envB s m)) (bounded_tlist (l := []) (by simp)) KLB
    (fun f m => mono (by omega) (FB f m))
  rw [List.append_nil] at buildL
  have LB : Bounded (a + 1 + i₁) (Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs) :=
    mono (by omega) (fill_bounded envB _)
  have vbDoneL : ∀ s ∈ [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs,
      tlist (freshVars (n + j + 2) (slots (prog.get j))), embed (codeOf (bcode (prog.get j).rhs)), t],
      Bounded (a + 1 + i₁) s := by
    intro s m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · exact LB
    · exact mono (by omega) (bounded_tlist envB)
    · exact embed_bounded _ _
    · exact mono (by omega) tB
  have doneL := meta_step (e := jDoneL) (k := 4) (n := a + 1 + i₁) (by simp [joinMeta]) rfl (by decide)
    (by decide) vbDoneL (fun f m => mono (by omega) (FB f m))
    (row := ttup 165 [embed (codeOf []), tkons (Pat.fill (freshVars (n + j + 2) (slots (prog.get j)))
      (prog.get j).lhs) tnil, tlist (freshVars (n + j + 2) (slots (prog.get j))),
      ttup 167 [embed (codeOf (bcode (prog.get j).rhs)), t]])
    (row' := ttup 165 [embed (codeOf (bcode (prog.get j).rhs)), tnil,
      tlist (freshVars (n + j + 2) (slots (prog.get j))),
      ttup 168 [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs, t]])
    rfl (by rw [target_k (p := jDoneL.rhs) (k := 4) rfl (by decide)]; rfl)
  have KRB : Bounded (a + 1 + i₁ + 1)
      (ttup 168 [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs, t]) :=
    bounded_ttup (by
      intro s m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact mono (by omega) LB
      · exact mono (by omega) tB)
  obtain ⟨i₂, buildR⟩ := build_run (freshVars (n + j + 2) (slots (prog.get j)))
    (ttup 168 [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs, t]) F
    (prog.get j).rhs withinR [] tnil (a + 1 + i₁ + 1)
    (fun s m => mono (by omega) (envB s m)) (bounded_tlist (l := []) (by simp)) KRB
    (fun f m => mono (by omega) (FB f m))
  rw [List.append_nil] at buildR
  have RB : Bounded (a + 1 + i₁ + 1 + i₂)
      (Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).rhs) :=
    mono (by omega) (fill_bounded envB _)
  have vbDoneR : ∀ s ∈ [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).rhs,
      tlist (freshVars (n + j + 2) (slots (prog.get j))),
      Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs, t],
      Bounded (a + 1 + i₁ + 1 + i₂) s := by
    intro s m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at m
    rcases m with rfl | rfl | rfl | rfl
    · exact RB
    · exact mono (by omega) (bounded_tlist envB)
    · exact mono (by omega) LB
    · exact mono (by omega) tB
  have doneR := meta_step (e := jDoneR) (k := 4) (n := a + 1 + i₁ + 1 + i₂) (by simp [joinMeta]) rfl
    (by decide) (by decide) vbDoneR (fun f m => mono (by omega) (FB f m))
    (row := ttup 165 [embed (codeOf []), tkons (Pat.fill (freshVars (n + j + 2) (slots (prog.get j)))
      (prog.get j).rhs) tnil, tlist (freshVars (n + j + 2) (slots (prog.get j))),
      ttup 168 [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs, t]])
    (row' := ttup 169 [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs,
      Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).rhs, t])
    rfl (by rw [target_k (p := jDoneR.rhs) (k := 4) rfl (by decide)]; rfl)
  refine ⟨n + j + 2, a + 1 + i₁ + 1 + i₂ + 1, by omega, by omega, ?_⟩
  rw [ha] at start buildL doneL buildR doneR ⊢
  have scopes : n + ↑j + 1 + 1 = n + j + 2 := rfl
  rw [scopes] at inst
  exact (((((((choose.tail inst).trans alloc).tail start).trans buildL).tail doneL).trans buildR).tail doneR)

theorem freshVars_vars (n₀ : ℕ) : ∀ k, ∀ w ∈ freshVars n₀ k, ∃ x, w = .var x
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, w, h => by
      rcases List.mem_cons.mp h with rfl | h
      · exact ⟨_, rfl⟩
      · exact freshVars_vars n₀ k w h

theorem freshVars_above (n₀ : ℕ) : ∀ k, ∀ w ∈ freshVars n₀ k, ∀ x ∈ w.freeVars, n₀ ≤ x.1
  | 0, _, h => absurd h List.not_mem_nil
  | k + 1, w, h => by
      rcases List.mem_cons.mp h with rfl | h
      · intro x hx
        rw [Term.mem_freeVars_var (σ := rows)] at hx
        rw [hx]
        exact Nat.le_add_right _ _
      · exact freshVars_above n₀ k w h

theorem freshVars_nodup (n₀ : ℕ) : ∀ k, (freshVars n₀ k).Nodup
  | 0 => List.nodup_nil
  | k + 1 => by
      refine List.nodup_cons.mpr ⟨fun member => ?_, freshVars_nodup n₀ k⟩
      have := freshVars_bounded n₀ k _ member (n₀ + k, 5) ((Term.mem_freeVars_var (σ := rows)).mpr rfl)
      exact lt_irrefl _ this

/-- **The allocation is fresh for the caller.** -/
theorem freshVars_fresh {t : Tm} {F : Multiset Tm} {n n₀ : ℕ} (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f)
    (below : n ≤ n₀) (k : ℕ) : FreshFor (freshVars n₀ k) t F := by
  refine ⟨freshVars_vars n₀ k, freshVars_nodup n₀ k, fun w hw x hx caller => ?_⟩
  have above := freshVars_above n₀ k w hw x hx
  rcases caller with hx' | ⟨f, member, hx'⟩
  · exact absurd (tB x hx') (by omega)
  · exact absurd (FB f member x hx') (by omega)

/-- **The forward direction, both ways.** For every compiled answer, the interpreter reaches an
answer, and the two agree up to renaming both ways. -/
theorem interpreter_join_forward {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) (data : DataRows F) {a : Tm} {G : Multiset Tm}
    (step : EqStep prog (thread t ::ₘ F, n) (thread a ::ₘ G, n + 1)) :
    ∃ m a' G', Relation.ReflTransGen (EqStep joinMeta) (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n)
      (thread (ttup 173 [a']) ::ₘ G', m) ∧ RenamedAnswer a G a' G' := by
  obtain ⟨j, θc, mgu, target⟩ := eqStep_inversion data.free step
  obtain ⟨ha, hG⟩ := answer_eq (congrArg Prod.fst target).symm (data.map θc).free
  subst ha hG
  obtain ⟨n₀, m, below, above, run⟩ := interpreter_reaches_store j tB FB
  obtain ⟨θ', mgu'⟩ := store_unifiable tB below above mgu
  have last := EqStep.call (prog := joinMeta) ⟨12, by decide⟩
    (ttup 169 [Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).lhs,
      Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).rhs, t]) F _ θ' mgu'
  rw [jApply_index, store_rhs] at last
  have rowsId : F.map (Subst.id rows).applyTerm = F :=
    (Multiset.map_congr rfl fun f _ => Subst.applyTerm_id f).trans (Multiset.map_id' F)
  have fresh : FreshFor (freshVars n₀ (slots (prog.get j))) ((Subst.id rows).applyTerm t)
      (F.map (Subst.id rows).applyTerm) := by
    rw [Subst.applyTerm_id, rowsId]
    exact freshVars_fresh tB FB below _
  have mono : ∀ {s : Tm}, Bounded n s → Bounded m s := fun h => h.mono (by omega)
  have envB : ∀ s ∈ freshVars n₀ (slots (prog.get j)), Bounded m s :=
    fun s hs => (freshVars_bounded n₀ _ s hs).mono above
  have rowB : Bounded m (ttup 169 [Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).lhs,
      Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).rhs, (Subst.id rows).applyTerm t]) := by
    rw [Subst.applyTerm_id]
    exact bounded_ttup (by
      intro s member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact fill_bounded envB _
      · exact fill_bounded envB _
      · exact mono tB)
  have mguId : IsMGU [(jApply.lhs.at m, ttup 169 [Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).lhs,
      Pat.fill (freshVars n₀ (slots (prog.get j))) (prog.get j).rhs, (Subst.id rows).applyTerm t])] θ' := by
    rw [Subst.applyTerm_id]
    exact mgu'
  obtain ⟨κ, κ', ren, ren', ans, ans', rowsEq⟩ := store_renamed tB FB (copy_id t F) fresh
    (freshVars_length _ _) rowB (fun f member => by rw [Subst.applyTerm_id]; exact mono (FB f member)) mgu mguId
  refine ⟨m + 1, θ' (m, 1), F.map θ'.applyTerm, run.tail last, κ, κ', ren, ren', ans, ans', ?_, ?_⟩
  · rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun f member => ?_
    have := (rowsEq f member).1
    rw [Subst.applyTerm_id] at this
    exact this
  · rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun f member => ?_
    have := (rowsEq f member).2
    rw [Subst.applyTerm_id] at this
    exact this

/-- **The two-way interpreter join.** Interpreted and compiled answers agree up to renaming, both
ways: every compiled answer has an interpreted one renaming it, and every interpreted answer, under
any run and any most general unifiers, renames a compiled one. -/
theorem interpreter_join_iff {prog : Program} {t : Tm} {F : Multiset Tm} {n : ℕ} (tB : Bounded n t)
    (FB : ∀ f ∈ F, Bounded n f) (data : DataRows F) :
    (∀ a G, EqStep prog (thread t ::ₘ F, n) (thread a ::ₘ G, n + 1) →
      ∃ m a' G', Relation.ReflTransGen (EqStep joinMeta) (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n)
        (thread (ttup 173 [a']) ::ₘ G', m) ∧ RenamedAnswer a G a' G') ∧
    (∀ m a' G', Relation.ReflTransGen (EqStep joinMeta) (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n)
        (thread (ttup 173 [a']) ::ₘ G', m) →
      ∃ a G, EqStep prog (thread t ::ₘ F, n) (thread a ::ₘ G, n + 1) ∧ RenamedAnswer a G a' G') :=
  ⟨fun _ _ step => interpreter_join_forward tB FB data step,
    fun _ _ _ run => interpreter_join_converse tB FB data run⟩

/-! ## The converse on the ordinary step -/

/-- **The converse on the ordinary step.** Every run of translated firings of the compiled
interpreter, a fixed family of thirteen schemas, ends in a configuration representing a run of the
interpreter; when that run has answered, one translated firing of the compiled program answers the
call with a compiled answer, and the two agree up to renaming both ways. -/
theorem interpreter_join_converse_on_step {prog : Program} {t : Tm} {F : List Tm}
    (hTag : ∀ r ∈ F, Tagged r) (data : DataRows (F : Multiset Tm)) (tB : Bounded 1 t)
    (FB : ∀ f ∈ F, Bounded 1 f) {D : ProgramTranslation.Config} {m : ℕ}
    (run : Relation.ReflTransGen (ProgramTranslation.Translated (compiled joinMeta))
      (openInitial (thread (ttup 160 [embed (progData prog), t]) :: F), 1) (D, m)) :
    ∃ W', ORepresents D W' m ∧ ∀ a' G', W' = thread (ttup 173 [a']) ::ₘ G' →
      ∃ a G D', ProgramTranslation.Translated (compiled prog) (openInitial (thread t :: F), 1) (D', 2) ∧
        ORepresents D' (thread a ::ₘ G) 2 ∧ RenamedAnswer a G a' G' := by
  have tagAll : ∀ s : Tm, ∀ r ∈ thread s :: F, Tagged r := by
    intro s r member
    rcases List.mem_cons.mp member with rfl | member
    · exact tagged_tagged 40 s
    · exact hTag r member
  have boundAll : ∀ s : Tm, Bounded 1 s → ∀ r ∈ thread s :: F, Bounded 1 r := by
    intro s sB r member
    rcases List.mem_cons.mp member with rfl | member
    · exact bounded_thread sB
    · exact FB r member
  have ttupB : Bounded 1 (ttup 160 [embed (progData prog), t]) := bounded_ttup (by
    intro s member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact embed_bounded 1 _
    · exact tB)
  obtain ⟨W', path, rep⟩ := (equations_execution joinMeta _ (tagAll _) (boundAll _ ttupB) 0 m).2 D run
  refine ⟨W', rep, fun a' G' answered => ?_⟩
  subst answered
  rw [← Multiset.cons_coe] at path
  have FB' : ∀ f ∈ (F : Multiset Tm), Bounded 1 f := fun f member => FB f (Multiset.mem_coe.mp member)
  obtain ⟨a, G, step, renamed⟩ := interpreter_join_converse tB FB' data path
  have start := openInitial_represents (thread t :: F) (boundAll t tB)
  rw [← Multiset.cons_coe] at start
  obtain ⟨D', firing, rep'⟩ := eqStep_sound start (fun r member => by
    rcases Multiset.mem_cons.mp member with rfl | member
    · exact tagged_tagged 40 t
    · exact hTag r (Multiset.mem_coe.mp member)) step
  exact ⟨a, G, D', firing, rep', renamed⟩

/-- **The forward direction on the ordinary step, both ways.** Every translated firing of the
compiled program on the call ends in a configuration representing a compiled step; when it
answers, a run of translated firings of the compiled interpreter reaches a configuration
representing an interpreted answer, and the two agree up to renaming both ways. -/
theorem interpreter_join_forward_on_step {prog : Program} {t : Tm} {F : List Tm}
    (hTag : ∀ r ∈ F, Tagged r) (data : DataRows (F : Multiset Tm)) (tB : Bounded 1 t)
    (FB : ∀ f ∈ F, Bounded 1 f) {D : ProgramTranslation.Config}
    (firing : ProgramTranslation.Translated (compiled prog) (openInitial (thread t :: F), 1) (D, 2)) :
    ∃ W, ORepresents D W 2 ∧ ∀ a G, W = thread a ::ₘ G →
      ∃ m a' G' D', Relation.ReflTransGen (ProgramTranslation.Translated (compiled joinMeta))
          (openInitial (thread (ttup 160 [embed (progData prog), t]) :: F), 1) (D', m) ∧
        ORepresents D' (thread (ttup 173 [a']) ::ₘ G') m ∧ RenamedAnswer a G a' G' := by
  have tagAll : ∀ s : Tm, ∀ r ∈ thread s :: F, Tagged r := by
    intro s r member
    rcases List.mem_cons.mp member with rfl | member
    · exact tagged_tagged 40 s
    · exact hTag r member
  have boundAll : ∀ s : Tm, Bounded 1 s → ∀ r ∈ thread s :: F, Bounded 1 r := by
    intro s sB r member
    rcases List.mem_cons.mp member with rfl | member
    · exact bounded_thread sB
    · exact FB r member
  have start := openInitial_represents (thread t :: F) (boundAll t tB)
  rw [← Multiset.cons_coe] at start
  obtain ⟨W, step, rep⟩ := eqFiring_complete start (fun r member => by
    rcases Multiset.mem_cons.mp member with rfl | member
    · exact tagged_tagged 40 t
    · exact hTag r (Multiset.mem_coe.mp member)) firing
  refine ⟨W, rep, fun a G answered => ?_⟩
  subst answered
  have FB' : ∀ f ∈ (F : Multiset Tm), Bounded 1 f := fun f member => FB f (Multiset.mem_coe.mp member)
  obtain ⟨m, a', G', run, renamed⟩ := interpreter_join_forward tB FB' data step
  have ttupB : Bounded 1 (ttup 160 [embed (progData prog), t]) := bounded_ttup (by
    intro s member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact embed_bounded 1 _
    · exact tB)
  rw [Multiset.cons_coe] at run
  obtain ⟨D', translated, rep'⟩ :=
    (equations_execution joinMeta _ (tagAll _) (boundAll _ ttupB) _ m).1 run
  exact ⟨m, a', G', D', translated, rep', renamed⟩

/-! ## Controls -/

section Controls

/-- `(= (f (s $z)) $z)`, R95's control equation. -/
def eqOpen : ProgramEquations.Equation := ⟨ptag 50 (ptag 51 (.var 0)), .var 0⟩

/-- **Every interpreted answer to an open call is a variable**: with `(= (f (s $z)) $z)`, the call
`(f $y)` beside `(out $y)` is answered, by every run under every unifier, with a variable. -/
theorem open_call_answers_are_variables {m : ℕ} {a' : Tm} {G' : Multiset Tm}
    (run : Relation.ReflTransGen (EqStep joinMeta)
      (thread (ttup 160 [embed (progData [eqOpen]), tagged 50 (.var (0, 0))]) ::ₘ {tagged 70 (.var (0, 0))}, 1)
      (thread (ttup 173 [a']) ::ₘ G', m)) :
    ∃ x, a' = .var x := by
  have tB : Bounded 1 (tagged 50 (.var (0, 0))) := fun v hv => by
    rw [freeVars_tagged, Term.mem_freeVars_var (σ := rows)] at hv
    rw [hv]
    decide
  have FB : ∀ f ∈ ({tagged 70 (.var (0, 0))} : Multiset Tm), Bounded 1 f := by
    intro f member
    rw [Multiset.mem_singleton] at member
    subst member
    intro v hv
    rw [freeVars_tagged, Term.mem_freeVars_var (σ := rows)] at hv
    rw [hv]
    decide
  have data : DataRows ({tagged 70 (.var (0, 0))} : Multiset Tm) := by
    intro f member
    rw [Multiset.mem_singleton] at member
    exact ⟨70, .var (0, 0), by decide, member⟩
  obtain ⟨a, G, step, κ, _κ', ren, _ren', rfl, _back, _rows, _rows'⟩ := interpreter_join_converse tB FB data run
  obtain ⟨j, θc, mgu, target⟩ := eqStep_inversion data.free step
  obtain ⟨rfl, -⟩ := answer_eq (congrArg Prod.fst target).symm (data.map θc).free
  rcases j with ⟨_ | k, hk⟩
  swap
  · exact absurd hk (by simp)
  obtain ⟨ρ, _ρ', isRen, _isRen', toθc, _rest⟩ :=
    mgu_unique_up_to_renaming ProgramInterpreterJoin.Controls.bindY_isMGU mgu
  have answer : θc.applyTerm (([eqOpen].get ⟨0, hk⟩).rhs.at 1) =
      ρ.applyTerm (ProgramInterpreterJoin.Controls.bindY (1, 0)) := toθc (1, 0)
  have unbound : ProgramInterpreterJoin.Controls.bindY (1, 0) = .var (1, 0) :=
    Subst.single_ne (σ := rows) _ (by decide)
  rw [unbound, Subst.applyTerm_var] at answer
  obtain ⟨y, hy⟩ := isRen (1, 0)
  obtain ⟨z, hz⟩ := ren y
  refine ⟨z, ?_⟩
  rw [answer, hy, Subst.applyTerm_var, hz]

/-- `(= (f b) c)`. -/
def eqB : ProgramEquations.Equation := ⟨ptag 50 (.sym 52), .sym 53⟩

/-- **A call no equation matches has no interpreted answer**: with `(= (f b) c)` alone, no run of
the interpreter, under any unifiers, answers `(f a)`. -/
theorem unmatched_never_interpreted {m : ℕ} {a' : Tm} {G' : Multiset Tm} :
    ¬ Relation.ReflTransGen (EqStep joinMeta)
      (thread (ttup 160 [embed (progData [eqB]), tagged 50 (.const 54)]) ::ₘ 0, 1)
      (thread (ttup 173 [a']) ::ₘ G', m) := by
  intro run
  have tB : Bounded 1 (tagged 50 (.const 54)) := fun v hv => by
    rw [freeVars_tagged] at hv
    exact absurd hv Term.not_mem_freeVars_const
  obtain ⟨a, G, step, -⟩ := interpreter_join_converse tB (fun f h => absurd h (Multiset.notMem_zero f))
    (fun f h => absurd h (Multiset.notMem_zero f)) run
  obtain ⟨j, θ, mgu, -⟩ := eqStep_inversion (fun f h => absurd h (Multiset.notMem_zero f)) step
  rcases j with ⟨_ | k, hk⟩
  swap
  · exact absurd hk (by simp)
  have same := (unifies_single θ _ _).mp mgu.unifies
  change θ.applyTerm (tagged 50 (.const 52)) = θ.applyTerm (tagged 50 (.const 54)) at same
  rw [apply_tagged, apply_tagged, tagged_inj, Subst.applyTerm_const, Subst.applyTerm_const] at same
  exact absurd (Term.const.inj same.2) (by decide)

/-- `(= (f a) b)` and `(= (f $x) c)`. -/
def twoEqs : Program := [⟨ptag 50 (.sym 60), .sym 61⟩, ⟨ptag 50 (.var 0), .sym 62⟩]

/-- **No spurious interpreted answer**: with `(= (f a) b)` and `(= (f $x) c)`, every answer the
interpreter reaches for `(f a)`, under any run and any unifiers, is `b` or `c`. -/
theorem two_equations_answers {m : ℕ} {a' : Tm} {G' : Multiset Tm}
    (run : Relation.ReflTransGen (EqStep joinMeta)
      (thread (ttup 160 [embed (progData twoEqs), tagged 50 (.const 60)]) ::ₘ 0, 1)
      (thread (ttup 173 [a']) ::ₘ G', m)) :
    a' = .const 61 ∨ a' = .const 62 := by
  have tB : Bounded 1 (tagged 50 (.const 60)) := fun v hv => by
    rw [freeVars_tagged] at hv
    exact absurd hv Term.not_mem_freeVars_const
  obtain ⟨a, G, step, κ, _κ', _ren, _ren', rfl, _back, _rows, _rows'⟩ := interpreter_join_converse tB
    (fun f h => absurd h (Multiset.notMem_zero f)) (fun f h => absurd h (Multiset.notMem_zero f)) run
  obtain ⟨j, θc, _mgu, target⟩ := eqStep_inversion (fun f h => absurd h (Multiset.notMem_zero f)) step
  have free0 : ThreadFree (Multiset.map θc.applyTerm (0 : Multiset Tm)) := by
    rw [Multiset.map_zero]
    exact fun f h => absurd h (Multiset.notMem_zero f)
  obtain ⟨rfl, -⟩ := answer_eq (congrArg Prod.fst target).symm free0
  rcases j with ⟨_ | _ | k, hk⟩
  · exact .inl rfl
  · exact .inr rfl
  · exact absurd hk (by simp [twoEqs])

end Controls

#print axioms answer_eq
#print axioms reached_initial
#print axioms reached_answer
#print axioms interpreter_join_converse
#print axioms interpreter_reaches_store
#print axioms freshVars_fresh
#print axioms interpreter_join_forward
#print axioms interpreter_join_iff
#print axioms interpreter_join_converse_on_step
#print axioms interpreter_join_forward_on_step
#print axioms open_call_answers_are_variables
#print axioms unmatched_never_interpreted
#print axioms two_equations_answers

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
