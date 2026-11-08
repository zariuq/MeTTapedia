import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterJoin

/-!
# The two-way interpreter join for calls with variables

* `interpreter_join`: for every compiled answer to a call with variables (one `EqStep` of the
  program, with any most general unifier), the fixed interpreter `joinMeta` has an administrative
  run (choose the equation, allocate one fresh variable per slot, build the renamed copy) to the
  store's firing, which is admitted, and whose answer under **every** most general unifier is the
  compiled answer under a renaming, the other rows renamed by the same renaming.
* `interpreter_answers`: the whole run, from the stored program to the answer.
* `interpreter_join_on_step`: the same on the ordinary step: one translated firing of the compiled
  program answers the call, and a run of translated firings of the compiled interpreter, a fixed
  family of thirteen schemas, reaches a configuration representing that answer renamed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded getD_mem)

theorem bounded_list {n : ℕ} {l : List Tm} (h : ∀ t ∈ l, Bounded n t) : ∀ t ∈ l, Bounded n t := h

/-- **The store's problem is solvable**: the copied left-hand side unifies with the call whenever the
equation does. -/
theorem store_unifiable {e : ProgramEquations.Equation} {t : Tm} {n n₀ m : ℕ} (tB : Bounded n t)
    (below : n ≤ n₀) (above : n₀ + slots e ≤ m) {θc : Subst rows} (mgu : IsMGU [(e.lhs.at n, t)] θc) :
    ∃ θ', IsMGU [(jApply.lhs.at m, ttup 169 [Pat.fill (freshVars n₀ (slots e)) e.lhs,
      Pat.fill (freshVars n₀ (slots e)) e.rhs, t])] θ' := by
  apply exists_isMGU
  have envLength : (freshVars n₀ (slots e)).length = slots e := freshVars_length n₀ _
  have withinL : ∀ x ∈ e.lhs.vars, x < (freshVars n₀ (slots e)).length := fun x hx => by
    rw [envLength]; exact lt_slots (List.mem_append_left _ hx)
  have withinR : ∀ x ∈ e.rhs.vars, x < (freshVars n₀ (slots e)).length := fun x hx => by
    rw [envLength]; exact lt_slots (List.mem_append_right _ hx)
  let δ : Subst rows := fun w =>
    if w = (m, 0) then θc.applyTerm t else if w = (m, 1) then θc.applyTerm (e.rhs.at n)
      else θc.applyTerm (unfresh n n₀ (slots e) w)
  have δcopy : ∀ u : Tm, (∀ w ∈ u.freeVars, w.1 < m) →
      δ.applyTerm u = θc.applyTerm ((unfresh n n₀ (slots e)).applyTerm u) := by
    intro u hu
    rw [← Subst.applyTerm_comp]
    refine Subst.applyTerm_congr fun w hw => ?_
    have lt := hu w hw
    have ne₀ : w ≠ (m, 0) := fun h => by rw [h] at lt; exact lt_irrefl m lt
    have ne₁ : w ≠ (m, 1) := fun h => by rw [h] at lt; exact lt_irrefl m lt
    simp only [δ, if_neg ne₀, if_neg ne₁]
    rfl
  have copyBounded : Bounded (n₀ + slots e) (Pat.fill (freshVars n₀ (slots e)) e.lhs) ∧
      Bounded (n₀ + slots e) (Pat.fill (freshVars n₀ (slots e)) e.rhs) :=
    ⟨fill_bounded (freshVars_bounded n₀ _) _, fill_bounded (freshVars_bounded n₀ _) _⟩
  have undoneL : (unfresh n n₀ (slots e)).applyTerm (Pat.fill (freshVars n₀ (slots e)) e.lhs) =
      e.lhs.at n := by
    rw [← matcher_at (n := n) _ withinL]
    exact copy_undone _ fun x hx => envLength ▸ withinL x hx
  have undoneR : (unfresh n n₀ (slots e)).applyTerm (Pat.fill (freshVars n₀ (slots e)) e.rhs) =
      e.rhs.at n := by
    rw [← matcher_at (n := n) _ withinR]
    exact copy_undone _ fun x hx => envLength ▸ withinR x hx
  have unfreshT : (unfresh n n₀ (slots e)).applyTerm t = t :=
    Subst.applyTerm_eq_self fun w hw => unfresh_below (lt_of_lt_of_le (tB w hw) below)
  refine ⟨δ, ?_⟩
  rw [unifies_single, show (jApply.lhs.at m) = ttup 169 [.var (m, 0), .var (m, 1), .var (m, 0)] from rfl]
  have v0 : δ (m, 0) = θc.applyTerm t := by simp [δ]
  have v1 : δ (m, 1) = θc.applyTerm (e.rhs.at n) := by simp [δ]
  have dL : δ.applyTerm (Pat.fill (freshVars n₀ (slots e)) e.lhs) = θc.applyTerm (e.lhs.at n) := by
    rw [δcopy _ fun w hw => lt_of_lt_of_le (copyBounded.1 w hw) above, undoneL]
  have dR : δ.applyTerm (Pat.fill (freshVars n₀ (slots e)) e.rhs) = θc.applyTerm (e.rhs.at n) := by
    rw [δcopy _ fun w hw => lt_of_lt_of_le (copyBounded.2 w hw) above, undoneR]
  have dt : δ.applyTerm t = θc.applyTerm t := by
    rw [δcopy t fun w hw => by have := tB w hw; omega, unfreshT]
  have compiled : θc.applyTerm (e.lhs.at n) = θc.applyTerm t := (unifies_single θc _ _).mp mgu.unifies
  simp only [ttup, tseq, apply_node, Subst.applyTerm_var, Subst.applyTerm_const, v0, v1, dL, dR, dt,
    compiled]

theorem jApply_index : joinMeta.get ⟨12, by decide⟩ = jApply := rfl

theorem store_rhs (θ' : Subst rows) (m : ℕ) : θ'.applyTerm (jApply.rhs.at m) = ttup 173 [θ' (m, 1)] := by
  show θ'.applyTerm (node (.const 173) (node (.var (m, 1)) (.const 0))) = _
  rw [apply_node, apply_node]
  rfl

theorem map_eqData_get (prog : Program) (j : Fin prog.length) :
    (prog.map eqData).get ⟨j, by simp⟩ = eqData (prog.get j) := by simp

/-- **The two-way interpreter join.** -/
theorem interpreter_join {prog : Program} (j : Fin prog.length) {t : Tm} {F : Multiset Tm} {n : ℕ}
    (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f) {θc : Subst rows}
    (mgu : IsMGU [((prog.get j).lhs.at n, t)] θc) :
    ∃ m L R, Relation.ReflTransGen (EqStep joinMeta)
        (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n) (thread (ttup 169 [L, R, t]) ::ₘ F, m) ∧
      (∃ θ', IsMGU [(jApply.lhs.at m, ttup 169 [L, R, t])] θ') ∧
      ∀ θ', IsMGU [(jApply.lhs.at m, ttup 169 [L, R, t])] θ' →
        EqStep joinMeta (thread (ttup 169 [L, R, t]) ::ₘ F, m)
          (thread (ttup 173 [θ' (m, 1)]) ::ₘ F.map θ'.applyTerm, m + 1) ∧
        ∃ κ : Subst rows, IsRenaming κ ∧ θ' (m, 1) = κ.applyTerm (θc.applyTerm ((prog.get j).rhs.at n)) ∧
          ∀ f ∈ F, θ'.applyTerm f = κ.applyTerm (θc.applyTerm f) := by
  -- the equation, its codes, its slots and the allocation scope
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
  -- allocation
  have alloc := alloc_run (embed (codeOf (bcode (prog.get j).lhs))) (embed (codeOf (bcode (prog.get j).rhs)))
    t F (slots (prog.get j)) [] (n + j + 2) (by simp) (embed_bounded _ _) (embed_bounded _ _)
    (mono (by omega) tB) (fun f m => mono (by omega) (FB f m))
  rw [List.append_nil] at alloc
  -- the environment of fresh variables
  have envB : ∀ s ∈ freshVars (n + j + 2) (slots (prog.get j)),
      Bounded (n + j + 2 + slots (prog.get j)) s := freshVars_bounded _ _
  have envLength : (freshVars (n + j + 2) (slots (prog.get j))).length = slots (prog.get j) :=
    freshVars_length _ _
  have withinL : ∀ x ∈ (prog.get j).lhs.vars, x < (freshVars (n + j + 2) (slots (prog.get j))).length :=
    fun x hx => by rw [envLength]; exact lt_slots (List.mem_append_left _ hx)
  have withinR : ∀ x ∈ (prog.get j).rhs.vars, x < (freshVars (n + j + 2) (slots (prog.get j))).length :=
    fun x hx => by rw [envLength]; exact lt_slots (List.mem_append_right _ hx)
  -- names for the scopes and the copy
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
  -- build the left-hand side
  have KLB : Bounded (a + 1) (ttup 167 [embed (codeOf (bcode (prog.get j).rhs)), t]) :=
    bounded_ttup (by
      intro s m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at m
      rcases m with rfl | rfl
      · exact embed_bounded _ _
      · exact mono (by omega) tB)
  obtain ⟨i₁, buildL⟩ := build_run (freshVars (n + j + 2) (slots (prog.get j)))
    (ttup 167 [embed (codeOf (bcode (prog.get j).rhs)), t]) F (prog.get j).lhs withinL [] tnil (a + 1)
    (fun s m => mono (by omega) (envB s m)) (bounded_tlist (l := []) (by simp)) KLB (fun f m => mono (by omega) (FB f m))
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
  -- build the right-hand side
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
  -- the whole administrative run
  refine ⟨a + 1 + i₁ + 1 + i₂ + 1, Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs,
    Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).rhs, ?_, ?_, ?_⟩
  · rw [ha] at start buildL doneL buildR doneR ⊢
    have scopes : n + ↑j + 1 + 1 = n + j + 2 := rfl
    rw [scopes] at inst
    exact (((((((choose.tail inst).trans alloc).tail start).trans buildL).tail doneL).trans buildR).tail doneR)
  · exact store_unifiable tB (by omega) (by omega) mgu
  · intro θ' mgu'
    refine ⟨?_, store_answer_renames tB FB (by omega) (by omega) mgu mgu'⟩
    have step := EqStep.call (prog := joinMeta) ⟨12, by decide⟩
      (ttup 169 [Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).lhs,
        Pat.fill (freshVars (n + j + 2) (slots (prog.get j))) (prog.get j).rhs, t]) F _ θ' mgu'
    rw [jApply_index, store_rhs] at step
    exact step

/-- **The interpreted answer, from the stored program**: a run of the interpreter whose answer and
other rows are the compiled ones under a renaming. -/
theorem interpreter_answers {prog : Program} (j : Fin prog.length) {t : Tm} {F : Multiset Tm} {n : ℕ}
    (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f) {θc : Subst rows}
    (mgu : IsMGU [((prog.get j).lhs.at n, t)] θc) :
    ∃ m a F', Relation.ReflTransGen (EqStep joinMeta)
        (thread (ttup 160 [embed (progData prog), t]) ::ₘ F, n) (thread (ttup 173 [a]) ::ₘ F', m) ∧
      ∃ κ : Subst rows, IsRenaming κ ∧ a = κ.applyTerm (θc.applyTerm ((prog.get j).rhs.at n)) ∧
        F' = (F.map θc.applyTerm).map κ.applyTerm := by
  obtain ⟨m, L, R, run, ⟨θ', mgu'⟩, all⟩ := interpreter_join j tB FB mgu
  obtain ⟨last, κ, ren, answer, rows⟩ := all θ' mgu'
  refine ⟨m + 1, θ' (m, 1), F.map θ'.applyTerm, run.tail last, κ, ren, answer, ?_⟩
  rw [Multiset.map_map]
  exact Multiset.map_congr rfl fun f member => rows f member


/-- **The join on the ordinary step.** One translated firing of the compiled program answers the
call; a run of translated firings of the compiled interpreter, a fixed family of schemas, reaches a
configuration representing that answer and the other rows under one renaming. -/
theorem interpreter_join_on_step {prog : Program} (j : Fin prog.length) {t : Tm} {F : List Tm}
    (hTag : ∀ r ∈ F, Tagged r) (tB : Bounded 1 t) (FB : ∀ f ∈ F, Bounded 1 f) {θc : Subst rows}
    (mgu : IsMGU [((prog.get j).lhs.at 1, t)] θc) :
    (∃ D, Translated (compiled prog) (openInitial (thread t :: F), 1) (D, 2) ∧
        ORepresents D (thread (θc.applyTerm ((prog.get j).rhs.at 1)) ::ₘ
          (F : Multiset Tm).map θc.applyTerm) 2) ∧
    ∃ m a F' D, Relation.ReflTransGen (Translated (compiled joinMeta))
        (openInitial (thread (ttup 160 [embed (progData prog), t]) :: F), 1) (D, m) ∧
      ORepresents D (thread (ttup 173 [a]) ::ₘ F') m ∧
      ∃ κ : Subst rows, IsRenaming κ ∧ a = κ.applyTerm (θc.applyTerm ((prog.get j).rhs.at 1)) ∧
        F' = ((F : Multiset Tm).map θc.applyTerm).map κ.applyTerm := by
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
  have FB' : ∀ f ∈ (F : Multiset Tm), Bounded 1 f := fun f member => FB f (Multiset.mem_coe.mp member)
  refine ⟨?_, ?_⟩
  · have rep := openInitial_represents (thread t :: F) (boundAll t tB)
    rw [← Multiset.cons_coe] at rep
    have step := EqStep.call j t (F : Multiset Tm) 1 θc mgu
    obtain ⟨D, firing, rep'⟩ := eqStep_sound rep (fun r member => by
      rcases Multiset.mem_cons.mp member with rfl | member
      · exact tagged_tagged 40 t
      · exact hTag r (Multiset.mem_coe.mp member)) step
    exact ⟨D, firing, rep'⟩
  · obtain ⟨m, a, F', run, κ, ren, answer, rows⟩ := interpreter_answers j tB FB' mgu
    rw [Multiset.cons_coe] at run
    have ttupB : Bounded 1 (ttup 160 [embed (progData prog), t]) := bounded_ttup (by
      intro s member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact embed_bounded 1 _
      · exact tB)
    obtain ⟨D, translated, rep⟩ :=
      (equations_execution joinMeta _ (tagAll _) (boundAll _ ttupB) _ m).1 run
    exact ⟨m, a, F', D, translated, rep, κ, ren, answer, rows⟩

#print axioms store_unifiable
#print axioms interpreter_join
#print axioms interpreter_answers
#print axioms interpreter_join_on_step

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
