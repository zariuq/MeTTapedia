import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramInterpreterJoinCalls

/-!
# Toward the converse of the interpreter join: step inversion and renamed administrative firings

The converse of `interpreter_answers` says that every answer the interpreter `joinMeta` reaches is a
renamed compiled answer. Its proof follows every run of the interpreter, under any most general
unifier at every firing. This file proves the pieces every stage of that proof uses:

- `eqStep_inversion`: with a single thread, every step fires one equation of the program on that
  thread, under a most general unifier of its problem.
- `tag_clash`: an equation whose left-hand side has another head tag than the thread never fires.
- `admin_step_renames`: on an instance of a rule's left-hand side, every most general unifier is the
  matcher followed by a renaming that is invertible on the matcher's range; the result and the other
  rows are the matcher's under that renaming.
- `answer_is_final`: an answer row ends every run.
- `inst_step_converse`: the stage that starts allocating, for every most general unifier.

What remains is the stage invariant along the whole run (selection, allocation, building both sides,
the store's firing), composing these renamings; it is not proved here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations ProgramCompiled
open ProgramMGURenaming
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
  (matcher Pat.fill matcher_at matcher_fixes matcher_isMGU fill_bounded)

/-- No row is a thread. -/
def ThreadFree (F : Multiset Tm) : Prop := ∀ f ∈ F, ∀ s, f ≠ thread s

/-- **Step inversion.** With a single thread, every step fires an equation of the program on it,
under a most general unifier of its problem, and applies that unifier to the other rows. -/
theorem eqStep_inversion {prog : Program} {r : Tm} {F : Multiset Tm} {n : ℕ} (free : ThreadFree F)
    {target : Multiset Tm × ℕ} (step : EqStep prog (thread r ::ₘ F, n) target) :
    ∃ (j : Fin prog.length) (θ : Subst rows), IsMGU [((prog.get j).lhs.at n, r)] θ ∧
      target = (thread (θ.applyTerm ((prog.get j).rhs.at n)) ::ₘ F.map θ.applyTerm, n + 1) := by
  generalize source : (thread r ::ₘ F, n) = start at step
  cases step with
  | call j t F' n' θ mgu =>
      have sameRows := congrArg Prod.fst source
      have sameScope := congrArg Prod.snd source
      simp only at sameRows sameScope
      subst sameScope
      rcases Multiset.cons_eq_cons.mp sameRows with ⟨heads, tails⟩ | ⟨_, rest, inF, _⟩
      · have same := (tagged_inj.mp heads).2
        subst same
        subst tails
        exact ⟨j, θ, mgu, rfl⟩
      · exact absurd rfl (free (thread t) (by rw [inF]; exact Multiset.mem_cons.mpr (Or.inl rfl)) t)

theorem ptup_at (k : ℕ) (ps : List Pat) (n : ℕ) : (ptup k ps).at n = node (.const k) ((pseq ps).at n) := rfl

/-- **Head tags clash.** -/
theorem tag_clash {k k' : ℕ} {ps : List Pat} {ts : List Tm} {n : ℕ} {θ : Subst rows}
    (unifies : Unifies θ [((ptup k ps).at n, ttup k' ts)]) : k = k' := by
  rw [unifies_single, ptup_at, ttup, apply_node, apply_node, node_inj] at unifies
  have heads := unifies.1
  rw [Subst.applyTerm_const, Subst.applyTerm_const] at heads
  exact Term.const.inj heads

/-- Every rule of the interpreter has a tagged left-hand side, and no tag is the answer's. -/
theorem joinMeta_tags : ∀ e ∈ joinMeta, ∃ k ps, e.lhs = ptup k ps ∧ k ≠ 173 := by
  intro e member
  simp only [joinMeta, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨_, _, rfl, by decide⟩

/-- **An answer row ends every run.** -/
theorem answer_is_final {a : Tm} {F : Multiset Tm} {n : ℕ} (free : ThreadFree F) (target : Multiset Tm × ℕ) :
    ¬ EqStep joinMeta (thread (ttup 173 [a]) ::ₘ F, n) target := by
  intro step
  obtain ⟨j, θ, mgu, _⟩ := eqStep_inversion free step
  obtain ⟨k, ps, shape, differ⟩ := joinMeta_tags _ (List.mem_iff_get.mpr ⟨j, rfl⟩)
  rw [shape] at mgu
  exact differ (tag_clash mgu.unifies)

/-- **A renamed administrative firing.** On an instance of a rule's left-hand side, every most
general unifier is the matcher followed by a renaming, invertible on the matcher's range: the result
and the other rows are the matcher's under that renaming. -/
theorem admin_step_renames {e : ProgramEquations.Equation} {n : ℕ} {vals : List Tm}
    (bounded : ∀ t ∈ vals, Bounded n t) (covers : ∀ x < vals.length, x ∈ e.lhs.vars)
    (within : ∀ x ∈ e.lhs.vars, x < vals.length) {F : Multiset Tm} (rowsBounded : ∀ f ∈ F, Bounded n f)
    {θ : Subst rows} (mgu : IsMGU [(e.lhs.at n, Pat.fill vals e.lhs)] θ) :
    ∃ κ : Subst rows, IsRenaming κ ∧
      θ.applyTerm (e.rhs.at n) = κ.applyTerm ((matcher n vals).applyTerm (e.rhs.at n)) ∧
      F.map θ.applyTerm = F.map κ.applyTerm ∧
      ∃ κ' : Subst rows, IsRenaming κ' ∧ ∀ x, RangeVar (matcher n vals) x → κ'.applyTerm (κ x) = .var x := by
  obtain ⟨κ, κ', isRen, isRen', toθ, _, back, _⟩ :=
    mgu_unique_up_to_renaming (matcher_isMGU bounded covers within) mgu
  refine ⟨κ, isRen, apply_comp_congr toθ _, ?_, κ', isRen', back⟩
  apply Multiset.map_congr rfl
  intro f member
  rw [apply_comp_congr toθ f, matcher_fixes (rowsBounded f member)]

/-- **The stage that starts allocating**, for every most general unifier: the only rule with its tag
fires, and the result is the matcher's next stage under a renaming. -/
theorem inst_step_converse {e : ProgramEquations.Equation} {t : Tm} {F : Multiset Tm} {n : ℕ}
    (free : ThreadFree F) (tB : Bounded n t) (FB : ∀ f ∈ F, Bounded n f) {target : Multiset Tm × ℕ}
    (step : EqStep joinMeta (thread (ttup 162 [embed (eqData e), t]) ::ₘ F, n) target) :
    ∃ κ : Subst rows, IsRenaming κ ∧
      target = ((thread (ttup 164 [embed (nat (slots e)), tlist [], embed (codeOf (bcode e.lhs)),
        embed (codeOf (bcode e.rhs)), t]) ::ₘ F).map κ.applyTerm, n + 1) := by
  obtain ⟨j, θ, mgu, rfl⟩ := eqStep_inversion free step
  have vals : ∀ s ∈ [embed (nat (slots e)), embed (codeOf (bcode e.lhs)), embed (codeOf (bcode e.rhs)), t],
      Bounded n s := by
    intro s member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact embed_bounded _ _
    · exact embed_bounded _ _
    · exact embed_bounded _ _
    · exact tB
  match j with
  | ⟨0, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨1, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨2, _⟩ =>
      have covers : ∀ x < 4, x ∈ jInst.lhs.vars := by decide
      have within : ∀ x ∈ jInst.lhs.vars, x < 4 := by decide
      obtain ⟨κ, isRen, result, rows, _⟩ := admin_step_renames (e := jInst) vals
        (fun x lt => covers x (by simpa using lt)) (fun x member => by simpa using within x member) FB mgu
      refine ⟨κ, isRen, ?_⟩
      change (thread (θ.applyTerm (jInst.rhs.at n)) ::ₘ F.map θ.applyTerm, n + 1) = _
      rw [result, rows, target_k (p := jInst.rhs) (k := 4) rfl (by decide), Multiset.map_cons]
      simp only [thread, apply_tagged]
      rfl
  | ⟨3, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨4, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨5, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨6, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨7, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨8, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨9, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨10, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨11, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)
  | ⟨12, _⟩ => exact absurd (tag_clash mgu.unifies) (by decide)

#print axioms eqStep_inversion
#print axioms tag_clash
#print axioms joinMeta_tags
#print axioms answer_is_final
#print axioms admin_step_renames
#print axioms inst_step_converse

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramInterpreterJoin
