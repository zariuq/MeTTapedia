import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramUnmatched
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedComplete

/-!
# Reference completeness with unmatched calls

`uruns_unload` maps runs of the machine with unmatched calls to reference runs in evaluation
contexts. Conversely (`ureference_complete`), every reference run with unmatched calls is matched by
a machine run, up to a renaming of fresh scopes fixing scope `0`. An unmatched call introduces no
variable, so the renaming does not change at that step; its negative premise moves from the
reference scope to the machine's, because a unifier at one fresh scope gives one at the other
(`absence_moves`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions

/-- **The negative premise moves with the renaming.** -/
theorem absence_moves {eqs : List NEquation} {m mb : ℕ} {w : Tm} {π' : Equiv.Perm ℕ} (at_m : π' m = mb)
    (none : ∀ e ∈ eqs, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at m, w)]) :
    ∀ e ∈ eqs, ∀ δ : Subst rows, ¬ Unifies δ [(e.lhs.at mb, (sren π').applyTerm w)] := by
  intro e member δ unifies
  refine none e member (δ ∘ₛ sren π') ?_
  rw [unifies_single_iff] at unifies ⊢
  rw [Subst.applyTerm_comp, Subst.applyTerm_comp, sren_at, at_m]
  exact unifies

/-- Machine runs are runs with unmatched calls. -/
theorem lift_kruns {defs : Defs} {a b : Multiset SRow × ℕ} (run : Relation.ReflTransGen (KStep defs) a b) :
    Relation.ReflTransGen (UStep defs) a b := by
  induction run with
  | refl => exact .refl
  | tail _ step ih => exact ih.tail (.machine step)

/-- **One reference step with unmatched calls is simulated, up to renaming.** -/
theorem ucstep_simulated {defs : Defs} {Wa Wa' : Multiset Tm} {na na' : ℕ}
    (step : UCStep defs (Wa, na) (Wa', na')) {Wb : Multiset SRow} {nb : ℕ} {π : Equiv.Perm ℕ}
    (R : Related Wa na Wb nb π) :
    ∃ Wb' nb' π', Relation.ReflTransGen (UStep defs) (Wb, nb) (Wb', nb') ∧ Related Wa' na' Wb' nb' π' := by
  generalize hs : (Wa, na) = start at step
  generalize ht : (Wa', na') = finish at step
  cases step with
  | reference step =>
      rw [← hs, ← ht] at step
      obtain ⟨Wb', nb', π', run, R'⟩ := cstep_simulated step R
      exact ⟨Wb', nb', π', lift_kruns run, R'⟩
  | unmatched u E w F n m fresh none =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht
      have rel := R.rel
      rw [Multiset.map_cons, Multiset.map_cons, sren_thread, fill_subst, sren_ver] at rel
      obtain ⟨s, sIn, same⟩ := find_row rel (Multiset.mem_cons_self _ _)
      have rest₁ := erase_row rel sIn same
      obtain ⟨s₂, s₂In, same₂⟩ := find_row rest₁ (Multiset.mem_cons_self _ _)
      have rest₂ := erase_row rest₁ s₂In same₂
      have isVer := unload_ver (R.clean s₂ (Multiset.mem_of_mem_erase s₂In)) same₂
      subst isVer
      have redex : Redex ((Ex.call (.val w)).subst (sren π)) := .inr ⟨_, rfl⟩
      obtain ⟨s', k, focused, run⟩ := refocus (defs := defs) (Wb.erase s) redex
        (unload_thread (R.clean s sIn) same) nb
      rw [Multiset.cons_erase sIn] at run
      generalize hr : (Ex.call (.val w)).subst (sren π) = r' at focused
      generalize hE : E.subst (sren π) = E' at focused
      cases focused with
      | build v' w' K => cases hr
      | call w' K =>
          simp only [Ex.subst, Ex.call.injEq, Ex.val.injEq] at hr
          subst hr
          have le' : nb ≤ nb + k := Nat.le_add_right _ _
          have threadIn : thread (encE (E.fill (.call (.val w)))) ∈
              thread (encE (E.fill (.call (.val w)))) ::ₘ ver u ::ₘ F := Multiset.mem_cons_self _ _
          have wSame : (sren (moved π m (nb + k))).applyTerm w = (sren π).applyTerm w :=
            sren_congr fun v hv => (R.agree fresh le' threadIn (call_vars hv)).1
          have noneB := absence_moves (moved_at π m (nb + k)) none
          rw [wSame] at noneB
          rw [show Wb.erase s = .version u ::ₘ (Wb.erase s).erase (.version u) from
            (Multiset.cons_erase s₂In).symm] at run
          have last := UStep.unmatched (defs := defs) u ((sren π).applyTerm w) K
            ((Wb.erase s).erase (.version u)) (nb + k) noneB
          have uRun : Relation.ReflTransGen (UStep defs) (Wb, nb)
              (.ap ((sren π).applyTerm w) K ::ₘ .version u ::ₘ (Wb.erase s).erase (.version u), nb + k) := 
            lift_kruns run
          have rel' : unloadAll (SRow.ret ((sren π).applyTerm w) K ::ₘ .citation u ::ₘ .version u ::ₘ
              (Wb.erase s).erase (.version u)) =
              (thread (encE (E.fill (.val w))) ::ₘ cite u ::ₘ ver u ::ₘ F).map (sren π).applyTerm := by
            rw [unloadAll_cons, unloadAll_cons, unloadAll_cons, rest₂, Multiset.map_cons, Multiset.map_cons,
              Multiset.map_cons, sren_cite, sren_ver, sren_thread, fill_subst, hE]
            show thread (encE (plug K (.val ((sren π).applyTerm w)))) ::ₘ _ = _
            rw [plug_ctxOf]
            rfl
          have oldB : ∀ t ∈ thread (encE (E.fill (.val w))) ::ₘ cite u ::ₘ ver u ::ₘ F, Bounded na t := by
            intro t member
            simp only [Multiset.mem_cons] at member
            rcases member with rfl | rfl | rfl | member
            · intro x hx
              rw [mem_thread] at hx
              rcases freeVars_encE_fill E (.call (.val w)) _ hx with hx | hx
              · exact R.boundedA _ threadIn x (mem_thread.mpr hx)
              · rw [encE, freeVars_tagged] at hx
                exact R.boundedA _ threadIn x (call_vars hx)
            · exact fun x hx => (ground_vars hx).elim
            · exact fun x hx => (ground_vars hx).elim
            · exact R.boundedA t (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem member))
          refine ⟨_, _, π, uRun.tail last, ⟨rel', ?_, fun t member => (oldB t member).mono (by omega), ?_,
            R.fixes, by have := R.positiveA; omega, by omega⟩⟩
          · intro r member
            simp only [Multiset.mem_cons] at member
            rcases member with rfl | rfl | rfl | member
            · trivial
            · trivial
            · trivial
            · exact R.clean r (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase member))
          · refine bounded_of_rel rel' fun t member y hy => ?_
            simp only [Multiset.mem_cons] at member
            rcases member with rfl | rfl | rfl | member
            · rw [mem_thread] at hy
              rcases freeVars_encE_fill E (.call (.val w)) _ hy with hy | hy
              · have := R.old_scope threadIn (mem_thread.mpr hy)
                omega
              · rw [encE, freeVars_tagged] at hy
                have := R.old_scope threadIn (call_vars hy)
                omega
            · exact (ground_vars hy).elim
            · exact (ground_vars hy).elim
            · have := R.old_scope (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem member)) hy
              omega

theorem ureference_simulated {defs : Defs} {a a' : Multiset Tm × ℕ}
    (run : Relation.ReflTransGen (UCStep defs) a a') {Wb : Multiset SRow} {nb : ℕ} {π : Equiv.Perm ℕ}
    (R : Related a.1 a.2 Wb nb π) :
    ∃ Wb' nb' π', Relation.ReflTransGen (UStep defs) (Wb, nb) (Wb', nb') ∧ Related a'.1 a'.2 Wb' nb' π' := by
  induction run with
  | refl => exact ⟨Wb, nb, π, .refl, R⟩
  | @tail b c _ step ih =>
      obtain ⟨Wb₁, nb₁, π₁, path, R₁⟩ := ih
      obtain ⟨Wa, na⟩ := b
      obtain ⟨Wb₂, nb₂, π₂, path₂, R₂⟩ := ucstep_simulated step R₁
      exact ⟨Wb₂, nb₂, π₂, path.trans path₂, R₂⟩

/-- **Reference completeness with unmatched calls as values.** -/
theorem ureference_complete (defs : Defs) (l : List SRow) (clean : ∀ s ∈ l, s.Clean)
    (bounded : ∀ s ∈ l, Bounded 1 s.unload) {Wa' : Multiset Tm} {na' : ℕ}
    (run : Relation.ReflTransGen (UCStep defs) (unloadAll (l : Multiset SRow), 1) (Wa', na')) :
    ∃ (Wb' : Multiset SRow) (nb' : ℕ) (π : Equiv.Perm ℕ),
      Relation.ReflTransGen (UStep defs) ((l : Multiset SRow), 1) (Wb', nb') ∧
      unloadAll Wb' = Wa'.map (sren π).applyTerm ∧ π 0 = 0 := by
  have R : Related (unloadAll (l : Multiset SRow)) 1 (l : Multiset SRow) 1 (Equiv.refl ℕ) := by
    refine ⟨?_, fun s member => clean s (Multiset.mem_coe.mp member), ?_,
      fun s member => bounded s (Multiset.mem_coe.mp member), rfl, le_rfl, le_rfl⟩
    · rw [Multiset.map_congr rfl fun t _ => sren_refl t, Multiset.map_id']
    · intro t member
      obtain ⟨s, sIn, rfl⟩ := Multiset.mem_map.mp member
      exact bounded s (Multiset.mem_coe.mp sIn)
  obtain ⟨Wb', nb', π', path, R'⟩ := ureference_simulated run R
  exact ⟨Wb', nb', π', path, R'.rel, R'.fixes⟩

#print axioms absence_moves
#print axioms ucstep_simulated
#print axioms ureference_simulated
#print axioms ureference_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
