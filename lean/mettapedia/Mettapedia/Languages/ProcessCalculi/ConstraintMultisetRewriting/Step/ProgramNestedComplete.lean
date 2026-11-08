import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedRefocus

/-!
# Every reference run in evaluation contexts is a machine run, up to renaming of fresh scopes

`kruns_unload` maps machine runs to reference runs. This file proves the converse
(`reference_complete`): for every reference run from the unloading of well-formed machine rows,
the machine has a run to rows whose unloading is the reference end under a renaming of scopes that
fixes scope `0`. The renaming is needed: the reference semantics renames an equation into any fresh
scope, the machine into the scope of its firing.

* **One reference step** (`cstep_simulated`): the machine refocuses (`refocus`), then fires the
  same rule. For a call, the reference scope `m` is sent to the machine's scope by composing the
  renaming with a swap, and the machine uses the conjugated unifier, a most general unifier of the
  renamed problem (`isMGU_sren`).
* The invariant: the machine's rows unload to the reference rows renamed; the reference rows name
  scopes below the reference counter, the machine's below its own; the renaming fixes scope `0`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations
open _root_.Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramEquations.Versions

/-! ## Rows whose unloading is a thread, the version row or a redefinition -/

/-- Data rows carry neither the thread tag nor the version or citation tag. -/
def SRow.Clean : SRow → Prop
  | .data k _ => k ≠ 40 ∧ k ≠ 41 ∧ k ≠ 42
  | _ => True

theorem SRow.Clean.subst {s : SRow} (clean : s.Clean) (θ : Subst rows) : (s.subst θ).Clean := by
  cases s <;> exact clean

theorem thread_inj {a b : Tm} (h : thread a = thread b) : a = b := (tagged_inj.mp h).2

theorem unload_thread {s : SRow} (clean : s.Clean) {X : Ex} (h : s.unload = thread (encE X)) :
    (∃ e K, s = .ev e K ∧ plug K e = X) ∨ (∃ v K, s = .ret v K ∧ plug K (.val v) = X) ∨
      (∃ w K, s = .ap w K ∧ plug K (.call (.val w)) = X) := by
  cases s with
  | ev e K => exact .inl ⟨e, K, rfl, encE_inj (thread_inj h)⟩
  | ret v K => exact .inr (.inl ⟨v, K, rfl, encE_inj (thread_inj h)⟩)
  | ap w K => exact .inr (.inr ⟨w, K, rfl, encE_inj (thread_inj h)⟩)
  | version u =>
      have := (tagged_inj.mp h).1
      omega
  | citation u =>
      have := (tagged_inj.mp h).1
      omega
  | redef u =>
      have inner := thread_inj h
      cases X <;> simp [redefTo, encE, tagged_inj] at inner
  | finished =>
      have inner := thread_inj h
      cases X <;> simp [done, encE, tagged] at inner <;> exact absurd inner node_ne_const.symm
  | data k t =>
      have := (tagged_inj.mp h).1
      exact absurd this clean.1

theorem unload_ver {s : SRow} (clean : s.Clean) {u : ℕ} (h : s.unload = ver u) : s = .version u := by
  cases s with
  | version u' =>
      have := (tagged_inj.mp h).2
      cases this
      rfl
  | data k t =>
      have := (tagged_inj.mp h).1
      exact absurd this clean.2.1
  | _ => have := (tagged_inj.mp h).1; simp at this

theorem unload_redef {s : SRow} (clean : s.Clean) {u : ℕ} (h : s.unload = thread (redefTo u)) :
    s = .redef u := by
  cases s with
  | ev e K =>
      have := thread_inj h
      generalize plug K e = e' at this
      cases e' <;> simp [encE, redefTo, tagged_inj] at this
  | ret v K =>
      have := thread_inj h
      generalize plug K (.val v) = e at this
      cases e <;> simp [encE, redefTo, tagged_inj] at this
  | ap w K =>
      have := thread_inj h
      generalize plug K (.call (.val w)) = e at this
      cases e <;> simp [encE, redefTo, tagged_inj] at this
  | redef u' =>
      have := (tagged_inj.mp (thread_inj h)).2
      cases this
      rfl
  | finished =>
      have := thread_inj h
      simp [done, redefTo, tagged] at this
      exact absurd this node_ne_const.symm
  | data k t =>
      have := (tagged_inj.mp h).1
      exact absurd this clean.1
  | _ => have := (tagged_inj.mp h).1; simp at this

/-! ## Variables of filled contexts and of unifiers' images -/

theorem freeVars_encE_fill (E : ECtx) (e e' : Ex) {x : ℕ × ℕ}
    (hx : x ∈ (encE (E.fill e')).freeVars) : x ∈ (encE (E.fill e)).freeVars ∨ x ∈ (encE e').freeVars := by
  induction E with
  | hole => exact .inr hx
  | pairL E b ih =>
      rw [ECtx.fill, encE, freeVars_tagged, mem_freeVars_node] at hx
      rw [ECtx.fill, encE, freeVars_tagged, mem_freeVars_node]
      rcases hx with hx | hx
      · rcases ih hx with h | h
        · exact .inl (.inl h)
        · exact .inr h
      · exact .inl (.inr hx)
  | pairR v E ih =>
      rw [ECtx.fill, encE, freeVars_tagged, mem_freeVars_node] at hx
      rw [ECtx.fill, encE, freeVars_tagged, mem_freeVars_node]
      rcases hx with hx | hx
      · exact .inl (.inl hx)
      · rcases ih hx with h | h
        · exact .inl (.inr h)
        · exact .inr h
  | arg E ih =>
      rw [ECtx.fill, encE, freeVars_tagged] at hx
      rw [ECtx.fill, encE, freeVars_tagged]
      exact ih hx

theorem freeVars_encE_in_fill (E : ECtx) (e : Ex) {x : ℕ × ℕ}
    (hx : x ∈ (encE e).freeVars) : x ∈ (encE (E.fill e)).freeVars := by
  induction E with
  | hole => exact hx
  | pairL E b ih =>
      rw [ECtx.fill, encE, freeVars_tagged, mem_freeVars_node]
      exact .inl ih
  | pairR v E ih =>
      rw [ECtx.fill, encE, freeVars_tagged, mem_freeVars_node]
      exact .inr ih
  | arg E ih =>
      rw [ECtx.fill, encE, freeVars_tagged]
      exact ih

/-- A most general unifier of a call with a left-hand side at `m` introduces only the call's
variables and those of scope `m`. -/
theorem mgu_vars {p : Pat} {m : ℕ} {w : Tm} {θ : Subst rows} (mgu : IsMGU [(p.at m, w)] θ) (t : Tm)
    {x : ℕ × ℕ} (hx : x ∈ (θ.applyTerm t).freeVars) : x ∈ t.freeVars ∨ x.1 = m ∨ x ∈ w.freeVars := by
  rcases Finset.mem_union.mp (mgu.relevant.freeVars_applyTerm_subset t hx) with h | h
  · exact .inl h
  · obtain ⟨e, member, occurs⟩ := (mem_eqVars (σ := rows)).mp h
    rw [List.mem_singleton] at member
    subst member
    rcases occurs with occurs | occurs
    · exact .inr (.inl (at_scope m p x occurs))
    · exact .inr (.inr occurs)

theorem mgu_bounded {p : Pat} {m n : ℕ} {w : Tm} {θ : Subst rows} (mgu : IsMGU [(p.at m, w)] θ)
    (wB : Bounded n w) (le : n ≤ m) {t : Tm} (tB : Bounded (m + 1) t) : Bounded (m + 1) (θ.applyTerm t) :=
  fun x hx => by
    rcases mgu_vars mgu t hx with h | h | h
    · exact tB x h
    · omega
    · have := wB x h
      omega

theorem sren_congr {π π' : Equiv.Perm ℕ} {t : Tm} (agree : ∀ v ∈ t.freeVars, π' v.1 = π v.1) :
    (sren π').applyTerm t = (sren π).applyTerm t :=
  Subst.applyTerm_congr fun v hv => by rw [sren_var, sren_var, agree v hv]

theorem sren_thread (π : Equiv.Perm ℕ) (e : Ex) :
    (sren π).applyTerm (thread (encE e)) = thread (encE (e.subst (sren π))) := by
  rw [thread, apply_tagged, encE_subst]
  rfl

theorem sren_ground (π : Equiv.Perm ℕ) (k u : ℕ) :
    (sren π).applyTerm (tagged k (.const u)) = tagged k (.const u) := by
  rw [apply_tagged]
  rfl

/-! ## Multiset bookkeeping -/

theorem find_row {Wb : Multiset SRow} {W : Multiset Tm} (rel : unloadAll Wb = W) {t : Tm} (tIn : t ∈ W) :
    ∃ s ∈ Wb, s.unload = t := by
  rw [← rel] at tIn
  obtain ⟨s, sIn, same⟩ := Multiset.mem_map.mp tIn
  exact ⟨s, sIn, same⟩

theorem erase_row {Wb : Multiset SRow} {t : Tm} {F : Multiset Tm} (rel : unloadAll Wb = t ::ₘ F) {s : SRow}
    (sIn : s ∈ Wb) (same : s.unload = t) : unloadAll (Wb.erase s) = F := by
  have split : Wb = s ::ₘ Wb.erase s := (Multiset.cons_erase sIn).symm
  rw [split, unloadAll_cons, same] at rel
  exact (Multiset.cons_inj_right _).mp rel

/-! ## One reference step -/

/-- The invariant relating a reference configuration and a machine configuration. -/
structure Related (Wa : Multiset Tm) (na : ℕ) (Wb : Multiset SRow) (nb : ℕ) (π : Equiv.Perm ℕ) : Prop where
  rel : unloadAll Wb = Wa.map (sren π).applyTerm
  clean : ∀ s ∈ Wb, s.Clean
  boundedA : ∀ t ∈ Wa, Bounded na t
  boundedB : ∀ s ∈ Wb, Bounded nb s.unload
  fixes : π 0 = 0
  positiveA : 1 ≤ na
  positiveB : 1 ≤ nb

theorem Related.old_scope {Wa : Multiset Tm} {na : ℕ} {Wb : Multiset SRow} {nb : ℕ} {π : Equiv.Perm ℕ}
    (R : Related Wa na Wb nb π) {t : Tm} (tIn : t ∈ Wa) {v : ℕ × ℕ} (hv : v ∈ t.freeVars) : π v.1 < nb := by
  obtain ⟨s, sIn, same⟩ := find_row R.rel (Multiset.mem_map_of_mem _ tIn)
  have := R.boundedB s sIn (π v.1, v.2) (by rw [same]; exact mem_freeVars_sren.mpr ⟨v, hv, rfl⟩)
  exact this

/-- The renaming sending the reference scope `m` to the machine's scope `mb`. -/
def moved (π : Equiv.Perm ℕ) (m mb : ℕ) : Equiv.Perm ℕ := π.trans (Equiv.swap (π m) mb)

theorem moved_at (π : Equiv.Perm ℕ) (m mb : ℕ) : moved π m mb m = mb := by
  simp [moved, Equiv.swap_apply_left]

theorem moved_old {π : Equiv.Perm ℕ} {m mb x : ℕ} (ne : x ≠ m) (below : π x ≠ mb) : moved π m mb x = π x := by
  simp only [moved, Equiv.trans_apply]
  exact Equiv.swap_apply_of_ne_of_ne (fun h => ne (π.injective h)) below

theorem Related.agree {Wa : Multiset Tm} {na : ℕ} {Wb : Multiset SRow} {nb : ℕ} {π : Equiv.Perm ℕ}
    (R : Related Wa na Wb nb π) {m mb : ℕ} (le : na ≤ m) (le' : nb ≤ mb) {t : Tm} (tIn : t ∈ Wa)
    {v : ℕ × ℕ} (hv : v ∈ t.freeVars) : moved π m mb v.1 = π v.1 ∧ π v.1 < nb := by
  have old := R.old_scope tIn hv
  have below := R.boundedA t tIn v hv
  exact ⟨moved_old (by omega) (by omega), old⟩

theorem unloadAll_subst (θ : Subst rows) (G : Multiset SRow) :
    unloadAll (G.map (SRow.subst θ)) = (unloadAll G).map θ.applyTerm := by
  rw [unloadAll, unloadAll, Multiset.map_map, Multiset.map_map]
  exact Multiset.map_congr rfl fun s _ => SRow.unload_subst θ s

theorem thread_subst (θ : Subst rows) (e : Ex) : thread (encE (e.subst θ)) = θ.applyTerm (thread (encE e)) := by
  rw [thread, thread, apply_tagged, encE_subst]

theorem mem_thread {x : ℕ × ℕ} {t : Tm} : x ∈ (thread t).freeVars ↔ x ∈ t.freeVars := by
  rw [thread, freeVars_tagged]

theorem sren_ver (π : Equiv.Perm ℕ) (u : ℕ) : (sren π).applyTerm (ver u) = ver u := sren_ground π 41 u

theorem sren_cite (π : Equiv.Perm ℕ) (u : ℕ) : (sren π).applyTerm (cite u) = cite u := sren_ground π 42 u

theorem sren_redef (π : Equiv.Perm ℕ) (u : ℕ) : (sren π).applyTerm (thread (redefTo u)) = thread (redefTo u) := by
  rw [thread, apply_tagged, redefTo, sren_ground]

theorem sren_done (π : Equiv.Perm ℕ) : (sren π).applyTerm (thread done) = thread done := by
  rw [thread, apply_tagged, done]
  rfl

/-- The variables of the call's data are variables of the thread. -/
theorem call_vars {E : ECtx} {w : Tm} {x : ℕ × ℕ} (hx : x ∈ w.freeVars) :
    x ∈ (thread (encE (E.fill (.call (.val w))))).freeVars := by
  rw [mem_thread]
  refine freeVars_encE_in_fill E _ ?_
  rw [encE, freeVars_tagged, encE, freeVars_tagged]
  exact hx

/-- Substitutions agreeing on a thread of a call agree on its context and its data. -/
theorem ctx_agree {θ θ' : Subst rows} {E : ECtx} {w : Tm}
    (agree : θ'.applyTerm (thread (encE (E.fill (.call (.val w))))) =
      θ.applyTerm (thread (encE (E.fill (.call (.val w)))))) :
    E.subst θ' = E.subst θ ∧ θ'.applyTerm w = θ.applyTerm w := by
  rw [← thread_subst, ← thread_subst] at agree
  have same := encE_inj (thread_inj agree)
  rw [fill_subst, fill_subst] at same
  obtain ⟨ctx, call⟩ := decomposition_unique (.inr ⟨_, rfl⟩) (.inr ⟨_, rfl⟩) _ _ same
  simp only [Ex.call.injEq, Ex.val.injEq] at call
  exact ⟨ctx, call⟩

/-- A built cell names only the variables of the pair it was built from. -/
theorem build_bounded {n : ℕ} {E : ECtx} {v w : Tm}
    (h : Bounded n (thread (encE (E.fill (.pair (.val v) (.val w)))))) :
    Bounded n (thread (encE (E.fill (.val (node v w))))) := by
  intro x hx
  rw [mem_thread] at hx
  rcases freeVars_encE_fill E (.pair (.val v) (.val w)) _ hx with hx | hx
  · exact h x (mem_thread.mpr hx)
  · rw [encE, freeVars_tagged, mem_freeVars_node] at hx
    refine h x (mem_thread.mpr (freeVars_encE_in_fill E _ ?_))
    rw [encE, freeVars_tagged, mem_freeVars_node, encE, freeVars_tagged, encE, freeVars_tagged]
    exact hx

theorem bounded_of_rel {Wb' : Multiset SRow} {Wa' : Multiset Tm} {π' : Equiv.Perm ℕ} {nb' : ℕ}
    (rel : unloadAll Wb' = Wa'.map (sren π').applyTerm)
    (vars : ∀ t ∈ Wa', ∀ v ∈ t.freeVars, π' v.1 < nb') : ∀ r ∈ Wb', Bounded nb' r.unload := by
  intro r rIn x hx
  have mem : r.unload ∈ Wa'.map (sren π').applyTerm := by
    rw [← rel]
    exact Multiset.mem_map_of_mem _ rIn
  obtain ⟨t, tIn, same⟩ := Multiset.mem_map.mp mem
  rw [← same] at hx
  obtain ⟨y, yIn, rfl⟩ := mem_freeVars_sren.mp hx
  exact vars t tIn y yIn

theorem ground_vars {k u : ℕ} {v : ℕ × ℕ} (hv : v ∈ (tagged k (.const u) : Tm).freeVars) : False := by
  rw [freeVars_tagged] at hv
  simp [Term.freeVars] at hv

/-- **One reference step is simulated by a machine run, up to renaming.** -/
theorem cstep_simulated {defs : Defs} {Wa Wa' : Multiset Tm} {na na' : ℕ}
    (step : CStep defs (Wa, na) (Wa', na')) {Wb : Multiset SRow} {nb : ℕ} {π : Equiv.Perm ℕ}
    (R : Related Wa na Wb nb π) :
    ∃ Wb' nb' π', Relation.ReflTransGen (KStep defs) (Wb, nb) (Wb', nb') ∧ Related Wa' na' Wb' nb' π' := by
  generalize hs : (Wa, na) = start at step
  generalize ht : (Wa', na') = finish at step
  cases step with
  | build E v w F n =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht
      have rel := R.rel
      rw [Multiset.map_cons, sren_thread, fill_subst] at rel
      obtain ⟨s, sIn, same⟩ := find_row rel (Multiset.mem_cons_self _ _)
      have rest := erase_row rel sIn same
      have redex : Redex ((Ex.pair (.val v) (.val w)).subst (sren π)) := .inl ⟨_, _, rfl⟩
      obtain ⟨s', k, focused, run⟩ := refocus (defs := defs) (Wb.erase s) redex
        (unload_thread (R.clean s sIn) same) nb
      rw [Multiset.cons_erase sIn] at run
      generalize hr : (Ex.pair (.val v) (.val w)).subst (sren π) = r' at focused
      generalize hE : E.subst (sren π) = E' at focused
      cases focused with
      | call w' K => cases hr
      | build v' w' K =>
          simp only [Ex.subst, Ex.pair.injEq, Ex.val.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          have last := KStep.right (defs := defs) ((sren π).applyTerm v) ((sren π).applyTerm w) K
            (Wb.erase s) (nb + k)
          have oldB : Bounded nb (thread (encE ((ctxOf K).fill
              (.pair (.val ((sren π).applyTerm v)) (.val ((sren π).applyTerm w)))))) := by
            have := R.boundedB s sIn
            rw [same, hE] at this
            exact this
          refine ⟨_, _, π, run.tail last, ⟨?_, ?_, ?_, ?_, R.fixes, R.positiveA, by omega⟩⟩
          · rw [unloadAll_cons, rest, Multiset.map_cons, sren_thread, fill_subst, hE]
            congr 1
            show thread (encE (plug K (.val (node ((sren π).applyTerm v) ((sren π).applyTerm w))))) = _
            rw [plug_ctxOf, Ex.subst, apply_node]
          · intro r member
            rcases Multiset.mem_cons.mp member with rfl | member
            · trivial
            · exact R.clean r (Multiset.mem_of_mem_erase member)
          · intro t member
            rcases Multiset.mem_cons.mp member with rfl | member
            · exact build_bounded (R.boundedA _ (Multiset.mem_cons_self _ _))
            · exact R.boundedA t (Multiset.mem_cons_of_mem member)
          · intro r member
            rcases Multiset.mem_cons.mp member with rfl | member
            · show Bounded (nb + k + 1) (thread (encE (plug K (.val (node _ _)))))
              rw [plug_ctxOf]
              exact (build_bounded oldB).mono (by omega)
            · exact (R.boundedB r (Multiset.mem_of_mem_erase member)).mono (by omega)
  | apply u j E w F n m fresh θ mgu =>
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
          have agreeThread : (sren (moved π m (nb + k))).applyTerm (thread (encE (E.fill (.call (.val w))))) =
              (sren π).applyTerm (thread (encE (E.fill (.call (.val w))))) :=
            sren_congr fun v hv => (R.agree fresh le' threadIn hv).1
          obtain ⟨ctxSame, wSame⟩ := ctx_agree agreeThread
          have problemB : renameProblem (moved π m (nb + k)) [(((defs u).get j).lhs.at m, w)] =
              [(((defs u).get j).lhs.at (nb + k), (sren π).applyTerm w)] := by
            simp only [renameProblem, List.map_cons, List.map_nil, sren_at, moved_at, wSame]
          have mguB := isMGU_sren (moved π m (nb + k)) mgu
          rw [problemB] at mguB
          rw [show Wb.erase s = .version u ::ₘ (Wb.erase s).erase (.version u) from
            (Multiset.cons_erase s₂In).symm] at run
          have last := KStep.apply (defs := defs) u j ((sren π).applyTerm w) K ((Wb.erase s).erase (.version u))
            (nb + k) (conj (moved π m (nb + k)) θ) mguB
          have wB : Bounded _ w := fun x hx => R.boundedA _ threadIn x (call_vars hx)
          have inner : (E.fill (((defs u).get j).rhs.at m)).subst (sren (moved π m (nb + k))) =
              (E.subst (sren π)).fill (((defs u).get j).rhs.at (nb + k)) := by
            rw [fill_subst, epat_at_sren, moved_at, ctxSame]
          have rel' : unloadAll (SRow.ev ((((defs u).get j).rhs.at (nb + k)).subst (conj (moved π m (nb + k)) θ))
              (K.map (Frame.subst (conj (moved π m (nb + k)) θ))) ::ₘ .citation u ::ₘ .version u ::ₘ
              ((Wb.erase s).erase (.version u)).map (SRow.subst (conj (moved π m (nb + k)) θ))) =
              (thread (encE ((E.fill (((defs u).get j).rhs.at m)).subst θ)) ::ₘ cite u ::ₘ ver u ::ₘ
                F.map θ.applyTerm).map (sren (moved π m (nb + k))).applyTerm := by
            rw [unloadAll_cons, unloadAll_cons, unloadAll_cons, unloadAll_subst, rest₂,
              Multiset.map_cons, Multiset.map_cons, Multiset.map_cons, sren_cite, sren_ver]
            congr 1
            · show thread (encE (plug (K.map (Frame.subst (conj (moved π m (nb + k)) θ)))
                ((((defs u).get j).rhs.at (nb + k)).subst (conj (moved π m (nb + k)) θ)))) = _
              rw [← plug_subst, plug_ctxOf, ← hE, sren_thread, ← Ex.subst_conj, inner]
            · congr 2
              rw [Multiset.map_map, Multiset.map_map]
              refine Multiset.map_congr rfl fun f member => ?_
              have fIn : f ∈ thread (encE (E.fill (.call (.val w)))) ::ₘ ver u ::ₘ F :=
                Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem member)
              show (conj (moved π m (nb + k)) θ).applyTerm ((sren π).applyTerm f) =
                (sren (moved π m (nb + k))).applyTerm (θ.applyTerm f)
              rw [← sren_congr fun v hv => (R.agree fresh le' fIn hv).1, conj_apply]
          refine ⟨_, _, moved π m (nb + k), run.tail last, ⟨?_, ?_, ?_, ?_, ?_, by omega, by omega⟩⟩
          · exact rel'
          · intro r member
            simp only [Multiset.mem_cons] at member
            rcases member with rfl | rfl | rfl | member
            · trivial
            · trivial
            · trivial
            · obtain ⟨r₀, r₀In, rfl⟩ := Multiset.mem_map.mp member
              exact (R.clean r₀ (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase r₀In))).subst _
          · -- the reference rows name scopes up to `m`
            intro t member
            simp only [Multiset.mem_cons] at member
            rcases member with rfl | rfl | rfl | member
            · rw [thread_subst]
              refine mgu_bounded mgu wB fresh fun x hx => ?_
              rw [mem_thread] at hx
              rcases freeVars_encE_fill E (.call (.val w)) _ hx with hx | hx
              · have := R.boundedA _ threadIn x (mem_thread.mpr hx)
                omega
              · rw [← EPat.enc_at] at hx
                have := at_scope m _ x hx
                omega
            · exact fun x hx => (ground_vars hx).elim
            · exact fun x hx => (ground_vars hx).elim
            · obtain ⟨f, fIn, rfl⟩ := Multiset.mem_map.mp member
              exact mgu_bounded mgu wB fresh
                ((R.boundedA f (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem fIn))).mono (by omega))
          · -- the machine rows name scopes up to its firing's
            refine bounded_of_rel rel' fun t member y hy => ?_
            have old : ∀ {t₀ : Tm}, t₀ ∈ thread (encE (E.fill (.call (.val w)))) ::ₘ ver u ::ₘ F →
                y ∈ t₀.freeVars → moved π m (nb + k) y.1 < nb + k + 1 := fun tIn yIn => by
              have := R.agree fresh le' tIn yIn
              omega
            have viaW : y ∈ w.freeVars → moved π m (nb + k) y.1 < nb + k + 1 := fun yIn =>
              old threadIn (call_vars yIn)
            have atM : y.1 = m → moved π m (nb + k) y.1 < nb + k + 1 := fun h => by
              rw [h, moved_at]
              omega
            simp only [Multiset.mem_cons] at member
            rcases member with rfl | rfl | rfl | member
            · rw [thread_subst] at hy
              rcases mgu_vars mgu _ hy with hy | hy | hy
              · rw [mem_thread] at hy
                rcases freeVars_encE_fill E (.call (.val w)) _ hy with hy | hy
                · exact old threadIn (mem_thread.mpr hy)
                · rw [← EPat.enc_at] at hy
                  exact atM (at_scope m _ y hy)
              · exact atM hy
              · exact viaW hy
            · exact (ground_vars hy).elim
            · exact (ground_vars hy).elim
            · obtain ⟨f, fIn, rfl⟩ := Multiset.mem_map.mp member
              rcases mgu_vars mgu f hy with hy | hy | hy
              · exact old (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem fIn)) hy
              · exact atM hy
              · exact viaW hy
          · have p₁ := R.positiveA
            have p₂ := R.positiveB
            rw [moved_old (by omega) (by rw [R.fixes]; omega), R.fixes]
  | redefine u u' F n =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hs
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj ht
      have rel := R.rel
      rw [Multiset.map_cons, Multiset.map_cons, sren_redef, sren_ver] at rel
      obtain ⟨s, sIn, same⟩ := find_row rel (Multiset.mem_cons_self _ _)
      have rest₁ := erase_row rel sIn same
      obtain ⟨s₂, s₂In, same₂⟩ := find_row rest₁ (Multiset.mem_cons_self _ _)
      have rest₂ := erase_row rest₁ s₂In same₂
      have isVer := unload_ver (R.clean s₂ (Multiset.mem_of_mem_erase s₂In)) same₂
      have isRedef := unload_redef (R.clean s sIn) same
      subst isVer isRedef
      have shape : Wb = .redef u' ::ₘ .version u ::ₘ (Wb.erase (.redef u')).erase (.version u) := by
        rw [Multiset.cons_erase s₂In, Multiset.cons_erase sIn]
      have last := KStep.redefine (defs := defs) u u' ((Wb.erase (.redef u')).erase (.version u)) nb
      rw [← shape] at last
      refine ⟨_, _, π, .single last, ⟨?_, ?_, ?_, ?_, R.fixes, R.positiveA, by omega⟩⟩
      · rw [unloadAll_cons, unloadAll_cons, rest₂, Multiset.map_cons, Multiset.map_cons, sren_done,
          sren_ver]
        rfl
      · intro r member
        simp only [Multiset.mem_cons] at member
        rcases member with rfl | rfl | member
        · trivial
        · trivial
        · exact R.clean r (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase member))
      · intro t member
        simp only [Multiset.mem_cons] at member
        rcases member with rfl | rfl | member
        · intro x hx
          rw [mem_thread, done] at hx
          simp [Term.freeVars] at hx
        · exact fun x hx => (ground_vars hx).elim
        · exact R.boundedA t (Multiset.mem_cons_of_mem (Multiset.mem_cons_of_mem member))
      · intro r member
        simp only [Multiset.mem_cons] at member
        rcases member with rfl | rfl | member
        · intro x hx
          change x ∈ (thread done).freeVars at hx
          rw [mem_thread, done] at hx
          simp [Term.freeVars] at hx
        · intro x hx
          change x ∈ (ver u').freeVars at hx
          exact (ground_vars hx).elim
        · exact (R.boundedB r (Multiset.mem_of_mem_erase (Multiset.mem_of_mem_erase member))).mono (by omega)

/-- **Every reference run is simulated by a machine run, up to renaming of fresh scopes.** -/
theorem creference_simulated {defs : Defs} {a a' : Multiset Tm × ℕ}
    (run : Relation.ReflTransGen (CStep defs) a a') {Wb : Multiset SRow} {nb : ℕ} {π : Equiv.Perm ℕ}
    (R : Related a.1 a.2 Wb nb π) :
    ∃ Wb' nb' π', Relation.ReflTransGen (KStep defs) (Wb, nb) (Wb', nb') ∧ Related a'.1 a'.2 Wb' nb' π' := by
  induction run with
  | refl => exact ⟨Wb, nb, π, .refl, R⟩
  | @tail b c _ step ih =>
      obtain ⟨Wb₁, nb₁, π₁, path, R₁⟩ := ih
      obtain ⟨Wa, na⟩ := b
      obtain ⟨Wb₂, nb₂, π₂, path₂, R₂⟩ := cstep_simulated step R₁
      exact ⟨Wb₂, nb₂, π₂, path.trans path₂, R₂⟩

theorem sren_refl (t : Tm) : (sren (Equiv.refl ℕ)).applyTerm t = t :=
  Subst.applyTerm_eq_self fun _ _ => rfl

/-- **Reference completeness.** From machine rows whose data rows avoid the thread, version and
citation tags, and whose unloadings name only scope `0`, every reference run in evaluation contexts
is matched by a machine run whose rows unload to the reference end under a renaming of scopes that
fixes scope `0`. -/
theorem reference_complete (defs : Defs) (l : List SRow) (clean : ∀ s ∈ l, s.Clean)
    (bounded : ∀ s ∈ l, Bounded 1 s.unload) {Wa' : Multiset Tm} {na' : ℕ}
    (run : Relation.ReflTransGen (CStep defs) (unloadAll (l : Multiset SRow), 1) (Wa', na')) :
    ∃ (Wb' : Multiset SRow) (nb' : ℕ) (π : Equiv.Perm ℕ),
      Relation.ReflTransGen (KStep defs) ((l : Multiset SRow), 1) (Wb', nb') ∧
      unloadAll Wb' = Wa'.map (sren π).applyTerm ∧ π 0 = 0 := by
  have R : Related (unloadAll (l : Multiset SRow)) 1 (l : Multiset SRow) 1 (Equiv.refl ℕ) := by
    refine ⟨?_, fun s member => clean s (Multiset.mem_coe.mp member), ?_,
      fun s member => bounded s (Multiset.mem_coe.mp member), rfl, le_rfl, le_rfl⟩
    · rw [Multiset.map_congr rfl fun t _ => sren_refl t, Multiset.map_id']
    · intro t member
      obtain ⟨s, sIn, rfl⟩ := Multiset.mem_map.mp member
      exact bounded s (Multiset.mem_coe.mp sIn)
  obtain ⟨Wb', nb', π', path, R'⟩ := creference_simulated run R
  exact ⟨Wb', nb', π', path, R'.rel, R'.fixes⟩

#print axioms unload_thread
#print axioms unload_ver
#print axioms unload_redef
#print axioms freeVars_encE_fill
#print axioms mgu_vars
#print axioms mgu_bounded
#print axioms ctx_agree
#print axioms build_bounded
#print axioms cstep_simulated
#print axioms creference_simulated
#print axioms reference_complete

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
