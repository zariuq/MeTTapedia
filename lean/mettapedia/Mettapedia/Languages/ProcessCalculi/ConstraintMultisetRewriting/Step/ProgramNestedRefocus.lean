import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedRenaming

/-!
# Refocusing: the machine reaches the redex the evaluation context names

From any machine thread whose plugged expression is `E[r]` for a redex `r`, administrative steps
reach the thread focused at `r` (`refocus`): the call `ap w K` with `ctxOf K = E` for a call of data,
or the return `ret w (right v :: K)` with `ctxOf K = E` for a cell of data. The administrative
steps do not change the unloading. The measure is the size of the focus and of the right sides
still pending in the frames (Danvy and Nielsen's refocusing, for this frame-stack machine).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows ProgramTranslation ProgramEquationsOpen ProgramEquations

/-- The size of an expression. -/
def Ex.size : Ex → ℕ
  | .val _ => 1
  | .pair a b => Ex.size a + Ex.size b + 1
  | .call a => Ex.size a + 1

/-- The work still pending in a frame stack: the sizes of the right sides to evaluate. -/
def pending : List Frame → ℕ
  | [] => 0
  | .left b :: K => Ex.size b + pending K
  | .right _ :: K => pending K
  | .arg :: K => pending K

/-- **A focused machine thread**: a call of data, or a cell of data ready to be built. -/
inductive Focused : SRow → ECtx → Ex → Prop
  | call (w : Tm) (K : List Frame) : Focused (.ap w K) (ctxOf K) (.call (.val w))
  | build (v w : Tm) (K : List Frame) : Focused (.ret w (.right v :: K)) (ctxOf K) (.pair (.val v) (.val w))

theorem refocus_measure {defs : Defs} (F : Multiset SRow) {E : ECtx} {r : Ex} (redex : Redex r) :
    ∀ μ : ℕ,
      (∀ (e : Ex) (K : List Frame) (n : ℕ), 2 * (Ex.size e + pending K) ≤ μ → plug K e = E.fill r →
        ∃ s k, Focused s E r ∧ Relation.ReflTransGen (KStep defs) (.ev e K ::ₘ F, n) (s ::ₘ F, n + k)) ∧
      (∀ (v : Tm) (K : List Frame) (n : ℕ), 2 * pending K + 1 ≤ μ → plug K (.val v) = E.fill r →
        ∃ s k, Focused s E r ∧ Relation.ReflTransGen (KStep defs) (.ret v K ::ₘ F, n) (s ::ₘ F, n + k))
  | 0 => by
      refine ⟨fun e K n le _ => ?_, fun v K n le _ => ?_⟩
      · cases e <;> simp [Ex.size] at le
      · omega
  | μ + 1 => by
      obtain ⟨ihEv, ihRet⟩ := refocus_measure F redex μ
      refine ⟨fun e K n le same => ?_, fun v K n le same => ?_⟩
      · cases e with
        | val t =>
            obtain ⟨s, k, focused, run⟩ := ihRet t K (n + 1) (by simp only [Ex.size] at le; omega) same
            exact ⟨s, k + 1, focused, by
              rw [show n + (k + 1) = n + 1 + k by omega]
              exact Relation.ReflTransGen.head (KStep.val t K F n) run⟩
        | pair a b =>
            obtain ⟨s, k, focused, run⟩ := ihEv a (.left b :: K) (n + 1)
              (by simp only [Ex.size, pending] at le ⊢; omega) same
            exact ⟨s, k + 1, focused, by
              rw [show n + (k + 1) = n + 1 + k by omega]
              exact Relation.ReflTransGen.head (KStep.pair a b K F n) run⟩
        | call a =>
            obtain ⟨s, k, focused, run⟩ := ihEv a (.arg :: K) (n + 1)
              (by simp only [Ex.size, pending] at le ⊢; omega) same
            exact ⟨s, k + 1, focused, by
              rw [show n + (k + 1) = n + 1 + k by omega]
              exact Relation.ReflTransGen.head (KStep.call a K F n) run⟩
      · match K, same, le with
        | [], same, _ => exact absurd ⟨v, same.symm⟩ (fill_redex_not_value redex E)
        | .left b :: K', same, le =>
            obtain ⟨s, k, focused, run⟩ := ihEv b (.right v :: K') (n + 1)
              (by simp only [pending] at le ⊢; omega) same
            exact ⟨s, k + 1, focused, by
              rw [show n + (k + 1) = n + 1 + k by omega]
              exact Relation.ReflTransGen.head (KStep.left v b K' F n) run⟩
        | .right u :: K', same, _ =>
            have plugged : (ctxOf K').fill (.pair (.val u) (.val v)) = E.fill r := by
              rw [← plug_ctxOf]
              exact same
            obtain ⟨rfl, rfl⟩ := decomposition_unique (.inl ⟨u, v, rfl⟩) redex _ _ plugged
            exact ⟨_, 0, .build u v K', .refl⟩
        | .arg :: K', same, _ =>
            have plugged : (ctxOf K').fill (.call (.val v)) = E.fill r := by
              rw [← plug_ctxOf]
              exact same
            obtain ⟨rfl, rfl⟩ := decomposition_unique (.inr ⟨v, rfl⟩) redex _ _ plugged
            exact ⟨_, 1, .call v K', .single (KStep.arg v K' F n)⟩

/-- **Refocusing.** -/
theorem refocus {defs : Defs} (F : Multiset SRow) {E : ECtx} {r : Ex} (redex : Redex r)
    {s₀ : SRow} (shape : (∃ e K, s₀ = .ev e K ∧ plug K e = E.fill r) ∨
      (∃ v K, s₀ = .ret v K ∧ plug K (.val v) = E.fill r) ∨
      (∃ w K, s₀ = .ap w K ∧ plug K (.call (.val w)) = E.fill r)) (n : ℕ) :
    ∃ s k, Focused s E r ∧ Relation.ReflTransGen (KStep defs) (s₀ ::ₘ F, n) (s ::ₘ F, n + k) := by
  rcases shape with ⟨e, K, rfl, same⟩ | ⟨v, K, rfl, same⟩ | ⟨w, K, rfl, same⟩
  · exact (refocus_measure F redex _).1 e K n le_rfl same
  · exact (refocus_measure F redex _).2 v K n le_rfl same
  · have plugged : (ctxOf K).fill (.call (.val w)) = E.fill r := by
      rw [← plug_ctxOf]
      exact same
    obtain ⟨rfl, rfl⟩ := decomposition_unique (.inr ⟨w, rfl⟩) redex _ _ plugged
    exact ⟨_, 0, .call w K, .refl⟩

/-! ## Reading a thread back -/

theorem encE_inj : ∀ {e e' : Ex}, encE e = encE e' → e = e'
  | .val t, .val t', h => by
      rw [encE, encE, tagged_inj] at h
      rw [h.2]
  | .pair a b, .pair a' b', h => by
      rw [encE, encE, tagged_inj, node_inj] at h
      rw [encE_inj h.2.1, encE_inj h.2.2]
  | .call a, .call a', h => by
      rw [encE, encE, tagged_inj] at h
      rw [encE_inj h.2]
  | .val _, .pair _ _, h => by rw [encE, encE, tagged_inj] at h; omega
  | .val _, .call _, h => by rw [encE, encE, tagged_inj] at h; omega
  | .pair _ _, .val _, h => by rw [encE, encE, tagged_inj] at h; omega
  | .pair _ _, .call _, h => by rw [encE, encE, tagged_inj] at h; omega
  | .call _, .val _, h => by rw [encE, encE, tagged_inj] at h; omega
  | .call _, .pair _ _, h => by rw [encE, encE, tagged_inj] at h; omega

#print axioms refocus_measure
#print axioms refocus
#print axioms encE_inj

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
