import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ProgramNestedSource

/-!
# The evaluation strategy is a strategy: unique decomposition

The reference semantics `CStep` rewrites a redex in an evaluation context. Its contexts are those of
call by value, left to right (`ECtx`): the hole is on the left of a pair, on the right of a pair whose
left side is data, or in a call's argument. A redex is a pair of data or a call of data.

* **Values do not decompose** (`fill_redex_not_value`).
* **Every expression is data or decomposes** (`decompose`): it is `val t`, or `E[r]` for an
  evaluation context `E` and a redex `r`.
* **The decomposition is unique** (`decomposition_unique`): the redex to contract next, and its
  context, are determined by the expression. The only choices of a reference step are the
  equation and the most general unifier, and the fresh scope.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested

open Mettapedia.Logic.LP
open ProgramRows

/-- A redex: a pair of data, or a call of data. -/
def Redex (r : Ex) : Prop := (∃ v w, r = .pair (.val v) (.val w)) ∨ ∃ w, r = .call (.val w)

/-- An expression that is data. -/
def IsData (e : Ex) : Prop := ∃ t, e = .val t

theorem redex_not_data {r : Ex} (redex : Redex r) : ¬ IsData r := by
  rintro ⟨t, rfl⟩
  rcases redex with ⟨v, w, h⟩ | ⟨w, h⟩ <;> cases h

/-- **A filled redex is not data.** -/
theorem fill_redex_not_value {r : Ex} (redex : Redex r) : ∀ (E : ECtx), ¬ IsData (E.fill r)
  | .hole => redex_not_data redex
  | .pairL _ _ => by rintro ⟨t, h⟩; cases h
  | .pairR _ _ => by rintro ⟨t, h⟩; cases h
  | .arg _ => by rintro ⟨t, h⟩; cases h

/-- **Every expression is data or a redex in an evaluation context.** -/
theorem decompose : ∀ e : Ex, IsData e ∨ ∃ (E : ECtx) (r : Ex), Redex r ∧ e = E.fill r
  | .val t => .inl ⟨t, rfl⟩
  | .pair a b => by
      rcases decompose a with ⟨v, rfl⟩ | ⟨E, r, redex, rfl⟩
      · rcases decompose b with ⟨w, rfl⟩ | ⟨E, r, redex, rfl⟩
        · exact .inr ⟨.hole, _, .inl ⟨v, w, rfl⟩, rfl⟩
        · exact .inr ⟨.pairR v E, r, redex, rfl⟩
      · exact .inr ⟨.pairL E b, r, redex, rfl⟩
  | .call a => by
      rcases decompose a with ⟨w, rfl⟩ | ⟨E, r, redex, rfl⟩
      · exact .inr ⟨.hole, _, .inr ⟨w, rfl⟩, rfl⟩
      · exact .inr ⟨.arg E, r, redex, rfl⟩

/-- **The decomposition is unique.** -/
theorem decomposition_unique {r r' : Ex} (redex : Redex r) (redex' : Redex r') :
    ∀ (E E' : ECtx), E.fill r = E'.fill r' → E = E' ∧ r = r'
  | .hole, .hole, h => ⟨rfl, h⟩
  | .hole, .pairL E' b, h => by
      rcases redex with ⟨v, w, rfl⟩ | ⟨w, rfl⟩
      · simp only [ECtx.fill, Ex.pair.injEq] at h
        exact absurd ⟨v, h.1.symm⟩ (fill_redex_not_value redex' E')
      · cases h
  | .hole, .pairR v E', h => by
      rcases redex with ⟨v', w, rfl⟩ | ⟨w, rfl⟩
      · simp only [ECtx.fill, Ex.pair.injEq] at h
        exact absurd ⟨w, h.2.symm⟩ (fill_redex_not_value redex' E')
      · cases h
  | .hole, .arg E', h => by
      rcases redex with ⟨v, w, rfl⟩ | ⟨w, rfl⟩
      · cases h
      · simp only [ECtx.fill, Ex.call.injEq] at h
        exact absurd ⟨w, h.symm⟩ (fill_redex_not_value redex' E')
  | .pairL E b, .hole, h => by
      rcases redex' with ⟨v, w, rfl⟩ | ⟨w, rfl⟩
      · simp only [ECtx.fill, Ex.pair.injEq] at h
        exact absurd ⟨v, h.1⟩ (fill_redex_not_value redex E)
      · cases h
  | .pairR v E, .hole, h => by
      rcases redex' with ⟨v', w, rfl⟩ | ⟨w, rfl⟩
      · simp only [ECtx.fill, Ex.pair.injEq] at h
        exact absurd ⟨w, h.2⟩ (fill_redex_not_value redex E)
      · cases h
  | .arg E, .hole, h => by
      rcases redex' with ⟨v, w, rfl⟩ | ⟨w, rfl⟩
      · cases h
      · simp only [ECtx.fill, Ex.call.injEq] at h
        exact absurd ⟨w, h⟩ (fill_redex_not_value redex E)
  | .pairL E b, .pairL E' b', h => by
      simp only [ECtx.fill, Ex.pair.injEq] at h
      obtain ⟨same, rfl⟩ := decomposition_unique redex redex' E E' h.1
      exact ⟨by rw [same, h.2], rfl⟩
  | .pairL E _, .pairR v E', h => by
      simp only [ECtx.fill, Ex.pair.injEq] at h
      exact absurd ⟨v, h.1⟩ (fill_redex_not_value redex E)
  | .pairR v E, .pairL E' _, h => by
      simp only [ECtx.fill, Ex.pair.injEq] at h
      exact absurd ⟨v, h.1.symm⟩ (fill_redex_not_value redex' E')
  | .pairR v E, .pairR v' E', h => by
      simp only [ECtx.fill, Ex.pair.injEq, Ex.val.injEq] at h
      obtain ⟨same, rfl⟩ := decomposition_unique redex redex' E E' h.2
      exact ⟨by rw [same, h.1], rfl⟩
  | .arg E, .arg E', h => by
      simp only [ECtx.fill, Ex.call.injEq] at h
      obtain ⟨same, rfl⟩ := decomposition_unique redex redex' E E' h
      exact ⟨by rw [same], rfl⟩
  | .pairL _ _, .arg _, h => by cases h
  | .pairR _ _, .arg _, h => by cases h
  | .arg _, .pairL _ _, h => by cases h
  | .arg _, .pairR _ _, h => by cases h

/-- **Controls**: the leftmost-innermost call is the next redex. In `((c) (c))` the left call is
contracted first, and the right one only once the left is data. -/
theorem left_call_first (w : Tm) :
    (Ex.pair (.call (.val w)) (.call (.val w))) = (ECtx.pairL .hole (.call (.val w))).fill (.call (.val w)) ∧
      ∀ (E : ECtx) (r : Ex), Redex r →
        Ex.pair (.call (.val w)) (.call (.val w)) = E.fill r → E = .pairL .hole (.call (.val w)) := by
  refine ⟨rfl, fun E _ redex h => ?_⟩
  exact (decomposition_unique redex (.inr ⟨w, rfl⟩) E (.pairL .hole (.call (.val w))) h.symm).1

theorem right_call_after (v w : Tm) :
    ∀ (E : ECtx) (r : Ex), Redex r →
      Ex.pair (.val v) (.call (.val w)) = E.fill r → E = .pairR v .hole :=
  fun E _ redex h => (decomposition_unique redex (.inr ⟨w, rfl⟩) E (.pairR v .hole) h.symm).1

#print axioms fill_redex_not_value
#print axioms decompose
#print axioms decomposition_unique
#print axioms left_call_first
#print axioms right_call_after

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.ProgramNested
