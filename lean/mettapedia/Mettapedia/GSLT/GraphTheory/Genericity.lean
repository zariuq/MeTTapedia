import Mettapedia.GSLT.GraphTheory.Solvability

/-!
# Genericity of unsolvable terms

An unsolvable subterm takes no part in a head normalization. If a term is
solvable, it stays solvable when unsolvable subterms are replaced by arbitrary
terms. This is the genericity lemma in the form that concerns head normal
forms.

## Main definitions

* `UnsolvableFilling t t'`: `t'` is `t` with some unsolvable subterms replaced
  by arbitrary terms.
* `LambdaContext`, `LambdaContext.plug`: one-hole contexts. Plugging does not
  rename, so a context may bind variables of the term in its hole.

## Main results

* `UnsolvableFilling.solvable`: the genericity lemma.
* `LambdaContext.solvable_plug_of_unsolvable`: if `C[U]` is solvable and `U`
  is unsolvable then `C[M]` is solvable for every `M`.
* `solvable_subst_of_unsolvable`: the same for substitution instances.

## Method

The head reduction of the filled term follows the head reduction of the
original term step by step. A head redex never lies inside a replaced
subterm: an unsolvable term in head position makes the whole term unsolvable
(`LambdaTerm.Unsolvable.app`, `LambdaTerm.Unsolvable.lam`). Contracting a
redex keeps the two terms related because the relation is closed under
substitution, which uses that unsolvability is closed under substitution and
shifting.

## References

* H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*, §14.3.
-/

namespace Mettapedia.GSLT.GraphTheory

/-- `UnsolvableFilling t t'`: `t'` is obtained from `t` by replacing some
unsolvable subterms by arbitrary terms. -/
inductive UnsolvableFilling : LambdaTerm → LambdaTerm → Prop where
  | var (n : Nat) : UnsolvableFilling (.var n) (.var n)
  | lam {t t' : LambdaTerm} : UnsolvableFilling t t' → UnsolvableFilling (.lam t) (.lam t')
  | app {t t' s s' : LambdaTerm} : UnsolvableFilling t t' → UnsolvableFilling s s' →
      UnsolvableFilling (.app t s) (.app t' s')
  | fill {t : LambdaTerm} (t' : LambdaTerm) : t.Unsolvable → UnsolvableFilling t t'

namespace UnsolvableFilling

theorem refl : ∀ t : LambdaTerm, UnsolvableFilling t t
  | .var n => .var n
  | .lam t => .lam (refl t)
  | .app t s => .app (refl t) (refl s)

theorem shift {t t' : LambdaTerm} (h : UnsolvableFilling t t') (d : Nat) :
    ∀ c : Nat, UnsolvableFilling (LambdaTerm.shift d c t) (LambdaTerm.shift d c t') := by
  induction h with
  | var n => exact fun c => refl _
  | lam _ ih =>
      intro c
      rw [LambdaTerm.shift_lam, LambdaTerm.shift_lam]
      exact .lam (ih (c + 1))
  | app _ _ ihf iha =>
      intro c
      rw [LambdaTerm.shift_app, LambdaTerm.shift_app]
      exact .app (ihf c) (iha c)
  | fill t' hU => exact fun c => .fill _ (hU.shift d c)

/-- The relation is closed under substitution of related terms. -/
theorem subst {t t' : LambdaTerm} (h : UnsolvableFilling t t') :
    ∀ {j : Nat} {u u' : LambdaTerm}, UnsolvableFilling u u' →
      UnsolvableFilling (LambdaTerm.subst j u t) (LambdaTerm.subst j u' t') := by
  induction h with
  | var n =>
      intro j u u' hu
      rcases Nat.lt_trichotomy n j with hlt | rfl | hgt
      · rw [LambdaTerm.subst_var_lt n j hlt, LambdaTerm.subst_var_lt n j hlt]
        exact .var n
      · rw [LambdaTerm.subst_var_eq, LambdaTerm.subst_var_eq]
        exact hu
      · rw [LambdaTerm.subst_var_gt n j hgt, LambdaTerm.subst_var_gt n j hgt]
        exact .var _
  | lam _ ih =>
      intro j u u' hu
      rw [LambdaTerm.subst_lam, LambdaTerm.subst_lam]
      exact .lam (ih (hu.shift 1 0))
  | app _ _ ihf iha =>
      intro j u u' hu
      rw [LambdaTerm.subst_app, LambdaTerm.subst_app]
      exact .app (ihf hu) (iha hu)
  | fill t' hU =>
      intro j u u' _
      exact .fill _ (hU.subst j u)

/-- A variable head is not inside a replaced subterm. -/
theorem isAppHead {t t' : LambdaTerm} (h : UnsolvableFilling t t')
    (hHead : t.isAppHead = true) : t'.isAppHead = true := by
  induction h with
  | var n => rfl
  | lam _ _ => simp [LambdaTerm.isAppHead] at hHead
  | app _ _ ihf _ => exact ihf hHead
  | fill t' hU =>
      exact absurd (LambdaTerm.solvable_of_isHNF (LambdaTerm.isHNF_of_isAppHead hHead)) hU

/-- Filling a head normal form gives a head normal form. -/
theorem isHNF {t t' : LambdaTerm} (h : UnsolvableFilling t t')
    (hHead : t.isHNF = true) : t'.isHNF = true := by
  induction h with
  | var n => rfl
  | lam _ ih => exact ih hHead
  | app hf _ _ _ => exact hf.isAppHead hHead
  | fill t' hU => exact absurd (LambdaTerm.solvable_of_isHNF hHead) hU

/-- A weak head step of a solvable term is followed by its fillings. -/
theorem weakHeadStep {t t₁ : LambdaTerm} (hstep : WeakHeadStep t t₁) :
    ∀ {t' : LambdaTerm}, UnsolvableFilling t t' → t.Solvable →
      ∃ t₁', WeakHeadStep t' t₁' ∧ UnsolvableFilling t₁ t₁' := by
  induction hstep with
  | beta body argument =>
      intro t' hfill hsolvable
      cases hfill with
      | app hf ha =>
          cases hf with
          | lam hb => exact ⟨_, .beta _ _, hb.subst ha⟩
          | fill _ hU => exact absurd hsolvable (hU.app argument)
      | fill _ hU => exact absurd hsolvable hU
  | appLeft argument _ ih =>
      intro t' hfill hsolvable
      cases hfill with
      | app hf ha =>
          obtain ⟨_, hstep₁, hfill₁⟩ := ih hf (solvable_of_solvable_app hsolvable)
          exact ⟨_, .appLeft _ hstep₁, .app hfill₁ ha⟩
      | fill _ hU => exact absurd hsolvable hU

/-- A head step of a solvable term is followed by its fillings. -/
theorem headStep {t t₁ : LambdaTerm} (hstep : HeadStep t t₁) :
    ∀ {t' : LambdaTerm}, UnsolvableFilling t t' → t.Solvable →
      ∃ t₁', HeadStep t' t₁' ∧ UnsolvableFilling t₁ t₁' := by
  induction hstep with
  | weak hw =>
      intro t' hfill hsolvable
      obtain ⟨t₁', hstep', hfill'⟩ := weakHeadStep hw hfill hsolvable
      exact ⟨t₁', .weak hstep', hfill'⟩
  | lam _ ih =>
      intro t' hfill hsolvable
      cases hfill with
      | lam hb =>
          obtain ⟨_, hstep₁, hfill₁⟩ := ih hb (solvable_lam_iff.1 hsolvable)
          exact ⟨_, .lam hstep₁, .lam hfill₁⟩
      | fill _ hU => exact absurd hsolvable hU

/-- **Genericity lemma.** A solvable term stays solvable when unsolvable
subterms are replaced by arbitrary terms. -/
theorem solvable {t t' : LambdaTerm} (hfill : UnsolvableFilling t t') (h : t.Solvable) :
    t'.Solvable := by
  have hn := headNormalizes_of_solvable h
  induction hn generalizing t' with
  | hnf hhead => exact LambdaTerm.solvable_of_isHNF (hfill.isHNF hhead)
  | step hstep hn ih =>
      obtain ⟨t₁', hstep', hfill'⟩ := headStep hstep hfill h
      exact LambdaTerm.solvable_of_reduces (Relation.ReflTransGen.single hstep'.parRed)
        (ih hfill' hn.solvable)

end UnsolvableFilling

/-- **Genericity for substitution.** If `t[U/j]` is solvable and `U` is
unsolvable, then `t[M/j]` is solvable for every `M`. -/
theorem solvable_subst_of_unsolvable {j : Nat} {u t : LambdaTerm} (hU : u.Unsolvable)
    (h : (LambdaTerm.subst j u t).Solvable) (m : LambdaTerm) :
    (LambdaTerm.subst j m t).Solvable :=
  ((UnsolvableFilling.refl t).subst (.fill m hU)).solvable h

/-! ## One-hole contexts -/

/-- One-hole contexts of λ-terms. Plugging does not rename: a context may
bind variables of the term in its hole. -/
inductive LambdaContext : Type where
  | hole : LambdaContext
  | lam : LambdaContext → LambdaContext
  | appLeft : LambdaContext → LambdaTerm → LambdaContext
  | appRight : LambdaTerm → LambdaContext → LambdaContext

namespace LambdaContext

/-- Put a term in the hole. -/
def plug : LambdaContext → LambdaTerm → LambdaTerm
  | .hole, t => t
  | .lam context, t => .lam (context.plug t)
  | .appLeft context argument, t => .app (context.plug t) argument
  | .appRight function context, t => .app function (context.plug t)

/-- Put a context in the hole of a context. -/
def comp : LambdaContext → LambdaContext → LambdaContext
  | .hole, inner => inner
  | .lam outer, inner => .lam (outer.comp inner)
  | .appLeft outer argument, inner => .appLeft (outer.comp inner) argument
  | .appRight function outer, inner => .appRight function (outer.comp inner)

theorem plug_comp (outer inner : LambdaContext) (t : LambdaTerm) :
    (outer.comp inner).plug t = outer.plug (inner.plug t) := by
  induction outer with
  | hole => rfl
  | lam _ ih => exact congrArg LambdaTerm.lam ih
  | appLeft _ argument ih => exact congrArg (fun function => LambdaTerm.app function argument) ih
  | appRight function _ ih => exact congrArg (LambdaTerm.app function) ih

/-- Parallel reduction is compatible with contexts. -/
theorem parRed_plug (context : LambdaContext) {t t' : LambdaTerm} (h : t ⇛ t') :
    (context.plug t) ⇛ (context.plug t') := by
  induction context with
  | hole => exact h
  | lam _ ih => exact ParRed.lam ih
  | appLeft _ argument ih => exact ParRed.app ih (ParRed.refl argument)
  | appRight function _ ih => exact ParRed.app (ParRed.refl function) ih

/-- Replacing an unsolvable term in the hole is a filling. -/
theorem unsolvableFilling_plug (context : LambdaContext) {t : LambdaTerm} (hU : t.Unsolvable)
    (t' : LambdaTerm) : UnsolvableFilling (context.plug t) (context.plug t') := by
  induction context with
  | hole => exact .fill t' hU
  | lam _ ih => exact .lam ih
  | appLeft _ argument ih => exact .app ih (UnsolvableFilling.refl argument)
  | appRight function _ ih => exact .app (UnsolvableFilling.refl function) ih

/-- **Genericity through contexts.** If `C[U]` is solvable and `U` is
unsolvable, then `C[M]` is solvable for every `M`. -/
theorem solvable_plug_of_unsolvable (context : LambdaContext) {t : LambdaTerm}
    (hU : t.Unsolvable) (h : (context.plug t).Solvable) (t' : LambdaTerm) :
    (context.plug t').Solvable :=
  (context.unsolvableFilling_plug hU t').solvable h

/-- No context separates two unsolvable terms by solvability. -/
theorem solvable_plug_iff_of_unsolvable (context : LambdaContext) {t t' : LambdaTerm}
    (ht : t.Unsolvable) (ht' : t'.Unsolvable) :
    (context.plug t).Solvable ↔ (context.plug t').Solvable :=
  ⟨fun h => context.solvable_plug_of_unsolvable ht h t',
    fun h => context.solvable_plug_of_unsolvable ht' h t⟩

end LambdaContext

end Mettapedia.GSLT.GraphTheory
