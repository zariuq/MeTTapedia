import Mettapedia.GSLT.GraphTheory.Basic
import Mathlib.Logic.Function.Iterate

/-!
# Solvability and semisensible theories

A λ-term is solvable when it β-reduces to a head normal form. This file proves
that a consistent sensible λ-theory is semisensible: it never equates an
unsolvable term with a solvable one.

## Main results

* `headNormalizes_of_solvable`: head reduction of a solvable term terminates in
  a head normal form.
* `solvable_of_solvable_subst`, `solvable_of_solvable_app`, `solvable_lam_iff`:
  substitution, application and abstraction never turn an unsolvable term into
  a solvable one.
* `solvable_shift_iff`: shifting neither creates nor destroys solvability.
* `exists_context_reduces_to_I`: every solvable term is sent to `I` by a context
  `(λ^q [·]) N₁ ⋯ Nₚ`.
* `LambdaTheory.consistent_iff_exists_not_equates`: a theory is consistent exactly
  when it does not equate all terms.
* `sensible_imp_semisensible`.

## Method

Standard reductions are presented inductively: weak head steps, followed by
standard reductions of the components of the variable, abstraction or
application that is reached. Appending a parallel step to a standard reduction
gives a standard reduction, by structural induction alone, so every parallel
reduction sequence is standard. A standard reduction ending in a head normal
form yields a terminating head reduction. Head reduction is deterministic and
commutes with substitution, which transfers head normalization from `t[u/j]`
back to `t`.

If `t` is unsolvable, `T ⊢ t = s` and `s` is solvable, then the context that
sends `s` to `I` sends `t` to an unsolvable term that `T` equates with `I`.
Sensibility then equates every term with `Ω`, so `T ⊢ I = K`.

## References

* H. P. Barendregt, *The Lambda Calculus: Its Syntax and Semantics*,
  chapters 8 and 16.
* G. D. Plotkin, *Call-by-name, call-by-value and the λ-calculus*,
  Theoretical Computer Science 1 (1975).
* R. Kashima, *A proof of the standardization theorem in λ-calculus* (2000).
-/

namespace Mettapedia.GSLT.GraphTheory

/-! ## Abstraction prefixes, applicative spines and closed terms

`LambdaTerm.lam^[k] t` is `t` under `k` binders, and `args.foldl .app t`
applies `t` to `args`, the first argument innermost. -/

namespace LambdaTerm

/-- A variable-headed spine is in head normal form. -/
theorem isHNF_of_isAppHead {t : LambdaTerm} (h : t.isAppHead = true) : t.isHNF = true := by
  cases t with
  | var _ => rfl
  | lam _ => simp [isAppHead] at h
  | app _ _ => exact h

/-- A variable-headed spine is a variable applied to a list of arguments. -/
theorem exists_eq_foldl_app_var_of_isAppHead {t : LambdaTerm} (h : t.isAppHead = true) :
    ∃ (head : Nat) (args : List LambdaTerm), t = args.foldl .app (.var head) := by
  induction t with
  | var n => exact ⟨n, [], rfl⟩
  | lam _ _ => simp [isAppHead] at h
  | app f a ihf _ =>
      obtain ⟨head, args, rfl⟩ := ihf h
      exact ⟨head, args ++ [a], by rw [List.foldl_append]; rfl⟩

/-- A head normal form is `λ^n. y M₁ ⋯ Mₖ`. -/
theorem exists_eq_iterate_lam_foldl_app_var_of_isHNF {t : LambdaTerm} (h : t.isHNF = true) :
    ∃ (n head : Nat) (args : List LambdaTerm),
      t = LambdaTerm.lam^[n] (args.foldl .app (.var head)) := by
  induction t with
  | var n => exact ⟨0, n, [], rfl⟩
  | lam _ ih =>
      obtain ⟨n, head, args, rfl⟩ := ih h
      exact ⟨n + 1, head, args, (Function.iterate_succ_apply' _ _ _).symm⟩
  | app f a _ _ =>
      obtain ⟨head, args, heq⟩ := exists_eq_foldl_app_var_of_isAppHead (t := .app f a) h
      exact ⟨0, head, args, heq⟩

/-- Substitution distributes over an applicative spine. -/
theorem subst_foldl_app (j : Nat) (u : LambdaTerm) :
    ∀ (head : LambdaTerm) (args : List LambdaTerm),
      subst j u (args.foldl .app head) = (args.map (subst j u)).foldl .app (subst j u head)
  | _, [] => rfl
  | head, a :: rest => by
      rw [List.map_cons, List.foldl_cons, List.foldl_cons, subst_foldl_app j u (.app head a) rest,
        subst_app]

/-- Substitution cannot create a variable head. -/
theorem isAppHead_of_isAppHead_subst {j : Nat} {u t : LambdaTerm}
    (h : (subst j u t).isAppHead = true) : t.isAppHead = true := by
  induction t with
  | var _ => rfl
  | lam _ _ => simp [subst, isAppHead] at h
  | app f a ihf _ =>
      rw [subst_app] at h
      exact ihf h

/-- Substitution cannot create a head normal form. -/
theorem isHNF_of_isHNF_subst {j : Nat} {u t : LambdaTerm}
    (h : (subst j u t).isHNF = true) : t.isHNF = true := by
  induction t generalizing j u with
  | var _ => rfl
  | lam b ih =>
      rw [subst_lam] at h
      exact ih (j := j + 1) (u := shift 1 0 u) h
  | app f a _ _ =>
      rw [subst_app] at h
      exact isAppHead_of_isAppHead_subst (t := f) h

/-- Shifting renames variables, so it neither creates nor destroys a variable head. -/
theorem isAppHead_shift (d : Nat) (t : LambdaTerm) :
    ∀ c : Nat, (shift d c t).isAppHead = t.isAppHead := by
  induction t with
  | var n =>
      intro c
      rcases Nat.lt_or_ge n c with hlt | hge
      · rw [shift_var_lt n d c hlt]
      · rw [shift_var_ge n d c hge]
        rfl
  | lam _ _ => exact fun _ => rfl
  | app f a ihf _ =>
      intro c
      rw [shift_app]
      exact ihf c

/-- Shifting neither creates nor destroys a head normal form. -/
theorem isHNF_shift (d : Nat) (t : LambdaTerm) :
    ∀ c : Nat, (shift d c t).isHNF = t.isHNF := by
  induction t with
  | var n =>
      intro c
      rcases Nat.lt_or_ge n c with hlt | hge
      · rw [shift_var_lt n d c hlt]
      · rw [shift_var_ge n d c hge]
        rfl
  | lam b ih =>
      intro c
      rw [shift_lam]
      exact ih (c + 1)
  | app f a _ _ =>
      intro c
      rw [shift_app]
      exact isAppHead_shift d f c

/-- `ClosedAt c t`: every free de Bruijn index of `t` is below `c`. -/
def ClosedAt : Nat → LambdaTerm → Prop
  | c, .var n => n < c
  | c, .lam t => ClosedAt (c + 1) t
  | c, .app t s => ClosedAt c t ∧ ClosedAt c s

/-- Shifting above every free index is the identity. -/
theorem shift_eq_self_of_closedAt (d : Nat) {c c' : Nat} {t : LambdaTerm}
    (h : t.ClosedAt c) (hc : c ≤ c') : shift d c' t = t := by
  induction t generalizing c c' with
  | var n => exact shift_var_lt n d c' (Nat.lt_of_lt_of_le h hc)
  | lam b ih => rw [shift_lam, ih h (Nat.succ_le_succ hc)]
  | app f a ihf iha => rw [shift_app, ihf h.1 hc, iha h.2 hc]

/-- Substituting for an index above every free index is the identity. -/
theorem subst_eq_self_of_closedAt (u : LambdaTerm) {c j : Nat} {t : LambdaTerm}
    (h : t.ClosedAt c) (hc : c ≤ j) : subst j u t = t := by
  induction t generalizing c j u with
  | var n => exact subst_var_lt n j (Nat.lt_of_lt_of_le h hc) u
  | lam b ih => rw [subst_lam, ih _ h (Nat.succ_le_succ hc)]
  | app f a ihf iha => rw [subst_app, ihf _ h.1 hc, iha _ h.2 hc]

/-- Each binder of a prefix closes one more index. -/
theorem closedAt_iterate_lam {c : Nat} (k : Nat) {t : LambdaTerm}
    (h : t.ClosedAt (c + k)) : (LambdaTerm.lam^[k] t).ClosedAt c := by
  induction k generalizing c with
  | zero => exact h
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih (c := c + 1) (by rwa [Nat.add_right_comm, Nat.add_assoc])

/-- The identity combinator is closed. -/
theorem closedAt_I (c : Nat) : I.ClosedAt c := Nat.succ_pos c

/-- Substituting a closed term under a binder prefix. -/
theorem subst_iterate_lam_of_closedAt {N : LambdaTerm} (hN : N.ClosedAt 0) :
    ∀ (p j : Nat) (body : LambdaTerm),
      subst j N (LambdaTerm.lam^[p] body) = LambdaTerm.lam^[p] (subst (j + p) N body)
  | 0, _, _ => rfl
  | p + 1, j, body => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', subst_lam,
        shift_eq_self_of_closedAt 1 hN (Nat.zero_le 0),
        subst_iterate_lam_of_closedAt hN p (j + 1) body, show j + 1 + p = j + (p + 1) by omega]

end LambdaTerm

/-- The selector `λz₁ ⋯ zₘ. I` is closed. -/
theorem closedAt_selector (m : Nat) : (LambdaTerm.lam^[m] LambdaTerm.I).ClosedAt 0 :=
  LambdaTerm.closedAt_iterate_lam m (LambdaTerm.closedAt_I _)

/-! ## Parallel reduction under abstraction prefixes and in function position -/

theorem parRed_iterate_lam (k : Nat) {t t' : LambdaTerm} (h : t ⇛ t') :
    (LambdaTerm.lam^[k] t) ⇛ (LambdaTerm.lam^[k] t') := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact ParRed.lam ih

theorem parRedStar_iterate_lam (k : Nat) {t t' : LambdaTerm} (h : t ⇛* t') :
    (LambdaTerm.lam^[k] t) ⇛* (LambdaTerm.lam^[k] t') :=
  Relation.ReflTransGen.lift (LambdaTerm.lam^[k]) (fun _ _ hx => parRed_iterate_lam k hx) _ _ h

theorem parRed_foldl_app_left {t t' : LambdaTerm} (h : t ⇛ t') (args : List LambdaTerm) :
    (args.foldl .app t) ⇛ (args.foldl .app t') := by
  induction args generalizing t t' with
  | nil => exact h
  | cons a rest ih => exact ih (ParRed.app h (ParRed.refl a))

theorem parRedStar_foldl_app_left {t t' : LambdaTerm} (h : t ⇛* t') (args : List LambdaTerm) :
    (args.foldl .app t) ⇛* (args.foldl .app t') :=
  Relation.ReflTransGen.lift (fun x => args.foldl LambdaTerm.app x)
    (fun _ _ hx => parRed_foldl_app_left hx args) _ _ h

/-- Reducts of an abstraction are abstractions of reducts of its body. -/
theorem parRedStar_lam_inv {t result : LambdaTerm} (h : (LambdaTerm.lam t) ⇛* result) :
    ∃ body, result = .lam body ∧ t ⇛* body := by
  induction h with
  | refl => exact ⟨t, rfl, Relation.ReflTransGen.refl⟩
  | tail _ step ih =>
      obtain ⟨body, rfl, hbody⟩ := ih
      cases step with
      | lam hstep => exact ⟨_, rfl, hbody.tail hstep⟩

/-! ## Weak head reduction and head reduction -/

/-- Weak head reduction contracts the redex at the head of an applicative spine
and never reduces under an abstraction. -/
inductive WeakHeadStep : LambdaTerm → LambdaTerm → Prop where
  | beta (body argument : LambdaTerm) :
      WeakHeadStep (.app (.lam body) argument) (LambdaTerm.subst 0 argument body)
  | appLeft {function function' : LambdaTerm} (argument : LambdaTerm) :
      WeakHeadStep function function' →
        WeakHeadStep (.app function argument) (.app function' argument)

/-- Finite sequences of weak head steps. -/
abbrev WeakHeadStar := Relation.ReflTransGen WeakHeadStep

/-- Head reduction: weak head reduction under the leading abstractions. -/
inductive HeadStep : LambdaTerm → LambdaTerm → Prop where
  | weak {t t' : LambdaTerm} : WeakHeadStep t t' → HeadStep t t'
  | lam {t t' : LambdaTerm} : HeadStep t t' → HeadStep (.lam t) (.lam t')

namespace WeakHeadStep

theorem parRed {t t' : LambdaTerm} (h : WeakHeadStep t t') : t ⇛ t' := by
  induction h with
  | beta body argument => exact ParRed.beta (ParRed.refl body) (ParRed.refl argument)
  | appLeft argument _ ih => exact ParRed.app ih (ParRed.refl argument)

theorem shift {t t' : LambdaTerm} (h : WeakHeadStep t t') (d c : Nat) :
    WeakHeadStep (LambdaTerm.shift d c t) (LambdaTerm.shift d c t') := by
  induction h with
  | beta body argument =>
      rw [LambdaTerm.shift_app, LambdaTerm.shift_lam, LambdaTerm.subst_0_shift]
      exact .beta _ _
  | appLeft argument _ ih =>
      rw [LambdaTerm.shift_app, LambdaTerm.shift_app]
      exact .appLeft _ ih

theorem subst {t t' : LambdaTerm} (h : WeakHeadStep t t') (j : Nat) (u : LambdaTerm) :
    WeakHeadStep (LambdaTerm.subst j u t) (LambdaTerm.subst j u t') := by
  induction h with
  | beta body argument =>
      rw [LambdaTerm.subst_app, LambdaTerm.subst_lam, LambdaTerm.subst_subst_composition]
      exact .beta _ _
  | appLeft argument _ ih =>
      rw [LambdaTerm.subst_app, LambdaTerm.subst_app]
      exact .appLeft _ ih

theorem deterministic {t t₁ t₂ : LambdaTerm} (h₁ : WeakHeadStep t t₁)
    (h₂ : WeakHeadStep t t₂) : t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | beta body argument =>
      cases h₂ with
      | beta => rfl
      | appLeft _ h => cases h
  | appLeft argument h ih =>
      cases h₂ with
      | beta => cases h
      | appLeft _ h' => rw [ih h']

/-- A term whose spine is not variable-headed is an abstraction or has a weak head step. -/
theorem exists_of_isAppHead_eq_false {t : LambdaTerm} (h : t.isAppHead = false) :
    (∃ body, t = .lam body) ∨ ∃ t', WeakHeadStep t t' := by
  induction t with
  | var _ => simp [LambdaTerm.isAppHead] at h
  | lam body _ => exact Or.inl ⟨body, rfl⟩
  | app f a ihf _ =>
      rcases ihf h with ⟨body, rfl⟩ | ⟨f', hf⟩
      · exact Or.inr ⟨_, .beta body a⟩
      · exact Or.inr ⟨_, .appLeft a hf⟩

end WeakHeadStep

namespace WeakHeadStar

theorem shift {t t' : LambdaTerm} (h : WeakHeadStar t t') (d c : Nat) :
    WeakHeadStar (LambdaTerm.shift d c t) (LambdaTerm.shift d c t') :=
  Relation.ReflTransGen.lift (LambdaTerm.shift d c)
    (fun _ _ (hs : WeakHeadStep _ _) => hs.shift d c) _ _ h

theorem subst {t t' : LambdaTerm} (h : WeakHeadStar t t') (j : Nat) (u : LambdaTerm) :
    WeakHeadStar (LambdaTerm.subst j u t) (LambdaTerm.subst j u t') :=
  Relation.ReflTransGen.lift (LambdaTerm.subst j u)
    (fun _ _ (hs : WeakHeadStep _ _) => hs.subst j u) _ _ h

theorem appLeft {t t' : LambdaTerm} (h : WeakHeadStar t t') (argument : LambdaTerm) :
    WeakHeadStar (.app t argument) (.app t' argument) :=
  Relation.ReflTransGen.lift (fun x => LambdaTerm.app x argument)
    (fun _ _ hs => WeakHeadStep.appLeft argument hs) _ _ h

end WeakHeadStar

namespace HeadStep

theorem parRed {t t' : LambdaTerm} (h : HeadStep t t') : t ⇛ t' := by
  induction h with
  | weak h => exact h.parRed
  | lam _ ih => exact ParRed.lam ih

theorem subst {t t' : LambdaTerm} (h : HeadStep t t') :
    ∀ (j : Nat) (u : LambdaTerm), HeadStep (LambdaTerm.subst j u t) (LambdaTerm.subst j u t') := by
  induction h with
  | weak h => exact fun j u => .weak (h.subst j u)
  | lam _ ih =>
      intro j u
      rw [LambdaTerm.subst_lam, LambdaTerm.subst_lam]
      exact .lam (ih (j + 1) (LambdaTerm.shift 1 0 u))

theorem shift {t t' : LambdaTerm} (h : HeadStep t t') (d : Nat) :
    ∀ c : Nat, HeadStep (LambdaTerm.shift d c t) (LambdaTerm.shift d c t') := by
  induction h with
  | weak h => exact fun c => .weak (h.shift d c)
  | lam _ ih =>
      intro c
      rw [LambdaTerm.shift_lam, LambdaTerm.shift_lam]
      exact .lam (ih (c + 1))

theorem deterministic {t t₁ t₂ : LambdaTerm} (h₁ : HeadStep t t₁) (h₂ : HeadStep t t₂) :
    t₁ = t₂ := by
  induction h₁ generalizing t₂ with
  | weak h =>
      cases h₂ with
      | weak h' => exact h.deterministic h'
      | lam _ => cases h
  | lam _ ih =>
      cases h₂ with
      | weak h' => cases h'
      | lam h' => rw [ih h']

/-- A term that is not a head normal form has a head step. -/
theorem exists_of_isHNF_eq_false {t : LambdaTerm} (h : t.isHNF = false) :
    ∃ t', HeadStep t t' := by
  induction t with
  | var _ => simp [LambdaTerm.isHNF] at h
  | lam _ ih =>
      obtain ⟨t', ht'⟩ := ih h
      exact ⟨_, .lam ht'⟩
  | app f a _ _ =>
      rcases WeakHeadStep.exists_of_isAppHead_eq_false (t := .app f a) h with ⟨_, hlam⟩ | ⟨t', ht'⟩
      · cases hlam
      · exact ⟨t', .weak ht'⟩

end HeadStep

/-- Head reduction reaches a head normal form after finitely many steps. -/
inductive HeadNormalizes : LambdaTerm → Prop where
  | hnf {t : LambdaTerm} : t.isHNF = true → HeadNormalizes t
  | step {t t' : LambdaTerm} : HeadStep t t' → HeadNormalizes t' → HeadNormalizes t

namespace HeadNormalizes

theorem solvable {t : LambdaTerm} (h : HeadNormalizes t) : t.Solvable := by
  induction h with
  | hnf h => exact LambdaTerm.solvable_of_isHNF h
  | step hs _ ih => exact LambdaTerm.solvable_of_reduces (Relation.ReflTransGen.single hs.parRed) ih

theorem lam {t : LambdaTerm} (h : HeadNormalizes t) : HeadNormalizes (.lam t) := by
  induction h with
  | hnf h => exact .hnf h
  | step hs _ ih => exact .step (.lam hs) ih

theorem of_weakHeadStar {t t' : LambdaTerm} (h : WeakHeadStar t t') (h' : HeadNormalizes t') :
    HeadNormalizes t := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact h'
  | head hstep _ ih => exact .step (.weak hstep) ih

end HeadNormalizes

/-! ## Standard reductions -/

/-- Standard reductions: weak head steps first, then standard reductions of the
components of the variable, abstraction or application reached. -/
inductive StandardRed : LambdaTerm → LambdaTerm → Prop where
  | var {t : LambdaTerm} {n : Nat} : WeakHeadStar t (.var n) → StandardRed t (.var n)
  | lam {t body body' : LambdaTerm} :
      WeakHeadStar t (.lam body) → StandardRed body body' → StandardRed t (.lam body')
  | app {t function argument function' argument' : LambdaTerm} :
      WeakHeadStar t (.app function argument) → StandardRed function function' →
        StandardRed argument argument' → StandardRed t (.app function' argument')

namespace StandardRed

theorem refl : ∀ t : LambdaTerm, StandardRed t t
  | .var _ => .var .refl
  | .lam body => .lam .refl (refl body)
  | .app function argument => .app .refl (refl function) (refl argument)

/-- Weak head steps can be prepended to a standard reduction. -/
theorem weakHead_trans {t t₁ u : LambdaTerm} (h : WeakHeadStar t t₁) (h' : StandardRed t₁ u) :
    StandardRed t u := by
  cases h' with
  | var hw => exact .var (h.trans hw)
  | lam hw hb => exact .lam (h.trans hw) hb
  | app hw hf ha => exact .app (h.trans hw) hf ha

theorem lam_inv {t body' : LambdaTerm} (h : StandardRed t (.lam body')) :
    ∃ body, WeakHeadStar t (.lam body) ∧ StandardRed body body' := by
  cases h with
  | lam hw hb => exact ⟨_, hw, hb⟩

theorem shift {t u : LambdaTerm} (h : StandardRed t u) (d : Nat) :
    ∀ c : Nat, StandardRed (LambdaTerm.shift d c t) (LambdaTerm.shift d c u) := by
  induction h with
  | @var t n hw =>
      intro c
      have hw' := hw.shift d c
      rcases Nat.lt_or_ge n c with hlt | hge
      · rw [LambdaTerm.shift_var_lt n d c hlt] at hw' ⊢
        exact .var hw'
      · rw [LambdaTerm.shift_var_ge n d c hge] at hw' ⊢
        exact .var hw'
  | lam hw _ ih =>
      intro c
      have hw' := hw.shift d c
      rw [LambdaTerm.shift_lam] at hw' ⊢
      exact .lam hw' (ih (c + 1))
  | app hw _ _ ihf iha =>
      intro c
      have hw' := hw.shift d c
      rw [LambdaTerm.shift_app] at hw' ⊢
      exact .app hw' (ihf c) (iha c)

/-- Standard reductions are closed under substitution of standard reductions. -/
theorem subst {t t' : LambdaTerm} (h : StandardRed t t') :
    ∀ {j : Nat} {u u' : LambdaTerm}, StandardRed u u' →
      StandardRed (LambdaTerm.subst j u t) (LambdaTerm.subst j u' t') := by
  induction h with
  | @var t n hw =>
      intro j u u' hu
      have hw' := hw.subst j u
      rcases Nat.lt_trichotomy n j with hlt | rfl | hgt
      · rw [LambdaTerm.subst_var_lt n j hlt] at hw' ⊢
        exact .var hw'
      · rw [LambdaTerm.subst_var_eq] at hw' ⊢
        exact weakHead_trans hw' hu
      · rw [LambdaTerm.subst_var_gt n j hgt] at hw' ⊢
        exact .var hw'
  | lam hw _ ih =>
      intro j u u' hu
      have hw' := hw.subst j u
      rw [LambdaTerm.subst_lam] at hw' ⊢
      exact .lam hw' (ih (hu.shift 1 0))
  | app hw _ _ ihf iha =>
      intro j u u' hu
      have hw' := hw.subst j u
      rw [LambdaTerm.subst_app] at hw' ⊢
      exact .app hw' (ihf hu) (iha hu)

/-- A parallel step extends a standard reduction to a standard reduction. -/
theorem parRed_trans {t u : LambdaTerm} (h : StandardRed t u) :
    ∀ {v : LambdaTerm}, (u ⇛ v) → StandardRed t v := by
  induction h with
  | var hw =>
      intro v huv
      cases huv
      exact .var hw
  | lam hw _ ih =>
      intro v huv
      cases huv with
      | lam hb => exact .lam hw (ih hb)
  | @app t function argument function' argument' hw _ _ ihf iha =>
      intro v huv
      cases huv with
      | app hf ha => exact .app hw (ihf hf) (iha ha)
      | beta hb ha =>
          obtain ⟨body, hbody, hstd⟩ := lam_inv (ihf (ParRed.lam hb))
          exact weakHead_trans
            ((hw.trans (hbody.appLeft argument)).tail (WeakHeadStep.beta body argument))
            (hstd.subst (iha ha))

/-- Standardization: every parallel reduction sequence is a standard reduction. -/
theorem of_parRedStar {t u : LambdaTerm} (h : t ⇛* u) : StandardRed t u := by
  induction h with
  | refl => exact refl t
  | tail _ hs ih => exact ih.parRed_trans hs

/-- A standard reduction to a variable-headed spine weak-head-reduces to one. -/
theorem exists_weakHeadStar_isAppHead {t u : LambdaTerm} (h : StandardRed t u)
    (hu : u.isAppHead = true) : ∃ v, WeakHeadStar t v ∧ v.isAppHead = true := by
  induction h with
  | var hw => exact ⟨_, hw, rfl⟩
  | lam _ _ _ => simp [LambdaTerm.isAppHead] at hu
  | @app t function argument function' argument' hw _ _ ihf _ =>
      obtain ⟨v, hv, hva⟩ := ihf hu
      exact ⟨.app v argument, hw.trans (hv.appLeft argument), hva⟩

/-- A standard reduction to a head normal form yields a terminating head reduction. -/
theorem headNormalizes {t u : LambdaTerm} (h : StandardRed t u) (hu : u.isHNF = true) :
    HeadNormalizes t := by
  induction h with
  | var hw => exact .of_weakHeadStar hw (.hnf rfl)
  | lam hw _ ih => exact .of_weakHeadStar hw (ih hu).lam
  | @app t function argument function' argument' hw hf _ _ _ =>
      obtain ⟨v, hv, hva⟩ := hf.exists_weakHeadStar_isAppHead hu
      exact .of_weakHeadStar (hw.trans (hv.appLeft argument)) (.hnf hva)

end StandardRed

/-- **Head normalization.** Head reduction of a solvable term terminates in a
head normal form. -/
theorem headNormalizes_of_solvable {t : LambdaTerm} (h : t.Solvable) : HeadNormalizes t := by
  obtain ⟨result, hred, hhead⟩ := h
  exact (StandardRed.of_parRedStar hred).headNormalizes hhead

theorem solvable_iff_headNormalizes {t : LambdaTerm} : t.Solvable ↔ HeadNormalizes t :=
  ⟨headNormalizes_of_solvable, HeadNormalizes.solvable⟩

/-! ## Head contexts preserve unsolvability -/

/-- A map on terms that commutes with head steps and creates no head normal
form reflects solvability: if head reduction of `f t` terminates then `t` is
solvable. Head reduction is deterministic, so the head reduction of `f t` is
the image of the head reduction of `t` for as long as `t` has a head step. -/
theorem solvable_of_headNormalizes_map (f : LambdaTerm → LambdaTerm)
    (reflectsHead : ∀ t : LambdaTerm, (f t).isHNF = true → t.isHNF = true)
    (commutes : ∀ {t t' : LambdaTerm}, HeadStep t t' → HeadStep (f t) (f t'))
    {s : LambdaTerm} (hs : HeadNormalizes s) :
    ∀ {t : LambdaTerm}, f t = s → t.Solvable := by
  induction hs with
  | hnf hhead =>
      intro t ht
      subst ht
      exact LambdaTerm.solvable_of_isHNF (reflectsHead t hhead)
  | @step s s' hstep _ ih =>
      intro t ht
      subst ht
      cases hHead : t.isHNF with
      | true => exact LambdaTerm.solvable_of_isHNF hHead
      | false =>
          obtain ⟨t', ht'⟩ := HeadStep.exists_of_isHNF_eq_false hHead
          have hs' : s' = f t' := hstep.deterministic (commutes ht')
          exact LambdaTerm.solvable_of_reduces (Relation.ReflTransGen.single ht'.parRed)
            (ih hs'.symm)

/-- If head reduction of `t[u/j]` terminates then `t` is solvable. -/
theorem solvable_of_headNormalizes_subst {j : Nat} {u s : LambdaTerm} (hs : HeadNormalizes s)
    {t : LambdaTerm} (ht : LambdaTerm.subst j u t = s) : t.Solvable :=
  solvable_of_headNormalizes_map (LambdaTerm.subst j u)
    (fun _ h => LambdaTerm.isHNF_of_isHNF_subst h) (fun h => h.subst j u) hs ht

/-- Substitution cannot make an unsolvable term solvable. -/
theorem solvable_of_solvable_subst {j : Nat} {u t : LambdaTerm}
    (h : (LambdaTerm.subst j u t).Solvable) : t.Solvable :=
  solvable_of_headNormalizes_subst (headNormalizes_of_solvable h) rfl

/-- Head normalization is preserved by shifting. -/
theorem HeadNormalizes.shift {t : LambdaTerm} (h : HeadNormalizes t) (d : Nat) :
    ∀ c : Nat, HeadNormalizes (LambdaTerm.shift d c t) := by
  induction h with
  | hnf hhead => exact fun c => .hnf ((LambdaTerm.isHNF_shift d _ c).trans hhead)
  | step hs _ ih => exact fun c => .step (hs.shift d c) (ih c)

/-- Shifting neither creates nor destroys solvability. -/
theorem solvable_shift_iff {d c : Nat} {t : LambdaTerm} :
    (LambdaTerm.shift d c t).Solvable ↔ t.Solvable := by
  constructor
  · intro h
    exact solvable_of_headNormalizes_map (LambdaTerm.shift d c)
      (fun t hhead => (LambdaTerm.isHNF_shift d t c).symm.trans hhead)
      (fun hstep => hstep.shift d c) (headNormalizes_of_solvable h) rfl
  · intro h
    exact ((headNormalizes_of_solvable h).shift d c).solvable

theorem solvable_lam_iff {t : LambdaTerm} : (LambdaTerm.lam t).Solvable ↔ t.Solvable := by
  constructor
  · rintro ⟨result, hred, hhead⟩
    obtain ⟨body, rfl, hbody⟩ := parRedStar_lam_inv hred
    exact ⟨body, hbody, hhead⟩
  · rintro ⟨result, hred, hhead⟩
    exact ⟨.lam result, parRedStar_iterate_lam 1 hred, hhead⟩

/-- If head reduction of `t u` terminates then `t` is solvable. -/
theorem solvable_of_headNormalizes_app {s : LambdaTerm} (hs : HeadNormalizes s) :
    ∀ {t u : LambdaTerm}, LambdaTerm.app t u = s → t.Solvable := by
  induction hs with
  | hnf hhead =>
      intro t u htu
      subst htu
      exact LambdaTerm.solvable_of_isHNF (LambdaTerm.isHNF_of_isAppHead hhead)
  | @step s s' hstep hs' ih =>
      intro t u htu
      subst htu
      cases hstep with
      | weak hw =>
          cases hw with
          | beta body _ => exact solvable_lam_iff.2 (solvable_of_headNormalizes_subst hs' rfl)
          | appLeft _ hf =>
              exact LambdaTerm.solvable_of_reduces (Relation.ReflTransGen.single hf.parRed) (ih rfl)

/-- An application is unsolvable whenever its function is. -/
theorem solvable_of_solvable_app {t u : LambdaTerm} (h : (LambdaTerm.app t u).Solvable) :
    t.Solvable :=
  solvable_of_headNormalizes_app (headNormalizes_of_solvable h) rfl

namespace LambdaTerm.Unsolvable

theorem subst {t : LambdaTerm} (h : t.Unsolvable) (j : Nat) (u : LambdaTerm) :
    (LambdaTerm.subst j u t).Unsolvable :=
  fun hs => h (solvable_of_solvable_subst hs)

theorem shift {t : LambdaTerm} (h : t.Unsolvable) (d c : Nat) :
    (LambdaTerm.shift d c t).Unsolvable :=
  fun hs => h (solvable_shift_iff.1 hs)

theorem lam {t : LambdaTerm} (h : t.Unsolvable) : (LambdaTerm.lam t).Unsolvable :=
  fun hs => h (solvable_lam_iff.1 hs)

theorem app {t : LambdaTerm} (h : t.Unsolvable) (u : LambdaTerm) :
    (LambdaTerm.app t u).Unsolvable :=
  fun hs => h (solvable_of_solvable_app hs)

theorem iterate_lam {t : LambdaTerm} (h : t.Unsolvable) (k : Nat) :
    (LambdaTerm.lam^[k] t).Unsolvable := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.lam

theorem foldl_app {t : LambdaTerm} (h : t.Unsolvable) (args : List LambdaTerm) :
    (args.foldl .app t).Unsolvable := by
  induction args generalizing t with
  | nil => exact h
  | cons a rest ih => exact ih (h.app a)

end LambdaTerm.Unsolvable

/-! ## Solvable terms are driven to the identity -/

/-- Applying `λz₁ ⋯ zₘ. I` to `m` arguments returns `I`. -/
theorem foldl_app_selector_reduces_to_I : ∀ args : List LambdaTerm,
    (args.foldl .app (LambdaTerm.lam^[args.length] LambdaTerm.I)) ⇛* LambdaTerm.I
  | [] => Relation.ReflTransGen.refl
  | a :: rest => by
      have hstep : (LambdaTerm.app (LambdaTerm.lam^[rest.length + 1] LambdaTerm.I) a) ⇛
          (LambdaTerm.lam^[rest.length] LambdaTerm.I) := by
        have hbeta := ParRed.beta (ParRed.refl (LambdaTerm.lam^[rest.length] LambdaTerm.I))
          (ParRed.refl a)
        rw [LambdaTerm.subst_eq_self_of_closedAt a (closedAt_selector rest.length)
          (Nat.zero_le 0)] at hbeta
        rw [Function.iterate_succ_apply']
        exact hbeta
      exact Relation.ReflTransGen.head (parRed_foldl_app_left hstep rest)
        (foldl_app_selector_reduces_to_I rest)

/-- Feeding a closed term `N` to all `p` binders of `λ^p. h M₁ ⋯ Mₖ` puts `N` at
the head, provided the head is `N` or a variable bound by the prefix. -/
theorem foldl_app_iterate_lam_replicate {N : LambdaTerm} (hN : N.ClosedAt 0) :
    ∀ (p : Nat) (head : LambdaTerm) (args : List LambdaTerm),
      (head = N ∨ ∃ y, y < p ∧ head = .var y) →
      ∃ args' : List LambdaTerm, args'.length = args.length ∧
        ((List.replicate p N).foldl .app (LambdaTerm.lam^[p] (args.foldl .app head))) ⇛*
          (args'.foldl .app N)
  | 0, head, args, hhead => by
      rcases hhead with hh | ⟨y, hy, _⟩
      · exact ⟨args, rfl, by rw [hh]; exact Relation.ReflTransGen.refl⟩
      · exact absurd hy (Nat.not_lt_zero y)
  | p + 1, head, args, hhead => by
      have hhead' : LambdaTerm.subst p N head = N ∨
          ∃ y, y < p ∧ LambdaTerm.subst p N head = .var y := by
        rcases hhead with hh | ⟨y, hy, rfl⟩
        · rw [hh]
          exact Or.inl (LambdaTerm.subst_eq_self_of_closedAt N hN (Nat.zero_le p))
        · by_cases hyp : y = p
          · subst hyp
            exact Or.inl (LambdaTerm.subst_var_eq y N)
          · exact Or.inr ⟨y, by omega, LambdaTerm.subst_var_lt y p (by omega) N⟩
      obtain ⟨args', hlen, hred⟩ := foldl_app_iterate_lam_replicate hN p
        (LambdaTerm.subst p N head) (args.map (LambdaTerm.subst p N)) hhead'
      refine ⟨args', hlen.trans (by simp), ?_⟩
      have hstep : (LambdaTerm.app (LambdaTerm.lam^[p + 1] (args.foldl .app head)) N) ⇛
          (LambdaTerm.lam^[p]
            ((args.map (LambdaTerm.subst p N)).foldl .app (LambdaTerm.subst p N head))) := by
        have hbeta := ParRed.beta
          (ParRed.refl (LambdaTerm.lam^[p] (args.foldl .app head))) (ParRed.refl N)
        rw [LambdaTerm.subst_iterate_lam_of_closedAt hN p 0, Nat.zero_add,
          LambdaTerm.subst_foldl_app] at hbeta
        rw [Function.iterate_succ_apply']
        exact hbeta
      exact Relation.ReflTransGen.head (parRed_foldl_app_left hstep _) hred

/-- **Solvable terms are driven to `I`.** If `s` is solvable then some context
`(λ^q [·]) N₁ ⋯ Nₚ` reduces `s` to `I`. -/
theorem exists_context_reduces_to_I {s : LambdaTerm} (hs : s.Solvable) :
    ∃ (q : Nat) (args : List LambdaTerm),
      (args.foldl .app (LambdaTerm.lam^[q] s)) ⇛* LambdaTerm.I := by
  obtain ⟨hnf, hred, hhead⟩ := hs
  obtain ⟨n, y, args, rfl⟩ := LambdaTerm.exists_eq_iterate_lam_foldl_app_var_of_isHNF hhead
  obtain ⟨args', hlen, hdrive⟩ := foldl_app_iterate_lam_replicate
    (closedAt_selector args.length) (y + 1 + n) (.var y) args (Or.inr ⟨y, by omega, rfl⟩)
  refine ⟨y + 1, List.replicate (y + 1 + n) (LambdaTerm.lam^[args.length] LambdaTerm.I), ?_⟩
  have hclose := parRedStar_foldl_app_left (parRedStar_iterate_lam (y + 1) hred)
    (List.replicate (y + 1 + n) (LambdaTerm.lam^[args.length] LambdaTerm.I))
  rw [← Function.iterate_add_apply] at hclose
  have hselect := foldl_app_selector_reduces_to_I args'
  rw [hlen] at hselect
  exact hclose.trans (hdrive.trans hselect)

/-! ## Equations of a λ-theory -/

namespace LambdaTheory

theorem equates_of_parRed (T : LambdaTheory) {t t' : LambdaTerm} (h : t ⇛ t') :
    T.equates t t' := by
  induction h with
  | var _ => exact T.refl _
  | lam _ ih => exact T.congLam ih
  | app _ _ ihf iha => exact T.trans (T.congAppLeft ihf) (T.congAppRight iha)
  | @beta body body' argument argument' _ _ ihb iha =>
      exact T.trans (T.trans (T.congAppLeft (T.congLam ihb)) (T.congAppRight iha))
        (T.beta body' argument')

theorem equates_of_parRedStar (T : LambdaTheory) {t t' : LambdaTerm} (h : t ⇛* t') :
    T.equates t t' := by
  induction h with
  | refl => exact T.refl _
  | tail _ hs ih => exact T.trans ih (T.equates_of_parRed hs)

theorem equates_iterate_lam (T : LambdaTheory) {t t' : LambdaTerm} (h : T.equates t t')
    (k : Nat) : T.equates (LambdaTerm.lam^[k] t) (LambdaTerm.lam^[k] t') := by
  induction k with
  | zero => exact h
  | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact T.congLam ih

theorem equates_foldl_app (T : LambdaTheory) {t t' : LambdaTerm} (h : T.equates t t')
    (args : List LambdaTerm) : T.equates (args.foldl .app t) (args.foldl .app t') := by
  induction args generalizing t t' with
  | nil => exact h
  | cons a rest ih => exact ih (T.congAppLeft h)

/-- A theory that equates `I` with `K` equates every term with `I`: `B` is
`I I B`, which the theory equates with `K I B`, and `K I B` reduces to `I`. -/
theorem equates_I_of_equates_I_K (T : LambdaTheory)
    (h : T.equates LambdaTerm.I LambdaTerm.K) (B : LambdaTerm) : T.equates B LambdaTerm.I := by
  have left : (LambdaTerm.app (.app LambdaTerm.I LambdaTerm.I) B) ⇛* B :=
    Relation.ReflTransGen.head
      (ParRed.app (ParRed.beta (ParRed.var 0) (ParRed.refl LambdaTerm.I)) (ParRed.refl B))
      (Relation.ReflTransGen.single (ParRed.beta (ParRed.var 0) (ParRed.refl B)))
  have right : (LambdaTerm.app (.app LambdaTerm.K LambdaTerm.I) B) ⇛* LambdaTerm.I :=
    Relation.ReflTransGen.head
      (ParRed.app (ParRed.beta (ParRed.refl (.lam (.var 1))) (ParRed.refl LambdaTerm.I))
        (ParRed.refl B))
      (Relation.ReflTransGen.single (ParRed.beta (ParRed.refl LambdaTerm.I) (ParRed.refl B)))
  exact T.trans (T.symm (T.equates_of_parRedStar left))
    (T.trans (T.congAppLeft (T.congAppLeft h)) (T.equates_of_parRedStar right))

/-- Consistency, defined as not equating `I` with `K`, is the usual notion: a
theory is consistent exactly when it does not equate all terms. -/
theorem consistent_iff_exists_not_equates {T : LambdaTheory} :
    T.Consistent ↔ ∃ t s : LambdaTerm, ¬T.equates t s :=
  ⟨fun h => ⟨_, _, h⟩, fun ⟨t, s, hts⟩ hIK =>
    hts (T.trans (T.equates_I_of_equates_I_K hIK t) (T.symm (T.equates_I_of_equates_I_K hIK s)))⟩

/-- A theory equating all unsolvables that equates one of them with `I` equates `I`
with `K`: every term `A` is `I A = U A`, which is unsolvable, hence equal to `Ω`. -/
theorem EquatesUnsolvables.equates_I_K_of_equates_unsolvable_I {T : LambdaTheory}
    (hSens : T.EquatesUnsolvables)
    {U : LambdaTerm} (hU : U.Unsolvable) (hUI : T.equates U LambdaTerm.I) :
    T.equates LambdaTerm.I LambdaTerm.K := by
  have hOmega : ∀ A : LambdaTerm, T.equates A LambdaTerm.Omega := by
    intro A
    have hbeta := T.beta (.var 0) A
    rw [LambdaTerm.subst_var_eq] at hbeta
    exact T.trans (T.symm hbeta)
      (T.trans (T.congAppLeft (T.symm hUI)) (hSens _ _ (hU.app A) Omega_unsolvable))
  exact T.trans (hOmega _) (T.symm (hOmega _))

end LambdaTheory

/-! ## Sensible theories -/

/-- Equating all unsolvables and consistency imply semisensibility.

If `T` equates an unsolvable `t` with a solvable `s`, the context that reduces
`s` to `I` (`exists_context_reduces_to_I`) turns `t` into an unsolvable term
(`LambdaTerm.Unsolvable.iterate_lam`, `LambdaTerm.Unsolvable.foldl_app`) that
`T` equates with `I`. Sensibility then gives `T ⊢ I = K`
(`LambdaTheory.EquatesUnsolvables.equates_I_K_of_equates_unsolvable_I`), contradicting
consistency. -/
theorem equates_unsolvables_consistent_imp_semisensible {T : LambdaTheory}
    (hSens : T.EquatesUnsolvables) (hCons : T.Consistent) : T.Semisensible := by
  intro t s ht hts hs
  obtain ⟨q, args, hI⟩ := exists_context_reduces_to_I hs
  exact hCons (hSens.equates_I_K_of_equates_unsolvable_I ((ht.iterate_lam q).foldl_app args)
    (T.trans (T.equates_foldl_app (T.equates_iterate_lam hts q) args)
      (T.equates_of_parRedStar hI)))

/-- Sensible theories are semisensible; consistency is part of sensibility. -/
theorem sensible_imp_semisensible {T : LambdaTheory}
    (h : T.Sensible) : T.Semisensible :=
  equates_unsolvables_consistent_imp_semisensible h.equates_unsolvables h.consistent

end Mettapedia.GSLT.GraphTheory
