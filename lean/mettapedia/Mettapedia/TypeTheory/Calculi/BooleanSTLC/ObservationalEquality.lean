import Mettapedia.TypeTheory.Calculi.BooleanSTLC.Evaluation

/-!
# Observational equality by recursion on type formers

Observational type theory decides when two values are equal by recursion on
their type: "values should be equal when they support equal observations",
which for types with inductive eliminators is equality of construction and for
types with projective eliminators is agreement of the projections (Altenkirch,
McBride and Swierstra, *Observational Equality, Now!*, PLPV 2007, §3.1).

For closed terms of the boolean calculus this module defines

* `ObsEq`: constructor-wise at `bool` (the same boolean), logical equivalence at
  `prop`, componentwise at products and pointwise at functions;
* `ObsEqLogical`: the same with the clause of the paper at functions, taking
  equal inputs to equal outputs.

It proves:

* both relations are invariant under evaluation (`ObsEq.congr`,
  `ObsEqLogical.congr`), and `ObsEq` is an equivalence;
* **the fundamental lemma** (`fundamental`): every open term maps related
  closing substitutions to related results, so every closed term is related to
  itself by `ObsEqLogical`;
* **the two clauses coincide** (`obsEqLogical_iff_obsEq`);
* **the context lemma** (`ObsEq.app_right`, `ObsEq.fill`): every closed context
  preserves observational equality, and observational equality is exactly
  agreement of all closed contexts with a ground result
  (`obsEq_iff_contextual`).

The argument is the logical-relations proof that logical and observational
equivalence coincide for Gödel's T (Harper, *Practical Foundations for
Programming Languages*, Ch. 47), with booleans, products and propositions in
place of natural numbers and evaluation in the standard model in place of a
transition system.

Controls (`Examples`): the identity on booleans and its expansion by case
analysis are observationally equal with distinct codes, as are an η-expansion
and its function; `⊤` and `⊤ ∧ ⊤` are observationally equal with distinct codes;
the identity and negation, and `⊤` and `⊥`, are observationally distinct.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.BooleanSTLC

/-! ## The two recursive definitions -/

/-- **Observational equality** of closed terms, by recursion on the type:
constructor-wise at booleans, logical equivalence at propositions,
componentwise at products and pointwise at functions. -/
def ObsEq : (A : Ty) → Closed A → Closed A → Prop
  | .bool, t, u => t.value = u.value
  | .prop, t, u => (t.value ↔ u.value)
  | .prod A B, t, u => ObsEq A (.fst t) (.fst u) ∧ ObsEq B (.snd t) (.snd u)
  | .arr A B, t, u => ∀ a : Closed A, ObsEq B (.app t a) (.app u a)

/-- Observational equality with the function clause of observational type
theory: functions are equal when they take equal inputs to equal outputs. -/
def ObsEqLogical : (A : Ty) → Closed A → Closed A → Prop
  | .bool, t, u => t.value = u.value
  | .prop, t, u => (t.value ↔ u.value)
  | .prod A B, t, u => ObsEqLogical A (.fst t) (.fst u) ∧ ObsEqLogical B (.snd t) (.snd u)
  | .arr A B, t, u =>
      ∀ a a' : Closed A, ObsEqLogical A a a' → ObsEqLogical B (.app t a) (.app u a')

/-! ## Invariance under evaluation, and the equivalence laws -/

/-- Terms with the same value are observationally equal. -/
theorem ObsEq.of_value_eq : ∀ {A : Ty} {t u : Closed A}, t.value = u.value → ObsEq A t u
  | .bool, _, _, h => h
  | .prop, _, _, h => Iff.of_eq h
  | .prod _ _, _, _, h =>
      ⟨ObsEq.of_value_eq (congrArg Prod.fst h), ObsEq.of_value_eq (congrArg Prod.snd h)⟩
  | .arr _ _, _, _, h => fun a => ObsEq.of_value_eq (congrFun h a.value)

/-- Observational equality depends only on values. -/
theorem ObsEq.congr {A : Ty} : ∀ {t t' u u' : Closed A},
    t.value = t'.value → u.value = u'.value → ObsEq A t u → ObsEq A t' u' := by
  induction A with
  | bool => intro _ _ _ _ ht hu h; exact Eq.trans ht.symm (Eq.trans h hu)
  | prop => intro _ _ _ _ ht hu h; exact Iff.trans (Iff.of_eq ht).symm (Iff.trans h (Iff.of_eq hu))
  | prod A B ihA ihB =>
      intro t t' u u' ht hu h
      exact ⟨ihA (t := .fst t) (t' := .fst t') (u := .fst u) (u' := .fst u')
          (congrArg Prod.fst ht) (congrArg Prod.fst hu) h.1,
        ihB (t := .snd t) (t' := .snd t') (u := .snd u) (u' := .snd u')
          (congrArg Prod.snd ht) (congrArg Prod.snd hu) h.2⟩
  | arr A B _ ihB =>
      intro t t' u u' ht hu h a
      exact ihB (t := .app t a) (t' := .app t' a) (u := .app u a) (u' := .app u' a)
        (congrFun ht a.value) (congrFun hu a.value) (h a)

theorem ObsEq.refl {A : Ty} (t : Closed A) : ObsEq A t t :=
  ObsEq.of_value_eq rfl

theorem ObsEq.symm {A : Ty} : ∀ {t u : Closed A}, ObsEq A t u → ObsEq A u t := by
  induction A with
  | bool => intro _ _ h; exact Eq.symm h
  | prop => intro _ _ h; exact Iff.symm h
  | prod A B ihA ihB => intro _ _ h; exact ⟨ihA h.1, ihB h.2⟩
  | arr A B _ ihB => intro _ _ h a; exact ihB (h a)

theorem ObsEq.trans {A : Ty} : ∀ {t u v : Closed A}, ObsEq A t u → ObsEq A u v → ObsEq A t v := by
  induction A with
  | bool => intro _ _ _ h h'; exact Eq.trans h h'
  | prop => intro _ _ _ h h'; exact Iff.trans h h'
  | prod A B ihA ihB => intro _ _ _ h h'; exact ⟨ihA h.1 h'.1, ihB h.2 h'.2⟩
  | arr A B _ ihB => intro _ _ _ h h' a; exact ihB (h a) (h' a)

/-- Observational equality as a setoid on closed terms of a type. -/
def obsEqSetoid (A : Ty) : Setoid (Closed A) :=
  ⟨ObsEq A, ⟨ObsEq.refl, ObsEq.symm, ObsEq.trans⟩⟩

/-- The logical clause also depends only on values. -/
theorem ObsEqLogical.congr {A : Ty} : ∀ {t t' u u' : Closed A},
    t.value = t'.value → u.value = u'.value → ObsEqLogical A t u → ObsEqLogical A t' u' := by
  induction A with
  | bool => intro _ _ _ _ ht hu h; exact Eq.trans ht.symm (Eq.trans h hu)
  | prop => intro _ _ _ _ ht hu h; exact Iff.trans (Iff.of_eq ht).symm (Iff.trans h (Iff.of_eq hu))
  | prod A B ihA ihB =>
      intro t t' u u' ht hu h
      exact ⟨ihA (t := .fst t) (t' := .fst t') (u := .fst u) (u' := .fst u')
          (congrArg Prod.fst ht) (congrArg Prod.fst hu) h.1,
        ihB (t := .snd t) (t' := .snd t') (u := .snd u) (u' := .snd u')
          (congrArg Prod.snd ht) (congrArg Prod.snd hu) h.2⟩
  | arr A B _ ihB =>
      intro t t' u u' ht hu h a a' related
      exact ihB (t := .app t a) (t' := .app t' a) (u := .app u a') (u' := .app u' a')
        (congrFun ht a.value) (congrFun hu a'.value) (h a a' related)

/-! ## The fundamental lemma -/

/-- **Fundamental lemma.**  An open term maps closing substitutions that are
related variable by variable to related closed terms. -/
theorem fundamental {Γ : Ctx} {A : Ty} (t : Tm Γ A) :
    ∀ σ σ' : Sub Γ [], (∀ ⦃B : Ty⦄ (v : Var Γ B), ObsEqLogical B (σ v) (σ' v)) →
      ObsEqLogical A (t.subst σ) (t.subst σ') := by
  induction t with
  | var v => intro _ _ h; exact h v
  | tt => intro _ _ _; exact rfl
  | ff => intro _ _ _; exact rfl
  | ite c t e ihc iht ihe =>
      intro σ σ' h
      have hc : (c.subst σ).value = (c.subst σ').value := ihc σ σ' h
      have hvalue : ∀ τ : Sub _ [], ((Tm.ite c t e).subst τ).value =
          cond (c.subst τ).value (t.subst τ).value (e.subst τ).value := fun _ => rfl
      cases hb : (c.subst σ).value with
      | true =>
          have hb' : (c.subst σ').value = true := hc.symm.trans hb
          exact ObsEqLogical.congr (by rw [hvalue σ, hb]; rfl) (by rw [hvalue σ', hb']; rfl)
            (iht σ σ' h)
      | false =>
          have hb' : (c.subst σ').value = false := hc.symm.trans hb
          exact ObsEqLogical.congr (by rw [hvalue σ, hb]; rfl) (by rw [hvalue σ', hb']; rfl)
            (ihe σ σ' h)
  | pair a b iha ihb =>
      intro σ σ' h
      refine ⟨ObsEqLogical.congr ?_ ?_ (iha σ σ' h), ObsEqLogical.congr ?_ ?_ (ihb σ σ' h)⟩ <;> rfl
  | fst p ih => intro σ σ' h; exact (ih σ σ' h).1
  | snd p ih => intro σ σ' h; exact (ih σ σ' h).2
  | lam b ih =>
      intro σ σ' h a a' related
      refine ObsEqLogical.congr (Tm.value_app_lam_subst σ b a).symm
        (Tm.value_app_lam_subst σ' b a').symm (ih (Sub.cons a σ) (Sub.cons a' σ') ?_)
      intro _ v
      cases v with
      | zero => exact related
      | succ w => exact h w
  | app f a ihf iha =>
      intro σ σ' h
      exact ihf σ σ' h (a.subst σ) (a.subst σ') (iha σ σ' h)
  | top => intro _ _ _; exact Iff.rfl
  | bot => intro _ _ _; exact Iff.rfl
  | and p q ihp ihq => intro σ σ' h; exact and_congr (ihp σ σ' h) (ihq σ σ' h)
  | imp p q ihp ihq => intro σ σ' h; exact imp_congr (ihp σ σ' h) (ihq σ σ' h)
  | isTrue b ih =>
      intro σ σ' h
      exact Iff.of_eq (congrArg (fun x : Bool => x = true) (ih σ σ' h))
  | allBool b ih =>
      intro σ σ' h
      show (∀ x : Bool, (b.subst σ.lift).eval (Env.empty.cons x)) ↔
        ∀ x : Bool, (b.subst σ'.lift).eval (Env.empty.cons x)
      refine forall_congr' fun x => ?_
      have related : ObsEqLogical .prop (b.subst (Sub.cons (Tm.ofBool x) σ))
          (b.subst (Sub.cons (Tm.ofBool x) σ')) := by
        refine ih _ _ ?_
        intro _ v
        cases v with
        | zero => exact rfl
        | succ w => exact h w
      exact (Iff.of_eq (Tm.eval_allBool_subst σ b x)).trans
        (related.trans (Iff.of_eq (Tm.eval_allBool_subst σ' b x).symm))

/-- Every closed term is related to itself by the logical clause. -/
theorem ObsEqLogical.refl {A : Ty} (t : Closed A) : ObsEqLogical A t t :=
  ObsEqLogical.congr (Tm.value_subst_closed t Sub.ofEmpty) (Tm.value_subst_closed t Sub.ofEmpty)
    (fundamental t Sub.ofEmpty Sub.ofEmpty fun _ v => nomatch v)

/-- **The pointwise clause and the clause of observational type theory
coincide on closed terms.** -/
theorem obsEqLogical_iff_obsEq : ∀ {A : Ty} {t u : Closed A}, ObsEqLogical A t u ↔ ObsEq A t u
  | .bool, _, _ => Iff.rfl
  | .prop, _, _ => Iff.rfl
  | .prod _ _, _, _ => and_congr obsEqLogical_iff_obsEq obsEqLogical_iff_obsEq
  | .arr _ _, _, u => by
      constructor
      · intro h a
        exact obsEqLogical_iff_obsEq.mp (h a a (ObsEqLogical.refl a))
      · intro h a a' related
        exact obsEqLogical_iff_obsEq.mpr
          (ObsEq.trans (h a) (obsEqLogical_iff_obsEq.mp (ObsEqLogical.refl u a a' related)))

/-! ## The context lemma -/

/-- **Every closed context preserves observational equality.** -/
theorem ObsEq.app_right {A B : Ty} (k : Closed (.arr A B)) {t u : Closed A}
    (related : ObsEq A t u) : ObsEq B (.app k t) (.app k u) :=
  obsEqLogical_iff_obsEq.mp (ObsEqLogical.refl k t u (obsEqLogical_iff_obsEq.mpr related))

/-- **Every term with one hole preserves observational equality.** -/
theorem ObsEq.fill {A B : Ty} (body : Tm [A] B) {t u : Closed A} (related : ObsEq A t u) :
    ObsEq B (body.fill t) (body.fill u) := by
  refine obsEqLogical_iff_obsEq.mp (fundamental body _ _ ?_)
  intro _ v
  cases v with
  | zero => exact obsEqLogical_iff_obsEq.mpr related
  | succ w => exact nomatch w

/-- Contextual equivalence: every closed context with a boolean result computes
the same boolean, and every closed context with a propositional result gives
logically equivalent propositions. -/
def Contextual (A : Ty) (t u : Closed A) : Prop :=
  (∀ k : Closed (.arr A .bool), (Tm.app k t).value = (Tm.app k u).value) ∧
    ∀ k : Closed (.arr A .prop), ((Tm.app k t).value ↔ (Tm.app k u).value)

theorem ObsEq.contextual {A : Ty} {t u : Closed A} (related : ObsEq A t u) :
    Contextual A t u :=
  ⟨fun k => related.app_right k, fun k => related.app_right k⟩

/-- The value of `λx. k (body x)` applied to `s`. -/
theorem Tm.value_app_lam_app_weaken {A B C : Ty} (k : Closed (.arr B C)) (body : Tm [A] B)
    (s : Closed A) :
    (Tm.app (.lam (.app k.weaken body)) s).value =
      k.value (body.eval (Env.empty.cons s.value)) := by
  show (k.weaken : Tm [A] _).eval _ _ = _
  rw [Tm.eval_weaken]
  rfl

theorem Contextual.fst {A B : Ty} {t u : Closed (.prod A B)}
    (h : Contextual (.prod A B) t u) : Contextual A (.fst t) (.fst u) := by
  constructor
  · intro k
    have e := h.1 (.lam (.app k.weaken (.fst (.var .zero))))
    rwa [Tm.value_app_lam_app_weaken, Tm.value_app_lam_app_weaken] at e
  · intro k
    have e := h.2 (.lam (.app k.weaken (.fst (.var .zero))))
    rwa [Tm.value_app_lam_app_weaken, Tm.value_app_lam_app_weaken] at e

theorem Contextual.snd {A B : Ty} {t u : Closed (.prod A B)}
    (h : Contextual (.prod A B) t u) : Contextual B (.snd t) (.snd u) := by
  constructor
  · intro k
    have e := h.1 (.lam (.app k.weaken (.snd (.var .zero))))
    rwa [Tm.value_app_lam_app_weaken, Tm.value_app_lam_app_weaken] at e
  · intro k
    have e := h.2 (.lam (.app k.weaken (.snd (.var .zero))))
    rwa [Tm.value_app_lam_app_weaken, Tm.value_app_lam_app_weaken] at e

theorem Contextual.app {A B : Ty} {t u : Closed (.arr A B)}
    (h : Contextual (.arr A B) t u) (a : Closed A) : Contextual B (.app t a) (.app u a) := by
  have body : ∀ s : Closed (.arr A B),
      (Tm.app (.var .zero) a.weaken : Tm [.arr A B] B).eval (Env.empty.cons s.value) =
        (Tm.app s a).value := fun s => by
    show s.value ((a.weaken : Tm [.arr A B] A).eval _) = s.value a.value
    rw [Tm.eval_weaken]
  constructor
  · intro k
    have e := h.1 (.lam (.app k.weaken (.app (.var .zero) a.weaken)))
    rwa [Tm.value_app_lam_app_weaken, Tm.value_app_lam_app_weaken, body, body] at e
  · intro k
    have e := h.2 (.lam (.app k.weaken (.app (.var .zero) a.weaken)))
    rwa [Tm.value_app_lam_app_weaken, Tm.value_app_lam_app_weaken, body, body] at e

theorem Contextual.obsEq : ∀ {A : Ty} {t u : Closed A}, Contextual A t u → ObsEq A t u
  | .bool, _, _, h => h.1 (.lam (.var .zero))
  | .prop, _, _, h => h.2 (.lam (.var .zero))
  | .prod _ _, _, _, h => ⟨Contextual.obsEq h.fst, Contextual.obsEq h.snd⟩
  | .arr _ _, _, _, h => fun a => Contextual.obsEq (h.app a)

/-- **Context lemma.**  Observational equality, defined by recursion on type
formers, is contextual equivalence. -/
theorem obsEq_iff_contextual {A : Ty} {t u : Closed A} : ObsEq A t u ↔ Contextual A t u :=
  ⟨ObsEq.contextual, Contextual.obsEq⟩

/-! ## Controls -/

namespace Examples

/-- The identity on booleans. -/
def idBool : Closed (.arr .bool .bool) := .lam (.var .zero)

/-- The identity on booleans, written by case analysis. -/
def condIdBool : Closed (.arr .bool .bool) := .lam (.ite (.var .zero) .tt .ff)

/-- Negation. -/
def notBool : Closed (.arr .bool .bool) := .lam (.ite (.var .zero) .ff .tt)

/-- The η-expansion of a closed function. -/
def etaExpand {A B : Ty} (f : Closed (.arr A B)) : Closed (.arr A B) :=
  .lam (.app f.weaken (.var .zero))

/-- Positive: the identity and its expansion by case analysis are
observationally equal. -/
theorem obsEq_idBool_condIdBool : ObsEq _ idBool condIdBool := by
  intro a
  show a.value = cond a.value true false
  generalize a.value = x
  cases x <;> rfl

/-- ... and their codes differ. -/
theorem idBool_code_ne : idBool.code ≠ condIdBool.code := by decide

/-- Negative: the identity and negation are observationally distinct. -/
theorem not_obsEq_idBool_notBool : ¬ ObsEq _ idBool notBool := fun h =>
  Bool.noConfusion (h .tt : (true : Bool) = false)

/-- Positive: η-expansion is observationally invisible. -/
theorem obsEq_etaExpand {A B : Ty} (f : Closed (.arr A B)) : ObsEq _ (etaExpand f) f :=
  fun a => ObsEq.of_value_eq (by
    show (f.weaken : Tm [A] _).eval _ _ = f.value a.value
    rw [Tm.eval_weaken]
    rfl)

/-- ... while it changes the code. -/
theorem etaExpand_idBool_code_ne : (etaExpand idBool).code ≠ idBool.code := by decide

/-- Positive: `⊤` and `⊤ ∧ ⊤` are observationally equal. -/
theorem obsEq_top_andTopTop : ObsEq .prop .top (.and .top .top) :=
  ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩

/-- ... and their codes differ. -/
theorem top_code_ne_andTopTop :
    (Tm.top : Closed .prop).code ≠ (Tm.and .top .top : Closed .prop).code := by
  decide

/-- Negative: `⊤` and `⊥` are observationally distinct. -/
theorem not_obsEq_top_bot : ¬ ObsEq .prop .top .bot := fun h => h.mp trivial

end Examples

end Mettapedia.TypeTheory.Calculi.BooleanSTLC
