import Mettapedia.Logic.HOL.ProofSyntaxModuloStructural

/-!
# Closed definitions are conservative for proofs modulo conversion

A closed definition `c := t` adds the defining equation `c = t` (empty pattern
telescope, `DefiningEquation.ofDefinition`) to the equations a checker computes
with. Proofs modulo the extended list translate to proofs modulo the old list
by unfolding `c` everywhere: `substConst` replaces `c` by `t` in every
sequent, every rule is kept, every hypothesis maps to its unfolding, and
every conversion article maps to an article (`ProofSyntaxModulo.unfoldDefinition`).

**Side conditions** (`ProofSyntaxModulo.definition_conservative`):

* `t : ClosedTerm Const σ` for `c : Const σ`: the body is closed and has the
  type of `c`, by the types;
* `t` does not mention `c` (`NoConstOccurrence c t`);
* `c` occurs in no equation of the old list (`EquationsAvoid c eqs`);
* `u` unfolds the definition (`Unfolds c t u`): it sends `c` to `t`, fixes
  every other constant, and each constant is either `c` or another one. Under
  decidable equality of types and of the constants at `c`'s type, `unfold c t`
  is such a map (`unfold_unfolds`).

Then a sequent whose hypotheses and conclusion do not mention `c` is provable
modulo `(c = t) :: eqs` iff it is provable modulo `eqs`. The body need not be
core: conversion articles are between core terms, so a body that is not core
never fires (`ProofSyntaxModulo.inert_definition`); a core body is unfolded.
Conversion articles between terms without `c` are conservative in the same way
(`CoreConversion.definition_conservative`).

**Unfolding** (`definition_unfold_iff`): for a core body, a core sequent is
provable modulo `(c = t) :: eqs` iff its unfolding is provable modulo `eqs`. The
definition is one δ-step (`SourceStep.ofDefinition`), and core terms convert to
their unfoldings (`Unfolds.conversion`).

The engine is general: a constant substitution by closed core terms that
sends each listed equation to a listed equation or to a trivial one maps
steps, articles and proofs (`SourceStep.substConst`, `CoreConversion.substConst`,
`ProofSyntaxModulo.substConst`).

**Controls** (`DefinitionControls`), over a signature with one propositional
constant `c`. Each of the following violates exactly one side condition, and
`∀p. p`, which does not mention `c` and has no proof without the new equation,
gains one:

* `c := c → ∀p. p` violates acyclicity: Curry's paradox
  (`curry_not_conservative`);
* `c := p`, with `p` a pattern variable, violates closedness: it identifies all
  core propositions (`loose_not_conservative`);
* `c := ∀p. p → p`, added to the listed `c := ∀p. p`, violates the absence of `c`
  from the listed equations (`redefinition_not_conservative`).

Violating a side condition does not by itself produce a counterexample:
`c := c → c` violates acyclicity, yet it holds in the model with `c` true, so it
proves no `∀p. p` (`loop_consistent`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Core terms, constant substitution, congruence of articles -/

theorem Term.isCore_weakenCtx (Γ : Ctx Base) {τ : Ty Base} (t : ClosedTerm Const τ) :
    (weakenCtx Γ t).isCore = t.isCore := by
  induction Γ with
  | nil => rfl
  | cons σ Γ ih => rw [weakenCtx_cons, weaken, Term.isCore_rename, ih]

section ConstSubst

variable {Const' : Ty Base → Type w}

/-- A constant substitution whose images are core terms. -/
def ConstSubstCore (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ) : Prop :=
  ∀ {τ : Ty Base} (c : Const τ), (f c).isCore = true

theorem Term.isCore_substConst {f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ}
    (core : ConstSubstCore f) {Γ : Ctx Base} {τ : Ty Base} (t : Term Const Γ τ) :
    (substConst f t).isCore = t.isCore := by
  induction t with
  | var => rfl
  | const c => exact (Term.isCore_weakenCtx _ (f c)).trans (core c)
  | app g a ihg iha => simp only [substConst, isCore, ihg, iha]
  | lam b ih => simp only [substConst, isCore, ih]
  | top | bot => rfl
  | and p q ihp ihq | or p q ihp ihq => simp only [substConst, isCore]
  | imp p q ihp ihq => simp only [substConst, isCore, ihp, ihq]
  | not p ih => simp only [substConst, isCore]
  | eq l r ihl ihr => simp only [substConst, isCore, ihl, ihr]
  | all b ih => simp only [substConst, isCore, ih]
  | ex b ih => simp only [substConst, isCore]

/-- The image of a defining equation under a constant substitution. -/
def DefiningEquation.substConst (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    (equation : DefiningEquation Const) : DefiningEquation Const' where
  context := equation.context
  type := equation.type
  left := HOL.substConst f equation.left
  right := HOL.substConst f equation.right

/-- `f` interprets the equations `eqs` in `eqs'`: each listed equation goes to a
listed equation, or to an equation whose two sides coincide. -/
def ConstSubstInterprets (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    (eqs : List (DefiningEquation Const)) (eqs' : List (DefiningEquation Const')) : Prop :=
  ∀ equation ∈ eqs, HOL.substConst f equation.left = HOL.substConst f equation.right ∨
    equation.substConst f ∈ eqs'

theorem substConst_weakenHyps (f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ)
    {Γ : Ctx Base} {σ : Ty Base} (Δ : List (Formula Const Γ)) :
    weakenHyps (σ := σ) (Δ.map (HOL.substConst f)) =
      (weakenHyps (σ := σ) Δ).map (HOL.substConst f) := by
  simp only [weakenHyps, List.map_map]
  exact List.map_congr_left fun φ _ => (substConst_weaken f φ).symm

/-- **Steps.** A definitional step goes to a step, or to an identity when its
equation goes to a trivial one. -/
theorem SourceStep.substConst {f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ}
    (core : ConstSubstCore f) {eqs : List (DefiningEquation Const)}
    {eqs' : List (DefiningEquation Const')} (interprets : ConstSubstInterprets f eqs eqs')
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ} (step : SourceStep eqs s t) :
    HOL.substConst f s = HOL.substConst f t ∨
      SourceStep eqs' (HOL.substConst f s) (HOL.substConst f t) := by
  induction step with
  | beta body argument =>
      right
      rw [substConst_instantiate]
      exact .beta _ _
  | delta equation listed substitution coreSubst =>
      rw [← substConst_subst f substitution equation.left,
        ← substConst_subst f substitution equation.right]
      rcases interprets equation listed with same | mapped
      · left
        rw [same]
      · right
        exact .delta (equation.substConst f) mapped (fun i => HOL.substConst f (substitution i))
          (fun i => (Term.isCore_substConst core _).trans (coreSubst i))
  | appFun argument _ ih =>
      exact ih.imp (congrArg (fun g => Term.app g (HOL.substConst f argument)))
        (SourceStep.appFun _)
  | appArg function _ ih =>
      exact ih.imp (congrArg (Term.app (HOL.substConst f function))) (SourceStep.appArg _)
  | lam _ ih => exact ih.imp (congrArg Term.lam) SourceStep.lam
  | impLeft right _ ih =>
      exact ih.imp (congrArg (fun p => Term.imp p (HOL.substConst f right)))
        (SourceStep.impLeft _)
  | impRight left _ ih =>
      exact ih.imp (congrArg (Term.imp (HOL.substConst f left))) (SourceStep.impRight _)
  | eqLeft right _ ih =>
      exact ih.imp (congrArg (fun l => Term.eq l (HOL.substConst f right))) (SourceStep.eqLeft _)
  | eqRight left _ ih =>
      exact ih.imp (congrArg (Term.eq (HOL.substConst f left))) (SourceStep.eqRight _)
  | all _ ih => exact ih.imp (congrArg Term.all) SourceStep.all

/-- **Articles.** A conversion article goes to a conversion article. -/
theorem CoreConversion.substConst {f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ}
    (core : ConstSubstCore f) {eqs : List (DefiningEquation Const)}
    {eqs' : List (DefiningEquation Const')} (interprets : ConstSubstInterprets f eqs eqs')
    {Γ : Ctx Base} {τ : Ty Base} {s t : Term Const Γ τ} (conversion : CoreConversion eqs s t) :
    CoreConversion eqs' (HOL.substConst f s) (HOL.substConst f t) := by
  induction conversion with
  | rel a b step =>
      obtain ⟨ha, hb, source⟩ := step
      rcases source.substConst core interprets with same | image
      · rw [same]
        exact .refl _
      · exact .rel _ _ ⟨(Term.isCore_substConst core a).trans ha,
          (Term.isCore_substConst core b).trans hb, image⟩
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

/-- **Proofs.** The image of a proof under a constant substitution by closed core
terms that interprets its equations. Every rule is kept; each sequent is
replaced by its image. -/
def ProofSyntaxModulo.substConst {f : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const' τ}
    (core : ConstSubstCore f) {eqs : List (DefiningEquation Const)}
    {eqs' : List (DefiningEquation Const')} (interprets : ConstSubstInterprets f eqs eqs')
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ φ) :
    ProofSyntaxModulo eqs' (Δ.map (HOL.substConst f)) (HOL.substConst f φ) :=
  match proof with
  | .hyp occurrence =>
      castIndices rfl (by simp) (.hyp (Δ := Δ.map (HOL.substConst f)) (occurrence.cast (by simp)))
  | .impI body => .impI (substConst core interprets body)
  | .impE function argument =>
      .impE (substConst core interprets function) (substConst core interprets argument)
  | .allI body =>
      .allI (castIndices (substConst_weakenHyps f _).symm rfl (substConst core interprets body))
  | .allE term function =>
      castIndices rfl (substConst_instantiate f term _).symm
        (.allE (HOL.substConst f term) (substConst core interprets function))
  | .convert article inner =>
      .convert (article.substConst core interprets) (substConst core interprets inner)

end ConstSubst

section Congruence

variable {eqs : List (DefiningEquation Const)}

/-- A map of terms that carries each core step to a core step carries articles. -/
theorem CoreConversion.map {eqs' : List (DefiningEquation Const)} {Γ Γ' : Ctx Base}
    {τ τ' : Ty Base} {F : Term Const Γ τ → Term Const Γ' τ'}
    (step : ∀ {a b : Term Const Γ τ}, CoreStep eqs a b → CoreStep eqs' (F a) (F b))
    {s t : Term Const Γ τ} (conversion : CoreConversion eqs s t) :
    CoreConversion eqs' (F s) (F t) := by
  induction conversion with
  | rel a b h => exact .rel _ _ (step h)
  | refl => exact .refl _
  | symm _ _ _ ih => exact .symm _ _ ih
  | trans _ _ _ _ _ first second => exact .trans _ _ _ first second

theorem CoreConversion.appFun {Γ : Ctx Base} {σ τ : Ty Base} {g g' : Term Const Γ (σ ⇒ τ)}
    {a : Term Const Γ σ} (core : a.isCore = true) (conversion : CoreConversion eqs g g') :
    CoreConversion eqs (.app g a) (.app g' a) :=
  conversion.map (F := fun g => .app g a) fun step =>
    ⟨by simp only [Term.isCore, step.1, core, Bool.and_self],
      by simp only [Term.isCore, step.2.1, core, Bool.and_self], .appFun _ step.2.2⟩

theorem CoreConversion.appArg {Γ : Ctx Base} {σ τ : Ty Base} {g : Term Const Γ (σ ⇒ τ)}
    {a a' : Term Const Γ σ} (core : g.isCore = true) (conversion : CoreConversion eqs a a') :
    CoreConversion eqs (.app g a) (.app g a') :=
  conversion.map (F := Term.app g) fun step =>
    ⟨by simp only [Term.isCore, step.1, core, Bool.and_self],
      by simp only [Term.isCore, step.2.1, core, Bool.and_self], .appArg _ step.2.2⟩

theorem CoreConversion.lam {Γ : Ctx Base} {σ τ : Ty Base} {b b' : Term Const (σ :: Γ) τ}
    (conversion : CoreConversion eqs b b') : CoreConversion eqs (.lam b) (.lam b') :=
  conversion.map (F := Term.lam) fun step =>
    ⟨by simpa only [Term.isCore] using step.1, by simpa only [Term.isCore] using step.2.1,
      .lam step.2.2⟩

theorem CoreConversion.impLeft {Γ : Ctx Base} {p p' q : Formula Const Γ}
    (core : q.isCore = true) (conversion : CoreConversion eqs p p') :
    CoreConversion eqs (.imp p q) (.imp p' q) :=
  conversion.map (F := fun p => .imp p q) fun step =>
    ⟨by simp only [Term.isCore, step.1, core, Bool.and_self],
      by simp only [Term.isCore, step.2.1, core, Bool.and_self], .impLeft _ step.2.2⟩

theorem CoreConversion.impRight {Γ : Ctx Base} {p q q' : Formula Const Γ}
    (core : p.isCore = true) (conversion : CoreConversion eqs q q') :
    CoreConversion eqs (.imp p q) (.imp p q') :=
  conversion.map (F := Term.imp p) fun step =>
    ⟨by simp only [Term.isCore, step.1, core, Bool.and_self],
      by simp only [Term.isCore, step.2.1, core, Bool.and_self], .impRight _ step.2.2⟩

theorem CoreConversion.eqLeft {Γ : Ctx Base} {τ : Ty Base} {l l' r : Term Const Γ τ}
    (core : r.isCore = true) (conversion : CoreConversion eqs l l') :
    CoreConversion eqs (.eq l r) (.eq l' r) :=
  conversion.map (F := fun l => .eq l r) fun step =>
    ⟨by simp only [Term.isCore, step.1, core, Bool.and_self],
      by simp only [Term.isCore, step.2.1, core, Bool.and_self], .eqLeft _ step.2.2⟩

theorem CoreConversion.eqRight {Γ : Ctx Base} {τ : Ty Base} {l r r' : Term Const Γ τ}
    (core : l.isCore = true) (conversion : CoreConversion eqs r r') :
    CoreConversion eqs (.eq l r) (.eq l r') :=
  conversion.map (F := Term.eq l) fun step =>
    ⟨by simp only [Term.isCore, step.1, core, Bool.and_self],
      by simp only [Term.isCore, step.2.1, core, Bool.and_self], .eqRight _ step.2.2⟩

theorem CoreConversion.all {Γ : Ctx Base} {σ : Ty Base} {b b' : Formula Const (σ :: Γ)}
    (conversion : CoreConversion eqs b b') : CoreConversion eqs (.all b) (.all b') :=
  conversion.map (F := Term.all) fun step =>
    ⟨by simpa only [Term.isCore] using step.1, by simpa only [Term.isCore] using step.2.1,
      .all step.2.2⟩

end Congruence

/-! ## More equations, and converted hypotheses -/

section Structural

variable {eqs eqs' : List (DefiningEquation Const)}

theorem SourceStep.widen (subset : eqs ⊆ eqs') {Γ : Ctx Base} {τ : Ty Base}
    {s t : Term Const Γ τ} (step : SourceStep eqs s t) : SourceStep eqs' s t := by
  induction step with
  | beta body argument => exact .beta _ _
  | delta equation listed substitution core => exact .delta equation (subset listed) _ core
  | appFun argument _ ih => exact .appFun _ ih
  | appArg function _ ih => exact .appArg _ ih
  | lam _ ih => exact .lam ih
  | impLeft right _ ih => exact .impLeft _ ih
  | impRight left _ ih => exact .impRight _ ih
  | eqLeft right _ ih => exact .eqLeft _ ih
  | eqRight left _ ih => exact .eqRight _ ih
  | all _ ih => exact .all ih

theorem CoreConversion.widen (subset : eqs ⊆ eqs') {Γ : Ctx Base} {τ : Ty Base}
    {s t : Term Const Γ τ} (conversion : CoreConversion eqs s t) : CoreConversion eqs' s t :=
  conversion.map (F := id) fun step => ⟨step.1, step.2.1, step.2.2.widen subset⟩

/-- A proof whose articles are articles of another list of equations is a proof
modulo that list: every rule and sequent is kept. -/
def ProofSyntaxModulo.mapArticles
    (transport : ∀ {Γ : Ctx Base} {l r : Formula Const Γ},
      CoreConversion eqs l r → CoreConversion eqs' l r)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo eqs Δ φ) : ProofSyntaxModulo eqs' Δ φ :=
  match proof with
  | .hyp occurrence => .hyp occurrence
  | .impI body => .impI (mapArticles transport body)
  | .impE function argument =>
      .impE (mapArticles transport function) (mapArticles transport argument)
  | .allI body => .allI (mapArticles transport body)
  | .allE term function => .allE term (mapArticles transport function)
  | .convert article inner => .convert (transport article) (mapArticles transport inner)

/-- A proof modulo fewer equations is a proof modulo more. -/
def ProofSyntaxModulo.widen (subset : eqs ⊆ eqs') {Γ : Ctx Base} {Δ : List (Formula Const Γ)}
    {φ : Formula Const Γ} (proof : ProofSyntaxModulo eqs Δ φ) : ProofSyntaxModulo eqs' Δ φ :=
  proof.mapArticles (CoreConversion.widen subset)

theorem forall₂_weakenHyps {Γ : Ctx Base} {σ : Ty Base} {Δ Δ' : List (Formula Const Γ)}
    (related : List.Forall₂ (CoreConversion eqs) Δ Δ') :
    List.Forall₂ (CoreConversion eqs) (weakenHyps (σ := σ) Δ) (weakenHyps (σ := σ) Δ') := by
  induction related with
  | nil => exact .nil
  | cons head _ ih => exact .cons (head.rename Rename.weaken) ih

/-- Hypotheses may be replaced by convertible ones: each use of a hypothesis
becomes a use of its replacement followed by the article. -/
def ProofSyntaxModulo.convertHyps {Γ : Ctx Base} {Δ Δ' : List (Formula Const Γ)}
    {φ : Formula Const Γ} (related : List.Forall₂ (CoreConversion eqs) Δ Δ')
    (proof : ProofSyntaxModulo eqs Δ φ) : ProofSyntaxModulo eqs Δ' φ :=
  match proof with
  | .hyp occurrence =>
      .convert (.symm _ _ (related.get occurrence.isLt
          (related.length_eq ▸ occurrence.isLt)))
        (.hyp (occurrence.cast related.length_eq))
  | .impI body => .impI (convertHyps (.cons (.refl _) related) body)
  | .impE function argument => .impE (convertHyps related function) (convertHyps related argument)
  | .allI body => .allI (convertHyps (forall₂_weakenHyps related) body)
  | .allE term function => .allE term (convertHyps related function)
  | .convert article inner => .convert article (convertHyps related inner)

end Structural

/-! ## Closed definitions -/

/-- The defining equation of the closed definition `c := t`. -/
def DefiningEquation.ofDefinition {σ : Ty Base} (c : Const σ) (t : ClosedTerm Const σ) :
    DefiningEquation Const where
  context := []
  type := σ
  left := .const c
  right := t

/-- `c` occurs in no listed equation. -/
def EquationsAvoid {σ : Ty Base} (c : Const σ) (eqs : List (DefiningEquation Const)) : Prop :=
  ∀ equation ∈ eqs, NoConstOccurrence c equation.left ∧ NoConstOccurrence c equation.right

theorem NoConstOccurrence.const_ctx {σ : Ty Base} {c : Const σ} {Γ Γ' : Ctx Base} {τ : Ty Base}
    {d : Const τ} (avoids : NoConstOccurrence c (.const d : Term Const Γ τ)) :
    NoConstOccurrence c (.const d : Term Const Γ' τ) := by
  cases avoids with
  | const_diff_type hne => exact .const_diff_type hne d
  | const_same_ne _ hne => exact .const_same_ne _ hne

/-! ### A definition with a non-core body never fires -/

/-- Substitution creates no core term: a term with a core instance is core. -/
theorem Term.isCore_of_isCore_subst :
    ∀ {Γ Δ : Ctx Base} {θ : Subst Const Γ Δ} {τ : Ty Base} (t : Term Const Γ τ),
      (HOL.subst θ t).isCore = true → t.isCore = true
  | _, _, _, _, .var _, _ => rfl
  | _, _, _, _, .const _, _ => rfl
  | _, _, _, _, .app g a, h => by
      simp only [HOL.subst, Term.isCore, Bool.and_eq_true] at h ⊢
      exact ⟨isCore_of_isCore_subst g h.1, isCore_of_isCore_subst a h.2⟩
  | _, _, _, _, .lam b, h => by
      simp only [HOL.subst, Term.isCore] at h ⊢
      exact isCore_of_isCore_subst b h
  | _, _, _, _, .imp p q, h => by
      simp only [HOL.subst, Term.isCore, Bool.and_eq_true] at h ⊢
      exact ⟨isCore_of_isCore_subst p h.1, isCore_of_isCore_subst q h.2⟩
  | _, _, _, _, .eq l r, h => by
      simp only [HOL.subst, Term.isCore, Bool.and_eq_true] at h ⊢
      exact ⟨isCore_of_isCore_subst l h.1, isCore_of_isCore_subst r h.2⟩
  | _, _, _, _, .all b, h => by
      simp only [HOL.subst, Term.isCore] at h ⊢
      exact isCore_of_isCore_subst b h
  | _, _, _, _, .top, h | _, _, _, _, .bot, h | _, _, _, _, .and _ _, h
  | _, _, _, _, .or _ _, h | _, _, _, _, .not _, h | _, _, _, _, .ex _, h => by
      simp [HOL.subst, Term.isCore] at h

section Inert

variable {σ : Ty Base} {c : Const σ} {t : ClosedTerm Const σ}
  {eqs : List (DefiningEquation Const)}

/-- A step with a core target never uses a definition whose body is not core. -/
theorem SourceStep.of_inert (inert : t.isCore = false) {Γ : Ctx Base} {τ : Ty Base}
    {l r : Term Const Γ τ} (step : SourceStep (DefiningEquation.ofDefinition c t :: eqs) l r)
    (core : r.isCore = true) : SourceStep eqs l r := by
  induction step with
  | beta body argument => exact .beta _ _
  | delta equation listed substitution coreSubst =>
      rcases List.mem_cons.mp listed with rfl | listed
      · have bodyCore : t.isCore = true := Term.isCore_of_isCore_subst _ core
        exact absurd (inert.symm.trans bodyCore) Bool.false_ne_true
      · exact .delta equation listed substitution coreSubst
  | appFun argument _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .appFun _ (ih core.1)
  | appArg function _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .appArg _ (ih core.2)
  | lam _ ih =>
      simp only [Term.isCore] at core
      exact .lam (ih core)
  | impLeft right _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .impLeft _ (ih core.1)
  | impRight left _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .impRight _ (ih core.2)
  | eqLeft right _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .eqLeft _ (ih core.1)
  | eqRight left _ ih =>
      simp only [Term.isCore, Bool.and_eq_true] at core
      exact .eqRight _ (ih core.2)
  | all _ ih =>
      simp only [Term.isCore] at core
      exact .all (ih core)

theorem CoreConversion.of_inert (inert : t.isCore = false) {Γ : Ctx Base} {τ : Ty Base}
    {l r : Term Const Γ τ}
    (conversion : CoreConversion (DefiningEquation.ofDefinition c t :: eqs) l r) :
    CoreConversion eqs l r :=
  conversion.map (F := id) fun step => ⟨step.1, step.2.1, step.2.2.of_inert inert step.2.1⟩

/-- **A definition whose body is not core is inert.** Conversion articles are
between core terms, so they never use it: every sequent has a proof modulo
`(c = t) :: eqs` iff it has one modulo `eqs`. -/
theorem ProofSyntaxModulo.inert_definition (inert : t.isCore = false) {Γ : Ctx Base}
    {Δ : List (Formula Const Γ)} {φ : Formula Const Γ} :
    Nonempty (ProofSyntaxModulo (DefiningEquation.ofDefinition c t :: eqs) Δ φ) ↔
      Nonempty (ProofSyntaxModulo eqs Δ φ) :=
  ⟨fun ⟨proof⟩ => ⟨proof.mapArticles (CoreConversion.of_inert inert)⟩,
    fun ⟨proof⟩ => ⟨proof.widen (List.subset_cons_self _ _)⟩⟩

end Inert

/-- `u` unfolds the closed definition `c := t`: it sends `c` to `t`, fixes every
other constant, and each constant is `c` or another constant. -/
structure Unfolds {σ : Ty Base} (c : Const σ) (t : ClosedTerm Const σ)
    (u : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const τ) : Prop where
  self : u c = t
  other : ∀ {τ : Ty Base} (d : Const τ),
    NoConstOccurrence c (.const d : ClosedTerm Const τ) → u d = .const d
  dichotomy : ∀ {τ : Ty Base} (d : Const τ),
    NoConstOccurrence c (.const d : ClosedTerm Const τ) ∨
      (⟨τ, d⟩ : (τ : Ty Base) × Const τ) = ⟨σ, c⟩

/-- The definition as one δ-step, in every context. -/
theorem SourceStep.ofDefinition {σ : Ty Base} (c : Const σ) (t : ClosedTerm Const σ)
    (eqs : List (DefiningEquation Const)) (Γ : Ctx Base) :
    SourceStep (DefiningEquation.ofDefinition c t :: eqs) (.const c : Term Const Γ σ)
      (weakenCtx Γ t) := by
  have vacuous : ∀ s : Subst Const [] Γ, HOL.subst s t = weakenCtx Γ t :=
    fun s => subst_weakenCtx (Γ' := []) s t
  rw [← vacuous fun i => nomatch i]
  exact .delta (DefiningEquation.ofDefinition c t) (.head _) _ fun i => nomatch i

namespace Unfolds

variable {σ : Ty Base} {c : Const σ} {t : ClosedTerm Const σ}
  {u : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const τ}

/-- The unfolding fixes every term that does not mention `c`. -/
theorem fixes (unfolds : Unfolds c t u) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} {X : Term Const Γ τ}, NoConstOccurrence c X →
      substConst u X = X
  | _, _, .var _, _ => rfl
  | Γ, _, .const d, h => by
      change weakenCtx Γ (u d) = .const d
      rw [unfolds.other d h.const_ctx, weakenCtx_const]
  | _, _, .app _ _, h => by
      cases h with
      | app hg ha => simp only [substConst, unfolds.fixes hg, unfolds.fixes ha]
  | _, _, .lam _, h => by
      cases h with
      | lam hb => simp only [substConst, unfolds.fixes hb]
  | _, _, .top, _ => rfl
  | _, _, .bot, _ => rfl
  | _, _, .and _ _, h => by
      cases h with
      | and hp hq => simp only [substConst, unfolds.fixes hp, unfolds.fixes hq]
  | _, _, .or _ _, h => by
      cases h with
      | or hp hq => simp only [substConst, unfolds.fixes hp, unfolds.fixes hq]
  | _, _, .imp _ _, h => by
      cases h with
      | imp hp hq => simp only [substConst, unfolds.fixes hp, unfolds.fixes hq]
  | _, _, .not _, h => by
      cases h with
      | not hp => simp only [substConst, unfolds.fixes hp]
  | _, _, .eq _ _, h => by
      cases h with
      | eq hl hr => simp only [substConst, unfolds.fixes hl, unfolds.fixes hr]
  | _, _, .all _, h => by
      cases h with
      | all hb => simp only [substConst, unfolds.fixes hb]
  | _, _, .ex _, h => by
      cases h with
      | ex hb => simp only [substConst, unfolds.fixes hb]

/-- A core body makes the unfolding a substitution by core terms. -/
theorem constSubstCore (unfolds : Unfolds c t u) (bodyCore : t.isCore = true) :
    ConstSubstCore u := by
  intro τ d
  show (u d).isCore = true
  rcases unfolds.dichotomy d with avoids | same
  · rw [unfolds.other d avoids]
    rfl
  · cases same
    rw [unfolds.self]
    exact bodyCore

/-- An equation without `c` is its own unfolding. -/
theorem equation_fixed (unfolds : Unfolds c t u) {equation : DefiningEquation Const}
    (avoids : NoConstOccurrence c equation.left ∧ NoConstOccurrence c equation.right) :
    equation.substConst u = equation := by
  obtain ⟨context, type, left, right⟩ := equation
  obtain ⟨hl, hr⟩ := avoids
  change DefiningEquation.mk context type (substConst u left) (substConst u right) = _
  rw [unfolds.fixes hl, unfolds.fixes hr]

/-- The unfolding interprets `(c = t) :: eqs` in `eqs`: the definition goes to
`t = t`, and every other equation to itself. -/
theorem interprets (unfolds : Unfolds c t u) (acyclic : NoConstOccurrence c t)
    {eqs : List (DefiningEquation Const)} (absent : EquationsAvoid c eqs) :
    ConstSubstInterprets u (DefiningEquation.ofDefinition c t :: eqs) eqs := by
  intro equation listed
  rcases List.mem_cons.mp listed with rfl | listed
  · left
    change u c = substConst u t
    rw [unfolds.fixes acyclic, unfolds.self]
  · right
    rw [unfolds.equation_fixed (absent equation listed)]
    exact listed

/-- **Core terms convert to their unfoldings**, modulo the definition. -/
theorem conversion (unfolds : Unfolds c t u) (bodyCore : t.isCore = true)
    {eqs : List (DefiningEquation Const)} :
    ∀ {Γ : Ctx Base} {τ : Ty Base} {X : Term Const Γ τ}, X.isCore = true →
      CoreConversion (DefiningEquation.ofDefinition c t :: eqs) X (substConst u X)
  | _, _, .var _, _ => .refl _
  | Γ, _, .const d, _ => by
      change CoreConversion _ (.const d) (weakenCtx Γ (u d))
      rcases unfolds.dichotomy d with avoids | same
      · rw [unfolds.other d avoids, weakenCtx_const]
        exact .refl _
      · cases same
        rw [unfolds.self]
        exact .rel _ _ ⟨rfl, (Term.isCore_weakenCtx Γ t).trans bodyCore,
          SourceStep.ofDefinition c t eqs Γ⟩
  | _, _, .app g a, core => by
      simp only [Term.isCore, Bool.and_eq_true] at core
      have unfolded : (substConst u g).isCore = true :=
        (Term.isCore_substConst (unfolds.constSubstCore bodyCore) g).trans core.1
      exact .trans _ _ _ ((unfolds.conversion bodyCore core.1).appFun core.2)
        ((unfolds.conversion bodyCore core.2).appArg unfolded)
  | _, _, .lam b, core => (unfolds.conversion bodyCore (X := b) core).lam
  | _, _, .imp p q, core => by
      simp only [Term.isCore, Bool.and_eq_true] at core
      have unfolded : (substConst u p).isCore = true :=
        (Term.isCore_substConst (unfolds.constSubstCore bodyCore) p).trans core.1
      exact .trans _ _ _ ((unfolds.conversion bodyCore core.1).impLeft core.2)
        ((unfolds.conversion bodyCore core.2).impRight unfolded)
  | _, _, .eq l r, core => by
      simp only [Term.isCore, Bool.and_eq_true] at core
      have unfolded : (substConst u l).isCore = true :=
        (Term.isCore_substConst (unfolds.constSubstCore bodyCore) l).trans core.1
      exact .trans _ _ _ ((unfolds.conversion bodyCore core.1).eqLeft core.2)
        ((unfolds.conversion bodyCore core.2).eqRight unfolded)
  | _, _, .all b, core => (unfolds.conversion bodyCore (X := b) core).all
  | _, _, .top, core | _, _, .bot, core | _, _, .and _ _, core | _, _, .or _ _, core
  | _, _, .not _, core | _, _, .ex _, core => by simp [Term.isCore] at core

end Unfolds

section Definition

variable {σ : Ty Base} {c : Const σ} {t : ClosedTerm Const σ}
  {u : ∀ {τ : Ty Base}, Const τ → ClosedTerm Const τ} {eqs : List (DefiningEquation Const)}

/-- **Unfolding a closed definition.** A proof modulo `(c = t) :: eqs` becomes a
proof modulo `eqs` of the unfolded sequent: every rule is kept, every
hypothesis and conclusion is unfolded, and every article is unfolded. -/
def ProofSyntaxModulo.unfoldDefinition (unfolds : Unfolds c t u) (bodyCore : t.isCore = true)
    (acyclic : NoConstOccurrence c t) (absent : EquationsAvoid c eqs)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (proof : ProofSyntaxModulo (DefiningEquation.ofDefinition c t :: eqs) Δ φ) :
    ProofSyntaxModulo eqs (Δ.map (HOL.substConst u)) (HOL.substConst u φ) :=
  proof.substConst (unfolds.constSubstCore bodyCore) (unfolds.interprets acyclic absent)

/-- Articles modulo the definition unfold to articles modulo `eqs`. -/
theorem CoreConversion.unfoldDefinition (unfolds : Unfolds c t u) (bodyCore : t.isCore = true)
    (acyclic : NoConstOccurrence c t) (absent : EquationsAvoid c eqs)
    {Γ : Ctx Base} {τ : Ty Base} {l r : Term Const Γ τ}
    (conversion : CoreConversion (DefiningEquation.ofDefinition c t :: eqs) l r) :
    CoreConversion eqs (HOL.substConst u l) (HOL.substConst u r) :=
  conversion.substConst (unfolds.constSubstCore bodyCore) (unfolds.interprets acyclic absent)

/-- **Closed definitions are conservative.** Let `c := t` be a closed definition:
`t` is a closed term of the type of `c` that does not mention `c`, and `c` occurs
in no equation of `eqs`. A sequent whose hypotheses and conclusion do not mention
`c` is provable modulo `(c = t) :: eqs` iff it is provable modulo `eqs`. A core
body is unfolded (`unfoldDefinition`); a body that is not core never fires
(`inert_definition`). -/
theorem ProofSyntaxModulo.definition_conservative (unfolds : Unfolds c t u)
    (acyclic : NoConstOccurrence c t) (absent : EquationsAvoid c eqs)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hypsAvoid : ∀ δ ∈ Δ, NoConstOccurrence c δ) (avoids : NoConstOccurrence c φ) :
    Nonempty (ProofSyntaxModulo (DefiningEquation.ofDefinition c t :: eqs) Δ φ) ↔
      Nonempty (ProofSyntaxModulo eqs Δ φ) := by
  cases bodyCore : t.isCore
  · exact ProofSyntaxModulo.inert_definition bodyCore
  constructor
  · rintro ⟨proof⟩
    have hyps : Δ.map (HOL.substConst u) = Δ := by
      conv_rhs => rw [← List.map_id Δ]
      exact List.map_congr_left fun δ listed => unfolds.fixes (hypsAvoid δ listed)
    exact ⟨castIndices hyps (unfolds.fixes avoids)
      (proof.unfoldDefinition unfolds bodyCore acyclic absent)⟩
  · rintro ⟨proof⟩
    exact ⟨proof.widen (List.subset_cons_self _ _)⟩

/-- **Unfolding is exact on core sequents.** A core sequent is provable modulo
`(c = t) :: eqs` iff its unfolding is provable modulo `eqs`. -/
theorem ProofSyntaxModulo.definition_unfold_iff (unfolds : Unfolds c t u)
    (bodyCore : t.isCore = true) (acyclic : NoConstOccurrence c t) (absent : EquationsAvoid c eqs)
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} {φ : Formula Const Γ}
    (hypsCore : ∀ δ ∈ Δ, δ.isCore = true) (core : φ.isCore = true) :
    Nonempty (ProofSyntaxModulo (DefiningEquation.ofDefinition c t :: eqs) Δ φ) ↔
      Nonempty (ProofSyntaxModulo eqs (Δ.map (HOL.substConst u)) (HOL.substConst u φ)) := by
  constructor
  · rintro ⟨proof⟩
    exact ⟨proof.unfoldDefinition unfolds bodyCore acyclic absent⟩
  · rintro ⟨proof⟩
    have hyps : List.Forall₂ (CoreConversion (DefiningEquation.ofDefinition c t :: eqs))
        (Δ.map (HOL.substConst u)) Δ := by
      rw [List.forall₂_map_left_iff]
      exact List.forall₂_same.mpr fun δ listed =>
        .symm _ _ (unfolds.conversion bodyCore (hypsCore δ listed))
    exact ⟨((proof.widen (List.subset_cons_self _ _)).convert
      (.symm _ _ (unfolds.conversion bodyCore core))).convertHyps hyps⟩

/-- Articles between terms without `c` are conservative. -/
theorem CoreConversion.definition_conservative (unfolds : Unfolds c t u)
    (acyclic : NoConstOccurrence c t) (absent : EquationsAvoid c eqs)
    {Γ : Ctx Base} {τ : Ty Base} {l r : Term Const Γ τ}
    (leftAvoids : NoConstOccurrence c l) (rightAvoids : NoConstOccurrence c r) :
    CoreConversion (DefiningEquation.ofDefinition c t :: eqs) l r ↔ CoreConversion eqs l r := by
  cases bodyCore : t.isCore
  · exact ⟨CoreConversion.of_inert bodyCore, CoreConversion.widen (List.subset_cons_self _ _)⟩
  constructor
  · intro conversion
    have image := conversion.unfoldDefinition unfolds bodyCore acyclic absent
    rwa [unfolds.fixes leftAvoids, unfolds.fixes rightAvoids] at image
  · exact CoreConversion.widen (List.subset_cons_self _ _)

end Definition

/-! ## Deciding occurrences and the canonical unfolding -/

/-- Whether a constant accepted by `test` occurs in the term. -/
def Term.anyConst (test : ∀ {τ : Ty Base}, Const τ → Bool) :
    {Γ : Ctx Base} → {τ : Ty Base} → Term Const Γ τ → Bool
  | _, _, .var _ => false
  | _, _, .const d => test d
  | _, _, .app g a => g.anyConst test || a.anyConst test
  | _, _, .lam b => b.anyConst test
  | _, _, .top => false
  | _, _, .bot => false
  | _, _, .and p q => p.anyConst test || q.anyConst test
  | _, _, .or p q => p.anyConst test || q.anyConst test
  | _, _, .imp p q => p.anyConst test || q.anyConst test
  | _, _, .not p => p.anyConst test
  | _, _, .eq l r => l.anyConst test || r.anyConst test
  | _, _, .all b => b.anyConst test
  | _, _, .ex b => b.anyConst test

section Occurrence

variable {σ : Ty Base} {c : Const σ} {test : ∀ {τ : Ty Base}, Const τ → Bool}

/-- A term none of whose constants passes a test that rejects only constants
other than `c` does not mention `c`. -/
theorem noConstOccurrence_of_anyConst
    (sound : ∀ {τ : Ty Base} (d : Const τ), test d = false →
      NoConstOccurrence c (.const d : ClosedTerm Const τ)) :
    ∀ {Γ : Ctx Base} {τ : Ty Base} (X : Term Const Γ τ), X.anyConst test = false →
      NoConstOccurrence c X
  | _, _, .var _, _ => .var
  | _, _, .const d, h => (sound d h).const_ctx
  | _, _, .app g a, h => by
      simp only [Term.anyConst, Bool.or_eq_false_iff] at h
      exact .app (noConstOccurrence_of_anyConst sound g h.1)
        (noConstOccurrence_of_anyConst sound a h.2)
  | _, _, .lam b, h => .lam (noConstOccurrence_of_anyConst sound b h)
  | _, _, .top, _ => .top
  | _, _, .bot, _ => .bot
  | _, _, .and p q, h => by
      simp only [Term.anyConst, Bool.or_eq_false_iff] at h
      exact .and (noConstOccurrence_of_anyConst sound p h.1)
        (noConstOccurrence_of_anyConst sound q h.2)
  | _, _, .or p q, h => by
      simp only [Term.anyConst, Bool.or_eq_false_iff] at h
      exact .or (noConstOccurrence_of_anyConst sound p h.1)
        (noConstOccurrence_of_anyConst sound q h.2)
  | _, _, .imp p q, h => by
      simp only [Term.anyConst, Bool.or_eq_false_iff] at h
      exact .imp (noConstOccurrence_of_anyConst sound p h.1)
        (noConstOccurrence_of_anyConst sound q h.2)
  | _, _, .not p, h => .not (noConstOccurrence_of_anyConst sound p h)
  | _, _, .eq l r, h => by
      simp only [Term.anyConst, Bool.or_eq_false_iff] at h
      exact .eq (noConstOccurrence_of_anyConst sound l h.1)
        (noConstOccurrence_of_anyConst sound r h.2)
  | _, _, .all b, h => .all (noConstOccurrence_of_anyConst sound b h)
  | _, _, .ex b, h => .ex (noConstOccurrence_of_anyConst sound b h)

theorem hypsAvoid_of_anyConst
    (sound : ∀ {τ : Ty Base} (d : Const τ), test d = false →
      NoConstOccurrence c (.const d : ClosedTerm Const τ))
    {Γ : Ctx Base} {Δ : List (Formula Const Γ)} (checked : Δ.all (!·.anyConst test) = true) :
    ∀ δ ∈ Δ, NoConstOccurrence c δ := by
  intro δ listed
  have := List.all_eq_true.mp checked δ listed
  exact noConstOccurrence_of_anyConst sound δ (by simpa using this)

theorem equationsAvoid_of_anyConst
    (sound : ∀ {τ : Ty Base} (d : Const τ), test d = false →
      NoConstOccurrence c (.const d : ClosedTerm Const τ))
    {eqs : List (DefiningEquation Const)}
    (checked : eqs.all (fun e => !e.left.anyConst test && !e.right.anyConst test) = true) :
    EquationsAvoid c eqs := by
  intro equation listed
  have := List.all_eq_true.mp checked equation listed
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at this
  exact ⟨noConstOccurrence_of_anyConst sound _ this.1,
    noConstOccurrence_of_anyConst sound _ this.2⟩

end Occurrence

section Canonical

variable [DecidableEq (Ty Base)] {σ : Ty Base} [DecidableEq (Const σ)]

/-- The unfolding of `c := t` at the type of `c`. -/
def unfoldAt (c : Const σ) (t : ClosedTerm Const σ) (d : Const σ) : ClosedTerm Const σ :=
  if d = c then t else .const d

/-- The unfolding of `c := t` under decidable equality of types and of the
constants at the type of `c`. -/
def unfold (c : Const σ) (t : ClosedTerm Const σ) {τ : Ty Base} (d : Const τ) :
    ClosedTerm Const τ :=
  if same : τ = σ then same ▸ unfoldAt c t (same ▸ d) else .const d

theorem unfold_unfolds (c : Const σ) (t : ClosedTerm Const σ) : Unfolds c t (unfold c t) where
  self := by
    show (if same : σ = σ then same ▸ unfoldAt c t (same ▸ c) else .const c) = t
    rw [dif_pos rfl]
    exact if_pos rfl
  other := by
    intro τ d avoids
    cases avoids with
    | const_diff_type hne =>
        show (if same : τ = σ then same ▸ unfoldAt c t (same ▸ d) else .const d) = .const d
        rw [dif_neg (Ne.symm hne)]
    | const_same_ne _ hne =>
        rw [unfold, dif_pos rfl]
        exact if_neg hne
  dichotomy := by
    intro τ d
    match decEq σ τ with
    | isTrue same =>
        subst same
        match decEq d c with
        | isTrue equal =>
            subst equal
            exact .inr rfl
        | isFalse differ => exact .inl (.const_same_ne d differ)
    | isFalse differ => exact .inl (.const_diff_type differ d)

end Canonical

/-! ## Controls: definitions that violate the side conditions -/

namespace DefinitionControls

/-- A signature with one propositional constant. -/
inductive Sig : Ty Unit → Type
  | c : Sig .prop

/-- `∀p. p`. -/
def falsity : ClosedFormula Sig := .all (σ := .prop) (.var .vz)

theorem falsity_avoids : NoConstOccurrence Sig.c falsity := .all .var

/-- `c` read as the proposition `b`. -/
def denWith (b : Prop) :
    {τ : Ty Unit} → Sig τ → Ty.denote.{0, 0} (fun _ : Unit => PUnit.{2}) τ
  | _, .c => ULift.up b

/-- The standard model with `c` read as `b`. -/
abbrev modelWith (b : Prop) : HenkinModel.{0, 0, 0} Unit Sig :=
  HenkinModel.standard.{0, 0, 0} (fun _ => PUnit.{2}) (denWith b)

theorem falsity_fails (b : Prop) {eqs : List (DefiningEquation Sig)}
    (hold : Soundness.EquationsHold (modelWith b) eqs) :
    ¬ Nonempty (ProofSyntaxModulo eqs [] falsity) := by
  rintro ⟨proof⟩
  have holds := Soundness.proofSyntaxModulo_sound proof hold
    (ρ := fun i => nomatch i) (fun i => nomatch i) (fun _ listed => absurd listed List.not_mem_nil)
  exact holds (ULift.up False) trivial

/-- Without equations `∀p. p` has no proof. -/
theorem falsity_not_derivable :
    ¬ Nonempty (ProofSyntaxModulo ([] : List (DefiningEquation Sig)) [] falsity) :=
  falsity_fails True fun _ listed => absurd listed List.not_mem_nil

/-- `∀p. p → p`. -/
def truth : ClosedFormula Sig := .all (σ := .prop) (.imp (.var .vz) (.var .vz))

def truthProof {eqs : List (DefiningEquation Sig)} : ProofSyntaxModulo eqs [] truth :=
  .allI (.impI (.hyp ⟨0, by decide⟩))

/-! ### Self-reference: Curry's `c := c → ∀p. p` -/

/-- The body `c → ∀p. p` mentions `c`. -/
def curryBody : ClosedTerm Sig .prop := .imp (.const .c) falsity

def curryEquation : DefiningEquation Sig := .ofDefinition .c curryBody

/-- The side condition it violates: its body mentions `c`. It is closed and core. -/
theorem curryBody_mentions : ¬ NoConstOccurrence Sig.c curryBody ∧ curryBody.isCore = true := by
  refine ⟨fun avoids => ?_, rfl⟩
  cases avoids with
  | imp hc _ =>
      cases hc with
      | const_diff_type hne => exact hne rfl
      | const_same_ne _ hne => exact hne rfl

theorem curryArticle : CoreConversion [curryEquation] (.const .c : ClosedFormula Sig) curryBody :=
  .rel _ _ ⟨rfl, rfl, SourceStep.ofDefinition Sig.c curryBody [] []⟩

/-- `¬c`, from `c` read as `¬c`. -/
def curryRefutation : ProofSyntaxModulo [curryEquation] [] curryBody :=
  .impI (.impE (.convert curryArticle (.hyp ⟨0, by decide⟩)) (.hyp ⟨0, by decide⟩))

/-- **Curry's paradox.** Modulo `c := c → ∀p. p`, `∀p. p` has a proof. -/
def curryFalsity : ProofSyntaxModulo [curryEquation] [] falsity :=
  .impE curryRefutation (.convert (.symm _ _ curryArticle) curryRefutation)

/-- **Conservativity fails** for the self-referential definition, at `∀p. p`,
which does not mention `c`. -/
theorem curry_not_conservative :
    ¬ ∀ φ : ClosedFormula Sig, NoConstOccurrence Sig.c φ →
      Nonempty (ProofSyntaxModulo [curryEquation] [] φ) →
        Nonempty (ProofSyntaxModulo ([] : List (DefiningEquation Sig)) [] φ) :=
  fun conservative => falsity_not_derivable (conservative falsity falsity_avoids ⟨curryFalsity⟩)

/-! ### An open body: `c := p` for every `p` -/

/-- `c = p` over the pattern telescope `p : prop`: the body is a variable. -/
def looseEquation : DefiningEquation Sig where
  context := [.prop]
  type := .prop
  left := .const .c
  right := .var .vz

/-- The side condition it violates: it is not a closed definition. -/
theorem looseEquation_not_closed (t : ClosedTerm Sig .prop) :
    looseEquation ≠ .ofDefinition .c t := fun same =>
  List.cons_ne_nil _ _ (congrArg DefiningEquation.context same)

/-- The loose equation identifies every two core propositions: `∀p. p → p`
with `c` with `∀p. p`. -/
theorem looseArticle : CoreConversion [looseEquation] truth falsity :=
  .trans _ (.const .c) _
    (.symm _ _ (.rel _ _ ⟨rfl, rfl,
      .delta looseEquation (.head _) (Subst.single truth) (CoreSubst.single rfl)⟩))
    (.rel _ _ ⟨rfl, rfl,
      .delta looseEquation (.head _) (Subst.single falsity) (CoreSubst.single rfl)⟩)

def looseFalsity : ProofSyntaxModulo [looseEquation] [] falsity :=
  .convert looseArticle truthProof

/-- **Conservativity fails** for the open definition, at `∀p. p`. -/
theorem loose_not_conservative :
    ¬ ∀ φ : ClosedFormula Sig, NoConstOccurrence Sig.c φ →
      Nonempty (ProofSyntaxModulo [looseEquation] [] φ) →
        Nonempty (ProofSyntaxModulo ([] : List (DefiningEquation Sig)) [] φ) :=
  fun conservative => falsity_not_derivable (conservative falsity falsity_avoids ⟨looseFalsity⟩)

/-! ### `c` already defined: a second definition -/

/-- `c := ∀p. p`, already listed. -/
def falsityDefinition : DefiningEquation Sig := .ofDefinition .c falsity

/-- `c := ∀p. p → p`, added: closed, core, and without `c`. -/
def truthDefinition : DefiningEquation Sig := .ofDefinition .c truth

/-- The side condition it violates: `c` occurs in the listed equation. The added
definition is closed, core and acyclic. -/
theorem redefinition_violates :
    ¬ EquationsAvoid Sig.c [falsityDefinition] ∧ truth.isCore = true ∧
      NoConstOccurrence Sig.c truth := by
  refine ⟨fun avoid => ?_, rfl, .all (.imp .var .var)⟩
  have mentions : NoConstOccurrence Sig.c (.const .c : ClosedTerm Sig .prop) :=
    (avoid falsityDefinition (.head _)).1
  cases mentions with
  | const_diff_type hne => exact hne rfl
  | const_same_ne _ hne => exact hne rfl

/-- The two definitions identify `∀p. p → p` with `c` with `∀p. p`. -/
theorem redefinitionArticle :
    CoreConversion [truthDefinition, falsityDefinition] truth falsity := by
  have toTruth : CoreConversion [truthDefinition, falsityDefinition] (.const .c) truth :=
    .rel _ _ ⟨rfl, rfl, SourceStep.ofDefinition Sig.c truth [falsityDefinition] []⟩
  have toFalsity : CoreConversion [truthDefinition, falsityDefinition] (.const .c) falsity :=
    .rel _ _ ⟨rfl, rfl,
      (SourceStep.ofDefinition Sig.c falsity [] []).widen (List.subset_cons_self _ _)⟩
  exact .trans _ _ _ (.symm _ _ toTruth) toFalsity

def redefinitionFalsity : ProofSyntaxModulo [truthDefinition, falsityDefinition] [] falsity :=
  .convert redefinitionArticle truthProof

/-- With `c` false, `c = ∀p. p` holds. -/
theorem falsityDefinition_holds :
    Soundness.EquationsHold (modelWith False) [falsityDefinition] := by
  intro equation listed ρ
  rw [List.mem_singleton] at listed
  subst listed
  exact congrArg ULift.up (propext ⟨False.elim, fun holds => holds (ULift.up False) trivial⟩)

/-- **Conservativity fails** when `c` occurs in the listed equations: the second
definition proves `∀p. p`, which has no proof from the first alone. -/
theorem redefinition_not_conservative :
    ¬ ∀ φ : ClosedFormula Sig, NoConstOccurrence Sig.c φ →
      Nonempty (ProofSyntaxModulo [truthDefinition, falsityDefinition] [] φ) →
        Nonempty (ProofSyntaxModulo [falsityDefinition] [] φ) :=
  fun conservative => falsity_fails False falsityDefinition_holds
    (conservative falsity falsity_avoids ⟨redefinitionFalsity⟩)

/-! ### A violation without a counterexample: `c := c → c` -/

def loopEquation : DefiningEquation Sig := .ofDefinition .c (.imp (.const .c) (.const .c))

/-- `c := c → c` mentions `c`, yet it holds with `c` true, so it proves no `∀p. p`. -/
theorem loop_consistent :
    ¬ NoConstOccurrence Sig.c (.imp (.const .c) (.const .c) : ClosedTerm Sig .prop) ∧
      ¬ Nonempty (ProofSyntaxModulo [loopEquation] [] falsity) := by
  refine ⟨fun avoids => ?_, falsity_fails True ?_⟩
  · cases avoids with
    | imp hc _ =>
        cases hc with
        | const_diff_type hne => exact hne rfl
        | const_same_ne _ hne => exact hne rfl
  · intro equation listed ρ
    rw [List.mem_singleton] at listed
    subst listed
    exact congrArg ULift.up (propext ⟨fun _ _ => trivial, fun _ => trivial⟩)

end DefinitionControls

#print axioms SourceStep.substConst
#print axioms CoreConversion.substConst
#print axioms ProofSyntaxModulo.convertHyps
#print axioms Unfolds.conversion
#print axioms ProofSyntaxModulo.definition_conservative
#print axioms ProofSyntaxModulo.definition_unfold_iff
#print axioms CoreConversion.definition_conservative
#print axioms unfold_unfolds
#print axioms DefinitionControls.curry_not_conservative
#print axioms DefinitionControls.loose_not_conservative
#print axioms DefinitionControls.redefinition_not_conservative
#print axioms ProofSyntaxModulo.inert_definition
#print axioms DefinitionControls.loop_consistent

end Mettapedia.Logic.HOL
