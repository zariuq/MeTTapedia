import Mettapedia.AutoBooks.Codex.IntuitionisticHOL.Soundness

namespace Mettapedia.AutoBooks.Codex.IntuitionisticHOL

/-!
# Lower-Bound Extension Regression

Positive and negative canaries around the extra environment-extension law used by
semilocal soundness for the quantifier rules.
-/

namespace LowerBoundExtensionRegression

open Mettapedia.Logic.HOL

inductive BaseSort where
  | atom
  deriving DecidableEq, Repr

abbrev atomTy : Ty BaseSort := .base .atom

inductive Atom where
  | good
  | bad
  | worse
  deriving DecidableEq, Repr

inductive Const : Ty BaseSort → Type where
  | good : Const atomTy
  | collapse : Const (atomTy ⇒ atomTy)

open Atom
open Const

/-- Native carrier family for a tiny higher-order countermodel. -/
def Carrier : Ty BaseSort → Type
  | .prop => Prop
  | .base _ => Atom
  | .arr σ τ => Carrier σ → Carrier τ

/-- Function constant that preserves `good` but collapses `bad` to `worse`. -/
def collapseFn : Carrier (atomTy ⇒ atomTy)
  | .good => .good
  | .bad => .worse
  | .worse => .worse

/-- Interpret the two nonlogical constants. -/
def constInterp : {τ : Ty BaseSort} → Const τ → Carrier τ
  | _, .good => .good
  | _, .collapse => collapseFn

/-- Values with acceptable extent at the current lower bound. -/
def extent : {τ : Ty BaseSort} → Carrier τ → Prop
  | .prop, _ => True
  | .base _, x => x ≠ .worse
  | .arr _ _, _ => True

/-- Logical relation of "good" values preserved by closed terms and `collapse`. -/
def Good : {τ : Ty BaseSort} → Carrier τ → Prop
  | .prop, _ => True
  | .base _, x => x = .good
  | .arr _ _, f => ∀ x, Good x → Good (f x)

/-- The tiny semilocal model validating closed-good terms but not bad extensions. -/
def model : SemilocalModel BaseSort Const where
  toApplicativeStructure :=
    { Carrier := Carrier
      const := constInterp
      app := fun f x => f x
      lam := fun f => f
      beta := by
        intro σ τ f x
        rfl
      eta := by
        intro σ τ f
        rfl }
  Omega := Prop
  frame := inferInstance
  truth := fun p => p
  extent := extent
  topP := True
  botP := False
  andP := And
  orP := Or
  impP := fun p q => p → q
  eqP := fun x y => x = y
  allP := fun f => ∀ x, extent x → f x
  exP := fun f => ∃ x, extent x ∧ f x
  truth_top := rfl
  truth_bot := rfl
  truth_and := by
    intro p q
    rfl
  truth_or := by
    intro p q
    rfl
  truth_imp := by
    intro p q
    rfl
  truth_all := by
    intro σ f
    apply propext
    simp [extent]
  truth_ex := by
    intro σ f
    apply propext
    simp [extent]

abbrev Env (Γ : Ctx BaseSort) := SemilocalModel.Env model Γ

/-- Pointwise goodness for environments. -/
def GoodEnv (ρ : Env Γ) : Prop :=
  ∀ {τ : Ty BaseSort} (v : Var Γ τ), Good (ρ v)

theorem good_const : {τ : Ty BaseSort} → (c : Const τ) → Good (constInterp c)
  | _, .good => rfl
  | _, .collapse => by
      intro x hx
      rcases hx with rfl
      rfl

theorem goodEnv_extend {ρ : Env Γ} (hρ : GoodEnv ρ) {σ : Ty BaseSort}
    {x : Carrier σ} (hx : Good x) :
    GoodEnv (ApplicativeStructure.Env.extend model.toApplicativeStructure ρ x) := by
  intro τ v
  cases v with
  | vz => simpa using hx
  | vs v => simpa using hρ v

/-- Terms over good environments evaluate to good values. -/
theorem eval_good {Γ : Ctx BaseSort} (ρ : Env Γ) (hρ : GoodEnv ρ) :
    ∀ {τ : Ty BaseSort} (t : Term Const Γ τ),
      Good (SemilocalModel.eval model ρ t)
  | _, .var v => hρ v
  | _, .const c => good_const c
  | _, .app f t => (eval_good ρ hρ f) _ (eval_good ρ hρ t)
  | _, .lam t => by
      intro x hx
      exact eval_good
        (ApplicativeStructure.Env.extend model.toApplicativeStructure ρ x)
        (goodEnv_extend hρ hx)
        t
  | _, .top => trivial
  | _, .bot => trivial
  | _, .and _ _ => trivial
  | _, .or _ _ => trivial
  | _, .imp _ _ => trivial
  | _, .not _ => trivial
  | _, .eq _ _ => trivial
  | _, .all _ => trivial
  | _, .ex _ => trivial

theorem good_implies_extent {τ : Ty BaseSort} {x : Carrier τ} (hx : Good x) :
    extent x := by
  cases τ with
  | prop => trivial
  | base b =>
      rcases hx with rfl
      simp [extent]
  | arr σ τ =>
      trivial

theorem hasExtentLowerBound_top_of_goodEnv {Γ : Ctx BaseSort} {ρ : Env Γ}
    (hρ : GoodEnv ρ) :
    SemilocalModel.HasExtentLowerBound model ⊤ ρ := by
  intro τ t _
  exact good_implies_extent (eval_good ρ hρ t)

/-- Environment exposing the collapse function at lower bound `⊤`. -/
def collapseEnv : Env [atomTy ⇒ atomTy]
  | _, .vz => collapseFn
  | _, .vs v => nomatch v

theorem collapseEnv_good : GoodEnv collapseEnv := by
  intro τ v
  cases v with
  | vz =>
      change Good collapseFn
      exact good_const .collapse
  | vs v => cases v

/-- Applying the older collapse variable to the newly adjoined bad element. -/
def badCollapseTerm : Term Const [atomTy, atomTy ⇒ atomTy] atomTy :=
  .app (.var (.vs .vz)) (.var .vz)

abbrev badElem : model.Carrier atomTy := Atom.bad

/-- Extend `collapseEnv` by the bad element at the head of the context. -/
def extendedCollapseEnv : Env [atomTy, atomTy ⇒ atomTy] :=
  ApplicativeStructure.Env.extend model.toApplicativeStructure collapseEnv badElem

@[simp] theorem eval_badCollapseTerm :
    SemilocalModel.eval model
      extendedCollapseEnv
      badCollapseTerm = Atom.worse := by
  rfl

/-- The paper-facing lower-bound extension law is not forced by the bare model fields. -/
theorem not_supportsLowerBoundExtension :
    ¬ SemilocalModel.SupportsLowerBoundExtension model := by
  intro h
  have hρ : SemilocalModel.HasExtentLowerBound model ⊤ collapseEnv :=
    hasExtentLowerBound_top_of_goodEnv collapseEnv_good
  have hbad := h ⊤ collapseEnv badElem hρ badCollapseTerm
  have hbadExtent : model.extent badElem := by
    simp [badElem, model, extent]
  have hworseExtent :
      model.extent (SemilocalModel.eval model extendedCollapseEnv badCollapseTerm) :=
    hbad (by
      change extent badElem ⊓ ⊤
      exact And.intro hbadExtent trivial)
  rw [eval_badCollapseTerm] at hworseExtent
  simp [model, extent] at hworseExtent

theorem not_supportsUniformRelativization :
    ¬ SemilocalModel.SupportsUniformRelativization model := by
  intro h
  exact not_supportsLowerBoundExtension
    (SemilocalModel.supportsLowerBoundExtension_of_supportsUniformRelativization model h)

theorem not_structuralExtent :
    ¬ SemilocalModel.StructuralExtent model := by
  intro h
  exact not_supportsLowerBoundExtension
    (SemilocalModel.StructuralExtent.supportsLowerBoundExtension h)

example (M : GlobalModel BaseSort Const) :
    SemilocalModel.StructuralExtent M.toSemilocalModel :=
  GlobalModel.structuralExtent M

example (M : GlobalModel BaseSort Const) :
    SemilocalModel.SupportsLowerBoundExtension M.toSemilocalModel :=
  GlobalModel.supportsLowerBoundExtension M

example (M : GlobalModel BaseSort Const) :
    SemilocalModel.SupportsUniformRelativization M.toSemilocalModel :=
  GlobalModel.supportsUniformRelativization M

example : ¬ SemilocalModel.SupportsLowerBoundExtension model :=
  not_supportsLowerBoundExtension

example : ¬ SemilocalModel.SupportsUniformRelativization model :=
  not_supportsUniformRelativization

example : ¬ SemilocalModel.StructuralExtent model :=
  not_structuralExtent

end LowerBoundExtensionRegression

end Mettapedia.AutoBooks.Codex.IntuitionisticHOL
