import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericEvent
import Mettapedia.OSLF.Syntax.CategoricalBindingStageMaps

/-!
# The generic substitution of an event

The substitution context of an arity `Γ ⊢ s` and a target context `Δ` has two
metavariables of arity `Γ ⊢ s`, the endpoints of an event, and one metavariable
of arity `Δ ⊢ γ` for each variable of `Γ`, an environment. Its generic judgment
and generic environment are read back as any judgment and environment, both
through arrows of equation contexts and through generalized elements of a
binding model. The generic substitution tree uses the one event variable
through the generic environment.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingModel (envArities envSub tailArrow)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution (substJudgment)

universe u

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-! ## The generic substitution -/

/-- The endpoints of an event of arity `Γ ⊢ s`, then an environment from `Γ`
to `Δ`. -/
abbrev substitutionContext (Γ Δ : Ctx S) (s : S.Srt) : Object S :=
  ⟨(Γ, s) :: (Γ, s) :: envArities Γ Δ⟩

abbrev substitutionBase (Γ Δ : Ctx S) (s : S.Srt) : Base equations :=
  ⟨substitutionContext Γ Δ s⟩

/-- The generic judgment of the substitution context. -/
def substitutionJudgment (Γ Δ : Ctx S) (s : S.Srt) :
    Judgment (modelAt equations (substitutionBase equations Γ Δ s)) :=
  ⟨Γ, s, termClass equations (metaVar (M := (substitutionContext Γ Δ s).arities) ⟨0, by simp⟩),
    termClass equations (metaVar (M := (substitutionContext Γ Δ s).arities) ⟨1, by simp⟩)⟩

/-- The generic environment of the substitution context. -/
def substitutionEnv (Γ Δ : Ctx S) (s : S.Srt) :
    BindingSubstitutionAlgebra.Environment S
      (modelAt equations (substitutionBase equations Γ Δ s)).substitution.Carrier Γ Δ :=
  fun γ v => termClass equations
    (instInto (tailArrow (Γ, s) ⟨(Γ, s) :: envArities Γ Δ⟩)
      (instInto (tailArrow (Γ, s) ⟨envArities Γ Δ⟩) (envSub Δ Γ γ v)))

/-- The generic substitution object: one event variable at the generic
judgment. -/
abbrev substitutionObject (Γ Δ : Ctx S) (s : S.Srt) : Classifier R equations :=
  object R equations (substitutionBase equations Γ Δ s)
    ((Context.empty R _).cons R _ (substitutionJudgment equations Γ Δ s))

/-- The event variable used through the generic environment. -/
def substitutionTree (Γ Δ : Ctx S) (s : S.Srt) :
    Tree R _ (seeds R _ (events R equations (substitutionObject R equations Γ Δ s)))
      (substJudgment (substitutionJudgment equations Γ Δ s) (substitutionEnv equations Γ Δ s)) :=
  Mettapedia.TypeTheory.IndexedPolynomial.Free.pure (rules R _)
    (IntrinsicScopedConditionalActedFree.mapHole _ _ (substitutionJudgment equations Γ Δ s)
      (exactHole R _ _ ⟨first R (substitutionJudgment equations Γ Δ s) (Context.empty R _), ⟨rfl⟩⟩)
      (substitutionEnv equations Γ Δ s))

/-- **The generic substitution of an event**, as an arrow into the generic
event object of the target context. -/
def substitutionRep (Γ Δ : Ctx S) (s : S.Srt) :
    substitutionObject R equations Γ Δ s ⟶ eventObject R equations Δ s :=
  rep R equations _ (substitutionTree R equations Γ Δ s)

/-! ## Reading the generic data through arrows -/

/-- The classes of an environment, at the metavariables of its arities. -/
def envClasses {X : Object S} (Δ : Ctx S) : ∀ {Γ : Ctx S},
    (∀ γ, Var Γ γ → EquationTermClass (authoredEquationPresentation S equations) X Δ γ) →
    ∀ i : Fin (envArities Γ Δ).length,
      EquationTermClass (authoredEquationPresentation S equations) X
        ((envArities Γ Δ).get i).1 ((envArities Γ Δ).get i).2
  | [], _ => fun i => i.elim0
  | γ :: _, σ => fun i => Fin.cases (motive := fun i =>
      EquationTermClass (authoredEquationPresentation S equations) X
        ((envArities (γ :: _) Δ).get i).1 ((envArities (γ :: _) Δ).get i).2)
      (σ γ .zero) (envClasses Δ fun γ v => σ γ (.succ v)) i

/-- A weakened term read through a pairing is the term read through the
rest. -/
theorem ofClasses_cons_tail {X : Object S} (a : MetaArity S) (L : List (MetaArity S))
    (classes : ∀ i : Fin (a :: L).length,
      EquationTermClass (authoredEquationPresentation S equations) X
        ((a :: L).get i).1 ((a :: L).get i).2)
    {Γ : Ctx S} {s : S.Srt} (t : Term (withMetas S L) Γ s) :
    (modelMap equations (X := ⟨X⟩) (Y := ⟨⟨a :: L⟩⟩)
        (ofClasses equations (a :: L) classes)).raw.map
        (termClass equations (instInto (tailArrow a ⟨L⟩) t)) =
      (modelMap equations (X := ⟨X⟩) (Y := ⟨⟨L⟩⟩)
        (ofClasses equations L fun i => classes i.succ)).raw.map (termClass equations t) := by
  have composite := consClass_comp_tail equations (classes ⟨0, Nat.succ_pos _⟩)
    (ofClasses equations L fun i => classes i.succ)
  have reading := congrArg (fun h => h.raw.map (termClass equations t))
    ((modelMap_comp equations (ofClasses equations (a :: L) classes)
      ((authoredEquationPresentation S equations).quotientFunctor.map (tailArrow a ⟨L⟩))).symm.trans
      (congrArg (modelMap equations) composite))
  exact reading

/-- The generic environment's metavariables read through the classes of an
environment. -/
theorem envClasses_envSub {X : Object S} (Δ : Ctx S) : ∀ {Γ : Ctx S}
    (σ : ∀ γ, Var Γ γ → EquationTermClass (authoredEquationPresentation S equations) X Δ γ)
    {γ : S.Srt} (v : Var Γ γ),
    (modelMap equations (X := ⟨X⟩) (Y := ⟨⟨envArities Γ Δ⟩⟩)
        (ofClasses equations (envArities Γ Δ) (envClasses equations Δ σ))).raw.map
        (termClass equations (envSub Δ Γ γ v)) = σ γ v
  | _ :: _, σ, _, .zero => ofClasses_metaVar equations _ (envClasses equations Δ σ) _
  | _ :: _, σ, _, .succ v =>
      (ofClasses_cons_tail equations _ _ _ _).trans
        (envClasses_envSub Δ (fun γ w => σ γ (.succ w)) v)

/-- The classes of a judgment and an environment at the substitution
context. -/
def substitutionClasses {X : Base equations} (J : Judgment (modelAt equations X)) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (modelAt equations X).substitution.Carrier J.1 Δ) :
    ∀ i : Fin (substitutionContext J.1 Δ J.2.1).arities.length,
      EquationTermClass (authoredEquationPresentation S equations) X.as
        ((substitutionContext J.1 Δ J.2.1).arities.get i).1
        ((substitutionContext J.1 Δ J.2.1).arities.get i).2 :=
  fun i => Fin.cases (motive := fun i =>
      EquationTermClass (authoredEquationPresentation S equations) X.as
        ((substitutionContext J.1 Δ J.2.1).arities.get i).1
        ((substitutionContext J.1 Δ J.2.1).arities.get i).2) J.2.2.1
    (fun i => Fin.cases (motive := fun i =>
      EquationTermClass (authoredEquationPresentation S equations) X.as
        (((J.1, J.2.1) :: envArities J.1 Δ).get i).1 (((J.1, J.2.1) :: envArities J.1 Δ).get i).2)
      J.2.2.2 (envClasses equations Δ σ) i) i

/-- The map of equation contexts sending the generic judgment and environment
to a given judgment and environment. -/
def substitutionBaseOf {X : Base equations} (J : Judgment (modelAt equations X)) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (modelAt equations X).substitution.Carrier J.1 Δ) :
    X ⟶ substitutionBase equations J.1 Δ J.2.1 :=
  ofClasses equations _ (substitutionClasses equations J σ)

theorem mapJudgment_substitutionBaseOf {X : Base equations} (J : Judgment (modelAt equations X))
    {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (modelAt equations X).substitution.Carrier J.1 Δ) :
    mapJudgment (modelMap equations (substitutionBaseOf equations J σ))
      (substitutionJudgment equations J.1 Δ J.2.1) = J := by
  obtain ⟨Γ, s, first, second⟩ := J
  have atFirst := ofClasses_metaVar equations (substitutionContext Γ Δ s).arities
    (substitutionClasses equations ⟨Γ, s, first, second⟩ σ) ⟨0, by simp⟩
  have atSecond := ofClasses_metaVar equations (substitutionContext Γ Δ s).arities
    (substitutionClasses equations ⟨Γ, s, first, second⟩ σ) ⟨1, by simp⟩
  exact congrArg₂ (fun one two => (⟨Γ, s, one, two⟩ : Judgment (modelAt equations X)))
    atFirst atSecond

theorem substitutionBaseOf_env {X : Base equations} (J : Judgment (modelAt equations X))
    {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (modelAt equations X).substitution.Carrier J.1 Δ)
    {γ : S.Srt} (v : Var J.1 γ) :
    (modelMap equations (substitutionBaseOf equations J σ)).raw.map
      (substitutionEnv equations J.1 Δ J.2.1 γ v) = σ γ v :=
  (ofClasses_cons_tail equations _ _ _ _).trans
    ((ofClasses_cons_tail equations _ _ _ _).trans (envClasses_envSub equations Δ σ v))

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

/-! ## Reading the generic data at generalized elements -/

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel.Model

open _root_.CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v

variable {S : Signature} {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (M : Model S D)

local notation "Base" => Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier.Base

/-- The point of the endpoints of an event and an environment. -/
def substitutionPoint {Z : D} {Γ Δ : Ctx S} {s : S.Srt} (first second : M.ElemOver Z Γ s)
    (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    Z ⟶ M.family (substitutionContext Γ Δ s).arities :=
  lift (M.elemEquiv first) (lift (M.elemEquiv second) (M.envPoint Δ σ))

/-- The point of an event and an environment goes to the point of their
images. -/
theorem _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.PointMap.substitutionPoint
    {M N : Model S D} {Z Z' : D} (m : PointMap M N Z Z') {Γ Δ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    m.family _ (M.substitutionPoint first second σ) =
      N.substitutionPoint (m.elem first) (m.elem second) (fun γ v => m.elem (σ γ v)) :=
  (m.family_cons _ _ _ _).trans (congrArg (lift _)
    ((m.family_cons _ _ _ _).trans (congrArg (lift _) (m.envPoint Δ σ))))

theorem comp_substitutionPoint {Z Z' : D} (k : Z' ⟶ Z) {Γ Δ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    k ≫ M.substitutionPoint first second σ =
      M.substitutionPoint (M.restageElem k first) (M.restageElem k second)
        (fun γ v => M.restageElem k (σ γ v)) :=
  (M.restagePoints k).substitutionPoint first second σ

variable {M' : List (MetaArity S)} (equations : List (EqAxiom S M'))
variable (sat : M.Satisfies (authoredEquationPresentation S equations))

/-- **The generic judgment read at the point of two endpoints is their
judgment.** -/
theorem mapJudgment_substitutionPoint {Z : D} {Γ Δ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) :
    mapJudgment (M.pointProgram _ sat (substitutionContext Γ Δ s)
        (M.substitutionPoint first second σ))
      (substitutionJudgment equations Γ Δ s) = ⟨Γ, s, first, second⟩ := by
  have atFirst := (M.restageElem_interp_metaVar (substitutionContext Γ Δ s).arities
    (M.substitutionPoint first second σ) ⟨0, by simp⟩).trans
      ((congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv first))
  have atSecond := (M.restageElem_interp_metaVar (substitutionContext Γ Δ s).arities
    (M.substitutionPoint first second σ) ⟨1, by simp⟩).trans
      ((congrArg M.elemOfPoint ((lift_snd_assoc _ _ _).trans (lift_fst _ _))).trans
        (M.elemEquiv.left_inv second))
  exact congrArg₂ (fun one two => (⟨Γ, s, one, two⟩ : Judgment (M.stage Z))) atFirst atSecond

/-- **The generic environment read at the point of an environment is that
environment.** -/
theorem substitutionPoint_env {Z : D} {Γ Δ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ)
    {γ : S.Srt} (v : Var Γ γ) :
    (M.pointProgram _ sat (substitutionContext Γ Δ s) (M.substitutionPoint first second σ)).raw.map
      (substitutionEnv equations Γ Δ s γ v) = σ γ v := by
  refine (M.restageElem_interp_tail (Γ, s) ⟨(Γ, s) :: envArities Γ Δ⟩ _ _).trans ?_
  refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
  refine (M.restageElem_interp_tail (Γ, s) ⟨envArities Γ Δ⟩ _ _).trans ?_
  refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
  exact M.restageElem_envSub Δ σ v

/-- **A point followed by the program classifier on a pairing of classes is
the pairing of the classes read at the point.** -/
theorem comp_consClass {Z : D} {X Y : Object S} {a : MetaArity S}
    (x : Z ⟶ M.family X.arities)
    (body : EquationTermClass (authoredEquationPresentation S equations) X a.1 a.2)
    (rest : (⟨X⟩ : EquationContexts (authoredEquationPresentation S equations)) ⟶ ⟨Y⟩) :
    x ≫ (M.equationClassifyingFunctor _ sat).map (consClass equations body rest) =
      lift (M.elemEquiv ((M.pointProgram _ sat X x).raw.map body))
        (x ≫ (M.equationClassifyingFunctor _ sat).map rest) := by
  induction body using Quot.ind with
  | _ t =>
      induction rest using Quot.ind with
      | _ raw =>
          refine (comp_lift _ _ _).trans ?_
          exact congrArg₂ lift (M.elemEquiv_restage x (M.interp X.arities t)).symm rfl

/-- The point of an environment of classes read at a point. -/
theorem comp_ofClasses_envClasses {Z : D} {X : Object S} (Δ : Ctx S) (x : Z ⟶ M.family X.arities) :
    ∀ {Γ : Ctx S}
      (σ : ∀ γ, Var Γ γ → EquationTermClass (authoredEquationPresentation S equations) X Δ γ),
      x ≫ (M.equationClassifyingFunctor _ sat).map
          (ofClasses equations (envArities Γ Δ) (envClasses equations Δ σ)) =
        M.envPoint Δ (fun γ v => (M.pointProgram _ sat X x).raw.map (σ γ v))
  | [], _ => toUnit_unique _ _
  | _ :: _, σ =>
      (M.comp_consClass equations sat x _ _).trans
        (congrArg (lift _) (comp_ofClasses_envClasses Δ x fun γ v => σ γ (.succ v)))

/-- **The point of a judgment and an environment of classes, read at a
point.** -/
theorem comp_substitutionBaseOf {Z : D} {X : Base equations} (x : Z ⟶ M.family X.as.arities)
    (J : Judgment (modelAt equations X)) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S (modelAt equations X).substitution.Carrier J.1 Δ) :
    x ≫ (M.equationClassifyingFunctor _ sat).map (substitutionBaseOf equations J σ) =
      M.substitutionPoint ((M.pointProgram _ sat X.as x).raw.map J.2.2.1)
        ((M.pointProgram _ sat X.as x).raw.map J.2.2.2)
        (fun γ v => (M.pointProgram _ sat X.as x).raw.map (σ γ v)) :=
  (M.comp_consClass equations sat x _ _).trans
    (congrArg (lift _) ((M.comp_consClass equations sat x _ _).trans
      (congrArg (lift _) (M.comp_ofClasses_envClasses equations sat Δ x σ))))

end Mettapedia.OSLF.Binding.CategoricalBindingModel.Model

end
