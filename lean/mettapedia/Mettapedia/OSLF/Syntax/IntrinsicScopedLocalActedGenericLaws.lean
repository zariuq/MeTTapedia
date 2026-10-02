import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericRule

/-!
# Generic inputs of the laws of a model

Two further contexts carry every input of a law of a model as a metavariable.
The double substitution context has the endpoints of an event of arity
`Γ ⊢ s` and environments from `Γ` to `Δ` and from `Δ` to `Θ`. The rule
substitution context has the metavariables of an occurrence of a rule in an
ambient context `Γ` and an environment from `Γ` to `Δ`. At a generalized
element, their generic data read back as the given inputs.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingModel (envArities envSub argArities tailArrow)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment)

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-! ## Environments in front of further metavariables -/

/-- Each variable of `Γ` goes to its metavariable in front of further
metavariables, applied to the variables of `Δ`. -/
def envSubIn (Δ : Ctx S) (rest : List (MetaArity S)) :
    ∀ Γ : Ctx S, Sub (withMetas S (envArities Γ Δ ++ rest)) Γ Δ
  | [], _, v => nomatch v
  | γ :: _, _, .zero => metaVar (M := envArities (γ :: _) Δ ++ rest) ⟨0, Nat.succ_pos _⟩
  | γ :: Γ, _, .succ v => instInto (tailArrow (Δ, γ) ⟨envArities Γ Δ ++ rest⟩) (envSubIn Δ rest Γ _ v)

/-- A term over further metavariables, past the metavariables of an
environment. -/
def weakenPastEnv (Γ : Ctx S) (rest : List (MetaArity S)) :
    ∀ (C : Ctx S) {Θ : Ctx S} {s : S.Srt},
      Term (withMetas S rest) Θ s → Term (withMetas S (envArities C Γ ++ rest)) Θ s
  | [], _, _, t => t
  | γ :: C, _, _, t =>
      instInto (tailArrow (Γ, γ) ⟨envArities C Γ ++ rest⟩) (weakenPastEnv Γ rest C t)

/-! ## Double substitution -/

/-- The endpoints of an event of arity `Γ ⊢ s`, an environment from `Γ` to
`Δ`, and one from `Δ` to `Θ`. -/
abbrev doubleSubstitutionContext (Γ Δ Θ : Ctx S) (s : S.Srt) : Object S :=
  ⟨(Γ, s) :: (Γ, s) :: (envArities Γ Δ ++ envArities Δ Θ)⟩

abbrev doubleSubstitutionBase (Γ Δ Θ : Ctx S) (s : S.Srt) : Base equations :=
  ⟨doubleSubstitutionContext Γ Δ Θ s⟩

def doubleSubstitutionJudgment (Γ Δ Θ : Ctx S) (s : S.Srt) :
    Judgment (modelAt equations (doubleSubstitutionBase equations Γ Δ Θ s)) :=
  ⟨Γ, s,
    termClass equations (metaVar (M := (doubleSubstitutionContext Γ Δ Θ s).arities) ⟨0, by simp⟩),
    termClass equations (metaVar (M := (doubleSubstitutionContext Γ Δ Θ s).arities) ⟨1, by simp⟩)⟩

/-- The first generic environment. -/
def doubleSubstitutionFirst (Γ Δ Θ : Ctx S) (s : S.Srt) :
    BindingSubstitutionAlgebra.Environment S
      (modelAt equations (doubleSubstitutionBase equations Γ Δ Θ s)).substitution.Carrier Γ Δ :=
  fun γ v => termClass equations
    (instInto (tailArrow (Γ, s) ⟨(Γ, s) :: (envArities Γ Δ ++ envArities Δ Θ)⟩)
      (instInto (tailArrow (Γ, s) ⟨envArities Γ Δ ++ envArities Δ Θ⟩)
        (envSubIn Δ (envArities Δ Θ) Γ γ v)))

/-- The second generic environment. -/
def doubleSubstitutionSecond (Γ Δ Θ : Ctx S) (s : S.Srt) :
    BindingSubstitutionAlgebra.Environment S
      (modelAt equations (doubleSubstitutionBase equations Γ Δ Θ s)).substitution.Carrier Δ Θ :=
  fun γ v => termClass equations
    (instInto (tailArrow (Γ, s) ⟨(Γ, s) :: (envArities Γ Δ ++ envArities Δ Θ)⟩)
      (instInto (tailArrow (Γ, s) ⟨envArities Γ Δ ++ envArities Δ Θ⟩)
        (weakenPastEnv Δ (envArities Δ Θ) Γ (envSub Θ Δ γ v))))

/-- The generic double substitution object: one event variable at the
generic judgment. -/
abbrev doubleSubstitutionObject (Γ Δ Θ : Ctx S) (s : S.Srt) : Classifier R equations :=
  object R equations (doubleSubstitutionBase equations Γ Δ Θ s)
    ((Context.empty R _).cons R _ (doubleSubstitutionJudgment equations Γ Δ Θ s))

/-! ## Rule substitution -/

/-- The metavariables of an occurrence of a rule in an ambient context, then
an environment from the ambient context. -/
abbrev ruleSubstitutionContext (index : Fin R.length) (Γ Δ : Ctx S) : Object S :=
  ⟨argArities Γ (R.get index).1 ++ (envArities (conclusionContext R index) Γ ++ envArities Γ Δ)⟩

abbrev ruleSubstitutionBase (index : Fin R.length) (Γ Δ : Ctx S) : Base equations :=
  ⟨ruleSubstitutionContext R index Γ Δ⟩

/-- The generic occurrence of the rule substitution context. -/
def ruleSubstitutionInstance (index : Fin R.length) (Γ Δ : Ctx S) :
    Instance R (modelAt equations (ruleSubstitutionBase R equations index Γ Δ)) where
  index := index
  ambient := Γ
  valuation i := termClass equations
    (valuationTerms Γ (envArities (conclusionContext R index) Γ ++ envArities Γ Δ) (R.get index).1 i)
  close γ v := termClass equations
    (weakenPast Γ (envArities (conclusionContext R index) Γ ++ envArities Γ Δ) (R.get index).1
      (envSubIn Γ (envArities Γ Δ) (conclusionContext R index) γ v))

/-- The generic environment of the rule substitution context. -/
def ruleSubstitutionEnv (index : Fin R.length) (Γ Δ : Ctx S) :
    BindingSubstitutionAlgebra.Environment S
      (modelAt equations (ruleSubstitutionBase R equations index Γ Δ)).substitution.Carrier Γ Δ :=
  fun γ v => termClass equations
    (weakenPast Γ (envArities (conclusionContext R index) Γ ++ envArities Γ Δ) (R.get index).1
      (weakenPastEnv Γ (envArities Γ Δ) (conclusionContext R index) (envSub Δ Γ γ v)))

/-- The generic rule substitution object: the premises of the generic
occurrence. -/
abbrev ruleSubstitutionObject (index : Fin R.length) (Γ Δ : Ctx S) : Classifier R equations :=
  object R equations (ruleSubstitutionBase R equations index Γ Δ)
    ⟨⟨(R.get index).2.premises.length,
      childJudgment R _ (ruleSubstitutionInstance R equations index Γ Δ)⟩⟩

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

/-! ## Reading the generic data at generalized elements -/

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel.Model

open _root_.CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v

variable {S : Signature} {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (M : Model S D)

/-- The point of an environment in front of a further point. -/
def envPointThen {Z : D} (Δ : Ctx S) {rest : List (MetaArity S)} (restPoint : Z ⟶ M.family rest) :
    ∀ {Γ : Ctx S}, (∀ γ, Var Γ γ → M.ElemOver Z Δ γ) → (Z ⟶ M.family (envArities Γ Δ ++ rest))
  | [], _ => restPoint
  | _ :: _, env => lift (M.elemEquiv (env _ .zero)) (envPointThen Δ restPoint fun γ v => env γ (.succ v))

theorem restageElem_envSubIn {Z : D} (Δ : Ctx S) {rest : List (MetaArity S)}
    (restPoint : Z ⟶ M.family rest) : ∀ {Γ : Ctx S}
    (env : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) {γ : S.Srt} (v : Var Γ γ),
    M.restageElem (M.envPointThen Δ restPoint env)
      (M.interp (envArities Γ Δ ++ rest) (envSubIn Δ rest Γ γ v)) = env γ v
  | _ :: _, env, _, .zero =>
      (M.restageElem_interp_metaVar _ _ _).trans
        ((congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv _))
  | γ :: Γ, env, _, .succ v => by
      refine (M.restageElem_interp_tail (Δ, γ) ⟨envArities Γ Δ ++ rest⟩ _ _).trans ?_
      refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
      exact restageElem_envSubIn Δ restPoint (fun γ w => env γ (.succ w)) v

theorem restageElem_weakenPastEnv {Z : D} (Γ : Ctx S) {rest : List (MetaArity S)}
    (restPoint : Z ⟶ M.family rest) : ∀ (C : Ctx S)
    (env : ∀ γ, Var C γ → M.ElemOver Z Γ γ) {Θ : Ctx S} {s : S.Srt} (t : Term (withMetas S rest) Θ s),
    M.restageElem (M.envPointThen Γ restPoint env)
      (M.interp (envArities C Γ ++ rest) (weakenPastEnv Γ rest C t)) =
        M.restageElem restPoint (M.interp rest t)
  | [], _, _, _, _ => rfl
  | γ :: C, env, _, _, t => by
      refine (M.restageElem_interp_tail (Γ, γ) ⟨envArities C Γ ++ rest⟩ _ _).trans ?_
      refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
      exact restageElem_weakenPastEnv Γ restPoint C (fun γ w => env γ (.succ w)) t

/-- The point of the endpoints of an event and two environments. -/
def doubleSubstitutionPoint {Z : D} {Γ Δ Θ : Ctx S} {s : S.Srt} (first second : M.ElemOver Z Γ s)
    (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ) (τ : ∀ γ, Var Δ γ → M.ElemOver Z Θ γ) :
    Z ⟶ M.family (doubleSubstitutionContext Γ Δ Θ s).arities :=
  lift (M.elemEquiv first) (lift (M.elemEquiv second) (M.envPointThen Δ (M.envPoint Θ τ) σ))

variable {M' : List (MetaArity S)} (equations : List (EqAxiom S M'))
variable (sat : M.Satisfies (authoredEquationPresentation S equations))

theorem mapJudgment_doubleSubstitutionPoint {Z : D} {Γ Δ Θ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ)
    (τ : ∀ γ, Var Δ γ → M.ElemOver Z Θ γ) :
    mapJudgment (M.pointProgram _ sat (doubleSubstitutionContext Γ Δ Θ s)
        (M.doubleSubstitutionPoint first second σ τ))
      (doubleSubstitutionJudgment equations Γ Δ Θ s) = ⟨Γ, s, first, second⟩ := by
  have atFirst := (M.restageElem_interp_metaVar (doubleSubstitutionContext Γ Δ Θ s).arities
    (M.doubleSubstitutionPoint first second σ τ) ⟨0, by simp⟩).trans
      ((congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv first))
  have atSecond := (M.restageElem_interp_metaVar (doubleSubstitutionContext Γ Δ Θ s).arities
    (M.doubleSubstitutionPoint first second σ τ) ⟨1, by simp⟩).trans
      ((congrArg M.elemOfPoint ((lift_snd_assoc _ _ _).trans (lift_fst _ _))).trans
        (M.elemEquiv.left_inv second))
  exact congrArg₂ (fun one two => (⟨Γ, s, one, two⟩ : Judgment (M.stage Z))) atFirst atSecond

theorem doubleSubstitutionPoint_first {Z : D} {Γ Δ Θ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ)
    (τ : ∀ γ, Var Δ γ → M.ElemOver Z Θ γ) {γ : S.Srt} (v : Var Γ γ) :
    (M.pointProgram _ sat (doubleSubstitutionContext Γ Δ Θ s)
        (M.doubleSubstitutionPoint first second σ τ)).raw.map
      (doubleSubstitutionFirst equations Γ Δ Θ s γ v) = σ γ v := by
  refine (M.restageElem_interp_tail (Γ, s) ⟨(Γ, s) :: (envArities Γ Δ ++ envArities Δ Θ)⟩ _ _).trans ?_
  refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
  refine (M.restageElem_interp_tail (Γ, s) ⟨envArities Γ Δ ++ envArities Δ Θ⟩ _ _).trans ?_
  refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
  exact M.restageElem_envSubIn Δ (M.envPoint Θ τ) σ v

theorem doubleSubstitutionPoint_second {Z : D} {Γ Δ Θ : Ctx S} {s : S.Srt}
    (first second : M.ElemOver Z Γ s) (σ : ∀ γ, Var Γ γ → M.ElemOver Z Δ γ)
    (τ : ∀ γ, Var Δ γ → M.ElemOver Z Θ γ) {γ : S.Srt} (v : Var Δ γ) :
    (M.pointProgram _ sat (doubleSubstitutionContext Γ Δ Θ s)
        (M.doubleSubstitutionPoint first second σ τ)).raw.map
      (doubleSubstitutionSecond equations Γ Δ Θ s γ v) = τ γ v := by
  refine (M.restageElem_interp_tail (Γ, s) ⟨(Γ, s) :: (envArities Γ Δ ++ envArities Δ Θ)⟩ _ _).trans ?_
  refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
  refine (M.restageElem_interp_tail (Γ, s) ⟨envArities Γ Δ ++ envArities Δ Θ⟩ _ _).trans ?_
  refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
  refine (M.restageElem_weakenPastEnv Δ (M.envPoint Θ τ) Γ σ _).trans ?_
  exact M.restageElem_envSub Θ τ v

variable (R : List (LocalRule S))

/-- The point of an occurrence of a rule and an environment. -/
def ruleSubstitutionPoint {Z : D} (occurrence : Instance R (M.stage Z)) {Δ : Ctx S}
    (σ : ∀ γ, Var occurrence.ambient γ → M.ElemOver Z Δ γ) :
    Z ⟶ M.family (ruleSubstitutionContext R occurrence.index occurrence.ambient Δ).arities :=
  M.valuationPoint occurrence.ambient (R.get occurrence.index).1 occurrence.valuation
    (M.envPointThen occurrence.ambient (M.envPoint Δ σ) occurrence.close)

theorem mapInstance_ruleSubstitutionPoint {Z : D} (occurrence : Instance R (M.stage Z)) {Δ : Ctx S}
    (σ : ∀ γ, Var occurrence.ambient γ → M.ElemOver Z Δ γ) :
    mapInstance R (M.pointProgram _ sat (ruleSubstitutionContext R occurrence.index occurrence.ambient Δ)
        (M.ruleSubstitutionPoint R occurrence σ))
      (ruleSubstitutionInstance R equations occurrence.index occurrence.ambient Δ) = occurrence := by
  obtain ⟨index, Γ, values, close⟩ := occurrence
  have valuationEq : SemanticContextualMetavariables.mapValuation
      (M.pointProgram _ sat (ruleSubstitutionContext R index Γ Δ)
        (M.ruleSubstitutionPoint R ⟨index, Γ, values, close⟩ σ))
      (ruleSubstitutionInstance R equations index Γ Δ).valuation = values := by
    funext i
    exact M.valuationPoint_valuationTerms Γ (R.get index).1 values _ i
  have closeEq : (fun γ v => (M.pointProgram _ sat (ruleSubstitutionContext R index Γ Δ)
      (M.ruleSubstitutionPoint R ⟨index, Γ, values, close⟩ σ)).raw.map
      ((ruleSubstitutionInstance R equations index Γ Δ).close γ v)) = close := by
    funext γ v
    exact (M.valuationPoint_weakenPast Γ (R.get index).1 values _ _).trans
      (M.restageElem_envSubIn Γ (M.envPoint Δ σ) close v)
  change (⟨index, Γ, _, _⟩ : Instance R _) = ⟨index, Γ, values, close⟩
  rw [valuationEq, closeEq]

theorem ruleSubstitutionPoint_env {Z : D} (occurrence : Instance R (M.stage Z)) {Δ : Ctx S}
    (σ : ∀ γ, Var occurrence.ambient γ → M.ElemOver Z Δ γ) {γ : S.Srt} (v : Var occurrence.ambient γ) :
    (M.pointProgram _ sat (ruleSubstitutionContext R occurrence.index occurrence.ambient Δ)
        (M.ruleSubstitutionPoint R occurrence σ)).raw.map
      (ruleSubstitutionEnv R equations occurrence.index occurrence.ambient Δ γ v) = σ γ v := by
  refine (M.valuationPoint_weakenPast occurrence.ambient (R.get occurrence.index).1
    occurrence.valuation _ _).trans ?_
  refine (M.restageElem_weakenPastEnv occurrence.ambient (M.envPoint Δ σ)
    (conclusionContext R occurrence.index) occurrence.close _).trans ?_
  exact M.restageElem_envSub Δ σ v

end Mettapedia.OSLF.Binding.CategoricalBindingModel.Model

end
