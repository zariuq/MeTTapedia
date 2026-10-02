import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericSubstitution

/-!
# The generic occurrence of a rule

For an authored rule and an ambient context, the rule context has one
metavariable for each of the rule's own metavariables, depending on its
declared binders followed by the ambient variables, and one metavariable for
each variable of the rule's conclusion context, depending on the ambient
variables. Its generic occurrence is read back as any occurrence of that rule
in that ambient context, both through arrows of equation contexts and through
generalized elements of a binding model. The generic rule tree applies the
rule to its ordered premises.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

open _root_.CategoryTheory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.CategoricalBindingModel (envArities envSub argArities tailArrow)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-! ## Terms of the generic occurrence -/

/-- Each metavariable of a telescope as its own metavariable, depending on its
binders and the ambient variables, in front of further metavariables. -/
def valuationTerms (Γ : Ctx S) (rest : List (MetaArity S)) :
    ∀ (L : List (MetaArity S)) (i : Fin L.length),
      Term (withMetas S (argArities Γ L ++ rest)) ((L.get i).1 ++ Γ) (L.get i).2
  | _ :: _, ⟨0, _⟩ => metaVar (M := argArities Γ (_ :: _) ++ rest) ⟨0, Nat.succ_pos _⟩
  | a :: L, ⟨n + 1, bound⟩ =>
      instInto (tailArrow (a.1 ++ Γ, a.2) ⟨argArities Γ L ++ rest⟩)
        (valuationTerms Γ rest L ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

/-- A term over further metavariables, past the metavariables of a
telescope. -/
def weakenPast (Γ : Ctx S) (rest : List (MetaArity S)) :
    ∀ (L : List (MetaArity S)) {Θ : Ctx S} {s : S.Srt},
      Term (withMetas S rest) Θ s → Term (withMetas S (argArities Γ L ++ rest)) Θ s
  | [], _, _, t => t
  | a :: L, _, _, t =>
      instInto (tailArrow (a.1 ++ Γ, a.2) ⟨argArities Γ L ++ rest⟩) (weakenPast Γ rest L t)

/-! ## The generic occurrence -/

/-- The conclusion context of a rule. -/
abbrev conclusionContext (index : Fin R.length) : Ctx S :=
  (R.get index).2.conclusion.ctx

/-- The metavariables of an occurrence of a rule in an ambient context. -/
abbrev ruleContext (index : Fin R.length) (Γ : Ctx S) : Object S :=
  ⟨argArities Γ (R.get index).1 ++ envArities (conclusionContext R index) Γ⟩

abbrev ruleBase (index : Fin R.length) (Γ : Ctx S) : Base equations :=
  ⟨ruleContext R index Γ⟩

/-- **The generic occurrence of a rule.** -/
def ruleInstance (index : Fin R.length) (Γ : Ctx S) :
    Instance R (modelAt equations (ruleBase R equations index Γ)) where
  index := index
  ambient := Γ
  valuation i := termClass equations
    (valuationTerms Γ (envArities (conclusionContext R index) Γ) (R.get index).1 i)
  close γ v := termClass equations
    (weakenPast Γ (envArities (conclusionContext R index) Γ) (R.get index).1
      (envSub Γ (conclusionContext R index) γ v))

/-- The generic rule object: the ordered premises of the generic occurrence. -/
abbrev ruleObject (index : Fin R.length) (Γ : Ctx S) : Classifier R equations :=
  object R equations (ruleBase R equations index Γ)
    ⟨⟨(R.get index).2.premises.length,
      childJudgment R _ (ruleInstance R equations index Γ)⟩⟩

/-- The rule applied to its premises. -/
def ruleTree (index : Fin R.length) (Γ : Ctx S) :
    Tree R _ (seeds R _ (events R equations (ruleObject R equations index Γ)))
      (conclusionJudgment R _ (ruleInstance R equations index Γ)) :=
  Mettapedia.TypeTheory.IndexedPolynomial.Free.node (rules R _)
    ⟨ruleInstance R equations index Γ, rfl⟩
    fun position => leaf R (events R equations (ruleObject R equations index Γ)) position

/-- **The generic occurrence of a rule**, as an arrow into the generic event
object of its conclusion. -/
def ruleRep (index : Fin R.length) (Γ : Ctx S) :
    ruleObject R equations index Γ ⟶
      eventObject R equations Γ (R.get index).2.conclusion.sort :=
  rep R equations _ (ruleTree R equations index Γ)

/-! ## Reading the generic occurrence through arrows -/

/-- The classes of a valuation of a telescope, in front of further classes. -/
def valuationClasses {X : Object S} (Γ : Ctx S) : ∀ (L : List (MetaArity S)) {rest : List (MetaArity S)},
    ((i : Fin L.length) →
      EquationTermClass (authoredEquationPresentation S equations) X ((L.get i).1 ++ Γ) (L.get i).2) →
    (∀ i : Fin rest.length,
      EquationTermClass (authoredEquationPresentation S equations) X (rest.get i).1 (rest.get i).2) →
    ∀ i : Fin (argArities Γ L ++ rest).length,
      EquationTermClass (authoredEquationPresentation S equations) X
        ((argArities Γ L ++ rest).get i).1 ((argArities Γ L ++ rest).get i).2
  | [], _, _, restClasses => restClasses
  | a :: L, rest, values, restClasses => fun i => Fin.cases (motive := fun i =>
      EquationTermClass (authoredEquationPresentation S equations) X
        ((argArities Γ (a :: L) ++ rest).get i).1 ((argArities Γ (a :: L) ++ rest).get i).2)
      (values ⟨0, Nat.succ_pos _⟩)
      (valuationClasses Γ L (fun i => values i.succ) restClasses) i

theorem valuationClasses_valuationTerms {X : Object S} (Γ : Ctx S) : ∀ (L : List (MetaArity S))
    {rest : List (MetaArity S)}
    (values : (i : Fin L.length) →
      EquationTermClass (authoredEquationPresentation S equations) X ((L.get i).1 ++ Γ) (L.get i).2)
    (restClasses : ∀ i : Fin rest.length,
      EquationTermClass (authoredEquationPresentation S equations) X (rest.get i).1 (rest.get i).2)
    (i : Fin L.length),
    (modelMap equations (X := ⟨X⟩) (Y := ⟨⟨argArities Γ L ++ rest⟩⟩)
        (ofClasses equations _ (valuationClasses equations Γ L values restClasses))).raw.map
        (termClass equations (valuationTerms Γ rest L i)) = values i
  | _ :: _, _, values, restClasses, ⟨0, _⟩ =>
      ofClasses_metaVar equations _ (valuationClasses equations Γ _ values restClasses) _
  | _ :: L, _, values, restClasses, ⟨n + 1, bound⟩ =>
      (ofClasses_cons_tail equations _ _ _ _).trans
        (valuationClasses_valuationTerms Γ L (fun i => values i.succ) restClasses
          ⟨n, Nat.lt_of_succ_lt_succ bound⟩)

theorem valuationClasses_weakenPast {X : Object S} (Γ : Ctx S) : ∀ (L : List (MetaArity S))
    {rest : List (MetaArity S)}
    (values : (i : Fin L.length) →
      EquationTermClass (authoredEquationPresentation S equations) X ((L.get i).1 ++ Γ) (L.get i).2)
    (restClasses : ∀ i : Fin rest.length,
      EquationTermClass (authoredEquationPresentation S equations) X (rest.get i).1 (rest.get i).2)
    {Θ : Ctx S} {s : S.Srt} (t : Term (withMetas S rest) Θ s),
    (modelMap equations (X := ⟨X⟩) (Y := ⟨⟨argArities Γ L ++ rest⟩⟩)
        (ofClasses equations _ (valuationClasses equations Γ L values restClasses))).raw.map
        (termClass equations (weakenPast Γ rest L t)) =
      (modelMap equations (X := ⟨X⟩) (Y := ⟨⟨rest⟩⟩)
        (ofClasses equations rest restClasses)).raw.map (termClass equations t)
  | [], _, _, _, _, _, _ => rfl
  | _ :: L, _, values, restClasses, _, _, t =>
      (ofClasses_cons_tail equations _ _ _ _).trans
        (valuationClasses_weakenPast Γ L (fun i => values i.succ) restClasses t)

/-- The map of equation contexts sending the generic occurrence to a given
occurrence. -/
def ruleBaseOf {X : Base equations} (occurrence : Instance R (modelAt equations X)) :
    X ⟶ ruleBase R equations occurrence.index occurrence.ambient :=
  ofClasses equations _ (valuationClasses equations occurrence.ambient (R.get occurrence.index).1
    occurrence.valuation (envClasses equations occurrence.ambient occurrence.close))

/-- **The generic occurrence read through the map of an occurrence is that
occurrence.** -/
theorem mapInstance_ruleBaseOf {X : Base equations} (occurrence : Instance R (modelAt equations X)) :
    mapInstance R (modelMap equations (ruleBaseOf R equations occurrence))
      (ruleInstance R equations occurrence.index occurrence.ambient) = occurrence := by
  obtain ⟨index, Γ, values, close⟩ := occurrence
  have valuationEq : SemanticContextualMetavariables.mapValuation
      (modelMap equations (ruleBaseOf R equations ⟨index, Γ, values, close⟩))
      (ruleInstance R equations index Γ).valuation = values := by
    funext i
    exact valuationClasses_valuationTerms equations Γ (R.get index).1 values
      (envClasses equations Γ close) i
  have closeEq : (fun γ v => (modelMap equations (ruleBaseOf R equations ⟨index, Γ, values, close⟩)).raw.map
      ((ruleInstance R equations index Γ).close γ v)) = close := by
    funext γ v
    exact (valuationClasses_weakenPast equations Γ (R.get index).1 values
      (envClasses equations Γ close) _).trans (envClasses_envSub equations Γ close v)
  change (⟨index, Γ, _, _⟩ : Instance R _) = ⟨index, Γ, values, close⟩
  rw [valuationEq, closeEq]

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

/-! ## Reading the generic occurrence at generalized elements -/

namespace Mettapedia.OSLF.Binding.CategoricalBindingModel.Model

open _root_.CategoryTheory
open CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u v

variable {S : Signature} {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable (M : Model S D)

local notation "Base" => Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier.Base

/-- The point of the values of a telescope, in front of a further point. -/
def valuationPoint {Z : D} (Γ : Ctx S) : ∀ (L : List (MetaArity S)) {rest : List (MetaArity S)},
    ((i : Fin L.length) → M.ElemOver Z ((L.get i).1 ++ Γ) (L.get i).2) →
    (Z ⟶ M.family rest) → (Z ⟶ M.family (argArities Γ L ++ rest))
  | [], _, _, restPoint => restPoint
  | _ :: L, _, values, restPoint =>
      lift (M.elemEquiv (values ⟨0, Nat.succ_pos _⟩))
        (valuationPoint Γ L (fun i => values i.succ) restPoint)

theorem valuationPoint_valuationTerms {Z : D} (Γ : Ctx S) : ∀ (L : List (MetaArity S))
    {rest : List (MetaArity S)}
    (values : (i : Fin L.length) → M.ElemOver Z ((L.get i).1 ++ Γ) (L.get i).2)
    (restPoint : Z ⟶ M.family rest) (i : Fin L.length),
    M.restageElem (M.valuationPoint Γ L values restPoint)
      (M.interp (argArities Γ L ++ rest) (valuationTerms Γ rest L i)) = values i
  | _ :: _, _, values, restPoint, ⟨0, _⟩ =>
      (M.restageElem_interp_metaVar _ _ _).trans
        ((congrArg M.elemOfPoint (lift_fst _ _)).trans (M.elemEquiv.left_inv _))
  | a :: L, rest, values, restPoint, ⟨n + 1, bound⟩ => by
      refine (M.restageElem_interp_tail (a.1 ++ Γ, a.2) ⟨argArities Γ L ++ rest⟩ _ _).trans ?_
      refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
      exact valuationPoint_valuationTerms Γ L (fun i => values i.succ) restPoint
        ⟨n, Nat.lt_of_succ_lt_succ bound⟩

theorem valuationPoint_weakenPast {Z : D} (Γ : Ctx S) : ∀ (L : List (MetaArity S))
    {rest : List (MetaArity S)}
    (values : (i : Fin L.length) → M.ElemOver Z ((L.get i).1 ++ Γ) (L.get i).2)
    (restPoint : Z ⟶ M.family rest) {Θ : Ctx S} {s : S.Srt} (t : Term (withMetas S rest) Θ s),
    M.restageElem (M.valuationPoint Γ L values restPoint)
      (M.interp (argArities Γ L ++ rest) (weakenPast Γ rest L t)) =
        M.restageElem restPoint (M.interp rest t)
  | [], _, _, _, _, _, _ => rfl
  | a :: L, rest, values, restPoint, _, _, t => by
      refine (M.restageElem_interp_tail (a.1 ++ Γ, a.2) ⟨argArities Γ L ++ rest⟩ _ _).trans ?_
      refine (congrArg (fun q => M.restageElem q _) (lift_snd _ _)).trans ?_
      exact valuationPoint_weakenPast Γ L (fun i => values i.succ) restPoint t

/-- The point of a telescope's values goes to the point of their images. -/
theorem _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.PointMap.valuationPoint
    {M N : Model S D} {Z Z' : D} (m : PointMap M N Z Z') (Γ : Ctx S) :
    ∀ (L : List (MetaArity S)) {rest : List (MetaArity S)}
    (values : (i : Fin L.length) → M.ElemOver Z ((L.get i).1 ++ Γ) (L.get i).2)
    (restPoint : Z ⟶ M.family rest),
    m.family _ (M.valuationPoint Γ L values restPoint) =
      N.valuationPoint Γ L (fun i => m.elem (values i)) (m.family _ restPoint)
  | [], _, _, _ => rfl
  | _ :: L, _, values, restPoint => (m.family_cons _ _ _ _).trans (congrArg (lift _)
      (PointMap.valuationPoint m Γ L (fun i => values i.succ) restPoint))

variable (R : List (LocalRule S))

/-- The point of an occurrence of a rule at a stage. -/
def rulePoint {Z : D} (occurrence : Instance R (M.stage Z)) :
    Z ⟶ M.family (ruleContext R occurrence.index occurrence.ambient).arities :=
  M.valuationPoint occurrence.ambient (R.get occurrence.index).1 occurrence.valuation
    (M.envPoint occurrence.ambient occurrence.close)

/-- The point of an occurrence goes to the point of the occurrence mapped
along a map of stage clones acting on elements as the map of points. -/
theorem _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.PointMap.rulePoint
    {M N : Model S D} {Z Z' : D} (m : PointMap M N Z Z')
    (φ : FreeBindingClone.Hom (M.stage Z) (N.stage Z'))
    (elem : ∀ {Γ : Ctx S} {s : S.Srt} (x : M.ElemOver Z Γ s), φ.raw.map x = m.elem x)
    (occurrence : Instance R (M.stage Z)) :
    m.family _ (M.rulePoint R occurrence) = N.rulePoint R (mapInstance R φ occurrence) := by
  refine (m.valuationPoint _ _ _ _).trans ?_
  have values : (fun i => m.elem (occurrence.valuation i)) =
      (mapInstance R φ occurrence).valuation := funext fun i => (elem _).symm
  have close : (fun γ v => m.elem (occurrence.close γ v)) = (mapInstance R φ occurrence).close :=
    funext fun _ => funext fun v => (elem _).symm
  refine congrArg₂ (N.valuationPoint _ _) values ?_
  exact (m.envPoint _ _).trans (congrArg (N.envPoint _) close)

/-- The point of an occurrence moves along a map of stages to the point of the
restaged occurrence. -/
theorem comp_rulePoint {Z Z' : D} (k : Z' ⟶ Z) (occurrence : Instance R (M.stage Z)) :
    k ≫ M.rulePoint R occurrence = M.rulePoint R (mapInstance R (M.stageRestage k) occurrence) :=
  (M.restagePoints k).rulePoint R (M.stageRestage k) (fun _ => rfl) occurrence

variable {M' : List (MetaArity S)} (equations : List (EqAxiom S M'))
variable (sat : M.Satisfies (authoredEquationPresentation S equations))

/-- **The generic occurrence read at the point of an occurrence is that
occurrence.** -/
theorem mapInstance_rulePoint {Z : D} (occurrence : Instance R (M.stage Z)) :
    mapInstance R (M.pointProgram _ sat (ruleContext R occurrence.index occurrence.ambient)
        (M.rulePoint R occurrence))
      (ruleInstance R equations occurrence.index occurrence.ambient) = occurrence := by
  obtain ⟨index, Γ, values, close⟩ := occurrence
  have valuationEq : SemanticContextualMetavariables.mapValuation
      (M.pointProgram _ sat (ruleContext R index Γ) (M.rulePoint R ⟨index, Γ, values, close⟩))
      (ruleInstance R equations index Γ).valuation = values := by
    funext i
    exact M.valuationPoint_valuationTerms Γ (R.get index).1 values (M.envPoint Γ close) i
  have closeEq : (fun γ v => (M.pointProgram _ sat (ruleContext R index Γ)
      (M.rulePoint R ⟨index, Γ, values, close⟩)).raw.map
      ((ruleInstance R equations index Γ).close γ v)) = close := by
    funext γ v
    exact (M.valuationPoint_weakenPast Γ (R.get index).1 values (M.envPoint Γ close) _).trans
      (M.restageElem_envSub Γ close v)
  change (⟨index, Γ, _, _⟩ : Instance R _) = ⟨index, Γ, values, close⟩
  rw [valuationEq, closeEq]

/-- The point of the classes of a telescope, read at a point. -/
theorem comp_ofClasses_valuationClasses {Z : D} {X : Object S} (Γ : Ctx S)
    (x : Z ⟶ M.family X.arities) : ∀ (L : List (MetaArity S)) {rest : List (MetaArity S)}
    (values : (i : Fin L.length) →
      EquationTermClass (authoredEquationPresentation S equations) X ((L.get i).1 ++ Γ) (L.get i).2)
    (restClasses : ∀ i : Fin rest.length,
      EquationTermClass (authoredEquationPresentation S equations) X (rest.get i).1 (rest.get i).2),
    x ≫ (M.equationClassifyingFunctor _ sat).map
        (ofClasses equations _ (valuationClasses equations Γ L values restClasses)) =
      M.valuationPoint Γ L (fun i => (M.pointProgram _ sat X x).raw.map (values i))
        (x ≫ (M.equationClassifyingFunctor _ sat).map (ofClasses equations rest restClasses))
  | [], _, _, _ => rfl
  | _ :: L, _, values, restClasses =>
      (M.comp_consClass equations sat x _ _).trans
        (congrArg (lift _) (comp_ofClasses_valuationClasses Γ x L (fun i => values i.succ)
          restClasses))

/-- **The point of an occurrence of classes, read at a point.** -/
theorem comp_ruleBaseOf {Z : D} {X : Base equations} (x : Z ⟶ M.family X.as.arities)
    (occurrence : Instance R (modelAt equations X)) :
    x ≫ (M.equationClassifyingFunctor _ sat).map (ruleBaseOf R equations occurrence) =
      M.rulePoint R (mapInstance R (M.pointProgram _ sat X.as x) occurrence) :=
  (M.comp_ofClasses_valuationClasses equations sat occurrence.ambient x _ _ _).trans
    (congrArg (M.valuationPoint _ _ _)
      (M.comp_ofClasses_envClasses equations sat occurrence.ambient x occurrence.close))

end Mettapedia.OSLF.Binding.CategoricalBindingModel.Model

end
