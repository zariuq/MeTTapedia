import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedClassification
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFunctorModelMaps

/-!
# The classifying property

Models of a rule-local operational presentation in a target category are
equivalent to the structure-preserving functors out of its classifier. A
model is recovered from its classifying functor: its event objects represent
the valuations of the generic event objects, and evaluating the generic
substitution and the generic occurrences of rules gives back its substitution
and rule actions. A structure-preserving functor is the classifying functor
of its model.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution (heq_transport)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v w
variable {S : Signature} {R : List (LocalRule S)}
variable {A : BindingCloneAlgebra.Algebra.{u} S} {B : BindingCloneAlgebra.Algebra.{v} S}

/-- Reading a rule action along a clone map recovers the action at the
interpreted occurrence when the premise witnesses agree. -/
theorem rulesAct_pulledInstance (h : FreeBindingClone.Hom A B)
    {carrier : Judgment B → Type w}
    (alg : (rules R B).Algebra (fun _ j => carrier j))
    (generic : Instance R A) (occurrence : Instance R B)
    (same : mapInstance R h generic = occurrence)
    (children : ∀ p : Fin (R.get occurrence.index).2.premises.length,
      carrier (childJudgment R B occurrence p))
    (premises : ∀ p : Fin (R.get generic.index).2.premises.length,
      carrier (mapJudgment h (childJudgment R A generic p)))
    (inputs : ∀ p q, HEq p q → HEq (children p) (premises q)) :
    HEq (alg.act () (conclusionJudgment R B occurrence) ⟨⟨occurrence, rfl⟩, children⟩)
      ((IndexedRuleAlgebraPullback.pullback (rulesMap R h) alg).act ()
        (conclusionJudgment R A generic) ⟨⟨generic, rfl⟩, premises⟩) := by
  have targets : conclusionJudgment R B occurrence = mapJudgment h (conclusionJudgment R A generic) :=
    (congrArg (conclusionJudgment R B) same.symm).trans (mapInstance_conclusion R h generic)
  have mapped := pullback_rulesMap_act h alg ⟨generic, rfl⟩ premises
  have acted := rulesAct_heq R alg targets same.symm rfl (mapShape R h ⟨generic, rfl⟩).2
    children (fun p => ((mapInstance_child R h generic p).symm ▸ premises p :
      carrier (childJudgment R B (mapInstance R h generic) p)))
    (fun p q samePosition => (inputs p q samePosition).trans (heq_transport _ _).symm)
  exact acted.trans (heq_of_eq mapped).symm

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel

/-! ## Evaluating the generic trees -/

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics.ClassifierTarget

open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context exactHole)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

universe u w p

variable {S : Signature} {R : List (LocalRule S)}
variable {M : List (MetaArity S)} {equations : List (EqAxiom S M)}
variable {target : ClassifierTarget.{u, w, p} R equations}

/-- **The generic substitution evaluates to the substitution action** on the
event and environment of a valuation. -/
theorem Valuation.evaluate_substitutionTree {Γ Δ : Ctx S} {s : S.Srt}
    (value : target.Valuation (substitutionObject R equations Γ Δ s)) :
    value.evaluate _ (substitutionTree R equations Γ Δ s) =
      (target.pointModel value.point).act (substitutionJudgment equations Γ Δ s)
        (value.event (first R _ (Context.empty R _))) (substitutionEnv equations Γ Δ s) _ rfl :=
  (value.assignment.map (substitutionJudgment equations Γ Δ s)
    (exactHole R _ _ ⟨first R _ (Context.empty R _), ⟨rfl⟩⟩)
    (substitutionEnv equations Γ Δ s) _ rfl).trans
    (congrArg (fun x => (target.pointModel value.point).act (substitutionJudgment equations Γ Δ s) x
      (substitutionEnv equations Γ Δ s) _ rfl) (value.evaluate_leaf (first R _ (Context.empty R _))))

/-- **The generic occurrence of a rule evaluates to the rule action** on the
premises of a valuation. -/
theorem Valuation.evaluate_ruleTree {index : Fin R.length} {Γ : Ctx S}
    (value : target.Valuation (ruleObject R equations index Γ)) :
    value.evaluate _ (ruleTree R equations index Γ) =
      (target.pointModel value.point).rules.act () _
        ⟨⟨ruleInstance R equations index Γ, rfl⟩, fun position => value.event position⟩ :=
  congrArg (fun children => (target.pointModel value.point).rules.act () _
    ⟨⟨ruleInstance R equations index Γ, rfl⟩, children⟩)
    (funext fun position => value.evaluate_leaf position)

open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (mapJudgment)

/-- A generic rule tree evaluates to the action at its interpreted occurrence
and the supplied premise witnesses. -/
theorem Valuation.evaluate_ruleTree_of_instance {index : Fin R.length} {Γ : Ctx S}
    (value : target.Valuation (ruleObject R equations index Γ))
    (occurrence : Instance R target.algebra)
    (same : mapInstance R (target.program value.point) (ruleInstance R equations index Γ) = occurrence)
    (children : ∀ p : Fin (R.get occurrence.index).2.premises.length,
      target.model.carrier (childJudgment R _ occurrence p))
    (inputs : ∀ p q, HEq p q → HEq (children p) (value.event q)) :
    HEq (value.evaluate _ (ruleTree R equations index Γ))
      (target.model.rules.act () (conclusionJudgment R _ occurrence) ⟨⟨occurrence, rfl⟩, children⟩) := by
  have folded := value.evaluate_ruleTree
  have acted := rulesAct_pulledInstance (target.program value.point) target.model.rules
    (ruleInstance R equations index Γ) occurrence same children value.event inputs
  exact (heq_of_eq folded).trans acted.symm

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics.ClassifierTarget

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedConditionalSubstitution
  (substJudgment heq_transport mapJudgment_substJudgment)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel (substJudgment_congr)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature} {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

omit [CartesianMonoidalCategory D] in
theorem _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.pairComponentsIso_inv_familyMap_fst
    [CartesianMonoidalCategory D] {M N : Model S D} (g : ∀ Γ s, M.power Γ s ⟶ N.power Γ s)
    (Γ : Ctx S) (s : S.Srt) :
    (M.pairComponentsIso Γ s).inv ≫ Model.familyMap g (pairContext Γ s).arities ≫ fst _ _ =
      fst _ _ ≫ g Γ s := by
  change lift (fst _ _) (lift (snd _ _) (toUnit _)) ≫ (g Γ s ⊗ₘ _) ≫ fst _ _ = _
  rw [tensorHom_fst, lift_fst_assoc]

omit [CartesianMonoidalCategory D] in
theorem _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.pairComponentsIso_inv_familyMap_snd
    [CartesianMonoidalCategory D] {M N : Model S D} (g : ∀ Γ s, M.power Γ s ⟶ N.power Γ s)
    (Γ : Ctx S) (s : S.Srt) :
    (M.pairComponentsIso Γ s).inv ≫ Model.familyMap g (pairContext Γ s).arities ≫ snd _ _ ≫ fst _ _ =
      snd _ _ ≫ g Γ s := by
  change lift (fst _ _) (lift (snd _ _) (toUnit _)) ≫ (g Γ s ⊗ₘ (g Γ s ⊗ₘ _)) ≫ snd _ _ ≫ fst _ _ = _
  rw [tensorHom_snd_assoc, tensorHom_fst, lift_snd_assoc, lift_fst_assoc]

namespace StructuredFunctor

variable (F : StructuredFunctor R equations (D := D))

/-- The value of a generic premise projection is the supplied premise event. -/
theorem ruleLift_event_heq {Z : D} (occurrence : Instance R (F.programModel.stage Z))
    (children : ∀ position : Fin (R.get occurrence.index).2.premises.length,
      F.eventModel.objects.StageEvent Z (childJudgment R _ occurrence position))
    (position : Fin (R.get occurrence.index).2.premises.length) :
    HEq (F.ruleLift occurrence children ≫ F.carrier.map (rep R equations
      (a := ruleObject R equations occurrence.index occurrence.ambient)
      (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position)
      (leaf R (events R equations (ruleObject R equations occurrence.index occurrence.ambient)) position)))
      (children position).1 := by
  have premise := F.treeEvent_premiseLift (F.programModel.rulePoint R occurrence)
    (ruleInstance R equations occurrence.index occurrence.ambient)
    (F.rulePremises occurrence children) position
  have inputs := F.rulePremises_heq occurrence children position
  have same : mapJudgment (F.pointProgram (F.ruleLift occurrence children ≫ F.programPoint _))
      (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position) =
        childJudgment R _ occurrence position := by
    have point : F.ruleLift occurrence children ≫ F.programPoint _ =
        F.programModel.rulePoint R occurrence := F.ruleLift_point occurrence children
    have moved := congrArg (fun x => mapJudgment (F.pointProgram x)
      (childJudgment R _ (ruleInstance R equations occurrence.index occurrence.ambient) position)) point
    have read := F.programModel.mapInstance_rulePoint R equations
      F.programInterpretation.satisfies occurrence
    have child := childJudgment_congr R read position position HEq.rfl
    exact moved.trans ((mapInstance_child R (F.pointProgram (F.programModel.rulePoint R occurrence))
      (ruleInstance R equations occurrence.index occurrence.ambient) position).symm.trans child)
  exact F.eventModel.objects.stageEvent_val_heq same (premise.trans inputs)

end StructuredFunctor

namespace CategoricalModel

variable [HasPullbacks D] (model : CategoricalModel R equations (D := D))

/-! ## Event objects represent the valuations of the generic event objects -/

/-- The classifying functor forgets event variables by the program
projection. -/
theorem map_toProgram (a : Classifier R equations) :
    model.classifyingFunctor.map (toProgram R equations a) = model.programProjection a := by
  have natural := model.map_programProjection (toProgram R equations a)
  change _ ≫ 𝟙 _ = _ ≫ model.programFunctor.map (𝟙 a.base) at natural
  rw [CategoryTheory.Functor.map_id] at natural
  exact (Category.comp_id _).symm.trans (natural.trans (Category.comp_id _))

omit [HasPullbacks D] in
/-- The endpoints the generic judgment names are the two components of the
pair context. -/
theorem judgmentEndpoints_pair (Γ : Ctx S) (s : S.Srt) :
    model.toEventModel.judgmentEndpoints (pairBase equations Γ s) (pairJudgment equations Γ s) =
      model.programModel.pairComponents Γ s := by
  have named := model.toEventModel.programFunctor_judgmentBase (pairJudgment equations Γ s)
  simp only [judgmentBase_pairJudgment] at named
  exact named.symm.trans ((congrArg (· ≫ model.programModel.pairComponents Γ s)
    (model.toEventModel.programFunctor.map_id (pairBase equations Γ s))).trans (Category.id_comp _))

omit [HasPullbacks D] in
/-- The endpoints the generic judgment names form an isomorphism. -/
theorem isIso_judgmentEndpoints_pair (Γ : Ctx S) (s : S.Srt) :
    IsIso (model.toEventModel.judgmentEndpoints (pairBase equations Γ s) (pairJudgment equations Γ s)) := by
  rw [model.judgmentEndpoints_pair Γ s]
  exact (model.programModel.pairComponentsIso Γ s).isIso_hom

/-- The event of the generic event object's valuations. -/
noncomputable abbrev genericEventProjection (Γ : Ctx S) (s : S.Srt) :
    model.classifyingObject (eventObject R equations Γ s) ⟶ model.objects.event Γ s :=
  model.toEventModel.eventProjection (pairBase equations Γ s) _
    (events R equations (eventObject R equations Γ s)).listed.label
    (first R (pairJudgment equations Γ s) (Context.empty R _))

theorem isIso_genericEventProjection (Γ : Ctx S) (s : S.Srt) :
    IsIso (model.genericEventProjection Γ s) := by
  have endpoints := model.isIso_judgmentEndpoints_pair Γ s
  have composite : IsIso (𝟙 (model.toEventModel.programModel.family (pairBase equations Γ s).as.arities) ≫
      model.toEventModel.judgmentEndpoints (pairBase equations Γ s) (pairJudgment equations Γ s)) := by
    rw [Category.id_comp]
    exact endpoints
  change IsIso (pullback.fst (model.toEventModel.eventEndpoints Γ s)
    (𝟙 _ ≫ model.toEventModel.judgmentEndpoints (pairBase equations Γ s) (pairJudgment equations Γ s)))
  exact (IsPullback.of_hasPullback _ _).isIso_fst_of_isIso composite

/-- **The event object is the object of valuations of the generic event
object**: valuations of one event variable between two metavariables are
determined by their event. -/
noncomputable def eventIso (Γ : Ctx S) (s : S.Srt) :
    model.objects.event Γ s ≅ model.classifyingObject (eventObject R equations Γ s) :=
  haveI := model.isIso_genericEventProjection Γ s
  (asIso (model.genericEventProjection Γ s)).symm

/-- A map into the object of valuations of the generic event object, followed
back to the event object, is the event of its valuation. -/
theorem comp_eventIso_inv {Γ : Ctx S} {s : S.Srt} {Z : D}
    (g : Z ⟶ model.classifyingObject (eventObject R equations Γ s)) :
    g ≫ (model.eventIso Γ s).inv =
      (((model.valuationsRepresentableBy (eventObject R equations Γ s)).homEquiv g).event
        (first R (pairJudgment equations Γ s) (Context.empty R _))).1 :=
  rfl

/-- **Reading the arrow of a tree back into an event object evaluates the
tree.** -/
theorem comp_rep_eventIso_inv {a : Classifier R equations} {Z : D}
    (g : Z ⟶ model.classifyingObject a) (J : Judgment (modelAt equations a.base))
    (tree : Tree R _ (seeds R _ (events R equations a)) J) :
    (g ≫ model.classifyingFunctor.map (rep R equations J tree)) ≫ (model.eventIso J.1 J.2.1).inv =
      (((model.valuationsRepresentableBy a).homEquiv g).evaluate J tree).1 := by
  refine (model.comp_eventIso_inv _).trans ?_
  have moved := model.classifyingFunctor_homEquiv (rep R equations J tree) g
  refine eq_of_heq ((model.objects.stageEvent_val_heq (congrArg
    (fun value : model.StageValuation Z (eventObject R equations J.1 J.2.1) =>
      mapJudgment ((model.stageTarget Z).program value.point) (pairJudgment equations J.1 J.2.1)) moved)
    (congr_arg_heq (fun value : model.StageValuation Z (eventObject R equations J.1 J.2.1) =>
      value.event (first R (pairJudgment equations J.1 J.2.1) (Context.empty R _))) moved)).trans ?_)
  refine (model.objects.stageEvent_val_heq ?_
    (((model.valuationsRepresentableBy a).homEquiv g).transport_event (rep R equations J tree)
      (first R (pairJudgment equations J.1 J.2.1) (Context.empty R _)))).trans ?_
  · exact congrArg (fun h => mapJudgment h (pairJudgment equations J.1 J.2.1))
      ((model.stageTarget Z).program_move (rep R equations J tree).base _)
  · refine model.objects.stageEvent_val_heq ?_ (((model.valuationsRepresentableBy a).homEquiv g).evaluate_heq
      (mapJudgment_judgmentBase equations J) (atSlot_rep R equations J tree))
    exact congrArg (mapJudgment _) (mapJudgment_judgmentBase equations J)

/-- The generic event's program point is its pair of endpoints. -/
theorem eventIso_hom_programProjection (Γ : Ctx S) (s : S.Srt) :
    (model.eventIso Γ s).hom ≫ model.programProjection (eventObject R equations Γ s) =
      model.toEventModel.eventEndpoints Γ s ≫ (model.programModel.pairComponentsIso Γ s).inv := by
  have square := (model.toEventModel.contextCones (pairBase equations Γ s)).event_endpoints _
    (events R equations (eventObject R equations Γ s)).listed.label
    (first R (pairJudgment equations Γ s) (Context.empty R _))
  change model.genericEventProjection Γ s ≫ model.toEventModel.eventEndpoints Γ s =
    model.programProjection _ ≫ model.toEventModel.judgmentEndpoints (pairBase equations Γ s)
      (pairJudgment equations Γ s) at square
  rw [model.judgmentEndpoints_pair Γ s] at square
  have atEvent : (model.eventIso Γ s).hom ≫ model.genericEventProjection Γ s = 𝟙 _ :=
    (model.eventIso Γ s).hom_inv_id
  have step : (model.eventIso Γ s).hom ≫ model.programProjection (eventObject R equations Γ s) ≫
      model.programModel.pairComponents Γ s = model.toEventModel.eventEndpoints Γ s :=
    (congrArg ((model.eventIso Γ s).hom ≫ ·) square.symm).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ model.toEventModel.eventEndpoints Γ s) atEvent).trans (Category.id_comp _)))
  exact (Category.comp_id _).symm.trans ((congrArg (_ ≫ ·)
    (model.programModel.pairComponentsIso Γ s).hom_inv_id.symm).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (model.programModel.pairComponentsIso Γ s).inv)
      ((Category.assoc _ _ _).trans step))))

/-! ## The program part of a model is recovered from its classifying functor -/

/-- The program classifier of a model and the program classifier of its
classifying functor's model. -/
noncomputable def programComparison :
    model.programModel.classifyingFunctor ≅ model.structured.programModel.classifyingFunctor :=
  (eqToIso model.quotient_programSection_classifyingFunctor).symm ≪≫
    model.structured.program.isoClassifying

/-- The program part of the unit. -/
noncomputable def programUnit : model.program ⟶ model.structured.programInterpretation :=
  CategoricalBindingInterpretationMaps.Hom.ofNat model.programComparison.hom

/-- Its inverse. -/
noncomputable def programUnitInv : model.structured.programInterpretation ⟶ model.program :=
  CategoricalBindingInterpretationMaps.Hom.ofNat model.programComparison.inv

theorem programUnit_inv : model.programUnit ≫ model.programUnitInv = 𝟙 model.program := by
  change CategoricalBindingInterpretationMaps.Hom.comp
    (CategoricalBindingInterpretationMaps.Hom.ofNat _)
    (CategoricalBindingInterpretationMaps.Hom.ofNat _) = CategoricalBindingInterpretationMaps.Hom.id _
  exact (CategoricalBindingInterpretationMaps.Hom.ofNat_comp _ _).symm.trans
    ((congrArg CategoricalBindingInterpretationMaps.Hom.ofNat model.programComparison.hom_inv_id).trans
      (CategoricalBindingInterpretationMaps.Hom.ofNat_id _))

theorem programUnitInv_unit :
    model.programUnitInv ≫ model.programUnit = 𝟙 model.structured.programInterpretation := by
  change CategoricalBindingInterpretationMaps.Hom.comp
    (CategoricalBindingInterpretationMaps.Hom.ofNat _)
    (CategoricalBindingInterpretationMaps.Hom.ofNat _) = CategoricalBindingInterpretationMaps.Hom.id _
  exact (CategoricalBindingInterpretationMaps.Hom.ofNat_comp _ _).symm.trans
    ((congrArg CategoricalBindingInterpretationMaps.Hom.ofNat model.programComparison.inv_hom_id).trans
      (CategoricalBindingInterpretationMaps.Hom.ofNat_id _))

/-- **On program objects the unit is the comparison of products.** -/
theorem familyMap_programUnit (X : Base equations) :
    Model.familyMap model.programUnit.underlying.power X.as.arities =
      (model.structured.programIso X).hom := by
  refine (Model.app_eq_familyMap model.programComparison.hom X.as).symm.trans ?_
  change NatTrans.app (eqToHom model.quotient_programSection_classifyingFunctor.symm) X.as ≫
    (model.structured.program.famIso X.as.arities).hom = _
  rw [eqToHom_app]
  exact (congrArg (· ≫ (model.structured.program.famIso X.as.arities).hom) (eqToHom_refl _ _)).trans
    (Category.id_comp _)

/-- The program point of a value of the classifying functor is its program
projection followed by the comparison of products. -/
theorem structured_programPoint (a : Classifier R equations) :
    model.structured.programPoint a =
      model.programProjection a ≫ Model.familyMap model.programUnit.underlying.power a.base.as.arities :=
  (congrArg (· ≫ (model.structured.programIso a.base).hom) (model.map_toProgram a)).trans
    (congrArg (model.programProjection a ≫ ·) (model.familyMap_programUnit a.base).symm)

/-! ## The event part of the unit -/

/-- The generic event's program point under the classifying functor is its
pair of endpoints, compared. -/
theorem eventIso_hom_structured_programPoint (Γ : Ctx S) (s : S.Srt) :
    (model.eventIso Γ s).hom ≫ model.structured.programPoint (eventObject R equations Γ s) =
      model.toEventModel.eventEndpoints Γ s ≫ (model.programModel.pairComponentsIso Γ s).inv ≫
        Model.familyMap model.programUnit.underlying.power (pairContext Γ s).arities :=
  (congrArg ((model.eventIso Γ s).hom ≫ ·) (model.structured_programPoint _)).trans
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (model.eventIso_hom_programProjection Γ s)).trans
      (Category.assoc _ _ _)))

/-- **The event part of the unit**: each event object goes to the object of
valuations of its generic event object. -/
noncomputable def eventUnit :
    model.objects.Hom model.structured.eventModel.objects model.programUnit where
  event Γ s := (model.eventIso Γ s).hom
  source Γ s :=
    (congrArg ((model.eventIso Γ s).hom ≫ ·) (StructuredFunctor.source_eq _ Γ s)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ fst _ _)
        (model.eventIso_hom_structured_programPoint Γ s)).trans ((Category.assoc _ _ _).trans
          ((congrArg (model.toEventModel.eventEndpoints Γ s ≫ ·) ((Category.assoc _ _ _).trans
            (Model.pairComponentsIso_inv_familyMap_fst model.programUnit.underlying.power Γ s))).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
              (model.toEventModel.source_eventEndpoints Γ s)))))))
  target Γ s :=
    (congrArg ((model.eventIso Γ s).hom ≫ ·) (StructuredFunctor.target_eq _ Γ s)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ snd _ _ ≫ fst _ _)
        (model.eventIso_hom_structured_programPoint Γ s)).trans ((Category.assoc _ _ _).trans
          ((congrArg (model.toEventModel.eventEndpoints Γ s ≫ ·) ((Category.assoc _ _ _).trans
            (Model.pairComponentsIso_inv_familyMap_snd model.programUnit.underlying.power Γ s))).trans
            ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
              (model.toEventModel.target_eventEndpoints Γ s)))))))

/-! ## Reading maps into classifying objects -/

/-- A map into a classifying object has the program point its image under the
classifying functor shows. -/
theorem point_of_structured {a : Classifier R equations} {Z : D} (g : Z ⟶ model.classifyingObject a)
    (point : Z ⟶ model.programModel.family a.base.as.arities)
    (same : g ≫ model.structured.programPoint a =
      point ≫ Model.familyMap model.programUnit.underlying.power a.base.as.arities) :
    ((model.valuationsRepresentableBy a).homEquiv g).point = point := by
  have moved : (g ≫ model.programProjection a) ≫ (model.structured.programIso a.base).hom =
      point ≫ (model.structured.programIso a.base).hom :=
    (Category.assoc _ _ _).trans ((congrArg (g ≫ ·) (congrArg (· ≫ (model.structured.programIso a.base).hom)
      (model.map_toProgram a)).symm).trans (same.trans
        (congrArg (point ≫ ·) (model.familyMap_programUnit a.base))))
  exact (cancel_mono (model.structured.programIso a.base).hom).mp moved

/-- A map into a classifying object has the events its image under the
classifying functor shows. -/
theorem event_of_structured {a : Classifier R equations} {Z : D} (g : Z ⟶ model.classifyingObject a)
    (position : Fin (events R equations a).listed.length)
    (x : Z ⟶ model.objects.event ((events R equations a).listed.label position).1
      ((events R equations a).listed.label position).2.1)
    (same : g ≫ model.classifyingFunctor.map (rep R equations _ (leaf R (events R equations a) position)) =
      x ≫ (model.eventIso _ _).hom) :
    (((model.valuationsRepresentableBy a).homEquiv g).event position).1 = x := by
  have read := model.comp_rep_eventIso_inv g _ (leaf R (events R equations a) position)
  have back : (x ≫ (model.eventIso _ _).hom) ≫ (model.eventIso _ _).inv = x :=
    (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (model.eventIso _ _).hom_inv_id).trans
      (Category.comp_id _))
  exact (congrArg Subtype.val (((model.valuationsRepresentableBy a).homEquiv g).evaluate_leaf
    position)).symm.trans (read.symm.trans ((congrArg (· ≫ (model.eventIso _ _).inv) same).trans back))

/-! ## The unit is a map of models -/

/-- **The unit commutes with substitution**: substituting in the classifying
functor's model evaluates the generic substitution, which is the model's own
substitution. -/
theorem unit_actsAlong (Z : D) :
    ActsAlong (stageMap model.programUnit Z) (model.stageModel Z)
      (model.structured.model.stageModel Z).act (model.eventUnit.stage Z) := by
  intro j e Δ σ
  let L := model.structured.substitutionLift (mapJudgment (stageMap model.programUnit Z) j)
    (model.eventUnit.stage Z j e) (fun t v => (stageMap model.programUnit Z).raw.map (σ t v))
  have point : ((model.valuationsRepresentableBy _).homEquiv L).point =
      model.programModel.substitutionPoint j.2.2.1 j.2.2.2 σ :=
    model.point_of_structured (a := substitutionObject R equations j.1 Δ j.2.1) L _
      ((model.structured.substitutionLift_point _ _ _).trans
      ((mapPoints model.programUnit Z).substitutionPoint j.2.2.1 j.2.2.2 σ).symm)
  have event : (((model.valuationsRepresentableBy _).homEquiv L).event
      (first R (substitutionJudgment equations j.1 Δ j.2.1) (Context.empty R _))).1 = e.1 :=
    model.event_of_structured (a := substitutionObject R equations j.1 Δ j.2.1) L
      (first R (substitutionJudgment equations j.1 Δ j.2.1) (Context.empty R _)) e.1
      (model.structured.substitutionLift_event _ _ _)
  have judgmentEq : mapJudgment (model.programModel.pointProgram _ model.program.satisfies _
      ((model.valuationsRepresentableBy _).homEquiv L).point)
        (substitutionJudgment equations j.1 Δ j.2.1) = j :=
    (congrArg (fun y => mapJudgment (model.programModel.pointProgram _ model.program.satisfies _ y)
      (substitutionJudgment equations j.1 Δ j.2.1)) point).trans
      (model.programModel.mapJudgment_substitutionPoint equations model.program.satisfies
        j.2.2.1 j.2.2.2 σ)
  have envEq : (fun t v => (model.programModel.pointProgram _ model.program.satisfies _
      ((model.valuationsRepresentableBy _).homEquiv L).point).raw.map
        (substitutionEnv equations j.1 Δ j.2.1 t v)) = σ :=
    funext fun _ => funext fun v =>
      (congrArg (fun y => (model.programModel.pointProgram _ model.program.satisfies _ y).raw.map
        (substitutionEnv equations j.1 Δ j.2.1 _ v)) point).trans
      (model.programModel.substitutionPoint_env equations model.program.satisfies j.2.2.1 j.2.2.2 σ v)
  have targetEq : substJudgment j σ = mapJudgment (model.programModel.pointProgram _
      model.program.satisfies _ ((model.valuationsRepresentableBy _).homEquiv L).point)
        (substJudgment (substitutionJudgment equations j.1 Δ j.2.1)
          (substitutionEnv equations j.1 Δ j.2.1)) :=
    (substJudgment_congr judgmentEq.symm (heq_of_eq envEq.symm)).trans
      (mapJudgment_substJudgment _ _ _).symm
  have rhs : (model.structured.act Z (mapJudgment (stageMap model.programUnit Z) j)
      (model.eventUnit.stage Z j e) (fun t v => (stageMap model.programUnit Z).raw.map (σ t v))
      (mapJudgment (stageMap model.programUnit Z) (substJudgment j σ))
      (mapJudgment_substJudgment _ j σ).symm).1 =
        L ≫ model.classifyingFunctor.map (substitutionRep R equations j.1 Δ j.2.1) :=
    eq_of_heq (model.structured.act_val_heq _ _ _ _ _)
  have back : ((model.act Z j e σ (substJudgment j σ) rfl).1 ≫ (model.eventIso Δ j.2.1).hom) ≫
      (model.eventIso Δ j.2.1).inv = (model.act Z j e σ (substJudgment j σ) rfl).1 :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (model.eventIso Δ j.2.1).hom_inv_id).trans
      (Category.comp_id _))
  have read : (L ≫ model.classifyingFunctor.map (substitutionRep R equations j.1 Δ j.2.1)) ≫
      (model.eventIso Δ j.2.1).inv =
        (((model.valuationsRepresentableBy _).homEquiv L).evaluate _
          (substitutionTree R equations j.1 Δ j.2.1)).1 :=
    model.comp_rep_eventIso_inv L _ (substitutionTree R equations j.1 Δ j.2.1)
  have evaluated := congrArg Subtype.val
    (((model.valuationsRepresentableBy _).homEquiv L).evaluate_substitutionTree)
  have acted : HEq (model.act Z j e σ (substJudgment j σ) rfl) ((model.stageModel Z).act _
      (((model.valuationsRepresentableBy _).homEquiv L).event
        (first R (substitutionJudgment equations j.1 Δ j.2.1) (Context.empty R _)))
      (fun t v => (model.programModel.pointProgram _ model.program.satisfies _
        ((model.valuationsRepresentableBy _).homEquiv L).point).raw.map
          (substitutionEnv equations j.1 Δ j.2.1 t v)) _
      (mapJudgment_substJudgment _ _ _).symm) :=
    (model.stageModel Z).toAction.act_heq judgmentEq.symm
      (model.objects.stageEvent_heq judgmentEq.symm (heq_of_eq event.symm)) (heq_of_eq envEq.symm)
      targetEq rfl _
  have core := (eq_of_heq (model.objects.stageEvent_val_heq targetEq acted)).trans
    (evaluated.symm.trans read.symm)
  exact Subtype.ext (((cancel_mono (model.eventIso Δ j.2.1).inv).mp (back.trans core)).trans rhs.symm)

/-- **The unit commutes with the rule actions**: a rule action in the
classifying functor's model evaluates the rule's generic occurrence, which is
the model's own rule action. -/
theorem unit_rulesAlong (Z : D) :
    RulesAlong (stageMap model.programUnit Z) (model.stageModel Z)
      (model.structured.model.stageModel Z).rules (model.eventUnit.stage Z) := by
  intro j shape children
  rcases shape with ⟨occurrence, rfl⟩
  let j := conclusionJudgment R (model.programModel.stage Z) occurrence
  let shape : (IntrinsicScopedLocalPolynomial.rules R (model.programModel.stage Z)).Shape () j :=
    ⟨occurrence, rfl⟩
  let premises : ∀ position : Fin (R.get shape.1.index).2.premises.length,
      model.structured.eventModel.objects.StageEvent Z
        (childJudgment R _ (mapInstance R (stageMap model.programUnit Z) shape.1) position) :=
    fun position => ((mapInstance_child R (stageMap model.programUnit Z) shape.1 position).symm ▸
      model.eventUnit.stage Z _ (children position) :
        model.structured.eventModel.objects.StageEvent Z
          (childJudgment R _ (mapInstance R (stageMap model.programUnit Z) shape.1) position))
  let L := model.structured.ruleLift (mapInstance R (stageMap model.programUnit Z) shape.1) premises
  have point : ((model.valuationsRepresentableBy _).homEquiv L).point =
      model.programModel.rulePoint R shape.1 :=
    model.point_of_structured (a := ruleObject R equations shape.1.index shape.1.ambient) L _
      ((model.structured.ruleLift_point _ _).trans
        ((mapPoints model.programUnit Z).rulePoint R (stageMap model.programUnit Z) (fun _ => rfl)
          shape.1).symm)
  have premiseRead : ∀ position, L ≫ model.classifyingFunctor.map (rep R equations
      (a := ruleObject R equations shape.1.index shape.1.ambient)
      (childJudgment R _ (ruleInstance R equations shape.1.index shape.1.ambient) position)
      (leaf R (events R equations (ruleObject R equations shape.1.index shape.1.ambient)) position)) =
        (children position).1 ≫ (model.eventIso _ _).hom := by
    intro position
    have lifted := model.structured.ruleLift_event_heq
      (mapInstance R (stageMap model.programUnit Z) shape.1) premises position
    have same : childJudgment R _ (mapInstance R (stageMap model.programUnit Z) shape.1) position =
        mapJudgment (stageMap model.programUnit Z) (childJudgment R _ shape.1 position) :=
      mapInstance_child R (stageMap model.programUnit Z) shape.1 position
    have inputs : HEq (premises position) (model.eventUnit.stage Z _ (children position)) :=
      heq_transport _ _
    have values : HEq (premises position).1 (model.eventUnit.stage Z _ (children position)).1 :=
      model.structured.eventModel.objects.stageEvent_val_heq same inputs
    exact eq_of_heq (lifted.trans values)
  have event : ∀ position, (((model.valuationsRepresentableBy _).homEquiv L).event position).1 =
      (children position).1 :=
    fun position => model.event_of_structured (a := ruleObject R equations shape.1.index
      shape.1.ambient) L position (children position).1 (premiseRead position)
  have instanceEq : mapInstance R (model.programModel.pointProgram _ model.program.satisfies _
      ((model.valuationsRepresentableBy _).homEquiv L).point)
        (ruleInstance R equations shape.1.index shape.1.ambient) = shape.1 :=
    (congrArg (fun y => mapInstance R (model.programModel.pointProgram _ model.program.satisfies _ y)
      (ruleInstance R equations shape.1.index shape.1.ambient)) point).trans
      (model.programModel.mapInstance_rulePoint R equations model.program.satisfies shape.1)
  have targetEq : j = mapJudgment (model.programModel.pointProgram _ model.program.satisfies _
      ((model.valuationsRepresentableBy _).homEquiv L).point)
        (conclusionJudgment R _ (ruleInstance R equations shape.1.index shape.1.ambient)) :=
    shape.2.symm.trans ((congrArg (conclusionJudgment R _) instanceEq.symm).trans
      (mapInstance_conclusion R _ _))
  have rhs : ((model.structured.rulesAlgebra Z).act () (mapJudgment (stageMap model.programUnit Z) j)
      ⟨mapShape R (stageMap model.programUnit Z) shape, premises⟩).1 =
        L ≫ model.classifyingFunctor.map
          (ruleRep R equations shape.1.index shape.1.ambient) :=
    eq_of_heq (model.structured.rulesAlgebra_val_heq _ _)
  have back : ((model.rules Z).act () j ⟨shape, children⟩).1 ≫
      (model.eventIso j.1 j.2.1).hom ≫ (model.eventIso j.1 j.2.1).inv =
        ((model.rules Z).act () j ⟨shape, children⟩).1 :=
    (congrArg (_ ≫ ·) (model.eventIso j.1 j.2.1).hom_inv_id).trans (Category.comp_id _)
  have read : (L ≫ model.classifyingFunctor.map (ruleRep R equations shape.1.index shape.1.ambient)) ≫
      (model.eventIso _ _).inv = (((model.valuationsRepresentableBy _).homEquiv L).evaluate _
        (ruleTree R equations shape.1.index shape.1.ambient)).1 :=
    model.comp_rep_eventIso_inv L _ (ruleTree R equations shape.1.index shape.1.ambient)
  have inputs : ∀ p q, HEq p q → HEq (children p)
      (((model.valuationsRepresentableBy _).homEquiv L).event q) := by
    intro p q hpq
    cases hpq
    have same : childJudgment R _ shape.1 p = mapJudgment
        (model.programModel.pointProgram _ model.program.satisfies _
          ((model.valuationsRepresentableBy _).homEquiv L).point)
        (childJudgment R _ (ruleInstance R equations shape.1.index shape.1.ambient) p) :=
      (childJudgment_congr R instanceEq.symm p p HEq.rfl).trans
        (mapInstance_child R _ (ruleInstance R equations shape.1.index shape.1.ambient) p)
    exact model.objects.stageEvent_heq same (heq_of_eq (event p).symm)
  have acted := ((model.valuationsRepresentableBy _).homEquiv L).evaluate_ruleTree_of_instance
    shape.1 instanceEq children inputs
  have core := (eq_of_heq (model.objects.stageEvent_val_heq targetEq acted.symm)).trans read.symm
  exact Subtype.ext (((cancel_mono (model.eventIso j.1 j.2.1).inv).mp
    (((Category.assoc _ _ _).trans back).trans core)).trans rhs.symm)


/-- The program comparison is an isomorphism of equation models. -/
noncomputable def programUnitIso : model.program ≅ model.structured.programInterpretation where
  hom := model.programUnit
  inv := model.programUnitInv
  hom_inv_id := model.programUnit_inv
  inv_hom_id := model.programUnitInv_unit

/-- The unit preserves the program, event, substitution and rule structure. -/
noncomputable def unitHom : model ⟶ model.structured.model where
  program := model.programUnit
  events := model.eventUnit
  stage Z := isHom_of_along (model.unit_actsAlong Z) (model.unit_rulesAlong Z)

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
