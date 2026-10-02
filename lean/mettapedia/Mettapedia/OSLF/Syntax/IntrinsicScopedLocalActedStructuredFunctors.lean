import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedModelMaps
import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedGenericEvent

/-!
# Structure-preserving functors out of the classifier

A structure-preserving functor out of the classifier has, on event-free
objects, the chosen products, binder exponentials and operators of the
equation-class binding classifier, and it sends each pullback of an
event-variable projection along an arrow to a pullback. Its values on the
generic event objects are event objects over its binding model, and its value
at every classifier object is an object of valuations for them.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.CategoricalBindingQuotientEquivalence
open Mettapedia.OSLF.Binding.CategoricalBindingEquationEquivalence
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature}

/-! ## Endpoints of judgments at the program classifier -/

/-- The two function-object components of a pair context. -/
def _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.pairComponents (M : Model S D) (Γ : Ctx S) (s : S.Srt) :
    M.family (pairContext Γ s).arities ⟶ M.power Γ s ⊗ M.power Γ s :=
  lift (fst _ _) (snd _ _ ≫ fst _ _)

/-- The two function-object components of a pair context, as an isomorphism. -/
def _root_.Mettapedia.OSLF.Binding.CategoricalBindingModel.Model.pairComponentsIso
    (M : Model S D) (Γ : Ctx S) (s : S.Srt) :
    M.family (pairContext Γ s).arities ≅ M.power Γ s ⊗ M.power Γ s where
  hom := M.pairComponents Γ s
  inv := lift (fst _ _) (lift (snd _ _) (toUnit _))
  hom_inv_id := by
    apply hom_ext
    · simp [Model.pairComponents]
    · apply hom_ext
      · simp [Model.pairComponents]
      · exact toUnit_unique _ _
  inv_hom_id := by
    apply hom_ext <;> simp [Model.pairComponents]

variable (R : List (LocalRule S)) {M' : List (MetaArity S)} (equations : List (EqAxiom S M'))

section Endpoints

variable {R equations}

/-- The endpoints of a judgment, as a map into the pair context. -/
def pairAssignment {X : Object S} {Γ : Ctx S} {s : S.Srt}
    (first second : Term (withMetas S X.arities) Γ s) : X ⟶ pairContext Γ s
  | ⟨0, _⟩ => first
  | ⟨1, _⟩ => second
  | ⟨_ + 2, bound⟩ => absurd bound (by simp)

theorem judgmentBase_mk {X : Base equations} {Γ : Ctx S} {s : S.Srt}
    (first second : Term (withMetas S X.as.arities) Γ s) :
    judgmentBase equations (X := X)
        ⟨Γ, s, termClass equations first, termClass equations second⟩ =
      (authoredEquationPresentation S equations).quotientFunctor.map
        (pairAssignment first second) := by
  refine Eq.trans (congrArg (ofClasses equations (pairContext Γ s).arities) ?_)
    (ofClasses_termClass equations (pairContext Γ s).arities (pairAssignment first second))
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨_ + 2, bound⟩ => exact absurd bound (by simp)

namespace EventModel

variable (model : EventModel equations (D := D))

/-- **The program classifier sends the endpoints of a judgment to the
endpoints it names.** -/
theorem programFunctor_judgmentBase {X : Base equations} (J : Judgment (modelAt equations X)) :
    model.programFunctor.map (judgmentBase equations J) ≫
        model.programModel.pairComponents J.1 J.2.1 =
      model.judgmentEndpoints X J := by
  obtain ⟨Γ, s, first, second⟩ := J
  induction first using Quotient.inductionOn with
  | _ t₀ =>
      induction second using Quotient.inductionOn with
      | _ t₁ =>
          refine (congrArg (fun u => model.programFunctor.map u ≫
            model.programModel.pairComponents Γ s) (judgmentBase_mk (X := X) t₀ t₁)).trans ?_
          apply hom_ext
          · refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (lift_fst _ _))).trans ?_
            refine ((model.programModel.assignHom_proj (pairAssignment t₀ t₁) ⟨0, by simp⟩).trans
              ?_).trans (lift_fst _ _).symm
            exact ((model.programModel.elemEquiv_restage (𝟙 _) _).trans
              (Category.id_comp _)).symm
          · refine ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (lift_snd _ _))).trans ?_
            refine ((model.programModel.assignHom_proj (pairAssignment t₀ t₁) ⟨1, by simp⟩).trans
              ?_).trans (lift_snd _ _).symm
            exact (model.programModel.elemEquiv_restage (𝟙 _) _ |>.trans
              (Category.id_comp _)).symm

end EventModel

end Endpoints

/-! ## Structure-preserving functors -/

/-- **A structure-preserving functor out of the classifier.** On event-free
objects it has the chosen products, binder exponentials and operators, and it
sends the pullback of each event-variable projection along each arrow to a
pullback. -/
structure StructuredFunctor where
  carrier : Classifier R equations ⥤ D
  program : Preserving ((authoredEquationPresentation S equations).quotientFunctor ⋙
    programSection R equations ⋙ carrier)
  pullback : ∀ {a b : Classifier R equations} (f : b ⟶ a)
    (j : Judgment (modelAt equations a.base)),
    IsPullback (carrier.map (reindex R equations f j))
      (carrier.map (projection R equations b (mapJudgment (modelMap equations f.base) j)))
      (carrier.map (projection R equations a j)) (carrier.map f)

instance : Category (StructuredFunctor R equations (D := D)) where
  Hom F G := F.carrier ⟶ G.carrier
  id F := 𝟙 F.carrier
  comp f g := f ≫ g
  id_comp := by intros; exact Category.id_comp _
  comp_id := by intros; exact Category.comp_id _
  assoc := by intros; exact Category.assoc _ _ _

namespace StructuredFunctor

variable {R equations} (F : StructuredFunctor R equations (D := D))

/-- The binding model of the functor's program part. -/
abbrev programModel : Model S D :=
  F.program.toModel

/-- The program part identifies equation-related assignments. -/
theorem respects {X Y : Object S} {σ τ : X ⟶ Y}
    (related : (authoredEquationPresentation S equations).homRel σ τ) :
    ((authoredEquationPresentation S equations).quotientFunctor ⋙
      programSection R equations ⋙ F.carrier).map σ =
    ((authoredEquationPresentation S equations).quotientFunctor ⋙
      programSection R equations ⋙ F.carrier).map τ :=
  congrArg (fun u => F.carrier.map ((programSection R equations).map u))
    (_root_.CategoryTheory.Quotient.sound _ related)

/-- The binding model of the program part, satisfying the equations. -/
def programInterpretation :
    SatisfyingInterpretation (D := D) (authoredEquationPresentation S equations) :=
  ⟨⟨F.programModel⟩, F.program.satisfies_of_respects _ F.respects⟩

/-- Program objects are the products of the function objects. -/
noncomputable def programIso (X : Base equations) :
    F.carrier.obj ((programSection R equations).obj X) ≅ F.programModel.family X.as.arities :=
  F.program.famIso X.as.arities

theorem programIso_natural {X Y : Base equations} (u : X ⟶ Y) :
    F.carrier.map ((programSection R equations).map u) ≫ (F.programIso Y).hom =
      (F.programIso X).hom ≫
        (F.programModel.equationClassifyingFunctor _ F.programInterpretation.satisfies).map u := by
  induction u using Quot.ind with
  | _ raw => exact F.program.isoClassifying.hom.naturality raw

/-- **The binding model and event objects of a structure-preserving
functor**: the event object of an arity is the value at its generic event
object, with the endpoints read through the program object. -/
noncomputable def eventModel : EventModel equations (D := D) where
  program := F.programInterpretation
  objects :=
    { event := fun Γ s => F.carrier.obj (eventObject R equations Γ s)
      source := fun Γ s => F.carrier.map (toProgram R equations _) ≫
        (F.programIso (pairBase equations Γ s)).hom ≫ fst _ _
      target := fun Γ s => F.carrier.map (toProgram R equations _) ≫
        (F.programIso (pairBase equations Γ s)).hom ≫ snd _ _ ≫ fst _ _ }

theorem eventEndpoints_eventModel (Γ : Ctx S) (s : S.Srt) :
    F.eventModel.eventEndpoints Γ s =
      F.carrier.map (toProgram R equations (eventObject R equations Γ s)) ≫
        (F.programIso (pairBase equations Γ s)).hom ≫ F.programModel.pairComponents Γ s := by
  apply hom_ext
  · refine (F.eventModel.source_eventEndpoints Γ s).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (lift_fst _ _))))).symm
  · refine (F.eventModel.target_eventEndpoints Γ s).trans ?_
    exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (lift_snd _ _))))).symm

/-- **Adding the first event variable is a pullback under the functor.** -/
theorem isPullback_first (X : Base equations) (n : ℕ)
    (label : Fin (n + 1) → Judgment (modelAt equations X)) :
    IsPullback
      (F.carrier.map (rep R equations (a := object R equations X ⟨⟨n + 1, label⟩⟩) (label 0)
        (leaf R ⟨⟨n + 1, label⟩⟩ 0)))
      (F.carrier.map (dropFirst R equations X n label))
      (F.eventModel.eventEndpoints (label 0).1 (label 0).2.1)
      ((F.carrier.map (toProgram R equations (object R equations X ⟨⟨n, Fin.tail label⟩⟩)) ≫
        (F.programIso X).hom) ≫ F.eventModel.judgmentEndpoints X (label 0)) := by
  let rest := object R equations X ⟨⟨n, Fin.tail label⟩⟩
  let endpoints := judgmentBase equations (label 0)
  let f : rest ⟶ (programSection R equations).obj (pairBase equations (label 0).1 (label 0).2.1) :=
    toProgram R equations rest ≫ (programSection R equations).map endpoints
  have judgmentEq : mapJudgment (modelMap equations f.base)
      (pairJudgment equations (label 0).1 (label 0).2.1) = label 0 :=
    (congrArg (fun u => mapJudgment (modelMap equations u)
      (pairJudgment equations (label 0).1 (label 0).2.1)) (Category.id_comp endpoints)).trans
      (mapJudgment_judgmentBase equations (label 0))
  have contextEq : (events R equations rest).cons R _
      (mapJudgment (modelMap equations f.base) (pairJudgment equations (label 0).1 (label 0).2.1)) =
        (⟨⟨n + 1, label⟩⟩ : Context R (modelAt equations X)) :=
    (congrArg (fun j => Context.cons R _ j ⟨⟨n, Fin.tail label⟩⟩) judgmentEq).trans
      (cons_self_tail R n label).symm
  have square := F.pullback f (pairJudgment equations (label 0).1 (label 0).2.1)
  rw [reindex_eventObject, projection_eq_toProgram] at square
  have moved := Mettapedia.CategoryTheory.IsPullback.of_apex_eq
    (congrArg (fun Γ => F.carrier.obj (object R equations X Γ)) contextEq)
    (Mettapedia.CategoryTheory.Functor.map_heq_of_source F.carrier
      (congrArg (object R equations X) contextEq)
      (rep_heq R equations contextEq judgmentEq (leaf_heq R contextEq HEq.rfl)))
    (Mettapedia.CategoryTheory.Functor.map_heq_of_source F.carrier
      (congrArg (object R equations X) contextEq)
      ((projection_heq R equations rest judgmentEq).trans
        (dropFirst_heq R equations X n label).symm))
    square
  refine moved.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (F.programIso _ ≪≫ F.programModel.pairComponentsIso (label 0).1 (label 0).2.1)
    ((Category.comp_id _).trans (Category.id_comp _).symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm) ?_ ?_
  · exact (F.eventEndpoints_eventModel _ _).symm.trans (Category.id_comp _).symm
  · refine Eq.trans ?_ (Category.id_comp _).symm
    change F.carrier.map (toProgram R equations rest ≫ (programSection R equations).map endpoints) ≫
      (F.programIso _).hom ≫ F.programModel.pairComponents _ _ = _
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
    refine (congrArg (F.carrier.map (toProgram R equations rest) ≫ ·) ?_).trans
      (Category.assoc _ _ _).symm
    refine (Category.assoc _ _ _).symm.trans ?_
    refine (congrArg (· ≫ F.programModel.pairComponents _ _) (F.programIso_natural endpoints)).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    exact congrArg ((F.programIso X).hom ≫ ·) (F.eventModel.programFunctor_judgmentBase (label 0))

/-- **The values of a structure-preserving functor are objects of
valuations.** -/
noncomputable def contextCones (X : Base equations) : F.eventModel.ContextCones X where
  obj n label := F.carrier.obj (object R equations X ⟨⟨n, label⟩⟩)
  program n label :=
    F.carrier.map (toProgram R equations (object R equations X ⟨⟨n, label⟩⟩)) ≫ (F.programIso X).hom
  event n label position := F.carrier.map (rep R equations (a := object R equations X ⟨⟨n, label⟩⟩)
    (label position) (leaf R ⟨⟨n, label⟩⟩ position))
  forget n label := F.carrier.map (dropFirst R equations X n label)
  forget_program n label :=
    (Category.assoc _ _ _).symm.trans (congrArg (· ≫ (F.programIso X).hom)
      ((F.carrier.map_comp _ _).symm.trans
        (congrArg F.carrier.map (dropFirst_toProgram R equations X n label))))
  forget_event n label position :=
    (F.carrier.map_comp _ _).symm.trans
      (congrArg F.carrier.map (dropFirst_comp_rep R equations X n label position))
  isPullback n label := F.isPullback_first X n label
  program_zero label :=
    Iso.isIso_hom (F.carrier.mapIso (@asIso _ _ _ _
      (toProgram R equations (object R equations X ⟨⟨0, label⟩⟩))
      (isIso_toProgram_zero R equations X label)) ≪≫ F.programIso X)

end StructuredFunctor

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

end
