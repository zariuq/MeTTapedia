import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedRepresentability
import Mettapedia.OSLF.Syntax.CategoricalBindingStageMaps

/-!
# Maps of models of a rule-local operational presentation

A map of models is a map of the binding models preserving every contextual
assignment, with a map of event objects for each context and sort commuting
with source and target, such that at every stage the induced map of
generalized events commutes with substitution and with every rule action.
Nothing requires a map to cover, to be injective, or to reflect reductions.

At every stage a map of models is a map of classifier targets. It therefore
acts on valuations, naturally along classifier arrows and in the stage, and
induces a natural transformation of classifying functors.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open Mettapedia.OSLF.Binding.CategoricalBindingModel
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalSubstitutionModel
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedSetSemantics
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

universe u v

variable {D : Type u} [Category.{v} D] [CartesianMonoidalCategory D]
variable {S : Signature}

/-! ## Maps of event objects -/

namespace EventObjects

variable {M N P : Model S D}

/-- Maps of event objects over a map of binding models, commuting with
source and target. -/
structure Hom (E : EventObjects M) (F : EventObjects N)
    (h : CategoricalBindingInterpretationMaps.Hom M N) where
  event : ∀ Γ s, E.event Γ s ⟶ F.event Γ s
  source : ∀ Γ s, event Γ s ≫ F.source Γ s = E.source Γ s ≫ h.underlying.power Γ s
  target : ∀ Γ s, event Γ s ≫ F.target Γ s = E.target Γ s ≫ h.underlying.power Γ s

variable {E : EventObjects M} {F : EventObjects N} {G : EventObjects P}
variable {h : CategoricalBindingInterpretationMaps.Hom M N}

/-- Along a map of stage clones moving each generalized element through the
function objects, a generalized event goes to a generalized event over the
moved judgment. -/
def Hom.stageAlong (f : Hom E F h) {Z : D} (φ : FreeBindingClone.Hom (M.stage Z) (N.stage Z))
    (moves : ∀ {Γ : Ctx S} {s : S.Srt} (x : M.ElemOver Z Γ s),
      N.elemEquiv (φ.raw.map x) = M.elemEquiv x ≫ h.underlying.power Γ s)
    (j : Judgment (M.stage Z)) (e : E.StageEvent Z j) : F.StageEvent Z (mapJudgment φ j) :=
  ⟨e.1 ≫ f.event j.1 j.2.1,
    (Category.assoc _ _ _).trans ((congrArg (e.1 ≫ ·) (f.source _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ h.underlying.power _ _) e.2.1).trans (moves _).symm))),
    (Category.assoc _ _ _).trans ((congrArg (e.1 ≫ ·) (f.target _ _)).trans
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ h.underlying.power _ _) e.2.2).trans (moves _).symm)))⟩

/-- The map of generalized events at a stage. -/
noncomputable def Hom.stage (f : Hom E F h) (Z : D) (j : Judgment (M.stage Z))
    (e : E.StageEvent Z j) : F.StageEvent Z (mapJudgment (stageMap h Z) j) :=
  f.stageAlong (stageMap h Z) (elemEquiv_stageElemMap h) j e

theorem Hom.stage_val (f : Hom E F h) (Z : D) (j : Judgment (M.stage Z))
    (e : E.StageEvent Z j) : (f.stage Z j e).1 = e.1 ≫ f.event j.1 j.2.1 :=
  rfl

/-- The identity maps of event objects. -/
def Hom.id (E : EventObjects M) : Hom E E (CategoricalBindingInterpretationMaps.Hom.id M) where
  event _ _ := 𝟙 _
  source _ _ := (Category.id_comp _).trans (Category.comp_id _).symm
  target _ _ := (Category.id_comp _).trans (Category.comp_id _).symm

/-- Composite maps of event objects. -/
def Hom.comp {k : CategoricalBindingInterpretationMaps.Hom N P} (f : Hom E F h) (g : Hom F G k) :
    Hom E G (CategoricalBindingInterpretationMaps.Hom.comp h k) where
  event Γ s := f.event Γ s ≫ g.event Γ s
  source Γ s := by
    rw [Category.assoc, g.source, ← Category.assoc, f.source, Category.assoc]
    rfl
  target Γ s := by
    rw [Category.assoc, g.target, ← Category.assoc, f.target, Category.assoc]
    rfl

end EventObjects

/-! ## Maps of models -/

variable {R : List (LocalRule S)}
variable {M' : List (MetaArity S)} {equations : List (EqAxiom S M')}

namespace CategoricalModel

variable {M N P Q : CategoricalModel R equations (D := D)}

/-- **A map of models**: a map of binding models preserving every contextual
assignment, and maps of event objects commuting with source and target, whose
generalized events commute with substitution and with every rule action at
every stage. -/
structure Hom (M N : CategoricalModel R equations (D := D)) where
  program : M.program ⟶ N.program
  events : M.objects.Hom N.objects program
  stage : ∀ Z : D, SubstitutionModel.IsHom R _ (M.stageModel Z)
    ((N.stageModel Z).pullback (stageMap program Z)) (events.stage Z)

theorem Hom.ext' {f g : Hom M N} (program : f.program = g.program)
    (event : ∀ Γ s, f.events.event Γ s = g.events.event Γ s) : f = g := by
  obtain ⟨fProgram, ⟨fEvent, _, _⟩, _⟩ := f
  obtain ⟨gProgram, ⟨gEvent, _, _⟩, _⟩ := g
  change fProgram = gProgram at program
  subst program
  have same : fEvent = gEvent := funext fun Γ => funext fun s => event Γ s
  subst same
  rfl

/-- Generalized events along the identity clone map are unchanged. -/
theorem isHom_stageAlong_id (M : CategoricalModel R equations (D := D)) (Z : D)
    (φ : FreeBindingClone.Hom (M.programModel.stage Z) (M.programModel.stage Z))
    (moves : ∀ {Γ : Ctx S} {s : S.Srt} (x : M.programModel.ElemOver Z Γ s),
      M.programModel.elemEquiv (φ.raw.map x) = M.programModel.elemEquiv x ≫ 𝟙 _)
    (identity : φ = FreeBindingClone.Hom.id _) :
    SubstitutionModel.IsHom R _ (M.stageModel Z) ((M.stageModel Z).pullback φ)
      ((EventObjects.Hom.id M.objects).stageAlong φ moves) := by
  subst identity
  exact SubstitutionModel.IsHom.congr R _ (fun _ e => Subtype.ext (Category.comp_id e.1).symm)
    (SubstitutionModel.Hom.id R _ (M.stageModel Z)).isHom

/-- The identity map of a model. -/
noncomputable def Hom.id (M : CategoricalModel R equations (D := D)) : Hom M M where
  program := 𝟙 M.program
  events := EventObjects.Hom.id M.objects
  stage Z := isHom_stageAlong_id M Z _ (elemEquiv_stageElemMap _) (stageMap_id M.programModel Z)

/-- Composite generalized events along the composite clone map. -/
theorem isHom_stageAlong_comp (f : Hom M N) (g : Hom N P) (Z : D)
    (φ : FreeBindingClone.Hom (M.programModel.stage Z) (P.programModel.stage Z))
    (moves : ∀ {Γ : Ctx S} {s : S.Srt} (x : M.programModel.ElemOver Z Γ s),
      P.programModel.elemEquiv (φ.raw.map x) =
        M.programModel.elemEquiv x ≫ (f.program.underlying.power Γ s ≫ g.program.underlying.power Γ s))
    (composite : φ = FreeBindingClone.Hom.comp (stageMap f.program Z) (stageMap g.program Z)) :
    SubstitutionModel.IsHom R _ (M.stageModel Z) ((P.stageModel Z).pullback φ)
      ((EventObjects.Hom.comp f.events g.events).stageAlong φ moves) := by
  subst composite
  exact (SubstitutionModel.IsHom.comp_pullback (stageMap f.program Z) (stageMap g.program Z)
    (f.stage Z) (g.stage Z)).congr R _ (fun _ e => Subtype.ext (Category.assoc e.1 _ _))

/-- Composite maps of models. -/
noncomputable def Hom.comp (f : Hom M N) (g : Hom N P) : Hom M P where
  program := f.program ≫ g.program
  events := EventObjects.Hom.comp f.events g.events
  stage Z := isHom_stageAlong_comp f g Z _ (elemEquiv_stageElemMap _)
    (stageMap_comp f.program g.program Z)

noncomputable instance category : Category (CategoricalModel R equations (D := D)) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext' (by change 𝟙 _ ≫ f.program = f.program; exact Category.id_comp _)
    fun _ _ => Category.id_comp _
  comp_id f := Hom.ext' (by change f.program ≫ 𝟙 _ = f.program; exact Category.comp_id _)
    fun _ _ => Category.comp_id _
  assoc f g k := Hom.ext'
    (by change (f.program ≫ g.program) ≫ k.program = f.program ≫ g.program ≫ k.program
        exact Category.assoc _ _ _)
    fun _ _ => Category.assoc _ _ _

@[simp] theorem id_program (M : CategoricalModel R equations (D := D)) :
    (𝟙 M : M ⟶ M).program = 𝟙 M.program :=
  rfl

@[simp] theorem id_event (M : CategoricalModel R equations (D := D)) (Γ : Ctx S) (s : S.Srt) :
    (𝟙 M : M ⟶ M).events.event Γ s = 𝟙 _ :=
  rfl

@[simp] theorem comp_program (f : M ⟶ N) (g : N ⟶ P) :
    (f ≫ g).program = f.program ≫ g.program :=
  rfl

@[simp] theorem comp_event (f : M ⟶ N) (g : N ⟶ P) (Γ : Ctx S) (s : S.Srt) :
    (f ≫ g).events.event Γ s = f.events.event Γ s ≫ g.events.event Γ s :=
  rfl

/-! ## At each stage a map of models is a map of targets -/

/-- The map of stage models. -/
noncomputable def Hom.stageHom (f : Hom M N) (Z : D) :
    SubstitutionModel.Hom R _ (M.stageModel Z) ((N.stageModel Z).pullback (stageMap f.program Z)) :=
  SubstitutionModel.Hom.ofIsHom R _ _ (f.stage Z)

/-- Program classifiers are natural along a map of binding models. -/
theorem programFunctor_map_naturality (f : Hom M N) {X Y : Base equations} (assignment : X ⟶ Y) :
    M.programFunctor.map assignment ≫ Model.familyMap f.program.underlying.power Y.as.arities =
      Model.familyMap f.program.underlying.power X.as.arities ≫ N.programFunctor.map assignment := by
  induction assignment using Quot.ind with
  | _ raw => exact f.program.assignment_comm raw

/-- **At each stage, a map of models is a map of classifier targets.** -/
noncomputable def Hom.targetHom (f : Hom M N) (Z : D) :
    (M.stageTarget Z).Hom (N.stageTarget Z) where
  base := stageMap f.program Z
  evidence := f.stageHom Z
  point x := x ≫ Model.familyMap f.program.underlying.power _
  point_move assignment x :=
    (Category.assoc _ _ _).trans ((congrArg (x ≫ ·) (programFunctor_map_naturality f assignment)).trans
      (Category.assoc _ _ _).symm)
  program_point x := pointProgram_stageMap _ M.program.satisfies N.program.satisfies f.program _ x

/-- Map a valuation at a stage. -/
noncomputable abbrev Hom.valuation (f : Hom M N) {Z : D} {a : Classifier R equations}
    (value : M.StageValuation Z a) : N.StageValuation Z a :=
  value.map (f.targetHom Z)

theorem Hom.valuation_event (f : Hom M N) {Z : D} {a : Classifier R equations}
    (value : M.StageValuation Z a) (position : Fin (IntrinsicScopedLocalActedClassifier.events R equations a).listed.length) :
    HEq ((f.valuation value).event position)
      (f.events.stage Z _ (value.event position)) :=
  cast_heq _ _

/-- Mapping valuations commutes with restaging. -/
theorem Hom.valuation_restage (f : Hom M N) {Z Z' : D} (k : Z' ⟶ Z) {a : Classifier R equations}
    (value : M.StageValuation Z a) :
    N.restageValuation k (f.valuation value) = f.valuation (M.restageValuation k value) := by
  apply ClassifierTarget.Valuation.ext' (Category.assoc _ _ _).symm
  intro position
  refine (ClassifierTarget.Valuation.map_map_event _ _ value position).trans ?_
  refine HEq.trans ?_ (ClassifierTarget.Valuation.map_map_event _ _ value position).symm
  refine N.objects.stageEvent_heq ?_ (heq_of_eq (Category.assoc _ _ _).symm)
  exact congrArg (fun φ => mapJudgment φ (mapJudgment
    (M.programModel.pointProgram _ M.program.satisfies _ value.point)
    ((IntrinsicScopedLocalActedClassifier.events R equations a).listed.label position)))
    (stageMap_restage f.program k)

theorem Hom.valuation_id (M : CategoricalModel R equations (D := D)) {Z : D}
    {a : Classifier R equations} (value : M.StageValuation Z a) :
    (Hom.id M).valuation value = value := by
  apply ClassifierTarget.Valuation.ext'
  · exact (congrArg (value.point ≫ ·) (Model.familyMap_id M.programModel _)).trans
      (Category.comp_id _)
  · intro position
    refine ((Hom.id M).valuation_event value position).trans ?_
    refine M.objects.stageEvent_heq ?_ (heq_of_eq (Category.comp_id _))
    exact (congrArg (fun φ => mapJudgment φ _) (stageMap_id M.programModel Z)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)

theorem Hom.valuation_comp (f : Hom M N) (g : Hom N P) {Z : D} {a : Classifier R equations}
    (value : M.StageValuation Z a) :
    (Hom.comp f g).valuation value = g.valuation (f.valuation value) := by
  apply ClassifierTarget.Valuation.ext'
  · exact (congrArg (value.point ≫ ·) (Model.familyMap_comp _ _ _)).trans
      (Category.assoc _ _ _).symm
  · intro position
    refine ((Hom.comp f g).valuation_event value position).trans ?_
    refine HEq.trans ?_ (ClassifierTarget.Valuation.map_map_event _ _ value position).symm
    refine P.objects.stageEvent_heq ?_ (heq_of_eq (Category.assoc _ _ _).symm)
    exact congrArg (fun φ => mapJudgment φ _) (stageMap_comp f.program g.program Z)

/-- A map of models on the valuations of one classifier object. -/
noncomputable def Hom.valuationsMap (f : Hom M N) (a : Classifier R equations) :
    M.valuations a ⟶ N.valuations a where
  app Z := TypeCat.ofHom (fun value => f.valuation value)
  naturality Z Z' k := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact (f.valuation_restage k.unop value).symm

/-- **A map of models is a natural transformation of valuation functors.** -/
noncomputable def Hom.valuationFunctorMap (f : Hom M N) :
    M.valuationFunctor ⟶ N.valuationFunctor where
  app a := f.valuationsMap a
  naturality a b arrow := by
    apply NatTrans.ext
    funext Z
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext value
    exact ClassifierTarget.Valuation.transport_map _ value arrow

theorem Hom.valuationFunctorMap_id (M : CategoricalModel R equations (D := D)) :
    (Hom.id M).valuationFunctorMap = 𝟙 M.valuationFunctor := by
  apply NatTrans.ext
  funext a
  apply NatTrans.ext
  funext Z
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact Hom.valuation_id M value

theorem Hom.valuationFunctorMap_comp (f : Hom M N) (g : Hom N P) :
    (Hom.comp f g).valuationFunctorMap = f.valuationFunctorMap ≫ g.valuationFunctorMap := by
  apply NatTrans.ext
  funext a
  apply NatTrans.ext
  funext Z
  apply TypeCat.Hom.ext
  apply TypeCat.Fun.ext
  funext value
  exact Hom.valuation_comp f g value

variable [HasPullbacks D]

/-- **The classifying natural transformation of a map of models.** -/
noncomputable def classifyingMap (f : M ⟶ N) : M.classifyingFunctor ⟶ N.classifyingFunctor :=
  Mettapedia.CategoryTheory.RepresentableLift.liftMap (Hom.valuationFunctorMap f)

theorem classifyingMap_id (M : CategoricalModel R equations (D := D)) :
    classifyingMap (𝟙 M) = 𝟙 M.classifyingFunctor :=
  (congrArg Mettapedia.CategoryTheory.RepresentableLift.liftMap
    (Hom.valuationFunctorMap_id M)).trans Mettapedia.CategoryTheory.RepresentableLift.liftMap_id

theorem classifyingMap_comp (f : M ⟶ N) (g : N ⟶ P) :
    classifyingMap (f ≫ g) = classifyingMap f ≫ classifyingMap g :=
  (congrArg Mettapedia.CategoryTheory.RepresentableLift.liftMap
    (Hom.valuationFunctorMap_comp f g)).trans
    (Mettapedia.CategoryTheory.RepresentableLift.liftMap_comp _ _)

/-- The classifying transformation moves valuations along the map. -/
theorem homEquiv_classifyingMap (f : M ⟶ N) (a : Classifier R equations) {Z : D}
    (point : Z ⟶ M.classifyingObject a) :
    (N.valuationsRepresentableBy a).homEquiv (point ≫ (classifyingMap f).app a) =
      Hom.valuation f ((M.valuationsRepresentableBy a).homEquiv point) :=
  Mettapedia.CategoryTheory.RepresentableLift.homEquiv_liftMap
    (represented := M.valuationsRepresentableBy) (represented' := N.valuationsRepresentableBy)
    (Hom.valuationFunctorMap f) a point

end CategoricalModel

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedCategoricalModels
