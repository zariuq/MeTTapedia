import Mettapedia.OSLF.Syntax.IntrinsicScopedLocalActedFibres
import Mettapedia.CategoryTheory.StrictCoGrothendieck
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# The classifier of a rule-local operational presentation

An object of the classifier is an authored equation context carrying a
finite ordered list of event variables in its equation-class binding model.
An arrow is a class of contextual assignments together with a firing tree for
each target event variable, over the source variables, in the reindexed
event context. Event leaves carry their contextual substitution, and rule
nodes carry only their own rule's metavariables.

The classifier is the contravariant Grothendieck construction of the event
contexts over the equation contexts. Its zero-event objects form the
equation-context category, fully and faithfully.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier

open _root_.CategoryTheory
open _root_.CategoryTheory.Pseudofunctor
open Mettapedia.OSLF.Binding.SecondOrderContext
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalPolynomial
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFiniteContext (Context seeds exactHole Hom)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFibres
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedFree (Tree interpret freeModel)
open Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedBaseChange (pushTree)
open Mettapedia.OSLF.Binding.AuthoredPositionedRulePolynomial (Judgment mapJudgment)

variable {S : Signature} (R : List (LocalRule S))
variable {M : List (MetaArity S)} (equations : List (EqAxiom S M))

/-- Authored equation contexts: second-order contexts modulo the equations. -/
abbrev Base := EquationContexts (authoredEquationPresentation S equations)

/-- The equation-class binding model of an authored equation context. -/
noncomputable abbrev modelAt (X : Base equations) : BindingCloneAlgebra.Algebra.{0} S :=
  (authoredEquationModelAt S equations X.as).algebra

/-- The binding-model map of a class of contextual assignments. -/
noncomputable abbrev modelMap {X Y : Base equations} (assignment : X ⟶ Y) :
    FreeBindingClone.Hom (modelAt equations Y) (modelAt equations X) :=
  authoredEquationModelMapQuot S equations assignment

/-- Event contexts over authored equation contexts, as a pseudofunctor. -/
noncomputable abbrev fibres : Pseudofunctor (LocallyDiscrete (Base equations)ᵒᵖ) Cat.{0, 0} :=
  (authoredLocalActedFibres R equations).toPseudofunctor'

/-- The classifier of the combined program and event presentation. -/
abbrev Classifier := CoGrothendieck (fibres R equations)

/-- An authored equation context with an ordered list of event variables. -/
def object (X : Base equations) (Γ : Context R (modelAt equations X)) :
    Classifier R equations :=
  ⟨X, Γ⟩

/-- A class of contextual assignments with a firing tree for each target
event variable, in the reindexed event context. -/
def arrow {X Y : Base equations} {Γ : Context R (modelAt equations X)}
    {Δ : Context R (modelAt equations Y)} (assignment : X ⟶ Y)
    (events : Γ ⟶ pushContext R (modelMap equations assignment) Δ) :
    object R equations X Γ ⟶ object R equations Y Δ :=
  ⟨assignment, events⟩

/-- Every classifier arrow is exactly a class of contextual assignments and
a simultaneous assignment of firing trees in the reindexed event context. -/
def homEquiv {X Y : Base equations} (Γ : Context R (modelAt equations X))
    (Δ : Context R (modelAt equations Y)) :
    (object R equations X Γ ⟶ object R equations Y Δ) ≃
      Σ assignment : X ⟶ Y,
        (Γ ⟶ pushContext R (modelMap equations assignment) Δ) where
  toFun combined := ⟨combined.base, combined.fiber⟩
  invFun pair := arrow R equations pair.1 pair.2
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## The program section -/

/-- Equation contexts are the classifier objects with no event variables. -/
noncomputable def programSection : Base equations ⥤ Classifier R equations where
  obj X := object R equations X (Context.empty R (modelAt equations X))
  map assignment := arrow R equations assignment (toEmpty R _ _ rfl)
  map_id X := by
    apply CoGrothendieck.Hom.ext
    case hfg₁ => rfl
    case hfg₂ => exact hom_ext_empty R rfl _ _
  map_comp first second := by
    apply CoGrothendieck.Hom.ext
    case hfg₁ => rfl
    case hfg₂ => exact hom_ext_empty R rfl _ _

instance programSection_faithful : (programSection R equations).Faithful where
  map_injective {_ _} _ _ same := congrArg CoGrothendieck.Hom.base same

instance programSection_full : (programSection R equations).Full where
  map_surjective {X Y} combined := by
    refine ⟨combined.base, ?_⟩
    apply CoGrothendieck.Hom.ext
    case hfg₁ => rfl
    case hfg₂ => exact hom_ext_empty R rfl _ _

/-- Forgetting the event variables recovers the equation contexts. -/
theorem programSection_forget :
    programSection R equations ⋙ CoGrothendieck.forget (fibres R equations) =
      𝟭 (Base equations) :=
  rfl

/-! ## Generators -/

/-- The event contexts over one equation context, inside the classifier. -/
noncomputable abbrev inclusion (X : Base equations) :
    Context R (modelAt equations X) ⥤ Classifier R equations :=
  CoGrothendieck.ι (fibres R equations) X

/-- An authored rule occurrence, from its ordered binder-local premises to
its conclusion. -/
noncomputable def constructor (X : Base equations)
    {judgment : Judgment (modelAt equations X)}
    (shape : Shape R (modelAt equations X) judgment) :
    object R equations X ⟨⟨(R.get shape.1.index).2.premises.length,
        childJudgment R (modelAt equations X) shape.1⟩⟩ ⟶
      object R equations X (Context.single R (modelAt equations X) judgment) :=
  (inclusion R equations X).map (constructorArrow R shape)

/-- One event variable used through a contextual substitution. -/
noncomputable def substitution (X : Base equations)
    (judgment : Judgment (modelAt equations X)) {Δ : Ctx S}
    (σ : BindingSubstitutionAlgebra.Environment S
      (modelAt equations X).substitution.Carrier judgment.1 Δ) :
    object R equations X (Context.single R (modelAt equations X) judgment) ⟶
      object R equations X (Context.single R (modelAt equations X)
        (IntrinsicScopedConditionalSubstitution.substJudgment judgment σ)) :=
  (inclusion R equations X).map (substitutionArrow R judgment σ)

/-! ## Composition on trees -/

/-- The event context of a classifier object. -/
abbrev events (a : Classifier R equations) : Context R (modelAt equations a.base) :=
  a.fiber

/-- The tree a composite assigns to a variable is the second arrow's tree,
reindexed along the first assignment, with the first arrow's trees
substituted for its variables. -/
theorem atSlot_comp {a b c : Classifier R equations} (u : a ⟶ b) (v : b ⟶ c)
    (position : Fin (events R equations c).listed.length) :
    HEq (atSlot R (modelAt equations a.base) (u ≫ v).fiber position)
      (interpret R (modelAt equations a.base)
        (seeds R _ (pushContext R (modelMap equations u.base) (events R equations b)))
        (freeModel R _ (seeds R _ (events R equations a))) u.fiber _
        (pushTree R (modelMap equations u.base)
          (pushSeed R (modelMap equations u.base) (events R equations b)) _
          (atSlot R (modelAt equations b.base) v.fiber position))) := by
  rw [Mettapedia.CategoryTheory.StrictCoGrothendieck.comp_fiber]
  refine (atSlot_comp_comp_eqToHom R (modelAt equations a.base) u.fiber
    (pushArrow R (modelMap equations u.base) v.fiber) _
    (position := position) HEq.rfl).trans (heq_of_eq ?_)
  exact (IntrinsicScopedLocalActedFibres.atSlot_comp R _ u.fiber
    (pushArrow R (modelMap equations u.base) v.fiber) position).trans
    (congrArg (interpret R _ _ _ u.fiber _)
      (atSlot_pushArrow R (modelMap equations u.base) v.fiber position))

/-- The identity arrow assigns to each variable its bare use. -/
theorem atSlot_id_heq (a : Classifier R equations)
    (position : Fin (events R equations a).listed.length) :
    HEq (atSlot R _ (𝟙 a : a ⟶ a).fiber position) (leaf R (events R equations a) position) := by
  erw [Mettapedia.CategoryTheory.StrictCoGrothendieck.id_fiber]
  exact atSlot_eqToHom R _ HEq.rfl

/-- Classifier arrows with equal assignments and the same tree at every
target variable are equal. -/
theorem hom_ext_heq {a b : Classifier R equations} {x y : a ⟶ b} (base : x.base = y.base)
    (slots : ∀ position : Fin (events R equations b).listed.length,
      HEq (atSlot R _ x.fiber position) (atSlot R _ y.fiber position)) :
    x = y := by
  apply CoGrothendieck.Hom.ext x y base
  apply hom_ext_slot R _
  intro position
  exact eq_of_heq ((slots position).trans
    (atSlot_comp_eqToHom R _ y.fiber _ (position := position) HEq.rfl).symm)

/-- A fibre arrow keeps its trees in the classifier. -/
theorem atSlot_inclusion (X : Base equations) {Γ Δ : Context R (modelAt equations X)}
    (φ : Γ ⟶ Δ) (position : Fin Δ.listed.length) :
    HEq (atSlot R _ ((inclusion R equations X).map φ).fiber position)
      (atSlot R _ φ position) := by
  erw [Mettapedia.CategoryTheory.StrictCoGrothendieck.ι_map_fiber]
  exact atSlot_comp_eqToHom R _ φ _ HEq.rfl

theorem modelMap_id (X : Base equations) :
    modelMap equations (𝟙 X) = FreeBindingClone.Hom.id (modelAt equations X) :=
  (authoredEquationQuotientModelPresheaf S equations).map_id (Opposite.op X)

theorem modelMap_comp {X Y Z : Base equations} (first : X ⟶ Y) (second : Y ⟶ Z) :
    modelMap equations (first ≫ second) =
      FreeBindingClone.Hom.comp (modelMap equations second) (modelMap equations first) :=
  (authoredEquationQuotientModelPresheaf S equations).map_comp second.op first.op

/-! ## Event-variable projections and their pullbacks -/

/-- Forget the first event variable of a classifier object. -/
noncomputable def projection (a : Classifier R equations)
    (judgment : Judgment (modelAt equations a.base)) :
    object R equations a.base ((events R equations a).cons R _ judgment) ⟶ a :=
  (inclusion R equations a.base).map
    (IntrinsicScopedLocalActedFibres.weaken R judgment (events R equations a))

/-- After the projection, each variable reads the tree of the corresponding
later variable. -/
theorem atSlot_comp_projection {a c : Classifier R equations}
    {judgment : Judgment (modelAt equations a.base)}
    (x : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment))
    (position : Fin (events R equations a).listed.length) :
    HEq (atSlot R _ (x ≫ projection R equations a judgment).fiber position)
      (atSlot R _ x.fiber position.succ) := by
  have judgmentEq : mapJudgment (modelMap equations (𝟙 a.base))
      ((events R equations a).listed.label position) =
        (events R equations a).listed.label position :=
    (congrArg (fun h => mapJudgment h ((events R equations a).listed.label position))
      (modelMap_id equations a.base)).trans
      (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)
  refine (atSlot_comp R equations x (projection R equations a judgment) position).trans ?_
  refine (interpret_heq R _ x.fiber
    (congrArg (mapJudgment (modelMap equations x.base)) judgmentEq)
    (pushTree_heq R (modelMap equations x.base)
      (pushSeed R (modelMap equations x.base) ((events R equations a).cons R _ judgment))
      judgmentEq
      ((atSlot_inclusion R equations a.base
          (IntrinsicScopedLocalActedFibres.weaken R judgment (events R equations a))
          position).trans
        (heq_of_eq (atSlot_weaken R judgment (events R equations a) position))))).trans ?_
  exact heq_of_eq ((congrArg (interpret R _ _ _ x.fiber _)
    (pushTree_leaf R (modelMap equations x.base) ((events R equations a).cons R _ judgment)
      position.succ)).trans (interpret_leaf R x.fiber position.succ))

/-- Over `f`, the extension by the reindexed judgment maps to the extension
by the original judgment: the new variable goes to the new variable, and the
others follow `f`. -/
noncomputable def reindexEvents {a b : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base)) :
    (events R equations b).cons R _ (mapJudgment (modelMap equations f.base) judgment) ⟶
      pushContext R (modelMap equations f.base) ((events R equations a).cons R _ judgment) :=
  ofSlots R _ (Fin.cons
    (α := fun position => Tree R (modelAt equations b.base)
      (seeds R _ ((events R equations b).cons R _
        (mapJudgment (modelMap equations f.base) judgment)))
      ((pushContext R (modelMap equations f.base)
        ((events R equations a).cons R _ judgment)).listed.label position))
    (leaf R ((events R equations b).cons R _
      (mapJudgment (modelMap equations f.base) judgment)) (first R _ (events R equations b)))
    (fun position => atSlot R _
      (IntrinsicScopedLocalActedFibres.weaken R (mapJudgment (modelMap equations f.base) judgment)
        (events R equations b) ≫ f.fiber) position))

/-- The reindexing arrow over `f`. -/
noncomputable def reindex {a b : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base)) :
    object R equations b.base ((events R equations b).cons R _
        (mapJudgment (modelMap equations f.base) judgment)) ⟶
      object R equations a.base ((events R equations a).cons R _ judgment) :=
  arrow R equations f.base (reindexEvents R equations f judgment)

theorem atSlot_reindexEvents_first {a b : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base)) :
    atSlot R _ (reindexEvents R equations f judgment) (first R judgment (events R equations a)) =
      leaf R ((events R equations b).cons R _ (mapJudgment (modelMap equations f.base) judgment))
        (first R _ (events R equations b)) := by
  unfold reindexEvents
  exact atSlot_ofSlots R _ _ _

theorem atSlot_reindexEvents_succ {a b : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base))
    (position : Fin (events R equations a).listed.length) :
    atSlot R _ (reindexEvents R equations f judgment) position.succ =
      atSlot R _ (IntrinsicScopedLocalActedFibres.weaken R
        (mapJudgment (modelMap equations f.base) judgment) (events R equations b) ≫ f.fiber)
        position := by
  unfold reindexEvents
  exact atSlot_ofSlots R _ _ _

/-- Through the reindexing arrow, the new variable reads the tree of the
new variable. -/
theorem atSlot_comp_reindex_first {a b c : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base))
    (m : c ⟶ object R equations b.base ((events R equations b).cons R _
      (mapJudgment (modelMap equations f.base) judgment))) :
    HEq (atSlot R _ (m ≫ reindex R equations f judgment).fiber
        (first R judgment (events R equations a)))
      (atSlot R _ m.fiber
        (first R (mapJudgment (modelMap equations f.base) judgment) (events R equations b))) := by
  refine (atSlot_comp R equations m (reindex R equations f judgment) _).trans (heq_of_eq ?_)
  change interpret R _ _ _ m.fiber _ (pushTree R _ _ _
    (atSlot R _ (reindexEvents R equations f judgment) (first R judgment (events R equations a)))) = _
  rw [atSlot_reindexEvents_first]
  exact (congrArg (interpret R _ _ _ m.fiber _)
    (pushTree_leaf R (modelMap equations m.base) _ _)).trans (interpret_leaf R m.fiber _)

/-- Arrows into an extended context agree when their assignments, their
trees for the new variable, and their composites with the projection agree. -/
theorem hom_ext_cons {a c : Classifier R equations}
    {judgment : Judgment (modelAt equations a.base)}
    {x y : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment)}
    (base : x.base = y.base)
    (firstSlot : HEq (atSlot R _ x.fiber (first R judgment (events R equations a)))
      (atSlot R _ y.fiber (first R judgment (events R equations a))))
    (rest : x ≫ projection R equations a judgment = y ≫ projection R equations a judgment) :
    x = y := by
  apply hom_ext_heq R equations base
  intro position
  cases position using Fin.cases with
  | zero => exact firstSlot
  | succ i =>
      exact (atSlot_comp_projection R equations x i).symm.trans
        ((congr_arg_heq (fun z : c ⟶ a => atSlot R (modelAt equations c.base) z.fiber i)
          rest).trans
          (atSlot_comp_projection R equations y i))

/-- The reindexing square commutes. -/
theorem reindex_comm {a b : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base)) :
    reindex R equations f judgment ≫ projection R equations a judgment =
      projection R equations b (mapJudgment (modelMap equations f.base) judgment) ≫ f := by
  apply hom_ext_heq R equations
  · change f.base ≫ 𝟙 a.base = 𝟙 b.base ≫ f.base
    rw [Category.comp_id, Category.id_comp]
  · intro position
    have judgmentEq : mapJudgment (modelMap equations (𝟙 b.base))
        ((pushContext R (modelMap equations f.base) (events R equations a)).listed.label
          position) =
        (pushContext R (modelMap equations f.base) (events R equations a)).listed.label
          position :=
      (congrArg (fun h => mapJudgment h _) (modelMap_id equations b.base)).trans
        (AuthoredPositionedRulePolynomial.mapJudgment_id _ _)
    have rhs : HEq
        (atSlot R _ (projection R equations b
          (mapJudgment (modelMap equations f.base) judgment) ≫ f).fiber position)
        (interpret R _ _ _ (IntrinsicScopedLocalActedFibres.weaken R
          (mapJudgment (modelMap equations f.base) judgment) (events R equations b)) _
          (atSlot R _ f.fiber position)) := by
      refine (atSlot_comp R equations (projection R equations b _) f position).trans ?_
      erw [Mettapedia.CategoryTheory.StrictCoGrothendieck.ι_map_fiber]
      exact interpret_comp_eqToHom R _ _ judgmentEq
        (pushTree_heq_of_eq_id R (modelMap_id equations b.base) _ _ _)
    refine (atSlot_comp_projection R equations (reindex R equations f judgment) position).trans ?_
    refine (heq_of_eq (atSlot_reindexEvents_succ R equations f judgment position)).trans ?_
    exact (heq_of_eq (IntrinsicScopedLocalActedFibres.atSlot_comp R _ _ f.fiber position)).trans
      rhs.symm

/-- The assignment of a cone over the reindexing square factors through `f`. -/
theorem cone_base {a b c : Classifier R equations} {f : b ⟶ a}
    {judgment : Judgment (modelAt equations a.base)}
    {fst : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment)}
    {snd : c ⟶ b} (condition : fst ≫ projection R equations a judgment = snd ≫ f) :
    fst.base = snd.base ≫ f.base :=
  (Category.comp_id fst.base).symm.trans (congrArg CoGrothendieck.Hom.base condition)

/-- The new variable of a cone, read in the reindexed extension. -/
theorem cone_judgment {a b c : Classifier R equations} {f : b ⟶ a}
    {judgment : Judgment (modelAt equations a.base)}
    {fst : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment)}
    {snd : c ⟶ b} (condition : fst ≫ projection R equations a judgment = snd ≫ f) :
    mapJudgment (modelMap equations fst.base) judgment =
      mapJudgment (modelMap equations snd.base)
        (mapJudgment (modelMap equations f.base) judgment) := by
  have sameMap : modelMap equations fst.base =
      FreeBindingClone.Hom.comp (modelMap equations f.base) (modelMap equations snd.base) :=
    (congrArg (modelMap equations) (cone_base R equations condition)).trans
      (modelMap_comp equations snd.base f.base)
  exact (congrArg (fun h => mapJudgment h judgment) sameMap).trans
    (AuthoredPositionedRulePolynomial.mapJudgment_comp _ _ judgment)

/-- The factorization of a cone through the reindexing square. -/
noncomputable def coneLift {a b c : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base))
    (fst : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment))
    (snd : c ⟶ b) (condition : fst ≫ projection R equations a judgment = snd ≫ f) :
    c ⟶ object R equations b.base ((events R equations b).cons R _
      (mapJudgment (modelMap equations f.base) judgment)) :=
  arrow R equations snd.base (ofSlots R _ (Fin.cons
    (α := fun position => Tree R (modelAt equations c.base) (seeds R _ (events R equations c))
      ((pushContext R (modelMap equations snd.base) ((events R equations b).cons R _
        (mapJudgment (modelMap equations f.base) judgment))).listed.label position))
    (cast (congrArg (Tree R (modelAt equations c.base) (seeds R _ (events R equations c)))
        (cone_judgment R equations condition))
      (atSlot R _ fst.fiber (first R judgment (events R equations a)) :
        Tree R (modelAt equations c.base) (seeds R _ (events R equations c))
          (mapJudgment (modelMap equations fst.base) judgment)))
    (fun position => atSlot R _ snd.fiber position)))

theorem coneLift_projection {a b c : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base))
    (fst : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment))
    (snd : c ⟶ b) (condition : fst ≫ projection R equations a judgment = snd ≫ f) :
    coneLift R equations f judgment fst snd condition ≫
        projection R equations b (mapJudgment (modelMap equations f.base) judgment) = snd := by
  apply hom_ext_heq R equations (Category.comp_id snd.base)
  intro position
  refine (atSlot_comp_projection R equations _ position).trans (heq_of_eq ?_)
  unfold coneLift
  exact atSlot_ofSlots R _ _ _

theorem coneLift_reindex {a b c : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base))
    (fst : c ⟶ object R equations a.base ((events R equations a).cons R _ judgment))
    (snd : c ⟶ b) (condition : fst ≫ projection R equations a judgment = snd ≫ f) :
    coneLift R equations f judgment fst snd condition ≫ reindex R equations f judgment = fst := by
  apply hom_ext_cons R equations (cone_base R equations condition).symm
  · refine (atSlot_comp_reindex_first R equations f judgment _).trans ?_
    unfold coneLift
    exact (heq_of_eq (atSlot_ofSlots R _ _ _)).trans (cast_heq _ _)
  · rw [Category.assoc, reindex_comm, ← Category.assoc, coneLift_projection, condition]

/-- **Event-variable projections have pullbacks along every arrow**: adding
a variable and reindexing its judgment along `f` is a pullback square. -/
theorem isPullback_reindex {a b : Classifier R equations} (f : b ⟶ a)
    (judgment : Judgment (modelAt equations a.base)) :
    IsPullback (reindex R equations f judgment)
      (projection R equations b (mapJudgment (modelMap equations f.base) judgment))
      (projection R equations a judgment) f := by
  refine IsPullback.of_isLimit (c := Limits.PullbackCone.mk _ _
    (reindex_comm R equations f judgment)) ?_
  refine Limits.PullbackCone.IsLimit.mk (reindex_comm R equations f judgment)
    (fun cone => coneLift R equations f judgment cone.fst cone.snd cone.condition)
    (fun cone => coneLift_reindex R equations f judgment _ _ _)
    (fun cone => coneLift_projection R equations f judgment _ _ _) ?_
  intro cone m throughReindex throughProjection
  have base : m.base = cone.snd.base :=
    (Category.comp_id m.base).symm.trans (congrArg CoGrothendieck.Hom.base throughProjection)
  apply hom_ext_cons R equations base
  · refine (atSlot_comp_reindex_first R equations f judgment m).symm.trans ?_
    refine (congr_arg_heq (fun z : cone.pt ⟶
        object R equations a.base ((events R equations a).cons R _ judgment) =>
      atSlot R (modelAt equations cone.pt.base) z.fiber (first R judgment (events R equations a)))
      throughReindex).trans ?_
    unfold coneLift
    exact ((heq_of_eq (atSlot_ofSlots R _ _ _)).trans (cast_heq _ _)).symm
  · rw [throughProjection, coneLift_projection]

end Mettapedia.OSLF.Binding.IntrinsicScopedLocalActedClassifier
