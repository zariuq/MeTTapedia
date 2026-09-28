import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms
import Mettapedia.OSLF.Syntax.IndexedRulePresentationCategory
import Mettapedia.OSLF.Syntax.IndexedRuleAlgebraPullback
import Mettapedia.OSLF.Syntax.LambdaSemanticRulePolynomial
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Lambda binding-clone maps as rule-presentation maps

The authored beta and congruence schemes are interpreted over semantic
binding clones.  A clone map sends their endpoints and recursive premises to
the corresponding judgments in the target clone.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaRulePolynomialMorphism

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.LambdaSemanticRulePolynomial
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open CategoryTheory

universe u v

variable {A : BindingCloneAlgebra.Algebra.{u} sig}
variable {B : BindingCloneAlgebra.Algebra.{v} sig}

private abbrev ShapeImageAt (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (targetJudgment : Judgment B) :=
  Σ target : RuleShape B targetJudgment,
    Σ position : premisePosition target ≃ premisePosition shape,
      PLift (
      ∀ p : premisePosition target,
        premiseJudgment target p =
          mapJudgment h (premiseJudgment shape (position p)))

private noncomputable def image (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → (shape : RuleShape A j) →
      ShapeImageAt h shape (mapJudgment h j)
  | _, .beta body arg => by
      have e : mapJudgment h
          (judgment A (app A (lam A body) arg)
            (LambdaSemanticRulePolynomial.instantiate A body arg)) =
        judgment B (app B (lam B (h.raw.map body)) (h.raw.map arg))
          (LambdaSemanticRulePolynomial.instantiate B
            (h.raw.map body) (h.raw.map arg)) := by
        simp only [mapJudgment, judgment, map_app h, map_lam h,
          map_instantiate h]
      have normal : ShapeImageAt h (RuleShape.beta body arg)
          (judgment B (app B (lam B (h.raw.map body)) (h.raw.map arg))
            (LambdaSemanticRulePolynomial.instantiate B
              (h.raw.map body) (h.raw.map arg))) := by
        refine ⟨.beta (h.raw.map body) (h.raw.map arg),
          Equiv.refl Empty, ⟨?_⟩⟩
        intro p
        exact p.elim
      exact e.symm ▸ normal

  | _, .appCongL source target arg => by
      have e : mapJudgment h
          (judgment A (app A source arg) (app A target arg)) =
        judgment B (app B (h.raw.map source) (h.raw.map arg))
          (app B (h.raw.map target) (h.raw.map arg)) := by
        simp only [mapJudgment, judgment, map_app h]
      have normal : ShapeImageAt h (RuleShape.appCongL source target arg)
          (judgment B (app B (h.raw.map source) (h.raw.map arg))
            (app B (h.raw.map target) (h.raw.map arg))) := by
        refine ⟨.appCongL (h.raw.map source) (h.raw.map target)
          (h.raw.map arg), Equiv.refl Unit, ⟨?_⟩⟩
        intro p
        cases p
        rfl
      exact e.symm ▸ normal
  | _, .appCongR funTerm source target => by
      have e : mapJudgment h
          (judgment A (app A funTerm source) (app A funTerm target)) =
        judgment B (app B (h.raw.map funTerm) (h.raw.map source))
          (app B (h.raw.map funTerm) (h.raw.map target)) := by
        simp only [mapJudgment, judgment, map_app h]
      have normal : ShapeImageAt h (RuleShape.appCongR funTerm source target)
          (judgment B (app B (h.raw.map funTerm) (h.raw.map source))
            (app B (h.raw.map funTerm) (h.raw.map target))) := by
        refine ⟨.appCongR (h.raw.map funTerm) (h.raw.map source)
          (h.raw.map target), Equiv.refl Unit, ⟨?_⟩⟩
        intro p
        cases p
        rfl
      exact e.symm ▸ normal
  | _, .lamCong source target => by
      have e : mapJudgment h (judgment A (lam A source) (lam A target)) =
        judgment B (lam B (h.raw.map source)) (lam B (h.raw.map target)) := by
        simp only [mapJudgment, judgment, map_lam h]
      have normal : ShapeImageAt h (RuleShape.lamCong source target)
          (judgment B (lam B (h.raw.map source))
            (lam B (h.raw.map target))) := by
        refine ⟨.lamCong (h.raw.map source) (h.raw.map target),
          Equiv.refl Unit, ⟨?_⟩⟩
        intro p
        cases p
        rfl
      exact e.symm ▸ normal

private noncomputable def rollImage (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (children : (p : premisePosition shape) →
      (rules B).Fix () (mapJudgment h (premiseJudgment shape p)))
    {targetJudgment : Judgment B}
    (pictured : ShapeImageAt h shape targetJudgment) :
    (rules B).Fix () targetJudgment :=
  .roll pictured.1 (fun p => by
    change (rules B).Fix () (premiseJudgment pictured.1 p)
    exact (pictured.2.2.down p).symm ▸ children (pictured.2.1 p))

private theorem rollImage_cast_heq (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (children : (p : premisePosition shape) →
      (rules B).Fix () (mapJudgment h (premiseJudgment shape p)))
    {j₁ j₂ : Judgment B} (e : j₁ = j₂)
    (pictured : ShapeImageAt h shape j₁) :
    rollImage h shape children (e ▸ pictured) ≍
      rollImage h shape children pictured := by
  cases e
  rfl

private theorem beta_rollImage_heq (h : FreeBindingClone.Hom A B)
    {Γ : Ctx sig} (body : SemTerm A (.term :: Γ))
    (arg : SemTerm A Γ)
    (children : (p : premisePosition (RuleShape.beta body arg)) →
      (rules B).Fix ()
        (mapJudgment h (premiseJudgment (RuleShape.beta body arg) p))) :
    rollImage h (RuleShape.beta body arg) children
      (image h (RuleShape.beta body arg)) ≍
    (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      (polynomial := rules B) (base := ())
      (RuleShape.beta (h.raw.map body) (h.raw.map arg))
      (fun (impossible : Empty) => impossible.elim)) := by
  simp only [image]
  apply HEq.trans (rollImage_cast_heq h _ children _ _)
  apply heq_of_eq
  simp only [rollImage, premisePosition]
  congr 1
  funext impossible
  exact impossible.elim

private theorem shapeImage_fst_cast (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    {j₁ j₂ : Judgment B} (e : j₁ = j₂)
    (x : ShapeImageAt h shape j₁) :
    (e ▸ x).1 = e ▸ x.1 := by
  cases e
  rfl

private theorem image_shape_heq (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → (shape : RuleShape A j) →
      (image h shape).1 ≍ mapShape h shape
  | _, .beta body arg => by
      apply HEq.trans
        (b := RuleShape.beta (h.raw.map body) (h.raw.map arg))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have hright : mapShape h (RuleShape.beta body arg) ≍
            RuleShape.beta (h.raw.map body) (h.raw.map arg) := by
          simp [mapShape]
          exact cast_heq _ _
        exact hright.symm

  | _, .appCongL source target arg => by
      apply HEq.trans
        (b := RuleShape.appCongL (h.raw.map source) (h.raw.map target)
          (h.raw.map arg))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have hright : mapShape h (RuleShape.appCongL source target arg) ≍
            RuleShape.appCongL (h.raw.map source) (h.raw.map target)
              (h.raw.map arg) := by
          simp [mapShape]
          exact cast_heq _ _
        exact hright.symm
  | _, .appCongR funTerm source target => by
      apply HEq.trans
        (b := RuleShape.appCongR (h.raw.map funTerm) (h.raw.map source)
          (h.raw.map target))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have hright : mapShape h (RuleShape.appCongR funTerm source target) ≍
            RuleShape.appCongR (h.raw.map funTerm) (h.raw.map source)
              (h.raw.map target) := by
          simp [mapShape]
          exact cast_heq _ _
        exact hright.symm
  | _, .lamCong source target => by
      apply HEq.trans
        (b := RuleShape.lamCong (h.raw.map source) (h.raw.map target))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have hright : mapShape h (RuleShape.lamCong source target) ≍
            RuleShape.lamCong (h.raw.map source) (h.raw.map target) := by
          simp [mapShape]
          exact cast_heq _ _
        exact hright.symm

/-- The packaged cartesian image selects exactly the earlier semantic rule
constructor; the two index transports agree by heterogeneous equality. -/
theorem image_shape_eq_mapShape (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j) :
    (image h shape).1 = mapShape h shape :=
  eq_of_heq (image_shape_heq h shape)

/-- Interpreting a lambda rule constructor in two stages agrees with
interpreting it along the composed binding-clone map, including all index
transports introduced by the binder-aware operations. -/
private theorem mapShape_cast {A B : BindingCloneAlgebra.Algebra.{u} sig}
    (h : FreeBindingClone.Hom A B) {j k : Judgment A}
    (e : j = k) (shape : RuleShape A j) :
    mapShape h (e ▸ shape) ≍ mapShape h shape := by
  cases e
  rfl
theorem mapShape_comp_heq {A B C : BindingCloneAlgebra.Algebra.{u} sig}
    (f : FreeBindingClone.Hom A B) (g : FreeBindingClone.Hom B C)
    {j : Judgment A} (shape : RuleShape A j) :
    mapShape (FreeBindingClone.Hom.comp f g) shape ≍
      mapShape g (mapShape f shape) := by
  cases shape with
  | beta body arg =>
      let canonical : RuleShape C
          (judgment C (app C (lam C (g.raw.map (f.raw.map body)))
            (g.raw.map (f.raw.map arg)))
            (LambdaSemanticRulePolynomial.instantiate C
              (g.raw.map (f.raw.map body)) (g.raw.map (f.raw.map arg)))) :=
        .beta (g.raw.map (f.raw.map body)) (g.raw.map (f.raw.map arg))
      have left : mapShape (FreeBindingClone.Hom.comp f g)
          (RuleShape.beta body arg) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment f
          (judgment A (app A (lam A body) arg)
            (LambdaSemanticRulePolynomial.instantiate A body arg)) =
          judgment B (app B (lam B (f.raw.map body)) (f.raw.map arg))
            (LambdaSemanticRulePolynomial.instantiate B (f.raw.map body) (f.raw.map arg)) := by
        simp only [mapJudgment, judgment, map_app f, map_lam f, map_instantiate f]
      have hf : mapShape f (RuleShape.beta body arg) ≍
          RuleShape.beta (f.raw.map body) (f.raw.map arg) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape f (RuleShape.beta body arg) =
          e.symm ▸ RuleShape.beta (f.raw.map body) (f.raw.map arg) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape g (RuleShape.beta (f.raw.map body) (f.raw.map arg)) ≍
          canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape g (mapShape f (RuleShape.beta body arg)) ≍ canonical := by
        rw [hfEq]
        exact (mapShape_cast g e.symm _).trans hg
      exact left.trans right.symm
  | appCongL source target arg =>
      let canonical : RuleShape C
          (judgment C
            (app C (g.raw.map (f.raw.map source)) (g.raw.map (f.raw.map arg)))
            (app C (g.raw.map (f.raw.map target)) (g.raw.map (f.raw.map arg)))) :=
        .appCongL (g.raw.map (f.raw.map source))
          (g.raw.map (f.raw.map target)) (g.raw.map (f.raw.map arg))
      have left : mapShape (FreeBindingClone.Hom.comp f g)
          (RuleShape.appCongL source target arg) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment f (judgment A (app A source arg) (app A target arg)) =
          judgment B (app B (f.raw.map source) (f.raw.map arg))
            (app B (f.raw.map target) (f.raw.map arg)) := by
        simp only [mapJudgment, judgment, map_app f]
      have hf : mapShape f (RuleShape.appCongL source target arg) ≍
          RuleShape.appCongL (f.raw.map source) (f.raw.map target)
            (f.raw.map arg) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape f (RuleShape.appCongL source target arg) =
          e.symm ▸ RuleShape.appCongL (f.raw.map source) (f.raw.map target)
            (f.raw.map arg) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape g
          (RuleShape.appCongL (f.raw.map source) (f.raw.map target)
            (f.raw.map arg)) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape g (mapShape f
          (RuleShape.appCongL source target arg)) ≍ canonical := by
        rw [hfEq]
        exact (mapShape_cast g e.symm _).trans hg
      exact left.trans right.symm
  | appCongR funTerm source target =>
      let canonical : RuleShape C
          (judgment C
            (app C (g.raw.map (f.raw.map funTerm)) (g.raw.map (f.raw.map source)))
            (app C (g.raw.map (f.raw.map funTerm)) (g.raw.map (f.raw.map target)))) :=
        .appCongR (g.raw.map (f.raw.map funTerm))
          (g.raw.map (f.raw.map source)) (g.raw.map (f.raw.map target))
      have left : mapShape (FreeBindingClone.Hom.comp f g)
          (RuleShape.appCongR funTerm source target) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment f
          (judgment A (app A funTerm source) (app A funTerm target)) =
          judgment B (app B (f.raw.map funTerm) (f.raw.map source))
            (app B (f.raw.map funTerm) (f.raw.map target)) := by
        simp only [mapJudgment, judgment, map_app f]
      have hf : mapShape f (RuleShape.appCongR funTerm source target) ≍
          RuleShape.appCongR (f.raw.map funTerm) (f.raw.map source)
            (f.raw.map target) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape f (RuleShape.appCongR funTerm source target) =
          e.symm ▸ RuleShape.appCongR (f.raw.map funTerm) (f.raw.map source)
            (f.raw.map target) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape g
          (RuleShape.appCongR (f.raw.map funTerm) (f.raw.map source)
            (f.raw.map target)) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape g (mapShape f
          (RuleShape.appCongR funTerm source target)) ≍ canonical := by
        rw [hfEq]
        exact (mapShape_cast g e.symm _).trans hg
      exact left.trans right.symm
  | lamCong source target =>
      let canonical : RuleShape C
          (judgment C
            (lam C (g.raw.map (f.raw.map source)))
            (lam C (g.raw.map (f.raw.map target)))) :=
        .lamCong (g.raw.map (f.raw.map source))
          (g.raw.map (f.raw.map target))
      have left : mapShape (FreeBindingClone.Hom.comp f g)
          (RuleShape.lamCong source target) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment f (judgment A (lam A source) (lam A target)) =
          judgment B (lam B (f.raw.map source)) (lam B (f.raw.map target)) := by
        simp only [mapJudgment, judgment, map_lam f]
      have hf : mapShape f (RuleShape.lamCong source target) ≍
          RuleShape.lamCong (f.raw.map source) (f.raw.map target) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape f (RuleShape.lamCong source target) =
          e.symm ▸ RuleShape.lamCong (f.raw.map source) (f.raw.map target) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape g
          (RuleShape.lamCong (f.raw.map source) (f.raw.map target)) ≍
            canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape g (mapShape f
          (RuleShape.lamCong source target)) ≍ canonical := by
        rw [hfEq]
        exact (mapShape_cast g e.symm _).trans hg
      exact left.trans right.symm

/-- Every binding-clone interpretation induces a cartesian map of the
authored lambda rule polynomial. Beta has no recursive premise; each
congruence rule retains its unique premise, including LamCong's extended
binder context. -/
noncomputable def polynomialHom (h : FreeBindingClone.Hom A B) :
    IndexedRulePolynomialMorphisms.Hom (rules A) (rules B)
      (fun _ => mapJudgment h) where
  onShape := fun _ _ shape => (image h shape).1
  onPosition := fun _ _ shape => (image h shape).2.1
  onNext := fun _ _ shape p => (image h shape).2.2.down p

/-- The four authored lambda rules form an object in the category of
context-indexed rule presentations. -/
def lambdaPresentation (A : BindingCloneAlgebra.Algebra.{u} sig) :
    IndexedRulePresentationCategory.Presentation Unit where
  Judgment _ := Judgment A
  rules := rules A

/-- A binding-clone interpretation supplies a genuine morphism of its
lambda rule presentations. -/
noncomputable def lambdaPresentationMap
    {A' B' : BindingCloneAlgebra.Algebra.{u} sig}
    (h : FreeBindingClone.Hom A' B') :
    IndexedRulePresentationCategory.Presentation.Map
      (lambdaPresentation A') (lambdaPresentation B') where
  judgment := fun _ => mapJudgment h
  rules := polynomialHom h

/-- The identity binding-clone map retains the authored lambda presentation,
including its beta and congruence premise addresses. -/
theorem lambdaPresentationMap_id
    (A : BindingCloneAlgebra.Algebra.{u} sig) :
    lambdaPresentationMap (FreeBindingClone.Hom.id A) =
      IndexedRulePresentationCategory.Presentation.Map.id
        (lambdaPresentation A) := by
  have judgmentEq :
      (lambdaPresentationMap (FreeBindingClone.Hom.id A)).judgment =
        (IndexedRulePresentationCategory.Presentation.Map.id
          (lambdaPresentation A)).judgment := by
    funext b j
    exact mapJudgment_id A j
  apply IndexedRulePresentationCategory.Presentation.Map.ext judgmentEq
  cases judgmentEq
  apply heq_of_eq
  have shapeEq :
      (lambdaPresentationMap (FreeBindingClone.Hom.id A)).rules.onShape =
        (IndexedRulePresentationCategory.Presentation.Map.id
          (lambdaPresentation A)).rules.onShape := by
    funext b i shape
    cases b
    cases shape <;> rfl
  apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    _ _ shapeEq
  intro b i shape
  cases b
  change Subsingleton (premisePosition shape)
  cases shape <;> dsimp [premisePosition] <;> infer_instance

/-- Composition of binding-clone interpretations composes their maps of
authored lambda rule presentations, including binder-local premise addresses. -/
theorem lambdaPresentationMap_comp {A B C : BindingCloneAlgebra.Algebra.{u} sig}
    (f : FreeBindingClone.Hom A B) (g : FreeBindingClone.Hom B C) :
    lambdaPresentationMap (FreeBindingClone.Hom.comp f g) =
      IndexedRulePresentationCategory.Presentation.Map.comp
        (lambdaPresentationMap f) (lambdaPresentationMap g) := by
  have judgmentEq :
      (lambdaPresentationMap (FreeBindingClone.Hom.comp f g)).judgment =
      (IndexedRulePresentationCategory.Presentation.Map.comp
        (lambdaPresentationMap f) (lambdaPresentationMap g)).judgment := by
    funext b j
    exact mapJudgment_comp f g j
  apply IndexedRulePresentationCategory.Presentation.Map.ext judgmentEq
  cases judgmentEq
  apply heq_of_eq
  have shapeEq :
      (lambdaPresentationMap (FreeBindingClone.Hom.comp f g)).rules.onShape =
      (IndexedRulePresentationCategory.Presentation.Map.comp
        (lambdaPresentationMap f) (lambdaPresentationMap g)).rules.onShape := by
    funext b i shape
    cases b
    change (polynomialHom (FreeBindingClone.Hom.comp f g)).onShape () i shape =
      (polynomialHom g).onShape () (mapJudgment f i)
        ((polynomialHom f).onShape () i shape)
    have hleft :
        (polynomialHom (FreeBindingClone.Hom.comp f g)).onShape () i shape =
          mapShape (FreeBindingClone.Hom.comp f g) shape :=
      image_shape_eq_mapShape (FreeBindingClone.Hom.comp f g) shape
    have hfirst : (polynomialHom f).onShape () i shape = mapShape f shape :=
      image_shape_eq_mapShape f shape
    have hsecond :
        (polynomialHom g).onShape () (mapJudgment f i)
          ((polynomialHom f).onShape () i shape) =
        mapShape g ((polynomialHom f).onShape () i shape) :=
      image_shape_eq_mapShape g _
    rw [hleft, hsecond, hfirst]
    exact eq_of_heq (mapShape_comp_heq f g shape)
  apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions _ _ shapeEq
  intro b i shape
  cases b
  change Subsingleton (premisePosition shape)
  cases shape <;> dsimp [premisePosition] <;> infer_instance

/-- The authored lambda rule presentation varies functorially with semantic
binding clones. Both endpoint judgments and recursive premise addresses are
preserved by identity and composition. -/
noncomputable def lambdaPresentationFunctor :
    BindingCloneAlgebra.Algebra.{u} sig ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj := lambdaPresentation
  map := fun h => lambdaPresentationMap h
  map_id := by
    intro A
    exact lambdaPresentationMap_id A
  map_comp := by
    intro A B C f g
    exact lambdaPresentationMap_comp f g

/-- The resulting interpretation transports full lambda firing histories,
including any recursive evidence beneath a binder. -/
noncomputable def interpretTree (h : FreeBindingClone.Hom A B)
    (j : Judgment A) : (rules A).Fix () j →
      (rules B).Fix () (mapJudgment h j) :=
  (polynomialHom h).mapFix () j

private theorem interpretTree_roll (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (children : (p : premisePosition shape) →
      (rules A).Fix () (premiseJudgment shape p)) :
    interpretTree h j (.roll shape children) =
      rollImage h shape
        (fun p => interpretTree h (premiseJudgment shape p) (children p))
        (image h shape) := by
  rfl

private theorem mapTree_roll (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (children : (p : premisePosition shape) →
      (rules A).Fix () (premiseJudgment shape p)) :
    mapTree h j (.roll shape children) =
      mapTreeLayer h shape
        (fun p => mapTree h (premiseJudgment shape p) (children p)) := by
  rfl


private theorem appCongR_layer_eq (h : FreeBindingClone.Hom A B)
    {Γ : Ctx sig} (funTerm source target : SemTerm A Γ)
    (children : (p : premisePosition (RuleShape.appCongR funTerm source target)) →
      (rules B).Fix ()
        (mapJudgment h
          (premiseJudgment (RuleShape.appCongR funTerm source target) p))) :
    rollImage h (RuleShape.appCongR funTerm source target) children
      (image h (RuleShape.appCongR funTerm source target)) =
    mapTreeLayer h (RuleShape.appCongR funTerm source target) children := by
  apply eq_of_heq
  apply HEq.trans
    (b := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      (polynomial := rules B) (base := ())
      (RuleShape.appCongR (h.raw.map funTerm) (h.raw.map source)
        (h.raw.map target)) (fun _ => children ())))
  · simp only [image]
    apply HEq.trans (rollImage_cast_heq h _ children _ _)
    apply heq_of_eq
    simp only [rollImage, premisePosition]
    congr 1
  · have hright : mapTreeLayer h (RuleShape.appCongR funTerm source target)
        children ≍
      (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (polynomial := rules B) (base := ())
        (RuleShape.appCongR (h.raw.map funTerm) (h.raw.map source)
        (h.raw.map target)) (fun _ => children ())) := by
      simp [mapTreeLayer]
      exact cast_heq _ _
    exact hright.symm

private theorem lamCong_layer_eq (h : FreeBindingClone.Hom A B)
    {Γ : Ctx sig} (source target : SemTerm A (.term :: Γ))
    (children : (p : premisePosition (RuleShape.lamCong source target)) →
      (rules B).Fix ()
        (mapJudgment h
          (premiseJudgment (RuleShape.lamCong source target) p))) :
    rollImage h (RuleShape.lamCong source target) children
      (image h (RuleShape.lamCong source target)) =
    mapTreeLayer h (RuleShape.lamCong source target) children := by
  apply eq_of_heq
  apply HEq.trans
    (b := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      (polynomial := rules B) (base := ())
      (RuleShape.lamCong (h.raw.map source) (h.raw.map target)) (fun _ => children ())))
  · simp only [image]
    apply HEq.trans (rollImage_cast_heq h _ children _ _)
    apply heq_of_eq
    simp only [rollImage, premisePosition]
    congr 1
  · have hright : mapTreeLayer h (RuleShape.lamCong source target)
        children ≍
      (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (polynomial := rules B) (base := ())
        (RuleShape.lamCong (h.raw.map source) (h.raw.map target)) (fun _ => children ())) := by
      simp [mapTreeLayer]
      exact cast_heq _ _
    exact hright.symm

private theorem beta_layer_eq (h : FreeBindingClone.Hom A B)
    {Γ : Ctx sig} (body : SemTerm A (.term :: Γ))
    (arg : SemTerm A Γ)
    (children : (p : premisePosition (RuleShape.beta body arg)) →
      (rules B).Fix ()
        (mapJudgment h (premiseJudgment (RuleShape.beta body arg) p))) :
    rollImage h (RuleShape.beta body arg) children
      (image h (RuleShape.beta body arg)) =
    mapTreeLayer h (RuleShape.beta body arg) children := by
  apply eq_of_heq
  apply HEq.trans (beta_rollImage_heq h body arg children)
  have hright : mapTreeLayer h (RuleShape.beta body arg) children ≍
      (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (polynomial := rules B) (base := ())
        (RuleShape.beta (h.raw.map body) (h.raw.map arg))
        (fun (impossible : Empty) => impossible.elim)) := by
    simp [mapTreeLayer]
    exact cast_heq _ _
  exact hright.symm

private theorem appCongL_layer_eq (h : FreeBindingClone.Hom A B)
    {Γ : Ctx sig} (source target arg : SemTerm A Γ)
    (children : (p : premisePosition (RuleShape.appCongL source target arg)) →
      (rules B).Fix ()
        (mapJudgment h
          (premiseJudgment (RuleShape.appCongL source target arg) p))) :
    rollImage h (RuleShape.appCongL source target arg) children
      (image h (RuleShape.appCongL source target arg)) =
    mapTreeLayer h (RuleShape.appCongL source target arg) children := by
  apply eq_of_heq
  apply HEq.trans
    (b := (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
      (polynomial := rules B) (base := ())
      (RuleShape.appCongL (h.raw.map source) (h.raw.map target)
        (h.raw.map arg)) (fun _ => children ())))
  · simp only [image]
    apply HEq.trans (rollImage_cast_heq h _ children _ _)
    apply heq_of_eq
    simp only [rollImage, premisePosition]
    congr 1
  · have hright : mapTreeLayer h (RuleShape.appCongL source target arg)
        children ≍
      (Mettapedia.TypeTheory.IndexedPolynomial.Fix.roll
        (polynomial := rules B) (base := ())
        (RuleShape.appCongL (h.raw.map source) (h.raw.map target)
          (h.raw.map arg)) (fun _ => children ())) := by
      simp [mapTreeLayer]
      exact cast_heq _ _
    exact hright.symm

/-- The packaged cartesian rule map and the existing semantic interpreter
agree on every authored rule constructor and every family of interpreted
premises, including the premise beneath LamCong's binder. -/
theorem ruleLayer_agrees (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (children : (p : premisePosition shape) →
      (rules B).Fix () (mapJudgment h (premiseJudgment shape p))) :
    rollImage h shape children (image h shape) =
      mapTreeLayer h shape children := by
  cases shape with
  | beta body arg => exact beta_layer_eq h body arg children
  | appCongL source target arg =>
      exact appCongL_layer_eq h source target arg children
  | appCongR funTerm source target =>
      exact appCongR_layer_eq h funTerm source target children
  | lamCong source target =>
      exact lamCong_layer_eq h source target children

/-- The generic free-tree interpretation is the previously constructed
semantic rule-tree interpretation, rather than a second unrelated action. -/
theorem interpretTree_eq_mapTree (h : FreeBindingClone.Hom A B)
    (j : Judgment A) (tree : (rules A).Fix () j) :
    interpretTree h j tree = mapTree h j tree := by
  exact Mettapedia.TypeTheory.IndexedPolynomial.Fix.eliminate (rules A)
    (fun _ j tree => interpretTree h j tree = mapTree h j tree)
    (fun base j shape children ih => by
      cases base
      change rollImage h shape
          (fun p => interpretTree h (premiseJudgment shape p) (children p))
          (image h shape) =
        mapTreeLayer h shape
          (fun p => mapTree h (premiseJudgment shape p) (children p))
      have recEq :
          (fun p => interpretTree h (premiseJudgment shape p) (children p)) =
          (fun p => mapTree h (premiseJudgment shape p) (children p)) := by
        funext p
        exact ih p
      rw [recEq]
      exact ruleLayer_agrees h shape _)
    () j tree

/-- The general relative rule-algebra fold specializes to the established
semantic interpretation of every lambda firing history. -/
theorem relativeFold_lambda_eq_mapTree (h : FreeBindingClone.Hom A B)
    (j : Judgment A) (tree : (rules A).Fix () j) :
    IndexedRuleAlgebraPullback.relativeFold (polynomialHom h)
      (Mettapedia.TypeTheory.IndexedPolynomial.Algebra.initial (rules B))
      () j tree = mapTree h j tree := by
  rw [IndexedRuleAlgebraPullback.relativeFold_initial_eq_mapFix]
  exact interpretTree_eq_mapTree h j tree

/-- A two-stage clone interpretation of a lambda firing history agrees with
composition of the corresponding rule-presentation maps. -/
theorem interpretTree_two_stage
    {C : BindingCloneAlgebra.Algebra sig}
    (f : FreeBindingClone.Hom A B)
    (g : FreeBindingClone.Hom B C)
    (j : Judgment A) (tree : (rules A).Fix () j) :
    ((polynomialHom f).comp (polynomialHom g)).mapFix () j tree =
      interpretTree g (mapJudgment f j) (interpretTree f j tree) :=
  IndexedRulePolynomialMorphisms.Hom.mapFix_comp
    (polynomialHom f) (polynomialHom g) () j tree

/-- The composition law for the generic rule-map action also holds for the
earlier direct semantic interpretation of complete lambda firing histories. -/
theorem mapTree_two_stage
    {C : BindingCloneAlgebra.Algebra sig}
    (f : FreeBindingClone.Hom A B)
    (g : FreeBindingClone.Hom B C)
    (j : Judgment A) (tree : (rules A).Fix () j) :
    ((polynomialHom f).comp (polynomialHom g)).mapFix () j tree =
      mapTree g (mapJudgment f j) (mapTree f j tree) := by
  rw [interpretTree_two_stage]
  rw [interpretTree_eq_mapTree f j tree]
  exact interpretTree_eq_mapTree g (mapJudgment f j) (mapTree f j tree)

/-- The authored least lambda step relation obtains a history in every
semantic binding-clone model through the cartesian polynomial map. -/
theorem sourceStep_to_model
    (h : FreeBindingClone.Hom
      (BindingCloneAlgebra.terms sig) B)
    {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    HasStep B (judgment B (h.raw.map source) (h.raw.map target)) := by
  obtain ⟨tree⟩ := sourceStep_iff_semanticTree.mp step
  exact ⟨interpretTree h
    (judgment (BindingCloneAlgebra.terms sig) source target) tree⟩

/-- In particular, the presented equation model receives each source
derivation together with its complete constructor-and-premise history. -/
theorem sourceStep_to_equation_model
    {M : List (MetaArity sig)} (E : List (EqAxiom sig M))
    {Γ : Ctx sig} {source target : Term sig Γ .term}
    (step : LambdaContextualRung.Step Γ source target) :
    HasStep (BindingEquationQuotientModel.algebra E)
      (judgment (BindingEquationQuotientModel.algebra E)
        (Quotient.mk _ source) (Quotient.mk _ target)) := by
  exact sourceStep_to_model (BindingEquationQuotientModel.projection E) step

/-- The application-congruence rule has one recursive premise while beta
has none, so a cartesian rule map cannot erase that premise by identifying
their position sets. -/
theorem cannot_erase_app_premise {Γ : Ctx sig}
    (body : SemTerm A (.term :: Γ)) (arg : SemTerm A Γ)
    (source target extra : SemTerm A Γ) :
    (premisePosition (RuleShape.beta body arg) ≃
      premisePosition (RuleShape.appCongL source target extra)) → False := by
  intro equivalence
  exact (equivalence.symm ()).elim

#print axioms IndexedRulePolynomialMorphisms.Hom.mapFix_comp
#print axioms IndexedRulePolynomialMorphisms.Hom.mapFix_unique
#print axioms image_shape_eq_mapShape
#print axioms polynomialHom
#print axioms lambdaPresentationMap
#print axioms lambdaPresentationMap_id
#print axioms mapShape_comp_heq
#print axioms lambdaPresentationMap_comp
#print axioms lambdaPresentationFunctor
#print axioms ruleLayer_agrees
#print axioms interpretTree_eq_mapTree
#print axioms relativeFold_lambda_eq_mapTree
#print axioms mapTree_two_stage
#print axioms sourceStep_to_model
#print axioms cannot_erase_app_premise

end Mettapedia.OSLF.Binding.LambdaRulePolynomialMorphism
