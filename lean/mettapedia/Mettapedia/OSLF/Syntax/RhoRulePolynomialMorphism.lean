import Mettapedia.OSLF.Syntax.RhoSemanticRulePolynomial
import Mettapedia.OSLF.Syntax.IndexedRulePolynomialMorphisms
import Mettapedia.OSLF.Syntax.IndexedRulePresentationCategory

/-!
# Semantic rho rule constructors under binding-clone maps

A clone interpretation acts on the entire indexed rho rule polynomial.
The cartesian position equivalence keeps COMM and Drop nullary and transports
ParCong's one recursive premise with its complete sorted endpoint judgment.
This is the rule-presentation map needed before folding free firing histories
into varying binding/equation models.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoRulePolynomialMorphism

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.RhoSchema
open Mettapedia.OSLF.Binding.BindingCloneAlgebra
open Mettapedia.OSLF.Binding.RhoSemanticRulePolynomial
open Mettapedia.OSLF.Binding.IndexedRulePolynomialMorphisms
open _root_.CategoryTheory

universe u v

variable {A : BindingCloneAlgebra.Algebra.{u} sig}
variable {B : BindingCloneAlgebra.Algebra.{v} sig}

private abbrev ShapeImageAt (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    (targetJudgment : Judgment B) :=
  Σ target : RuleShape B targetJudgment,
    Σ position : premisePosition target ≃ premisePosition shape,
      PLift (∀ p : premisePosition target,
        premiseJudgment target p =
          mapJudgment h (premiseJudgment shape (position p)))

/-- Package the exact image of one constructor together with its premise
position equivalence and the indexed premise-judgment equation. -/
private noncomputable def image (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → (shape : RuleShape A j) →
      ShapeImageAt h shape (mapJudgment h j)
  | _, .comm channel payload continuation => by
      have endpoints : mapJudgment h
          (judgment A (commSource A channel payload continuation)
            (commTarget A payload continuation)) =
        judgment B
          (commSource B (h.raw.map channel) (h.raw.map payload)
            (h.raw.map continuation))
          (commTarget B (h.raw.map payload)
            (h.raw.map continuation)) := by
        simp only [mapJudgment, judgment, map_commSource h,
          map_commTarget h]
      have normal : ShapeImageAt h
          (RuleShape.comm channel payload continuation)
          (judgment B
            (commSource B (h.raw.map channel) (h.raw.map payload)
              (h.raw.map continuation))
            (commTarget B (h.raw.map payload)
              (h.raw.map continuation))) := by
        refine ⟨.comm (h.raw.map channel) (h.raw.map payload)
          (h.raw.map continuation), Equiv.refl Empty, ⟨?_⟩⟩
        intro impossible
        exact impossible.elim
      exact endpoints.symm ▸ normal

  | _, .drop process => by
      have endpoints : mapJudgment h
          (judgment A (drop A (quote A process)) process) =
        judgment B (drop B (quote B (h.raw.map process)))
          (h.raw.map process) := by
        simp only [mapJudgment, judgment, map_drop h, map_quote h]
      have normal : ShapeImageAt h (RuleShape.drop process)
          (judgment B (drop B (quote B (h.raw.map process)))
            (h.raw.map process)) := by
        refine ⟨.drop (h.raw.map process), Equiv.refl Empty, ⟨?_⟩⟩
        intro impossible
        exact impossible.elim
      exact endpoints.symm ▸ normal
  | _, .parCong source target rest => by
      have endpoints : mapJudgment h
          (judgment A (par A source rest) (par A target rest)) =
        judgment B
          (par B (h.raw.map source) (h.raw.map rest))
          (par B (h.raw.map target) (h.raw.map rest)) := by
        simp only [mapJudgment, judgment, map_par h]
      have normal : ShapeImageAt h (RuleShape.parCong source target rest)
          (judgment B
            (par B (h.raw.map source) (h.raw.map rest))
            (par B (h.raw.map target) (h.raw.map rest))) := by
        refine ⟨.parCong (h.raw.map source) (h.raw.map target)
          (h.raw.map rest), Equiv.refl Unit, ⟨?_⟩⟩
        intro position
        cases position
        rfl
      exact endpoints.symm ▸ normal

private theorem shapeImage_fst_cast (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j)
    {j₁ j₂ : Judgment B} (e : j₁ = j₂)
    (pictured : ShapeImageAt h shape j₁) :
    (e ▸ pictured).1 = e ▸ pictured.1 := by
  cases e
  rfl

private theorem image_shape_heq (h : FreeBindingClone.Hom A B) :
    {j : Judgment A} → (shape : RuleShape A j) →
      (image h shape).1 ≍ mapShape h shape
  | _, .comm channel payload continuation => by
      apply HEq.trans
        (b := RuleShape.comm (h.raw.map channel) (h.raw.map payload)
          (h.raw.map continuation))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have right : mapShape h
            (RuleShape.comm channel payload continuation) ≍
          RuleShape.comm (h.raw.map channel) (h.raw.map payload)
            (h.raw.map continuation) := by
          simp [mapShape]
          exact cast_heq _ _
        exact right.symm
  | _, .drop process => by
      apply HEq.trans (b := RuleShape.drop (h.raw.map process))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have right : mapShape h (RuleShape.drop process) ≍
          RuleShape.drop (h.raw.map process) := by
          simp [mapShape]
          exact cast_heq _ _
        exact right.symm
  | _, .parCong source target rest => by
      apply HEq.trans
        (b := RuleShape.parCong (h.raw.map source) (h.raw.map target)
          (h.raw.map rest))
      · simp only [image, shapeImage_fst_cast]
        exact rec_heq_of_heq _ HEq.rfl
      · have right : mapShape h
            (RuleShape.parCong source target rest) ≍
          RuleShape.parCong (h.raw.map source) (h.raw.map target)
            (h.raw.map rest) := by
          simp [mapShape]
          exact cast_heq _ _
        exact right.symm

theorem image_shape_eq_mapShape (h : FreeBindingClone.Hom A B)
    {j : Judgment A} (shape : RuleShape A j) :
    (image h shape).1 = mapShape h shape :=
  eq_of_heq (image_shape_heq h shape)

private theorem mapShape_cast
    {A B : BindingCloneAlgebra.Algebra.{u} sig}
    (h : FreeBindingClone.Hom A B) {j k : Judgment A}
    (e : j = k) (shape : RuleShape A j) :
    mapShape h (e ▸ shape) ≍ mapShape h shape := by
  cases e
  rfl

/-- Mapping a constructor through two clone interpretations agrees with
mapping it once through their composite, including the context-dependent
COMM target. Heterogeneous equality accounts only for endpoint-index casts. -/
theorem mapShape_comp_heq
    {A B C : BindingCloneAlgebra.Algebra.{u} sig}
    (first : FreeBindingClone.Hom A B)
    (later : FreeBindingClone.Hom B C)
    {j : Judgment A} (shape : RuleShape A j) :
    mapShape (FreeBindingClone.Hom.comp first later) shape ≍
      mapShape later (mapShape first shape) := by
  cases shape with
  | comm channel payload continuation =>
      let canonical : RuleShape C
          (judgment C
            (commSource C (later.raw.map (first.raw.map channel))
              (later.raw.map (first.raw.map payload))
              (later.raw.map (first.raw.map continuation)))
            (commTarget C (later.raw.map (first.raw.map payload))
              (later.raw.map (first.raw.map continuation)))) :=
        .comm (later.raw.map (first.raw.map channel))
          (later.raw.map (first.raw.map payload))
          (later.raw.map (first.raw.map continuation))
      have left : mapShape (FreeBindingClone.Hom.comp first later)
          (RuleShape.comm channel payload continuation) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment first
          (judgment A (commSource A channel payload continuation)
            (commTarget A payload continuation)) =
        judgment B
          (commSource B (first.raw.map channel) (first.raw.map payload)
            (first.raw.map continuation))
          (commTarget B (first.raw.map payload)
            (first.raw.map continuation)) := by
        simp only [mapJudgment, judgment, map_commSource first,
          map_commTarget first]
      have hf : mapShape first
          (RuleShape.comm channel payload continuation) ≍
        RuleShape.comm (first.raw.map channel) (first.raw.map payload)
          (first.raw.map continuation) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape first
          (RuleShape.comm channel payload continuation) =
        e.symm ▸ RuleShape.comm (first.raw.map channel)
          (first.raw.map payload) (first.raw.map continuation) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape later
          (RuleShape.comm (first.raw.map channel)
            (first.raw.map payload) (first.raw.map continuation)) ≍
        canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape later
          (mapShape first (RuleShape.comm channel payload continuation)) ≍
        canonical := by
        rw [hfEq]
        exact (mapShape_cast later e.symm _).trans hg
      exact left.trans right.symm
  | drop process =>
      let canonical : RuleShape C
          (judgment C
            (drop C (quote C (later.raw.map (first.raw.map process))))
            (later.raw.map (first.raw.map process))) :=
        .drop (later.raw.map (first.raw.map process))
      have left : mapShape (FreeBindingClone.Hom.comp first later)
          (RuleShape.drop process) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment first
          (judgment A (drop A (quote A process)) process) =
        judgment B (drop B (quote B (first.raw.map process)))
          (first.raw.map process) := by
        simp only [mapJudgment, judgment, map_drop first,
          map_quote first]
      have hf : mapShape first (RuleShape.drop process) ≍
          RuleShape.drop (first.raw.map process) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape first (RuleShape.drop process) =
          e.symm ▸ RuleShape.drop (first.raw.map process) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape later
          (RuleShape.drop (first.raw.map process)) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape later
          (mapShape first (RuleShape.drop process)) ≍ canonical := by
        rw [hfEq]
        exact (mapShape_cast later e.symm _).trans hg
      exact left.trans right.symm
  | parCong source target rest =>
      let canonical : RuleShape C
          (judgment C
            (par C (later.raw.map (first.raw.map source))
              (later.raw.map (first.raw.map rest)))
            (par C (later.raw.map (first.raw.map target))
              (later.raw.map (first.raw.map rest)))) :=
        .parCong (later.raw.map (first.raw.map source))
          (later.raw.map (first.raw.map target))
          (later.raw.map (first.raw.map rest))
      have left : mapShape (FreeBindingClone.Hom.comp first later)
          (RuleShape.parCong source target rest) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have e : mapJudgment first
          (judgment A (par A source rest) (par A target rest)) =
        judgment B
          (par B (first.raw.map source) (first.raw.map rest))
          (par B (first.raw.map target) (first.raw.map rest)) := by
        simp only [mapJudgment, judgment, map_par first]
      have hf : mapShape first (RuleShape.parCong source target rest) ≍
        RuleShape.parCong (first.raw.map source)
          (first.raw.map target) (first.raw.map rest) := by
        simp [mapShape]
        exact cast_heq _ _
      have hfEq : mapShape first (RuleShape.parCong source target rest) =
          e.symm ▸ RuleShape.parCong (first.raw.map source)
            (first.raw.map target) (first.raw.map rest) := by
        apply eq_of_heq
        exact hf.trans (rec_heq_of_heq e.symm HEq.rfl).symm
      have hg : mapShape later
          (RuleShape.parCong (first.raw.map source)
            (first.raw.map target) (first.raw.map rest)) ≍ canonical := by
        simp [mapShape, canonical]
        exact cast_heq _ _
      have right : mapShape later
          (mapShape first (RuleShape.parCong source target rest)) ≍
        canonical := by
        rw [hfEq]
        exact (mapShape_cast later e.symm _).trans hg
      exact left.trans right.symm
/-- Binding-clone morphisms induce cartesian maps of the semantic rho rule
polynomial: each recursive input is retained exactly once. -/
noncomputable def polynomialHom (h : FreeBindingClone.Hom A B) :
    IndexedRulePolynomialMorphisms.Hom (rules A) (rules B)
      (fun _ => mapJudgment h) where
  onShape := fun _ _ shape => (image h shape).1
  onPosition := fun _ _ shape => (image h shape).2.1
  onNext := fun _ _ shape position => (image h shape).2.2.down position

/-- The source's intrinsic COMM/Drop/ParCong rule scheme is an indexed
presentation over every semantic binding clone. -/
def rhoPresentation (A : BindingCloneAlgebra.Algebra.{u} sig) :
    IndexedRulePresentationCategory.Presentation Unit where
  Judgment _ := Judgment A
  rules := rules A

/-- A clone interpretation transports the whole rho rule presentation,
including the exact number and judgment of recursive premises. -/
noncomputable def rhoPresentationMap
    {A' B' : BindingCloneAlgebra.Algebra.{u} sig}
    (h : FreeBindingClone.Hom A' B') :
    IndexedRulePresentationCategory.Presentation.Map
      (rhoPresentation A') (rhoPresentation B') where
  judgment := fun _ => mapJudgment h
  rules := polynomialHom h

/-- Identity on a binding clone is identity on the full rho rule
presentation, including the ParCong child address. -/
theorem rhoPresentationMap_id
    (A : BindingCloneAlgebra.Algebra.{u} sig) :
    rhoPresentationMap (FreeBindingClone.Hom.id A) =
      IndexedRulePresentationCategory.Presentation.Map.id
        (rhoPresentation A) := by
  have judgmentEq :
      (rhoPresentationMap (FreeBindingClone.Hom.id A)).judgment =
        (IndexedRulePresentationCategory.Presentation.Map.id
          (rhoPresentation A)).judgment := by
    funext b j
    exact mapJudgment_id A j
  apply IndexedRulePresentationCategory.Presentation.Map.ext judgmentEq
  cases judgmentEq
  apply heq_of_eq
  have shapeEq :
      (rhoPresentationMap (FreeBindingClone.Hom.id A)).rules.onShape =
        (IndexedRulePresentationCategory.Presentation.Map.id
          (rhoPresentation A)).rules.onShape := by
    funext b i shape
    cases b
    cases shape <;> rfl
  apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    _ _ shapeEq
  intro b i shape
  cases b
  change Subsingleton (premisePosition shape)
  cases shape <;> dsimp [premisePosition] <;> infer_instance

/-- Consecutive clone interpretations compose on semantic rho constructors
and on every recursive premise address. -/
theorem rhoPresentationMap_comp
    {A B C : BindingCloneAlgebra.Algebra.{u} sig}
    (first : FreeBindingClone.Hom A B)
    (later : FreeBindingClone.Hom B C) :
    rhoPresentationMap (FreeBindingClone.Hom.comp first later) =
      IndexedRulePresentationCategory.Presentation.Map.comp
        (rhoPresentationMap first) (rhoPresentationMap later) := by
  have judgmentEq :
      (rhoPresentationMap (FreeBindingClone.Hom.comp first later)).judgment =
        (IndexedRulePresentationCategory.Presentation.Map.comp
          (rhoPresentationMap first) (rhoPresentationMap later)).judgment := by
    funext b j
    exact mapJudgment_comp first later j
  apply IndexedRulePresentationCategory.Presentation.Map.ext judgmentEq
  cases judgmentEq
  apply heq_of_eq
  have shapeEq :
      (rhoPresentationMap (FreeBindingClone.Hom.comp first later)).rules.onShape =
        (IndexedRulePresentationCategory.Presentation.Map.comp
          (rhoPresentationMap first) (rhoPresentationMap later)).rules.onShape := by
    funext b i shape
    cases b
    change (polynomialHom
        (FreeBindingClone.Hom.comp first later)).onShape () i shape =
      (polynomialHom later).onShape () (mapJudgment first i)
        ((polynomialHom first).onShape () i shape)
    have left :
        (polynomialHom
          (FreeBindingClone.Hom.comp first later)).onShape () i shape =
          mapShape (FreeBindingClone.Hom.comp first later) shape :=
      image_shape_eq_mapShape _ shape
    have middle : (polynomialHom first).onShape () i shape =
        mapShape first shape := image_shape_eq_mapShape first shape
    have right :
        (polynomialHom later).onShape () (mapJudgment first i)
          ((polynomialHom first).onShape () i shape) =
        mapShape later ((polynomialHom first).onShape () i shape) :=
      image_shape_eq_mapShape later _
    rw [left, right, middle]
    exact eq_of_heq (mapShape_comp_heq first later shape)
  apply IndexedRulePolynomialMorphisms.Hom.ext_of_subsingleton_positions
    _ _ shapeEq
  intro b i shape
  cases b
  change Subsingleton (premisePosition shape)
  cases shape <;> dsimp [premisePosition] <;> infer_instance

/-- The intrinsic source rho rule presentation varies functorially over
semantic binding clones. Constructor maps preserve all recursive positions,
so this is stronger than an endpoint-relation translation. -/
noncomputable def rhoPresentationFunctor :
    BindingCloneAlgebra.Algebra.{u} sig ⥤
      IndexedRulePresentationCategory.Presentation Unit where
  obj := rhoPresentation
  map := fun h => rhoPresentationMap h
  map_id := by intro A; exact rhoPresentationMap_id A
  map_comp := by
    intro A B C first later
    exact rhoPresentationMap_comp first later

/-- A clone interpretation acts on every complete proof-relevant rho firing
tree, recursively transporting ParCong premise histories. -/
noncomputable def interpretTree (h : FreeBindingClone.Hom A B)
    (j : Judgment A) :
    (rules A).Fix () j → (rules B).Fix () (mapJudgment h j) :=
  (polynomialHom h).mapFix () j

/-- The initial raw binding clone has a rule-presentation map into the full
source-equation model. It transports every authored COMM continuation and
Drop instance using the same semantic clone interpretation. -/
noncomputable def rawToSourcePresentation :
    IndexedRulePresentationCategory.Presentation.Map
      (rhoPresentation (BindingCloneAlgebra.terms sig))
      (rhoPresentation
        (FreeBindingEquationModel.presented rhoSourceE).algebra) :=
  rhoPresentationMap (FreeBindingClone.interpretHom
    (FreeBindingEquationModel.presented rhoSourceE).algebra)

end Mettapedia.OSLF.Binding.RhoRulePolynomialMorphism
