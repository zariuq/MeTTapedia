import Mettapedia.TypeTheory.PresheafPiIndexComparison
import Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Types.Limits

/-!
# Pointwise dependent-product limits under presheaf substitution

The dependent future-index equivalence compares not only the indexing
categories but the complete endpoint diagrams read by the pointwise
right-Kan formula. Whenever their limits are available, this yields a
canonical isomorphism between the two pointwise products. Naturality
across context arrows assembles these into a family-level isomorphism
for presheaf substitutions. This is not yet an authored dependent-product
former.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.PresheafPiLimitComparison

open CategoryTheory Limits
open Mettapedia.TypeTheory.CategoryOfElementsBaseChange
open Mettapedia.TypeTheory.PresheafPiIndexComparison

universe u v w wEvidence wResult

variable {Context : Type u} [Category.{v} Context]
variable {source target : Context ⥤ Type w}

/-- The actual pointwise dependent-product diagram after reindexing
the domain and codomain along a natural context substitution. -/
abbrev reindexedPiDiagram (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    (point : source.Elements) :
    reindexedStructuredFutureIndex substitution domain point ⥤ Type wResult :=
  StructuredArrow.proj point
      (CategoryOfElements.π (substitution.mapElements ⋙ domain)) ⋙
    mapPrecompElements substitution.mapElements domain ⋙ codomain

/-- The observed pointwise dependent-product diagram reads the same
codomain family at the substituted source point. -/
abbrev observedPiDiagram (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    (point : source.Elements) :
    structuredFutureIndex substitution domain point ⥤ Type wResult :=
  StructuredArrow.proj (substitution.mapElements.obj point)
    (CategoryOfElements.π domain) ⋙ codomain

/-- The equivalence of dependent future indices identifies their
pointwise codomain diagrams on objects and morphisms. -/
theorem dependentPiDiagram_baseChange
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    (point : source.Elements) :
    (dependentIndexBaseChangeEquivalence substitution domain point).functor ⋙
        observedPiDiagram substitution domain codomain point =
      reindexedPiDiagram substitution domain codomain point := by
  rfl

/-- Precomposing an outgoing route changes the current point but not
the endpoint or evidence read by the reindexed dependent body. -/
theorem reindexedPiDiagram_precompose
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    {earlier later : source.Elements}
    (route : earlier ⟶ later) :
    StructuredArrow.map route ⋙
        reindexedPiDiagram substitution domain codomain earlier =
      reindexedPiDiagram substitution domain codomain later := by
  rfl

/-- The observed pointwise diagram has the same strict endpoint
invariance under precomposition of its current point. -/
theorem observedPiDiagram_precompose
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    {earlier later : source.Elements}
    (route : earlier ⟶ later) :
    StructuredArrow.map (substitution.mapElements.map route) ⋙
        observedPiDiagram substitution domain codomain earlier =
      observedPiDiagram substitution domain codomain later := by
  rfl

/-- Under the standard limit-existence hypotheses, the equivalence
of full evidence-bearing index categories induces an isomorphism of
the actual pointwise dependent products. -/
noncomputable def pointwisePiLimitIso
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    (point : source.Elements)
    [HasLimit (reindexedPiDiagram substitution domain codomain point)]
    [HasLimit (observedPiDiagram substitution domain codomain point)] :
    limit (reindexedPiDiagram substitution domain codomain point) ≅
      limit (observedPiDiagram substitution domain codomain point) :=
  HasLimit.isoOfEquivalence
    (dependentIndexBaseChangeEquivalence substitution domain point)
    (eqToIso (dependentPiDiagram_baseChange substitution domain codomain point))

/-- The inverse comparison evaluates an observed dependent product at
the forward image of an exact reindexed future question. This is its
projection computation rule and retains that question's evidence. -/
theorem pointwisePiLimitIso_inv_projection
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type wResult)
    (point : source.Elements)
    [HasLimit (reindexedPiDiagram substitution domain codomain point)]
    [HasLimit (observedPiDiagram substitution domain codomain point)]
    (item : reindexedStructuredFutureIndex substitution domain point) :
    (pointwisePiLimitIso substitution domain codomain point).inv ≫
        limit.π (reindexedPiDiagram substitution domain codomain point) item =
      limit.π (observedPiDiagram substitution domain codomain point)
        ((dependentIndexBaseChangeEquivalence substitution domain point).functor.obj item) := by
  unfold pointwisePiLimitIso
  rw [HasLimit.isoOfEquivalence_inv_π]
  have diagramProof_refl :
      dependentPiDiagram_baseChange substitution domain codomain point =
        (rfl :
          (dependentIndexBaseChangeEquivalence substitution domain point).functor ⋙
              observedPiDiagram substitution domain codomain point =
            reindexedPiDiagram substitution domain codomain point) :=
    Subsingleton.elim _ _
  rw [diagramProof_refl]
  change limit.π (observedPiDiagram substitution domain codomain point)
      ((dependentIndexBaseChangeEquivalence substitution domain point).functor.obj item) ≫
      𝟙 _ = _
  exact Category.comp_id _

/-- Choosing a result universe large enough for both index categories
discharges the limit-existence hypotheses for ordinary type-valued
dependent bodies. -/
noncomputable def pointwisePiLimitIso_sameUniverse
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    (point : source.Elements) :
    limit (reindexedPiDiagram substitution domain codomain point) ≅
      limit (observedPiDiagram substitution domain codomain point) :=
  pointwisePiLimitIso substitution domain codomain point

/-- The source dependent product as Mathlib's actual pointwise right
Kan extension, with a result universe large enough for its index. -/
noncomputable abbrev reindexedPiFamily
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence)) :
    source.Elements ⥤ Type (max u v w wEvidence) :=
  (CategoryOfElements.π (substitution.mapElements ⋙ domain)).pointwiseRightKanExtension
    (mapPrecompElements substitution.mapElements domain ⋙ codomain)

/-- The target dependent product observed at source contexts. -/
noncomputable abbrev observedPiFamily
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence)) :
    source.Elements ⥤ Type (max u v w wEvidence) :=
  substitution.mapElements ⋙
    (CategoryOfElements.π domain).pointwiseRightKanExtension codomain

/-- The two ways of reaching one observed future question have equal
limit projections. Their index objects are canonically isomorphic;
the coherence isomorphism acts as identity on endpoint evidence. -/
theorem observedPi_projection_coherence
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    {earlier later : source.Elements}
    (route : earlier ⟶ later)
    (item : reindexedStructuredFutureIndex substitution domain later) :
    limit.π (observedPiDiagram substitution domain codomain earlier)
        ((dependentIndexBaseChangeForward substitution domain earlier).obj
          ((StructuredArrow.map route).obj item)) =
      limit.π (observedPiDiagram substitution domain codomain earlier)
        ((StructuredArrow.map (substitution.mapElements.map route)).obj
          ((dependentIndexBaseChangeForward substitution domain later).obj item)) := by
  let coherence := dependentIndexBaseChangeForward_naturalIso
    substitution domain route
  have mappedId :
      (observedPiDiagram substitution domain codomain earlier).map
          (coherence.hom.app item) = 𝟙 _ := by
    change codomain.map
      ((StructuredArrow.proj (substitution.mapElements.obj earlier)
        (CategoryOfElements.π domain)).map (coherence.hom.app item)) = 𝟙 _
    rw [dependentIndexBaseChangeForward_naturalIso_endpoint]
    exact codomain.map_id _
  have coneLaw := limit.w
    (observedPiDiagram substitution domain codomain earlier)
    (coherence.hom.app item)
  rw [mappedId] at coneLaw
  exact (Category.comp_id _).symm.trans coneLaw

/-- The same projection coherence stated through the assembled
equivalence, whose forward functor is definitionally the existing
base-change action. -/
theorem observedPi_projection_coherence_equivalence
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    {earlier later : source.Elements}
    (route : earlier ⟶ later)
    (item : reindexedStructuredFutureIndex substitution domain later) :
    limit.π (observedPiDiagram substitution domain codomain earlier)
        ((dependentIndexBaseChangeEquivalence substitution domain earlier).functor.obj
          ((StructuredArrow.map route).obj item)) =
      limit.π (observedPiDiagram substitution domain codomain earlier)
        ((StructuredArrow.map (substitution.mapElements.map route)).obj
          ((dependentIndexBaseChangeEquivalence substitution domain later).functor.obj item)) := by
  exact observedPi_projection_coherence substitution domain codomain route item

/-- The pointwise right-Kan map at a source context arrow evaluates
the later question by precomposing that arrow. -/
theorem reindexedPiFamily_map_projection
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    {earlier later : source.Elements}
    (route : earlier ⟶ later)
    (item : reindexedStructuredFutureIndex substitution domain later) :
    (reindexedPiFamily substitution domain codomain).map route ≫
        limit.π (reindexedPiDiagram substitution domain codomain later) item =
      limit.π (reindexedPiDiagram substitution domain codomain earlier)
        ((StructuredArrow.map route).obj item) := by
  unfold reindexedPiFamily reindexedPiDiagram
  exact limit.lift_π _ item

/-- The observed right-Kan map has the corresponding projection rule
at the substituted context arrow. -/
theorem observedPiFamily_map_projection
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence))
    {earlier later : source.Elements}
    (route : earlier ⟶ later)
    (item : structuredFutureIndex substitution domain later) :
    (observedPiFamily substitution domain codomain).map route ≫
        limit.π (observedPiDiagram substitution domain codomain later) item =
      limit.π (observedPiDiagram substitution domain codomain earlier)
        ((StructuredArrow.map (substitution.mapElements.map route)).obj item) := by
  unfold observedPiFamily observedPiDiagram
  exact limit.lift_π _ item

section
set_option backward.isDefEq.respectTransparency false
/-- The pointwise dependent-product comparison assembled as a natural
isomorphism of families over the source presheaf context. -/
noncomputable def presheafPiBaseChangeIso
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence)) :
    reindexedPiFamily substitution domain codomain ≅
      observedPiFamily substitution domain codomain :=
  (NatIso.ofComponents
    (fun point =>
      (pointwisePiLimitIso_sameUniverse substitution domain codomain point).symm)
    (by
      intro earlier later route
      apply limit.hom_ext
      intro item
      change
        ((observedPiFamily substitution domain codomain).map route ≫
            (pointwisePiLimitIso substitution domain codomain later).inv) ≫
          limit.π (reindexedPiDiagram substitution domain codomain later) item =
        ((pointwisePiLimitIso substitution domain codomain earlier).inv ≫
            (reindexedPiFamily substitution domain codomain).map route) ≫
          limit.π (reindexedPiDiagram substitution domain codomain later) item
      rw [Category.assoc]
      rw [pointwisePiLimitIso_inv_projection
        substitution domain codomain later item]
      rw [observedPiFamily_map_projection
        substitution domain codomain route
        ((dependentIndexBaseChangeEquivalence substitution domain later).functor.obj item)]
      calc
        _ = limit.π (observedPiDiagram substitution domain codomain earlier)
            ((dependentIndexBaseChangeEquivalence substitution domain earlier).functor.obj
              ((StructuredArrow.map route).obj item)) :=
          (observedPi_projection_coherence_equivalence
            substitution domain codomain route item).symm
        _ = (pointwisePiLimitIso substitution domain codomain earlier).inv ≫
            limit.π (reindexedPiDiagram substitution domain codomain earlier)
              ((StructuredArrow.map route).obj item) :=
          (pointwisePiLimitIso_inv_projection substitution domain codomain
            earlier ((StructuredArrow.map route).obj item)).symm
        _ = (pointwisePiLimitIso substitution domain codomain earlier).inv ≫
            ((reindexedPiFamily substitution domain codomain).map route ≫
              limit.π (reindexedPiDiagram substitution domain codomain later) item) := by
          rw [reindexedPiFamily_map_projection]
        _ = _ := (Category.assoc _ _ _).symm
    )).symm
end

/-- The chosen right Kan extension and Mathlib's pointwise construction
are canonically isomorphic. This keeps the base-change theorem tied to
the existing right-adjoint Π candidate, not a parallel definition. -/
noncomputable def chosenRightKanPointwiseIso
    {A : Type u} [Category.{v} A]
    {B : Type w} [Category.{wEvidence} B]
    (projection : A ⥤ B)
    (body : A ⥤ Type wResult)
    [Functor.HasPointwiseRightKanExtension projection body] :
    projection.rightKanExtension body ≅
      projection.pointwiseRightKanExtension body :=
  (projection.rightKanExtension body).rightKanExtensionUnique
    (projection.rightKanExtensionCounit body)
    (projection.pointwiseRightKanExtension body)
  (projection.pointwiseRightKanExtensionCounit body)

/-- The canonical chosen-to-pointwise comparison preserves the
right-Kan counit, hence does not silently change dependent-function
evaluation when switching between the two constructions. -/
theorem chosenRightKanPointwiseIso_counit
    {A : Type u} [Category.{v} A]
    {B : Type w} [Category.{wEvidence} B]
    (projection : A ⥤ B)
    (body : A ⥤ Type wResult)
    [Functor.HasPointwiseRightKanExtension projection body] :
    Functor.whiskerLeft projection
        (chosenRightKanPointwiseIso projection body).hom ≫
      projection.pointwiseRightKanExtensionCounit body =
        projection.rightKanExtensionCounit body := by
  change Functor.whiskerLeft projection
      ((projection.pointwiseRightKanExtension body).liftOfIsRightKanExtension
        (projection.pointwiseRightKanExtensionCounit body)
        (projection.rightKanExtension body)
        (projection.rightKanExtensionCounit body)) ≫
      projection.pointwiseRightKanExtensionCounit body =
        projection.rightKanExtensionCounit body
  exact (projection.pointwiseRightKanExtension body).liftOfIsRightKanExtension_fac
    (projection.pointwiseRightKanExtensionCounit body)
    (projection.rightKanExtension body)
    (projection.rightKanExtensionCounit body)

/-- The inverse comparison likewise preserves the evaluation counit. -/
theorem chosenRightKanPointwiseIso_inv_counit
    {A : Type u} [Category.{v} A]
    {B : Type w} [Category.{wEvidence} B]
    (projection : A ⥤ B)
    (body : A ⥤ Type wResult)
    [Functor.HasPointwiseRightKanExtension projection body] :
    Functor.whiskerLeft projection
        (chosenRightKanPointwiseIso projection body).inv ≫
      projection.rightKanExtensionCounit body =
        projection.pointwiseRightKanExtensionCounit body := by
  rw [← chosenRightKanPointwiseIso_counit projection body]
  rw [← Category.assoc, ← Functor.whiskerLeft_comp,
    Iso.inv_hom_id, Functor.whiskerLeft_id']
  exact Category.id_comp _

/-- The family-level base-change isomorphism also applies to the
chosen right-Kan dependent products used by the existing semantic
indexed-family construction. -/
noncomputable def chosenPresheafPiBaseChangeIso
    (substitution : source ⟶ target)
    (domain : target.Elements ⥤ Type wEvidence)
    (codomain : domain.Elements ⥤ Type (max u v w wEvidence)) :
    (CategoryOfElements.π (substitution.mapElements ⋙ domain)).rightKanExtension
        (mapPrecompElements substitution.mapElements domain ⋙ codomain) ≅
      substitution.mapElements ⋙
        (CategoryOfElements.π domain).rightKanExtension codomain :=
  (chosenRightKanPointwiseIso
    (CategoryOfElements.π (substitution.mapElements ⋙ domain))
    (mapPrecompElements substitution.mapElements domain ⋙ codomain)).trans
      ((presheafPiBaseChangeIso substitution domain codomain).trans
        (Functor.isoWhiskerLeft substitution.mapElements
          (chosenRightKanPointwiseIso (CategoryOfElements.π domain) codomain).symm))

#print axioms reindexedPiDiagram
#print axioms observedPiDiagram
#print axioms dependentPiDiagram_baseChange
#print axioms reindexedPiDiagram_precompose
#print axioms observedPiDiagram_precompose
#print axioms pointwisePiLimitIso
#print axioms pointwisePiLimitIso_inv_projection
#print axioms pointwisePiLimitIso_sameUniverse
#print axioms reindexedPiFamily
#print axioms observedPiFamily
#print axioms observedPi_projection_coherence
#print axioms observedPi_projection_coherence_equivalence
#print axioms reindexedPiFamily_map_projection
#print axioms observedPiFamily_map_projection
#print axioms presheafPiBaseChangeIso
#print axioms chosenRightKanPointwiseIso
#print axioms chosenRightKanPointwiseIso_counit
#print axioms chosenRightKanPointwiseIso_inv_counit
#print axioms chosenPresheafPiBaseChangeIso

end Mettapedia.TypeTheory.PresheafPiLimitComparison
