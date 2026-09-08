import Mettapedia.GSLT.LanguageDef.TheoryGraph
import Mettapedia.GSLT.LanguageDef.InstitutionConsequence
import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
import Mathlib.CategoryTheory.FiberedCategory.Grothendieck

/-!
# Satisfying models fibred over the theory graph

A closed theory is not one of its models.  This module keeps the two apart
and records the only transport that exists between them without further
assumptions: models move *backward* along theory translations, by reduct.

The theory graph over model-valued institutions is the Grothendieck
construction of closed theories along the consequence functor.  For a node
`X`, a satisfying model is a model of the node's institution at the theory's
signature that satisfies every theorem.  A theory-graph arrow `f : X ⟶ Y`
consists of a comorphism and a signature morphism that preserves theorems;
the satisfaction conditions of the comorphism and of the target institution
turn the reduct of a `Y`-model along `f` into an `X`-model.  Reducts compose
contravariantly, so satisfying models form a functor `Nodeᵒᵖ ⥤ Cat`, and the
total category of satisfying models is its contravariant Grothendieck
construction.  Its projection to the theory graph is a Grothendieck fibration
whose cartesian lifts are the reducts; there is no covariant transport, and
the canary module exhibits the obstruction.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.TheoryGraphModels

open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.NIKMetalogic
open Mettapedia.Logic

universe uSignature uSignatureHom uSentence uModel uModelHom

/-! ## Theory nodes over model-valued institutions -/

/-- The theory graph over model-valued institutions: closed theories of the
consequence images, as a Grothendieck construction.  The projection to the
consequence-level theory graph is `Grothendieck.pre`. -/
abbrev Node :=
  Grothendieck
    (InstitutionConsequence.consequenceFunctor.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom} ⋙
      TheoryGraph.closedTheories.{uSignature, uSignatureHom, uSentence})

namespace Node

variable (X : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})

/-- The model-valued institution of a node. -/
abbrev logic :
    Institution.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} X.base.Signature :=
  X.base.logic

/-- The closed theory of a node, over the consequence image of its institution. -/
abbrev theory :
    PiInstitution.TheoryObject (InstitutionConsequence.consequenceProjection X.base.logic) :=
  X.fiber

/-- The signature of a node's theory. -/
abbrev signature : X.base.Signature :=
  X.fiber.signature

end Node

/-- A node from an institution object and a closed theory of its consequence
image. -/
def Node.mk' (institution : InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom})
    (theory : PiInstitution.TheoryObject
      (InstitutionConsequence.consequenceProjection institution.logic)) :
    Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  ⟨institution, theory⟩

/-- An arrow from a comorphism, a signature morphism out of the translated
signature, and preservation of the source theorems.  Preservation of the
whole direct image follows from closure. -/
def Node.Hom.mk {source target : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (route : source.base ⟶ target.base)
    (mapSignature : route.mapSignature.obj source.signature ⟶ target.signature)
    (preserves : ∀ {formula}, formula ∈ source.theory.theory.1 →
      target.logic.sentence.map mapSignature (route.mapSentence.app source.signature formula) ∈
        target.theory.theory.1) :
    source ⟶ target where
  base := route
  fiber :=
    { mapSignature := mapSignature
      preserves := by
        intro formula theoremhood
        have transported :=
          (InstitutionConsequence.consequenceProjection target.logic).translation mapSignature _
            (Set.mem_image_of_mem _ theoremhood)
        have closed :
            (InstitutionConsequence.consequenceProjection target.logic).consequence
                target.signature target.theory.theory.1 =
              target.theory.theory.1 :=
          target.theory.theory.2
        rw [← closed]
        refine ((InstitutionConsequence.consequenceProjection target.logic).consequence _).monotone
          ?_ transported
        rintro _ ⟨_, ⟨sourceFormula, sourceMember, rfl⟩, rfl⟩
        exact preserves sourceMember }

/-- The projection of a node to the consequence-level theory graph. -/
abbrev toTheoryGraph :
    Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} ⥤
      TheoryGraph.Object.{uSignature, uSignatureHom, uSentence} :=
  Grothendieck.pre TheoryGraph.closedTheories InstitutionConsequence.consequenceFunctor

/-! ## Satisfying models of a node -/

/-- A model at the theory's signature satisfies the theory when it satisfies
every theorem. -/
def Satisfies (X : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})
    (model : X.logic.model.obj (Opposite.op X.signature)) : Prop :=
  ∀ formula ∈ X.theory.theory.1, X.logic.satisfies X.signature model formula

/-- Satisfying a generated theory is satisfying its axioms: semantic
consequence adds nothing a model of the axioms could miss. -/
theorem satisfies_generated_iff
    (institution : InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence,
      uModel, uModelHom})
    (signature : institution.Signature)
    (axioms : Set (institution.logic.sentence.obj signature))
    (model : institution.logic.model.obj (Opposite.op signature)) :
    Satisfies (Node.mk' institution
        (PiInstitution.generatedTheory
          (InstitutionConsequence.consequenceProjection institution.logic) signature axioms))
        model ↔
      ∀ formula ∈ axioms, institution.logic.satisfies signature model formula := by
  constructor
  · intro satisfies formula axiomMember
    exact satisfies formula
      (((InstitutionConsequence.consequenceProjection institution.logic).consequence
        signature).le_closure axioms axiomMember)
  · intro satisfiesAxioms formula theoremhood
    exact theoremhood model satisfiesAxioms

/-- The satisfying models of a node, as the full subcategory of the
institution's model category at the theory's signature. -/
abbrev Model (X : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :=
  ObjectProperty.FullSubcategory (Satisfies X)

/-! ## Reduct along a theory-graph arrow -/

/-- The reduct of a model along an arrow, as a morphism of model categories:
first the reduct along the signature morphism inside the target institution,
then the comorphism's view of a target model as a source model. -/
def reductHom {X Y : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) :
    Y.logic.model.obj (Opposite.op Y.signature) ⟶ X.logic.model.obj (Opposite.op X.signature) :=
  Y.logic.model.map f.fiber.mapSignature.op ≫ f.base.mapModel.app (Opposite.op X.signature)

/-- The reduct of a satisfying model satisfies the source theory. -/
theorem satisfies_reductHom {X Y : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) (model : Model Y) :
    Satisfies X ((reductHom f).toFunctor.obj model.obj) := by
  intro formula theoremhood
  have preserved :
      (InstitutionConsequence.consequenceProjection Y.logic).sentence.map f.fiber.mapSignature
          ((InstitutionConsequence.comorphismProjection f.base).mapSentence X.signature formula) ∈
        Y.theory.theory.1 :=
    f.fiber.preserves
      (TheoryGraph.mapSentence_mem_directImage
        (InstitutionConsequence.comorphismProjection f.base) X.theory theoremhood)
  have satisfiedTarget := model.property _ preserved
  have reduced :=
    (Y.logic.satisfaction_condition f.fiber.mapSignature model.obj
      (f.base.mapSentence.app X.signature formula)).1 satisfiedTarget
  exact (f.base.satisfaction_condition X.signature _ formula).1 reduced

/-- The reduct functor on satisfying models. -/
def reduct {X Y : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) : Model Y ⥤ Model X :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (reductHom f).toFunctor)
    (fun model => satisfies_reductHom f model)

theorem lift_congr {C : Type*} [Category C] {D : Type*} [Category D]
    (P : ObjectProperty D) {F G : C ⥤ D} (h : F = G)
    (hF : ∀ c, P (F.obj c)) (hG : ∀ c, P (G.obj c)) :
    P.lift F hF = P.lift G hG := by
  subst h
  rfl

/-- The reduct along the identity arrow is the identity on model categories. -/
theorem reductHom_id (X : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :
    reductHom (𝟙 X) = 𝟙 _ := by
  change X.logic.model.map (Grothendieck.Hom.fiber (𝟙 X)).mapSignature.op ≫
      (Institution.Comorphism.identity X.logic).mapModel.app (Opposite.op X.signature) = 𝟙 _
  rw [Grothendieck.id_fiber, TheoryGraph.eqToHom_mapSignature]
  change X.logic.model.map (CategoryStruct.id (Opposite.op X.signature)) ≫
      (Institution.Comorphism.identity X.logic).mapModel.app (Opposite.op X.signature) = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  simp only [Institution.Comorphism.identity, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Functor.leftUnitor_hom_app]
  change X.logic.model.map (CategoryStruct.id (Opposite.op X.signature)) ≫ 𝟙 _ = 𝟙 _
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

/-- Reducts compose contravariantly. -/
theorem reductHom_comp {X Y Z : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    reductHom (f ≫ g) = reductHom g ≫ reductHom f := by
  change Z.logic.model.map (Grothendieck.Hom.fiber (f ≫ g)).mapSignature.op ≫
      (Institution.Comorphism.comp f.base g.base).mapModel.app (Opposite.op X.signature) = _
  rw [Grothendieck.comp_fiber, TheoryGraph.theoryHom_comp_mapSignature,
    TheoryGraph.theoryHom_comp_mapSignature, TheoryGraph.eqToHom_mapSignature]
  change Z.logic.model.map
      (CategoryStruct.id _ ≫
        (TheoryGraph.directImageHom (InstitutionConsequence.comorphismProjection g.base)
          f.fiber).mapSignature ≫ g.fiber.mapSignature).op ≫
      (Functor.whiskerLeft f.base.mapSignature.op g.base.mapModel ≫ f.base.mapModel).app
        (Opposite.op X.signature) = _
  rw [TheoryGraph.directImageHom_mapSignature]
  have naturality :
      Z.logic.model.map (g.base.mapSignature.map f.fiber.mapSignature).op ≫
          g.base.mapModel.app (f.base.mapSignature.op.obj (Opposite.op X.signature)) =
        g.base.mapModel.app (Opposite.op Y.signature) ≫
          Y.logic.model.map f.fiber.mapSignature.op :=
    g.base.mapModel.naturality f.fiber.mapSignature.op
  simp only [reductHom, Category.assoc, Category.id_comp, op_comp,
    CategoryTheory.Functor.map_comp, NatTrans.comp_app, Functor.whiskerLeft_app,
    InstitutionConsequence.comorphismProjection_mapSignature]
  rw [reassoc_of% naturality]

/-- Satisfying models, contravariantly fibred over theory nodes. -/
def modelsOf :
    (Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})ᵒᵖ ⥤ Cat.{uModelHom, uModel} where
  obj X := Cat.of (Model X.unop)
  map f := (reduct f.unop).toCatHom
  map_id X := by
    apply Cat.ext
    change ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (reductHom (𝟙 X.unop)).toFunctor) _ = 𝟭 _
    rw [lift_congr (Satisfies X.unop) (G := ObjectProperty.ι _)
      (by rw [reductHom_id]; rfl) _ (fun model => model.property)]
    rfl
  map_comp f g := by
    apply Cat.ext
    change ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ (reductHom (g.unop ≫ f.unop)).toFunctor) _ =
      reduct f.unop ⋙ reduct g.unop
    rw [lift_congr (Satisfies _)
      (G := ObjectProperty.ι _ ⋙ (reductHom f.unop).toFunctor ⋙ (reductHom g.unop).toFunctor)
      (by rw [reductHom_comp]; rfl) _
      (fun model => satisfies_reductHom g.unop ((reduct f.unop).obj model))]
    rfl

/-! ## The total category of satisfying models -/

/-- Satisfying models as a pseudofunctor on the locally discrete node
category: the input of the contravariant Grothendieck construction. -/
abbrev modelsPseudofunctor :
    Pseudofunctor
      (LocallyDiscrete (Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})ᵒᵖ)
      Cat.{uModelHom, uModel} :=
  modelsOf.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}.toPseudofunctor'

/-- Satisfying models over the theory graph: the contravariant Grothendieck
construction of `modelsOf`.  Objects are a node with a satisfying model;
an arrow over `f : X ⟶ Y` is a model morphism into the reduct along `f`. -/
abbrev SatisfyingModel :=
  Pseudofunctor.CoGrothendieck
    modelsPseudofunctor.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}

/-- Project a satisfying model to its theory node.  This is the fibration of
models over theories: reducts are its cartesian lifts. -/
abbrev toNode :
    SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} ⥤
      Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  Pseudofunctor.CoGrothendieck.forget _

instance toNode_isFibered :
    Functor.IsFibered toNode.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  inferInstanceAs
    (Functor.IsFibered (Pseudofunctor.CoGrothendieck.forget
      modelsPseudofunctor.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}))

/-- Project a satisfying model to the consequence-level theory graph. -/
abbrev toClosedTheory :
    SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} ⥤
      TheoryGraph.Object.{uSignature, uSignatureHom, uSentence} :=
  toNode ⋙ toTheoryGraph

/-- Project a satisfying model to its institution. -/
abbrev toInstitution :
    SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} ⥤
      InstitutionCategory.Object.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  toNode ⋙ Grothendieck.forget _

/-- The models of one node embed as the fibre over that node. -/
abbrev fibre (X : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :
    Model X ⥤ SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  Pseudofunctor.CoGrothendieck.ι
    modelsPseudofunctor.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} X

/-- A satisfying model of a node, as an object of the total category. -/
def SatisfyingModel.mk' (X : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom})
    (model : Model X) :
    SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  ⟨X, model⟩

/-- The theory node of a satisfying model. -/
abbrev SatisfyingModel.node
    (object : SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :
    Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom} :=
  object.base

/-- The model carried by a satisfying model. -/
abbrev SatisfyingModel.model
    (object : SatisfyingModel.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) :
    Model object.node :=
  object.fiber

/-- Positive transport: along any theory-graph arrow, every satisfying model
of the target reduces to a satisfying model of the source, and the reduct is
the cartesian lift of the arrow. -/
def transport {X Y : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) (model : Model Y) :
    SatisfyingModel.mk' X ((reduct f).obj model) ⟶ SatisfyingModel.mk' Y model :=
  Pseudofunctor.CoGrothendieck.cartesianLift
    (F := modelsPseudofunctor.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) model f

theorem transport_base {X Y : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) (model : Model Y) :
    (transport f model).base = f :=
  rfl

instance transport_isHomLift
    {X Y : Node.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}}
    (f : X ⟶ Y) (model : Model Y) :
    Functor.IsHomLift toNode f (transport f model) :=
  Pseudofunctor.CoGrothendieck.isHomLift_cartesianLift
    (F := modelsPseudofunctor.{uSignature, uSignatureHom, uSentence, uModel, uModelHom}) model f

#print axioms modelsOf
#print axioms reductHom_id
#print axioms reductHom_comp
#print axioms satisfies_reductHom
#print axioms transport
#print axioms toNode_isFibered

end Mettapedia.GSLT.LanguageDef.TheoryGraphModels
