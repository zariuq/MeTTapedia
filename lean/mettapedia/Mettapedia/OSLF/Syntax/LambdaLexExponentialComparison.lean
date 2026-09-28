import Mettapedia.OSLF.Syntax.LambdaChosenExponential
import Mettapedia.OSLF.Syntax.CartesianModelLexTargetEquivalence
import Mettapedia.OSLF.Syntax.CartesianModelLexPresheafExtension
import Mettapedia.OSLF.Syntax.TermCloneCategoryComparison
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# The authored lambda binder in the generated finite-limit interpretation

The relative finite-limit classifier preserves authored context products. In
its Yoneda-valued interpretation, the generated program presentation is
isomorphic to the actual presheaf of scoped lambda terms. Internal homs can
then be transported across that comparison. This establishes the binder's
chosen function object in this presheaf interpretation; a finite-limit target
is not asserted to carry exponentials merely because it has finite limits.
Operational beta remains a step between distinct raw terms.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.LambdaLexExponentialComparison

open CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalClosed
open CategoryTheory.MonoidalCategory
open Mettapedia.OSLF.CartesianContextModels
open Mettapedia.OSLF.Binding.LambdaCategoricalModel
open Mettapedia.OSLF.Binding.LambdaExponentialComparison
open Mettapedia.OSLF.Binding.LambdaContextualRung
open Mettapedia.OSLF.Binding.ContextualTermAbstraction
open Mettapedia.OSLF.Binding.LambdaPresheafOperations

/-- Contravariance of a chosen internal hom in an isomorphic argument. -/
noncomputable def internalHomPreIso {C : Type*} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] {X Y : C} (i : X ≅ Y) :
    ihom X ≅ ihom Y where
  hom := pre i.inv
  inv := pre i.hom
  hom_inv_id := by
    rw [← pre_map i.hom i.inv, i.hom_inv_id, pre_id]
  inv_hom_id := by
    rw [← pre_map i.inv i.hom, i.inv_hom_id, pre_id]

/-- Internal homs preserve isomorphisms in both arguments, with the expected
contravariance in the domain. This is independent of the lambda signature. -/
noncomputable def internalHomTransportIso {C : Type*} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] {X X' Y Y' : C}
    (domain : X ≅ X') (codomain : Y ≅ Y') :
    (ihom X).obj Y ≅ (ihom X').obj Y' :=
  (ihom X).mapIso codomain ≪≫ (internalHomPreIso domain).app Y'

/-- Evaluation is coherent with transport of the domain and codomain of an
internal hom. The domain is contravariant, so its inverse acts on the input. -/
theorem uncurry_internalHomTransportIso {C : Type*} [Category C]
    [MonoidalCategory C] [MonoidalClosed C] {X X' Y Y' Z : C}
    (domain : X ≅ X') (codomain : Y ≅ Y')
    (body : Z ⟶ (ihom X).obj Y) :
    MonoidalClosed.uncurry
        (body ≫ (internalHomTransportIso domain codomain).hom) =
      (domain.inv ▷ Z) ≫ MonoidalClosed.uncurry body ≫
        codomain.hom := by
  change MonoidalClosed.uncurry
      (body ≫ (ihom X).map codomain.hom ≫
        (pre domain.inv).app Y') = _
  rw [← Category.assoc, uncurry_pre_app, uncurry_natural_right]

private instance : HasFiniteProducts (Syntactic.Ctxt sig) :=
  hasFiniteProducts_of_has_binary_and_terminal

/-- The actual raw lambda context theory interpreted by Yoneda. -/
noncomputable def sourceYonedaModel :
    CartesianTargetInterpretations (Syntactic.Ctxt sig)
      ((Syntactic.Ctxt sig)ᵒᵖ ⥤ Type) :=
  ⟨yoneda, by
    change PreservesFiniteProducts
      (yoneda : Syntactic.Ctxt sig ⥤ (Syntactic.Ctxt sig)ᵒᵖ ⥤ Type)
    infer_instance⟩

/-- The checked finite-limit extension of the authored lambda contexts. -/
noncomputable def sourceYonedaExtension :
    LeftExactTargetInterpretations (Syntactic.Ctxt sig)
      ((Syntactic.Ctxt sig)ᵒᵖ ⥤ Type) :=
  extendPresheafAuthoredModel (Syntactic.Ctxt sig) (Syntactic.Ctxt sig)
    sourceYonedaModel

/-- The generated presentation of one program variable. -/
noncomputable def generatedPrograms : Base ⥤ Type :=
  sourceYonedaExtension.1.obj
    ((authoredContext (Syntactic.Ctxt sig)).obj (Syntactic.single Srt.term))

/-- Generated programs are naturally isomorphic to intrinsically scoped
lambda terms, at every context and under every substitution. -/
noncomputable def programsGeneratedIso : Programs ≅ generatedPrograms :=
  Syntactic.termPresheafYonedaIso sig Srt.term ≪≫
    ((extendPresheafAuthoredModelRestrictionIso
      (Syntactic.Ctxt sig) (Syntactic.Ctxt sig)
      sourceYonedaModel).app (Syntactic.single Srt.term)).symm

/-- The explicit binder-body presheaf is the chosen function object on the
generated program presentation, up to the canonical transport isomorphism. -/
noncomputable def bodiesGeneratedFunctionIso :
    Bodies ≅ (ihom generatedPrograms).obj generatedPrograms :=
  bodyChosenIso ≪≫
    internalHomTransportIso programsGeneratedIso programsGeneratedIso

/-- Transport the product's program coordinate along the generated/source
comparison, leaving the arbitrary test presheaf unchanged. -/
noncomputable def productTransport (test : Base ⥤ Type) :
    FunctorToTypes.prod test Programs ≅
      FunctorToTypes.prod test generatedPrograms :=
  (FunctorToTypes.binaryProductIso test Programs).symm ≪≫
    prod.mapIso (Iso.refl test) programsGeneratedIso ≪≫
      FunctorToTypes.binaryProductIso test generatedPrograms

/-- The tensor/pointwise-product comparison on generated programs is
transported from the existing lambda comparison. -/
noncomputable def generatedTensorToPointwise (test : Base ⥤ Type) :
    generatedPrograms ⊗ test ≅
      FunctorToTypes.prod test generatedPrograms :=
  whiskerRightIso programsGeneratedIso.symm test ≪≫
    tensorToPointwise test ≪≫ productTransport test

/-- The chosen internal hom on generated programs evaluates by transporting
the original chosen evaluation along the natural program comparison. -/
theorem chosenGeneratedUncurry :
    MonoidalClosed.uncurry bodiesGeneratedFunctionIso.hom =
      (programsGeneratedIso.inv ▷ Bodies) ≫
        MonoidalClosed.uncurry bodyChosenIso.hom ≫
          programsGeneratedIso.hom := by
  change MonoidalClosed.uncurry
      (bodyChosenIso.hom ≫
        (internalHomTransportIso programsGeneratedIso
          programsGeneratedIso).hom) = _
  exact uncurry_internalHomTransportIso
    programsGeneratedIso programsGeneratedIso bodyChosenIso.hom

theorem productTransport_fst (test : Base ⥤ Type) :
    (productTransport test).hom ≫ FunctorToTypes.prod.fst =
      FunctorToTypes.prod.fst := by
  simp [productTransport, Category.assoc]

theorem productTransport_snd (test : Base ⥤ Type) :
    (productTransport test).hom ≫ FunctorToTypes.prod.snd =
      FunctorToTypes.prod.snd ≫ programsGeneratedIso.hom := by
  simp [productTransport, Category.assoc]
  rw [← Category.assoc
    (FunctorToTypes.binaryProductIso test Programs).inv
    prod.snd programsGeneratedIso.hom]
  rw [FunctorToTypes.binaryProductIso_inv_comp_snd]

/-- Reindex the arbitrary test coordinate of a generated-program pair. -/
noncomputable def generatedProductPrecompose {F G : Base ⥤ Type} (α : G ⟶ F) :
    FunctorToTypes.prod G generatedPrograms ⟶
      FunctorToTypes.prod F generatedPrograms :=
  FunctorToTypes.prod.lift
    (FunctorToTypes.prod.fst ≫ α) FunctorToTypes.prod.snd

/-- The source/generated comparison respects every map of test presheaves.
This is the coherence needed to transport the binder exponential law, not
just a pointwise family of bijections. -/
theorem productTransport_natural_test {F G : Base ⥤ Type} (α : G ⟶ F) :
    productPrecompose Srt.term α ≫ (productTransport F).hom =
      (productTransport G).hom ≫ generatedProductPrecompose α := by
  have sourceFst :
      productPrecompose Srt.term α ≫ FunctorToTypes.prod.fst =
        FunctorToTypes.prod.fst ≫ α := by
    ext X pair
    rfl
  have sourceSnd :
      productPrecompose Srt.term α ≫ FunctorToTypes.prod.snd =
        FunctorToTypes.prod.snd := by
    ext X pair
    rfl
  have fstEqual :
      (productPrecompose Srt.term α ≫ (productTransport F).hom) ≫
          FunctorToTypes.prod.fst =
        ((productTransport G).hom ≫ generatedProductPrecompose α) ≫
          FunctorToTypes.prod.fst := by
    simp only [Category.assoc, productTransport_fst,
      generatedProductPrecompose, FunctorToTypes.prod.lift_fst]
    rw [← Category.assoc (productTransport G).hom
      FunctorToTypes.prod.fst α, productTransport_fst]
    exact sourceFst
  have sndEqual :
      (productPrecompose Srt.term α ≫ (productTransport F).hom) ≫
          FunctorToTypes.prod.snd =
        ((productTransport G).hom ≫ generatedProductPrecompose α) ≫
          FunctorToTypes.prod.snd := by
    simp only [Category.assoc, productTransport_snd,
      generatedProductPrecompose, FunctorToTypes.prod.lift_snd]
    rw [← Category.assoc, sourceSnd]
  ext X pair
  · exact congrArg (fun arrow => arrow.app X pair) fstEqual
  · exact congrArg (fun arrow => arrow.app X pair) sndEqual

/-- Full exponential hom-set law for the generated program presentation.
The isomorphism is induced by the actual source/generator comparison and the
proved binder-body universal property. -/
noncomputable def generatedCurryEquiv (test : Base ⥤ Type) :
    (FunctorToTypes.prod test generatedPrograms ⟶ generatedPrograms) ≃
      (test ⟶ Bodies) where
  toFun operation :=
    lambdaHomEquiv test
      ((productTransport test).hom ≫ operation ≫ programsGeneratedIso.inv)
  invFun body :=
    (productTransport test).inv ≫
      (lambdaHomEquiv test).symm body ≫ programsGeneratedIso.hom
  left_inv operation := by
    dsimp
    rw [Equiv.symm_apply_apply]
    simp [Category.assoc]
  right_inv body := by
    dsimp
    simp [Category.assoc]

private theorem lambdaHomEquiv_natural_test {F G : Base ⥤ Type}
    (α : G ⟶ F)
    (operation : FunctorToTypes.prod F Programs ⟶ Programs) :
    lambdaHomEquiv G (productPrecompose Srt.term α ≫ operation) =
      α ≫ lambdaHomEquiv F operation :=
  curryBody_natural_test (S := sig) Srt.term Srt.term α operation

/-- Currying in the generated interpretation is natural in its test
presheaf, so reindexing a context before or after abstraction agrees. -/
theorem generatedCurryEquiv_natural_test {F G : Base ⥤ Type}
    (α : G ⟶ F)
    (operation : FunctorToTypes.prod F generatedPrograms ⟶
      generatedPrograms) :
    generatedCurryEquiv G (generatedProductPrecompose α ≫ operation) =
      α ≫ generatedCurryEquiv F operation := by
  change (lambdaHomEquiv G)
      ((productTransport G).hom ≫
        (generatedProductPrecompose α ≫ operation) ≫
          programsGeneratedIso.inv) =
    α ≫ (lambdaHomEquiv F)
      ((productTransport F).hom ≫ operation ≫
        programsGeneratedIso.inv)
  have commute := productTransport_natural_test α
  have operationEq :
      (productTransport G).hom ≫
          (generatedProductPrecompose α ≫ operation) ≫
            programsGeneratedIso.inv =
        productPrecompose Srt.term α ≫
          ((productTransport F).hom ≫ operation ≫
            programsGeneratedIso.inv) := by
    calc
      (productTransport G).hom ≫
          (generatedProductPrecompose α ≫ operation) ≫
            programsGeneratedIso.inv =
        ((productTransport G).hom ≫ generatedProductPrecompose α) ≫
          operation ≫ programsGeneratedIso.inv := by simp [Category.assoc]
      _ = (productPrecompose Srt.term α ≫
          (productTransport F).hom) ≫
            operation ≫ programsGeneratedIso.inv := by rw [commute]
      _ = productPrecompose Srt.term α ≫
          ((productTransport F).hom ≫ operation ≫
            programsGeneratedIso.inv) := by simp [Category.assoc]
  rw [operationEq]
  exact lambdaHomEquiv_natural_test α
    ((productTransport F).hom ≫ operation ≫ programsGeneratedIso.inv)

/-- The inverse operation is natural as well: contextual evaluation
commutes with reindexing before a body is supplied. -/
theorem generatedUncurryEquiv_natural_test {F G : Base ⥤ Type}
    (α : G ⟶ F) (body : F ⟶ Bodies) :
    (generatedCurryEquiv G).symm (α ≫ body) =
      generatedProductPrecompose α ≫
        (generatedCurryEquiv F).symm body := by
  apply (generatedCurryEquiv G).injective
  rw [generatedCurryEquiv_natural_test]
  simp only [Equiv.apply_symm_apply]

/-- Evaluation after abstraction recovers the original contextual operation.
This is the exponential beta law, distinct from authored operational beta. -/
theorem generated_uncurry_curry (test : Base ⥤ Type)
    (operation : FunctorToTypes.prod test generatedPrograms ⟶
      generatedPrograms) :
    (generatedCurryEquiv test).symm
      (generatedCurryEquiv test operation) = operation :=
  (generatedCurryEquiv test).symm_apply_apply operation

/-- Abstraction after evaluation recovers the original body map. This is
exponential eta, not an equation identifying raw lambda syntax trees. -/
theorem generated_curry_uncurry (test : Base ⥤ Type)
    (body : test ⟶ Bodies) :
    generatedCurryEquiv test
      ((generatedCurryEquiv test).symm body) = body :=
  (generatedCurryEquiv test).apply_symm_apply body

/-- Evaluation for the generated presentation, obtained from its universal
property and the identity of the explicit binder-body object. -/
noncomputable def generatedBodyEvaluation :
    FunctorToTypes.prod Bodies generatedPrograms ⟶ generatedPrograms :=
  (generatedCurryEquiv Bodies).symm (𝟙 Bodies)

/-- Generated evaluation is precisely capture-avoiding body application,
transported through the program comparison. -/
theorem generatedBodyEvaluation_eq_transport :
    generatedBodyEvaluation =
      (productTransport Bodies).inv ≫ bodyAt ≫ programsGeneratedIso.hom := by
  change (productTransport Bodies).inv ≫
    (lambdaHomEquiv Bodies).symm (𝟙 Bodies) ≫ programsGeneratedIso.hom = _
  rw [show (lambdaHomEquiv Bodies).symm (𝟙 Bodies) = bodyAt by
    exact exponentialEvaluation_eq_bodyAt]

/-- The chosen internal-hom evaluation and the generated curry/uncurry
evaluation are the same map. Thus the internal-hom comparison respects the
authored capture-avoiding substitution, rather than merely matching objects. -/
theorem chosenGeneratedEvaluation_eq_generatedBodyEvaluation :
    (generatedTensorToPointwise Bodies).inv ≫
        MonoidalClosed.uncurry bodiesGeneratedFunctionIso.hom =
      generatedBodyEvaluation := by
  rw [generatedBodyEvaluation_eq_transport,
    chosenGeneratedUncurry]
  simp only [generatedTensorToPointwise, Iso.trans_inv,
    Category.assoc]
  have cancel :
      (whiskerRightIso programsGeneratedIso.symm Bodies).inv ≫
          (programsGeneratedIso.inv ▷ Bodies) =
        𝟙 (Programs ⊗ Bodies) := by
    simp [whiskerRightIso, ← comp_whiskerRight]
  rw [← Category.assoc
      (whiskerRightIso programsGeneratedIso.symm Bodies).inv
      (programsGeneratedIso.inv ▷ Bodies)
      (MonoidalClosed.uncurry bodyChosenIso.hom ≫
        programsGeneratedIso.hom), cancel]
  simp only [Category.id_comp]
  rw [← Category.assoc (tensorToPointwise Bodies).inv
    (MonoidalClosed.uncurry bodyChosenIso.hom)
      programsGeneratedIso.hom]
  dsimp only [bodyChosenIso]
  rw [chosenEvaluation_eq_bodyAt]

/-- The isomorphism to Mathlib's chosen internal hom is exactly the curry of
the transported capture-avoiding evaluation. This removes any ambiguity
between the explicit binder universal property and the chosen CCC operation. -/
theorem chosenGeneratedBody_is_curry :
    MonoidalClosed.curry
        ((generatedTensorToPointwise Bodies).hom ≫
          generatedBodyEvaluation) =
      bodiesGeneratedFunctionIso.hom := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_curry]
  rw [← chosenGeneratedEvaluation_eq_generatedBodyEvaluation]
  simp

/-- Both endpoints of an authored step are transported through the same
source-to-generated program comparison. -/
noncomputable def endpointTransport :
    Programs ⨯ Programs ≅ generatedPrograms ⨯ generatedPrograms :=
  prod.mapIso programsGeneratedIso programsGeneratedIso

/-- The authored reduction subobject, now on the generated program carrier.
Its domain retains the witness of the original reduction judgment. -/
noncomputable def generatedReductionSubobject :
    Subobject (generatedPrograms ⨯ generatedPrograms) :=
  Subobject.mk (LambdaReductionSubobject.reduction.ι ≫
    productIso.inv ≫ endpointTransport.hom)

/-- A beta redex and its capture-avoiding contractum are endpoints in the
generated interpretation. -/
noncomputable def generatedBetaEndpoints :
    FunctorToTypes.prod Bodies Programs ⟶
      generatedPrograms ⨯ generatedPrograms :=
  betaCategoricalPairs ≫ endpointTransport.hom

/-- The authored operational beta witness still factors through the
generated reduction relation. -/
theorem generated_beta_factors :
    generatedReductionSubobject.Factors generatedBetaEndpoints := by
  apply (Subobject.mk_factors_iff _ _).mpr
  refine ⟨betaWitness, ?_⟩
  change betaWitness ≫
      (LambdaReductionSubobject.reduction.ι ≫ productIso.inv ≫
        endpointTransport.hom) =
    betaCategoricalPairs ≫ endpointTransport.hom
  rw [← Category.assoc, ← Category.assoc, beta_square]
  rfl

/-- Factorization through the generated relation is exactly the scoped
authored reduction judgment at every test context and substitution. -/
theorem generated_factors_iff_steps
    {test : Base ⥤ Type}
    (endpoints : test ⟶ generatedPrograms ⨯ generatedPrograms) :
    generatedReductionSubobject.Factors endpoints ↔
      ∀ (X : Base) (point : test.obj X),
        (match ((endpoints ≫ endpointTransport.inv) ≫ productIso.hom).app X point with
          | ⟨.term, source, target⟩ =>
              LambdaContextualRung.Step X.unop.vars source target) := by
  have original := factors_iff_steps (endpoints ≫ endpointTransport.inv)
  suffices bridge :
      generatedReductionSubobject.Factors endpoints ↔
        reductionSubobject.Factors (endpoints ≫ endpointTransport.inv) by
    exact bridge.trans original
  constructor
  · intro factors
    obtain ⟨lift, equality⟩ := (Subobject.mk_factors_iff _ _).mp factors
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    change lift ≫
      (LambdaReductionSubobject.reduction.ι ≫ productIso.inv ≫
        endpointTransport.hom) = endpoints at equality
    change lift ≫
      (LambdaReductionSubobject.reduction.ι ≫ productIso.inv) =
        endpoints ≫ endpointTransport.inv
    have afterInverse := congrArg
      (fun arrow => arrow ≫ endpointTransport.inv) equality
    calc
      lift ≫ (LambdaReductionSubobject.reduction.ι ≫ productIso.inv) =
          (lift ≫ (LambdaReductionSubobject.reduction.ι ≫ productIso.inv)) ≫
            (endpointTransport.hom ≫ endpointTransport.inv) := by simp
      _ = (lift ≫
          (LambdaReductionSubobject.reduction.ι ≫ productIso.inv ≫
            endpointTransport.hom)) ≫ endpointTransport.inv := by
              rw [← Category.assoc
                (lift ≫ (LambdaReductionSubobject.reduction.ι ≫ productIso.inv))
                endpointTransport.hom endpointTransport.inv]
              apply congrArg (fun arrow => arrow ≫ endpointTransport.inv)
              calc
                (lift ≫ (LambdaReductionSubobject.reduction.ι ≫ productIso.inv)) ≫
                    endpointTransport.hom =
                  lift ≫ ((LambdaReductionSubobject.reduction.ι ≫
                    productIso.inv) ≫ endpointTransport.hom) :=
                      Category.assoc _ _ _
                _ = lift ≫ (LambdaReductionSubobject.reduction.ι ≫
                    productIso.inv ≫ endpointTransport.hom) :=
                      congrArg (fun arrow => lift ≫ arrow)
                        (Category.assoc _ _ _)
      _ = endpoints ≫ endpointTransport.inv := afterInverse
  · intro factors
    obtain ⟨lift, equality⟩ := (Subobject.mk_factors_iff _ _).mp factors
    apply (Subobject.mk_factors_iff _ _).mpr
    refine ⟨lift, ?_⟩
    change lift ≫
      (LambdaReductionSubobject.reduction.ι ≫ productIso.inv) =
        endpoints ≫ endpointTransport.inv at equality
    change lift ≫
      (LambdaReductionSubobject.reduction.ι ≫ productIso.inv ≫
        endpointTransport.hom) = endpoints
    calc
      lift ≫ (LambdaReductionSubobject.reduction.ι ≫ productIso.inv ≫
          endpointTransport.hom) =
        (lift ≫ (LambdaReductionSubobject.reduction.ι ≫ productIso.inv)) ≫
          endpointTransport.hom := by
            calc
              lift ≫ (LambdaReductionSubobject.reduction.ι ≫
                  productIso.inv ≫ endpointTransport.hom) =
                lift ≫ ((LambdaReductionSubobject.reduction.ι ≫
                  productIso.inv) ≫ endpointTransport.hom) :=
                    congrArg (fun arrow => lift ≫ arrow)
                      (Category.assoc _ _ _).symm
              _ = (lift ≫ (LambdaReductionSubobject.reduction.ι ≫
                    productIso.inv)) ≫ endpointTransport.hom :=
                      (Category.assoc _ _ _).symm
      _ = (endpoints ≫ endpointTransport.inv) ≫
          endpointTransport.hom :=
            congrArg (fun arrow => arrow ≫ endpointTransport.hom) equality
      _ = endpoints := by simp [Category.assoc]

/-- Transport through any presheaf isomorphism cannot turn the open authored
beta step into an equation of terms. In particular, this applies to
`programsGeneratedIso`. -/
theorem open_beta_not_equality_after_iso
    {G : Base ⥤ Type} (i : Programs ≅ G) :
    (betaRedex ≫ i.hom).app
      (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) ≠
    (bodyAt ≫ i.hom).app
      (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) := by
  intro equal
  apply open_beta_not_raw_equality
  have cancel (point : Programs.obj
      (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)) :
      i.inv.app
        (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
          (i.hom.app
            (Opposite.op ⟨([Srt.term] : Ctx sig)⟩) point) = point := by
    have h := congrArg
      (fun transformation => transformation.app
        (Opposite.op ⟨([Srt.term] : Ctx sig)⟩) point)
      i.hom_inv_id
    exact h
  have back := congrArg
    (fun value => i.inv.app
      (Opposite.op ⟨([Srt.term] : Ctx sig)⟩) value) equal
  change i.inv.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      (i.hom.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
        (betaRedex.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
          ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
           (.var (.zero : Var [Srt.term] Srt.term))))) =
    i.inv.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      (i.hom.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
        (bodyAt.app (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
          ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
           (.var (.zero : Var [Srt.term] Srt.term))))) at back
  simpa only [cancel] using back

/-- The concrete generated lambda program comparison preserves the negative
open-beta control. -/
theorem generated_open_beta_not_equality :
    (betaRedex ≫ programsGeneratedIso.hom).app
      (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) ≠
    (bodyAt ≫ programsGeneratedIso.hom).app
      (Opposite.op ⟨([Srt.term] : Ctx sig)⟩)
      ((.var (.zero : Var [Srt.term, Srt.term] Srt.term)),
       (.var (.zero : Var [Srt.term] Srt.term))) :=
  open_beta_not_equality_after_iso programsGeneratedIso

end Mettapedia.OSLF.Binding.LambdaLexExponentialComparison
