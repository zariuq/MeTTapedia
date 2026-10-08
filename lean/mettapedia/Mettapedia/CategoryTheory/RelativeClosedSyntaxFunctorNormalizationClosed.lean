import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationNative

/-!
# Complete evaluation and abstraction of a normalized closed functor

The actual canonical exponential comparison determines how a functor maps
currying. Applying the constructor comparisons retains the context, the
argument and the supplied body. The right-oriented authored evaluation is
recovered through the actual exchange map of the Cartesian structure.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open GeneratedCategory

universe k w

variable {C : Type k} [Category.{k} C] {symbols : Symbols.{k}}
variable {signature : Signature (C := C) (symbols := symbols)}
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : Object signature ⥤ D) [PreservesFiniteLimits mapping]
variable [MonoidalClosedFunctor mapping]

set_option backward.isDefEq.respectTransparency false in
theorem curry_comparison {context argument result : Object signature}
    (body : argument ⊗ context ⟶ result) :
    (normalizedFunctor mapping).map (MonoidalClosed.curry body) ≫
        (expComparison (normalizedFunctor mapping) argument).natTrans.app result =
      MonoidalClosed.curry
        (inv (CartesianMonoidalCategory.prodComparison (normalizedFunctor mapping) argument context) ≫
          (normalizedFunctor mapping).map body) := by
  apply MonoidalClosed.uncurry_injective
  rw [MonoidalClosed.uncurry_natural_left, uncurry_expComparison,
    MonoidalClosed.uncurry_curry, ← Category.assoc,
    ← CartesianMonoidalCategory.prodComparison_inv_natural_whiskerLeft,
    Category.assoc, ← Functor.map_comp, ← MonoidalClosed.uncurry_eq,
    MonoidalClosed.uncurry_curry]

set_option backward.isDefEq.respectTransparency false in
theorem normalized_curry {context argument result : Object signature}
    (body : argument ⊗ context ⟶ result) :
    (normalizedFunctor mapping).map (MonoidalClosed.curry body) =
      MonoidalClosed.curry
        (eqToHom (normalized_product_object mapping argument context).symm ≫
          (normalizedFunctor mapping).map body) ≫
        eqToHom (normalized_exponential_object mapping argument result).symm := by
  have inverse : inv (CartesianMonoidalCategory.prodComparison
      (normalizedFunctor mapping) argument context) =
      eqToHom (normalized_product_object mapping argument context).symm := by
    symm
    apply IsIso.eq_inv_of_hom_inv_id
    rw [normalized_productComparison]
    simp only [eqToHom_trans, eqToHom_refl]
  have actual := curry_comparison mapping body
  rw [normalized_expComparison, inverse] at actual
  apply (cancel_mono (eqToHom (normalized_exponential_object mapping argument result))).mp
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id] using actual

set_option backward.isDefEq.respectTransparency false in
theorem source_curry {context argument result : Object signature}
    (body : argument ⊗ context ⟶ result) :
    MonoidalClosed.curry body =
      abstraction ((GeneratedCategory.exchange context argument).hom ≫ body) := by
  change (exponentialAdjunction argument).homEquiv context result body = _
  exact exponentialAdjunction_readout argument context result body

set_option backward.isDefEq.respectTransparency false in
theorem source_abstraction {context argument result : Object signature}
    (body : product context argument ⟶ result) :
    abstraction body =
      MonoidalClosed.curry ((GeneratedCategory.exchange argument context).hom ≫ body) := by
  have actual := source_curry ((GeneratedCategory.exchange argument context).hom ≫ body)
  have cancel : (GeneratedCategory.exchange context argument).hom ≫
      (GeneratedCategory.exchange argument context).hom = 𝟙 (product context argument) :=
    (GeneratedCategory.exchange context argument).hom_inv_id
  rw [← Category.assoc, cancel, Category.id_comp] at actual
  exact actual.symm

set_option backward.isDefEq.respectTransparency false in
theorem normalized_abstraction {context argument result : Object signature}
    (body : product context argument ⟶ result) :
    (normalizedFunctor mapping).map (abstraction body) =
      Interpretation.abstraction
        (eqToHom (normalized_product_object mapping context argument).symm ≫
          (normalizedFunctor mapping).map body) ≫
        eqToHom (normalized_exponential_object mapping argument result).symm := by
  rw [source_abstraction, normalized_curry, Functor.map_comp, normalized_exchange]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rfl

omit [MonoidalClosed D] [HasFiniteLimits D] in
theorem exchange_cast {argument before after : D} (same : before = after) :
    eqToHom (congrArg (fun value : D => value ⊗ argument) same) ≫
        Interpretation.exchange after argument =
      Interpretation.exchange before argument ≫
        eqToHom (congrArg (fun value : D => argument ⊗ value) same) := by
  cases same
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
theorem normalized_evaluation (argument result : Object signature) :
    (normalizedFunctor mapping).map (evaluation argument result) =
      eqToHom ((normalized_product_object mapping (exponentialObject argument result) argument).trans
        (congrArg (fun value : D => value ⊗ (normalizedFunctor mapping).obj argument)
          (normalized_exponential_object mapping argument result))) ≫
        Interpretation.evaluation ((normalizedFunctor mapping).obj argument)
          ((normalizedFunctor mapping).obj result) := by
  have represented : evaluation argument result =
      (GeneratedCategory.exchange (exponentialObject argument result) argument).hom ≫
        (ihom.ev argument).app result := by
    rw [← monoidal_evaluation]
    exact congrArg (fun incoming : product (exponentialObject argument result) argument ⟶
      product argument (exponentialObject argument result) => incoming ≫ (ihom.ev argument).app result)
      (cartesian_exchange (exponentialObject argument result) argument)
  rw [represented, Functor.map_comp, normalized_exchange, normalized_leftEvaluation]
  have exchanged := exchange_cast (argument := (normalizedFunctor mapping).obj argument)
    (normalized_exponential_object mapping argument result)
  have full := congrArg
    (fun arrow => eqToHom (normalized_product_object mapping (exponentialObject argument result) argument) ≫
      arrow ≫ (ihom.ev ((normalizedFunctor mapping).obj argument)).app
        ((normalizedFunctor mapping).obj result)) exchanged.symm
  simpa only [Interpretation.evaluation, Category.assoc, eqToHom_trans_assoc,
    eqToHom_trans, eqToHom_refl, Category.id_comp] using full

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
