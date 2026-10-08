import Mettapedia.CategoryTheory.RelativeClosedSyntaxFunctorNormalizationReadout

/-!
# Native structural comparisons of a normalized closed functor

The constructor isomorphisms determine the normalized functor's actual
canonical product and exponential comparisons. The proof uses naturality of
these comparisons, including the contravariant exponential argument; it
does not supply structural preservation as additional assignment data.
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

omit [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
    [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping] in
theorem comparison_transport {source : Object signature} {first second : ObjectImage mapping source}
    (same : first = second) :
    first.comparison.hom ≫ eqToHom (congrArg ObjectImage.value same) = second.comparison.hom := by
  cases same
  exact Category.comp_id _

theorem normalized_terminal_object :
    (normalizedFunctor mapping).obj (terminal signature) = 𝟙_ D :=
  congrArg ObjectImage.value (objectImage_terminal mapping)

theorem normalized_product_object (first second : Object signature) :
    (normalizedFunctor mapping).obj (product first second) =
      (normalizedFunctor mapping).obj first ⊗ (normalizedFunctor mapping).obj second :=
  congrArg ObjectImage.value (objectImage_product mapping first second)

theorem normalized_exponential_object (argument result : Object signature) :
    (normalizedFunctor mapping).obj (exponentialObject argument result) =
      ((normalizedFunctor mapping).obj argument ⟶[D] (normalizedFunctor mapping).obj result) :=
  congrArg ObjectImage.value (objectImage_exponential mapping argument result)

set_option backward.isDefEq.respectTransparency false in
theorem normalized_productComparison (first second : Object signature) :
    CartesianMonoidalCategory.prodComparison (normalizedFunctor mapping) first second =
      eqToHom (normalized_product_object mapping first second) := by
  apply (cancel_epi (objectImage mapping (product first second)).comparison.hom).mp
  have natural := CartesianClosedFunctorCoherence.product_naturalIso (comparison mapping) first second
  have choices := comparison_transport mapping (objectImage_product mapping first second)
  change (objectImage mapping (product first second)).comparison.hom ≫
      eqToHom (normalized_product_object mapping first second) =
    CartesianMonoidalCategory.prodComparison mapping first second ≫
      ((objectImage mapping first).comparison.hom ⊗ₘ
        (objectImage mapping second).comparison.hom) at choices
  exact natural.symm.trans choices.symm

set_option backward.isDefEq.respectTransparency false in
theorem normalized_expComparison (argument result : Object signature) :
    (expComparison (normalizedFunctor mapping) argument).natTrans.app result =
      eqToHom (normalized_exponential_object mapping argument result) := by
  apply (cancel_epi (objectImage mapping (exponentialObject argument result)).comparison.hom).mp
  have natural := CartesianClosedFunctorCoherence.exponential_naturalIso
    (comparison mapping) argument result
  have choices := comparison_transport mapping (objectImage_exponential mapping argument result)
  change (objectImage mapping (exponentialObject argument result)).comparison.hom ≫
      eqToHom (normalized_exponential_object mapping argument result) =
    (expComparison mapping argument).natTrans.app result ≫
      (MonoidalClosed.pre (objectImage mapping argument).comparison.inv).app (mapping.obj result) ≫
        (ihom (objectImage mapping argument).value).map
          (objectImage mapping result).comparison.hom at choices
  exact natural.symm.trans choices.symm

theorem normalized_terminal_arrow (source : Object signature) :
    (normalizedFunctor mapping).map (toTerminal source) =
      CartesianMonoidalCategory.toUnit ((normalizedFunctor mapping).obj source) ≫
        eqToHom (normalized_terminal_object mapping).symm := by
  apply (cancel_mono (eqToHom (normalized_terminal_object mapping))).mp
  exact Subsingleton.elim _ _

theorem normalized_first (first second : Object signature) :
    (normalizedFunctor mapping).map (GeneratedCategory.first first second) =
      eqToHom (normalized_product_object mapping first second) ≫
        CartesianMonoidalCategory.fst ((normalizedFunctor mapping).obj first)
          ((normalizedFunctor mapping).obj second) :=
  (CartesianMonoidalCategory.prodComparison_fst (normalizedFunctor mapping) first second).symm.trans
    (congrArg (fun arrow => arrow ≫ CartesianMonoidalCategory.fst _ _)
      (normalized_productComparison mapping first second))

theorem normalized_second (first second : Object signature) :
    (normalizedFunctor mapping).map (GeneratedCategory.second first second) =
      eqToHom (normalized_product_object mapping first second) ≫
        CartesianMonoidalCategory.snd ((normalizedFunctor mapping).obj first)
          ((normalizedFunctor mapping).obj second) :=
  (CartesianMonoidalCategory.prodComparison_snd (normalizedFunctor mapping) first second).symm.trans
    (congrArg (fun arrow => arrow ≫ CartesianMonoidalCategory.snd _ _)
      (normalized_productComparison mapping first second))

theorem normalized_pairing {source first second : Object signature}
    (before : source ⟶ first) (after : source ⟶ second) :
    (normalizedFunctor mapping).map (pairing before after) =
      CartesianMonoidalCategory.lift ((normalizedFunctor mapping).map before)
          ((normalizedFunctor mapping).map after) ≫
        eqToHom (normalized_product_object mapping first second).symm := by
  apply (cancel_mono (eqToHom (normalized_product_object mapping first second))).mp
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, ← normalized_first, ← Functor.map_comp, pairing_first,
      CartesianMonoidalCategory.lift_fst]
  · rw [Category.assoc, ← normalized_second, ← Functor.map_comp, pairing_second,
      CartesianMonoidalCategory.lift_snd]

theorem normalized_exchange (first second : Object signature) :
    (normalizedFunctor mapping).map (GeneratedCategory.exchange first second).hom =
      eqToHom (normalized_product_object mapping first second) ≫
        Interpretation.exchange ((normalizedFunctor mapping).obj first)
          ((normalizedFunctor mapping).obj second) ≫
            eqToHom (normalized_product_object mapping second first).symm := by
  change (normalizedFunctor mapping).map
    (pairing (GeneratedCategory.second first second) (GeneratedCategory.first first second)) = _
  rw [normalized_pairing, normalized_first, normalized_second,
    ← CartesianMonoidalCategory.comp_lift, Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem normalized_leftEvaluation (argument result : Object signature) :
    (normalizedFunctor mapping).map ((ihom.ev argument).app result) =
      eqToHom ((normalized_product_object mapping argument (exponentialObject argument result)).trans
        (congrArg (fun value : D => (normalizedFunctor mapping).obj argument ⊗ value)
          (normalized_exponential_object mapping argument result))) ≫
        (ihom.ev ((normalizedFunctor mapping).obj argument)).app
          ((normalizedFunctor mapping).obj result) := by
  have actual := expComparison_ev (normalizedFunctor mapping) argument result
  change ((normalizedFunctor mapping).obj argument ◁
      (expComparison (normalizedFunctor mapping) argument).natTrans.app result) ≫
        (ihom.ev ((normalizedFunctor mapping).obj argument)).app
          ((normalizedFunctor mapping).obj result) =
    inv (CartesianMonoidalCategory.prodComparison (normalizedFunctor mapping) argument
      (exponentialObject argument result)) ≫
        (normalizedFunctor mapping).map ((ihom.ev argument).app result) at actual
  have mapped := congrArg
    (fun arrow => CartesianMonoidalCategory.prodComparison (normalizedFunctor mapping) argument
      (exponentialObject argument result) ≫ arrow) actual
  simp only [IsIso.hom_inv_id_assoc] at mapped
  rw [normalized_productComparison, normalized_expComparison,
    MonoidalCategory.whiskerLeft_eqToHom, ← Category.assoc, eqToHom_trans] at mapped
  exact mapped.symm

omit [CartesianMonoidalCategory D] [MonoidalClosed D] in
@[reassoc] theorem equalizerTransport_inclusion {source target before after : D}
    (first second : source ⟶ target) (input : source ≅ before) (output : target ≅ after) :
    (equalizerTransport first second input output).hom ≫
      equalizer.ι (input.inv ≫ first ≫ output.hom) (input.inv ≫ second ≫ output.hom) =
        equalizer.ι first second ≫ input.hom := by
  dsimp only [equalizerTransport]
  exact IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

theorem normalized_equalizer_object {source target : Object signature}
    (first second : RawHom source target) :
    (normalizedFunctor mapping).obj (PresentedEqualizer.object first second) =
      equalizer ((normalizedFunctor mapping).map (classOf first))
        ((normalizedFunctor mapping).map (classOf second)) :=
  congrArg ObjectImage.value (objectImage_equalizer mapping first second)

set_option backward.isDefEq.respectTransparency false in
theorem normalized_equalizer_inclusion {source target : Object signature}
    (first second : RawHom source target) :
    (normalizedFunctor mapping).map (PresentedEqualizer.inclusion first second) =
      eqToHom (normalized_equalizer_object mapping first second) ≫
        equalizer.ι ((normalizedFunctor mapping).map (classOf first))
          ((normalizedFunctor mapping).map (classOf second)) := by
  have full : (objectImage mapping (PresentedEqualizer.object first second)).comparison.hom ≫
      eqToHom (normalized_equalizer_object mapping first second) ≫
        equalizer.ι ((normalizedFunctor mapping).map (classOf first))
          ((normalizedFunctor mapping).map (classOf second)) =
    mapping.map (PresentedEqualizer.inclusion first second) ≫
      (objectImage mapping source).comparison.hom := by
    rw [← Category.assoc, comparison_transport mapping (objectImage_equalizer mapping first second)]
    change ((mappedPresentedIso mapping first second).hom ≫
        (equalizerTransport (mapping.map (classOf first)) (mapping.map (classOf second))
          (objectImage mapping source).comparison (objectImage mapping target).comparison).hom) ≫
            equalizer.ι _ _ = _
    rw [Category.assoc, equalizerTransport_inclusion, ← Category.assoc, mappedPresentedIso_inclusion]
  apply (cancel_epi (objectImage mapping (PresentedEqualizer.object first second)).comparison.hom).mp
  change (objectImage mapping (PresentedEqualizer.object first second)).comparison.hom ≫
    ((objectImage mapping (PresentedEqualizer.object first second)).comparison.inv ≫
      mapping.map (PresentedEqualizer.inclusion first second) ≫
        (objectImage mapping source).comparison.hom) = _
  simpa only [Iso.hom_inv_id_assoc, Category.assoc] using full.symm

end Mettapedia.CategoryTheory.RelativeClosedSyntax.FunctorNormalization
