import Mettapedia.CategoryTheory.RelativeClosedBaseRealizationUniqueness
import Mettapedia.CategoryTheory.CartesianClosedFunctorCoherence

/-!
# Complete native inverse readouts of a weak closed base map

The independently realized inverse declarations are the inverses of the
actual canonical terminal, product, equalizer and exponential comparisons.
The right-oriented abstraction is compared with Mathlib's left-oriented
exponential comparison through the genuine exchange square. No literal
identification of selected choices is required.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.CanonicalReadout

open _root_.CategoryTheory _root_.CategoryTheory.Limits MonoidalCategory
open Interpretation RealizationUniqueness

universe k w

variable {C : Type k} [Category.{k} C]
variable [CartesianMonoidalCategory C] [MonoidalClosed C] [HasFiniteLimits C]
variable {D : Type w} [Category.{k} D]
variable [CartesianMonoidalCategory D] [MonoidalClosed D] [HasFiniteLimits D]
variable (mapping : C ⥤ D) [PreservesFiniteLimits mapping] [MonoidalClosedFunctor mapping]

omit [MonoidalClosed C] [HasFiniteLimits C] [MonoidalClosed D] [HasFiniteLimits D]
  [MonoidalClosedFunctor mapping] [PreservesFiniteLimits mapping] in
theorem exchange_square (first second : C) :
    CartesianMonoidalCategory.prodComparison mapping first second ≫
      Interpretation.exchange (mapping.obj first) (mapping.obj second) =
    mapping.map (Interpretation.exchange first second) ≫
      CartesianMonoidalCategory.prodComparison mapping second first := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, Interpretation.exchange_first,
      CartesianMonoidalCategory.prodComparison_fst, CartesianMonoidalCategory.prodComparison_snd,
      ← mapping.map_comp]
  · simp only [Category.assoc, Interpretation.exchange_second,
      CartesianMonoidalCategory.prodComparison_snd, CartesianMonoidalCategory.prodComparison_fst,
      ← mapping.map_comp]

omit [MonoidalClosed C] [HasFiniteLimits C] [MonoidalClosed D] [HasFiniteLimits D]
  [MonoidalClosedFunctor mapping] in
theorem inverse_exchange_square (first second : C) :
    inv (CartesianMonoidalCategory.prodComparison mapping first second) ≫
      mapping.map (Interpretation.exchange first second) =
    Interpretation.exchange (mapping.obj first) (mapping.obj second) ≫
      inv (CartesianMonoidalCategory.prodComparison mapping second first) := by
  apply (cancel_mono (CartesianMonoidalCategory.prodComparison mapping second first)).mp
  simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [← exchange_square mapping first second]
  simp only [IsIso.inv_hom_id_assoc]

omit [HasFiniteLimits C] [HasFiniteLimits D] [MonoidalClosedFunctor mapping] in
theorem right_exponential_comparison (argument result : C) :
    Interpretation.abstraction
      (inv (CartesianMonoidalCategory.prodComparison mapping (argument ⟶[C] result) argument) ≫
        mapping.map (Interpretation.evaluation argument result)) =
      (expComparison mapping argument).natTrans.app result := by
  apply MonoidalClosed.uncurry_injective
  rw [Interpretation.abstraction, MonoidalClosed.uncurry_curry, Interpretation.evaluation,
    mapping.map_comp]
  have changed := congrArg
    (fun incoming => Interpretation.exchange (mapping.obj argument) (mapping.obj (argument ⟶[C] result)) ≫
      incoming ≫ mapping.map ((ihom.ev argument).app result))
    (inverse_exchange_square mapping (argument ⟶[C] result) argument)
  calc
    _ = Interpretation.exchange (mapping.obj argument) (mapping.obj (argument ⟶[C] result)) ≫
        (Interpretation.exchange (mapping.obj (argument ⟶[C] result)) (mapping.obj argument) ≫
          (inv (CartesianMonoidalCategory.prodComparison mapping argument (argument ⟶[C] result)) ≫
            mapping.map ((ihom.ev argument).app result))) := by
      simpa only [Category.assoc] using changed
    _ = inv (CartesianMonoidalCategory.prodComparison mapping argument (argument ⟶[C] result)) ≫
        mapping.map ((ihom.ev argument).app result) := by
      rw [← Category.assoc, Interpretation.exchange_exchange, Category.id_comp]
    _ = _ := (uncurry_expComparison mapping argument result).symm

def forward : (choice : Choice C) →
    mapping.obj (selected choice) ⟶ WeakDiagram.nativeSource mapping choice
  | .terminal => CartesianMonoidalCategory.terminalComparison mapping
  | .product first second => CartesianMonoidalCategory.prodComparison mapping first second
  | .equalizer first second => equalizerComparison first second mapping
  | .exponential argument result => (expComparison mapping argument).natTrans.app result

instance forward_isIso (choice : Choice C) : IsIso (forward mapping choice) := by
  cases choice <;> dsimp only [forward] <;> infer_instance

variable (meanings : Assignment C (symbols C) D)
variable (realized : Realization (signature (C := C)) meanings)
variable [PreservesFiniteLimits meanings.base] [MonoidalClosedFunctor meanings.base]

omit [MonoidalClosedFunctor meanings.base] in
theorem product_forward (first last : C) :
    RealizationUniqueness.forward meanings realized (.product first last) =
      forward meanings.base (.product first last) := rfl

theorem product_inverse (first last : C) :
    RealizationUniqueness.inverse meanings realized (.product first last) =
      inv (forward meanings.base (.product first last)) := by
  apply IsIso.eq_inv_of_hom_inv_id
  exact (congrArg (· ≫ RealizationUniqueness.inverse meanings realized (.product first last))
    (product_forward meanings realized first last).symm).trans
      (forward_inverse meanings realized (.product first last))

theorem forward_complete (choice : Choice C) :
    RealizationUniqueness.forward meanings realized choice = forward meanings.base choice := by
  cases choice with
  | terminal => rfl
  | product first last => exact product_forward meanings realized first last
  | equalizer first last => rfl
  | exponential argument result =>
      change Interpretation.abstraction
        (RealizationUniqueness.inverse meanings realized (.product (argument ⟶[C] result) argument) ≫
          meanings.base.map (Interpretation.evaluation argument result)) = _
      rw [product_inverse]
      exact right_exponential_comparison meanings.base argument result

theorem inverse_complete (choice : Choice C) :
    RealizationUniqueness.inverse meanings realized choice = inv (forward meanings.base choice) := by
  apply IsIso.eq_inv_of_hom_inv_id
  exact (congrArg (· ≫ RealizationUniqueness.inverse meanings realized choice)
    (forward_complete meanings realized choice).symm).trans
      (forward_inverse meanings realized choice)

include realized in
theorem complete_arrow (choice : Choice C) : meanings.evaluateArrow (.name choice) =
    some ⟨WeakDiagram.nativeSource meanings.base choice, meanings.base.obj (selected choice),
      inv (forward meanings.base choice)⟩ :=
  (inverse_read meanings realized choice).trans
    (congrArg (fun value => some (⟨_, _, value⟩ : ArrowValue D)) (inverse_complete meanings realized choice))

end Mettapedia.CategoryTheory.RelativeClosedSyntax.BaseComparisons.CanonicalReadout
