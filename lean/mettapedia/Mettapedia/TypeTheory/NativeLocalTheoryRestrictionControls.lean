import Mettapedia.TypeTheory.NativeLocalTheoryRestriction
import Mettapedia.TypeTheory.DependentProductRestrictionControls
import Mathlib.Logic.Equiv.Bool
import Mathlib.Data.Fintype.Card
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.NormNum

/-!
# Nonidentity theory restriction with dependent native witnesses

Exchanging two worlds changes the decoded argument domain from one to
two values. The actual local sum comparison keeps both supplied witnesses.
The product comparison retains every future-argument readout and has an
inverse because this theory route is an equivalence. The separate missing
future control remains a failure of unrestricted product invertibility.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.TypeTheory.NativeLocalTheoryRestrictionControls

open _root_.CategoryTheory
open Mettapedia.Computability.ComputationalTrinity
open DisplayedPresheafTransport DisplayedPresheafComprehension DisplayedPresheafCwf
open DisplayedPresheafIndexedCwfBridge DisplayedPresheafPi
open ContextualLocalUniverses NativeLocalTypeFormers NativeLocalTypeOperations
open NativeLocalTheoryRestriction DisplayedPresheafTheoryRestriction
open DisplayedPresheafTheoryRestrictionAction

abbrev World := Discrete Bool
abbrev constant (carrier : Type) : Face.{0, 0, 0} World where
  obj _ := carrier
  map _ := 𝟙 carrier
  map_id _ := rfl
  map_comp _ _ := rfl
abbrev base : Face.{0, 0, 0} World := constant PUnit
abbrev naturals : Face.{0, 0, 0} World := constant Nat

def falseWorld : Worldᵒᵖ := Opposite.op (Discrete.mk false)
def trueWorld : Worldᵒᵖ := Opposite.op (Discrete.mk true)

abbrev finiteFamily : DisplayedFamily.{0, 0, 0, 0} naturals where
  obj point := Fin (point.2 + 1)
  map arrow := TypeCat.ofHom fun value =>
    Fin.cast (congrArg (fun n : Nat => n + 1) arrow.property) value
  map_id _ := by ext value; rfl
  map_comp _ _ := by ext value; rfl

def sizeName : base ⟶ naturals where
  app world := TypeCat.ofHom fun _ => if world.unop.as then 1 else 0
  naturality := by
    intro first second arrow
    apply ConcreteCategory.hom_ext
    intro receipt
    change (if second.unop.as then 1 else 0) = (if first.unop.as then 1 else 0)
    exact congrArg (fun value : Bool => if value then 1 else 0)
      (Discrete.eq_of_hom arrow.unop)

abbrev domain : NativeType base := ⟨naturals, finiteFamily, sizeName⟩

def argumentName : totalSpace domain.decoded ⟶ naturals where
  app _ := TypeCat.ofHom fun receipt => receipt.2.val
  naturality := by intros; rfl

abbrev codomain : NativeType (totalSpace domain.decoded) :=
  ⟨naturals, finiteFamily, argumentName⟩

def exchange : World ≌ World := Discrete.equivalence Equiv.boolNot

theorem actual_world_changed : exchange.functor.op.obj falseWorld = trueWorld := rfl

theorem theory_action_retains_the_parameter_and_name :
    (restrict exchange.functor domain).parameters = exchange.functor.op ⋙ naturals ∧
      (restrict exchange.functor domain).name.app falseWorld PUnit.unit = (1 : Nat) := ⟨rfl, rfl⟩

theorem nonidentity_theory_changes_the_fibre :
    domain.decoded.obj ⟨falseWorld, PUnit.unit⟩ = Fin 1 ∧
      (restrict exchange.functor domain).decoded.obj ⟨falseWorld, PUnit.unit⟩ = Fin 2 := ⟨rfl, rfl⟩

def suppliedPair : (DisplayedPresheafSigma.sigmaDisplayed domain.decoded codomain.decoded).obj
    ⟨trueWorld, PUnit.unit⟩ :=
  ⟨(⟨1, by decide⟩ : Fin 2), (⟨1, by decide⟩ : Fin 2)⟩

noncomputable def sourceSumDecoder :=
  (restrictionFunctor exchange.functor base).mapIso
    (eqToIso (C := DisplayedFamily base) (sigmaDecode domain codomain))

noncomputable def retainedPair : (restrict exchange.functor (sigma domain codomain)).decoded.obj
    ⟨falseWorld, PUnit.unit⟩ :=
  sourceSumDecoder.inv.app ⟨falseWorld, PUnit.unit⟩ suppliedPair

noncomputable def mappedPair :=
  (sumIso exchange.functor domain codomain).hom.app ⟨falseWorld, PUnit.unit⟩ retainedPair

noncomputable def decodedPair :=
  (eqToIso (C := DisplayedFamily (exchange.functor.op ⋙ base))
    (sigmaDecode (restrict exchange.functor domain) (body exchange.functor domain codomain))).hom.app
      ⟨falseWorld, PUnit.unit⟩ mappedPair

theorem actual_pair_readout : decodedPair = suppliedPair := by
  have square := ConcreteCategory.congr_hom
    (NatTrans.congr_app (sum_decoder_square exchange.functor domain codomain)
      ⟨falseWorld, PUnit.unit⟩) retainedPair
  change decodedPair = (sumComparison
    exchange.functor base domain.decoded codomain.decoded).hom.app
      ⟨falseWorld, PUnit.unit⟩ (sourceSumDecoder.hom.app ⟨falseWorld, PUnit.unit⟩ retainedPair)
    at square
  have cancelled := ConcreteCategory.congr_hom
    (sourceSumDecoder.inv_hom_id_app ⟨falseWorld, PUnit.unit⟩) suppliedPair
  simp only [types_comp_apply, types_id_apply] at cancelled
  change sourceSumDecoder.hom.app ⟨falseWorld, PUnit.unit⟩ retainedPair = suppliedPair
    at cancelled
  exact square.trans (congrArg ((sumComparison exchange.functor base
    domain.decoded codomain.decoded).hom.app ⟨falseWorld, PUnit.unit⟩) cancelled)

theorem pair_witnesses_retained : decodedPair.1.val = 1 ∧ decodedPair.2.val = 1 := by
  rw [actual_pair_readout]
  exact ⟨rfl, rfl⟩

noncomputable def productAlongExchange := productEquivalence exchange.functor domain codomain

theorem supplied_product_has_an_actual_inverse :
    productAlongExchange.hom ≫ productAlongExchange.inv = 𝟙 _ :=
  productAlongExchange.hom_inv_id

theorem product_inverse_is_for_the_canonical_map :
    productAlongExchange.hom = productMap exchange.functor domain codomain :=
  productEquivalence_hom exchange.functor domain codomain

/-- Every supplied native function is read at the exchanged world and
the exact supplied dependent argument. -/
theorem supplied_function_readout
    (function : (restrict exchange.functor (pi domain codomain)).decoded.obj
      ⟨falseWorld, PUnit.unit⟩)
    (argument : (restrict exchange.functor domain).decoded.obj ⟨falseWorld, PUnit.unit⟩) :
    ((((DependentProductNativeComparison.nativeIso
        (restrictFamily exchange.functor base domain.decoded)).hom.app
      (displayedToTotalElements (restrictFamily exchange.functor base domain.decoded) ⋙
        (codomainFunctor exchange.functor base domain.decoded).obj codomain.decoded)).app
      ⟨falseWorld, PUnit.unit⟩
      ((piDecodeIso (restrict exchange.functor domain)
        (body exchange.functor domain codomain)).hom.app ⟨falseWorld, PUnit.unit⟩
        ((productMap exchange.functor domain codomain).app ⟨falseWorld, PUnit.unit⟩
          function))).app ⟨falseWorld, PUnit.unit⟩ (𝟙 _) argument) =
    ((((DependentProductNativeComparison.nativeIso domain.decoded).hom.app
      (displayedToTotalElements domain.decoded ⋙ codomain.decoded)).app
      ⟨trueWorld, PUnit.unit⟩
      ((piDecodeIso domain codomain).hom.app ⟨trueWorld, PUnit.unit⟩ function)).app
      ⟨trueWorld, PUnit.unit⟩ (𝟙 _) argument) := by
  exact product_future_readout exchange.functor domain codomain
    ⟨falseWorld, PUnit.unit⟩ ⟨falseWorld, PUnit.unit⟩ (𝟙 _) function argument

/-- At a supplied point the complete dependent pair is recovered through
the canonical sum comparison and the independent native sum decoder. -/
theorem mapped_pair_readout :
    HEq decodedPair suppliedPair := heq_of_eq actual_pair_readout

theorem omitting_the_world_change_changes_the_type :
    (restrict exchange.functor domain).decoded.obj ⟨falseWorld, PUnit.unit⟩ ≠
      domain.decoded.obj ⟨falseWorld, PUnit.unit⟩ := by
  intro same
  have cards := congrArg Nat.card same
  change Nat.card (Fin 2) = Nat.card (Fin 1) at cards
  norm_num [Nat.card_eq_fintype_card] at cards

theorem unrestricted_future_restriction_is_not_injective :
    ¬ Function.Injective
      (DependentProductRestriction.restrictSection
        DependentProductRestrictionControls.initialWorld
        DependentProductRestrictionControls.argumentFamily
        DependentProductRestrictionControls.evidenceFamily
        (X := Discrete.mk ())) :=
  DependentProductRestrictionControls.comparison_not_injective

end Mettapedia.TypeTheory.NativeLocalTheoryRestrictionControls
