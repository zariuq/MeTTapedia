import Mettapedia.TypeTheory.PresheafClosedComprehension
import Mettapedia.TypeTheory.NativeLocalParameterControls

/-!
# Actual function specification in the total codomain category

The argument retains one Boolean evidence value over each natural program
index. The function exchanges that value. Abstraction and evaluation in
the actual arrow category recover this commuting square on every argument.
Two such functions differ even though their codomain program maps agree.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.PresheafCodomainClosureControls

open _root_.CategoryTheory MonoidalCategory CartesianMonoidalCategory
open DisplayedPresheafTransport DisplayedPresheafComprehension
open NativeLocalParameterControls

abbrev Cosmos := PresheafCodomainCosmos.Total World

def evidence : DisplayedFamily naturals := (Functor.const _).obj Bool

def specification : Cosmos := Arrow.mk (totalProjection evidence)

def keepValues : specification ⟶ specification := 𝟙 specification

def exchangeValues : specification ⟶ specification :=
  Arrow.homMk
    { app := fun _ => TypeCat.ofHom fun receipt => ⟨receipt.1, !receipt.2⟩
      naturality := by intros; rfl }
    (𝟙 naturals) (by ext point receipt; rfl)

noncomputable def exchangeBody : specification ⊗ specification ⟶ specification :=
  fst specification specification ≫ exchangeValues

noncomputable def function : specification ⟶
    (PresheafCodomainCosmos.exponential World specification).obj specification :=
  PresheafCodomainCosmos.homEquiv World specification specification specification exchangeBody

theorem application_recovers_supplied_body : MonoidalClosed.uncurry function = exchangeBody :=
  PresheafCodomainCosmos.beta World exchangeBody

theorem generic_application_exchanges_value :
    (lift (𝟙 specification) (𝟙 specification) ≫
      MonoidalClosed.uncurry function).left.app world ⟨7, false⟩ = ⟨7, true⟩ := by
  rw [application_recovers_supplied_body]
  simp only [exchangeBody, lift_fst_assoc]
  rfl

theorem public_program_maps_agree :
    (PresheafCodomainCosmos.codomain World).map keepValues =
      (PresheafCodomainCosmos.codomain World).map exchangeValues := rfl

theorem actual_evidence_maps_disagree : keepValues ≠ exchangeValues := by
  intro same
  have values := congrArg
    (fun square : specification ⟶ specification => square.left.app world ⟨7, false⟩) same
  have flags := congrArg (fun receipt => receipt.2) values
  change false = true at flags
  cases flags

end Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.PresheafCodomainClosureControls
