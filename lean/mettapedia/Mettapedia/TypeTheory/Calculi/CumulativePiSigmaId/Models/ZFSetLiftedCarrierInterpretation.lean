import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetContextualUniverseInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseLift

/-!
# The full lower ZFSet carrier in the larger set-coded universe hierarchy

The carrier code and its set-operation semantics are constructed without a
cardinal hypothesis. Placing that particular code in the fixed larger-
ambient unbounded hierarchy uses an explicitly larger-ambient hypothesis.
No lower-level cofinality assumption is silently promoted to the next Lean
universe, and this construction does not select a global native universe
policy or provide all-term native soundness.
-/

open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetLiftedCarrierInterpretation

open Mettapedia.Logic.HOL.Embedding
open ZFSetUniverseClosure ZFSetDependentProducts ZFSetUniverseLift
open ZFSetInterpretation

universe u

/-- The assumption is at the target ambient level, not the level of the
original HOL set carrier. -/
noncomputable def carrierAtZero (h : CofinalInaccessibles.{u + 1}) :
    Code h carrierCode.{u} 0 := ⟨carrierCode, seed_mem_universeSet h carrierCode (0 : Nat)⟩

noncomputable def decodedCarrier (h : CofinalInaccessibles.{u + 1}) :
    El (carrierAtZero h) ≃ ZFSet.{u} := carrierEquiv

noncomputable def contextualCode (h : CofinalInaccessibles.{u + 1})
    (Γ : Type (u + 2)) : Γ → Code h carrierCode.{u} 0 :=
  fun _ => carrierAtZero h

theorem contextualCode_decoding (h : CofinalInaccessibles.{u + 1})
    (Γ : Type (u + 2)) :
    (ZFSetContextualUniverseInterpretation.hierarchy h carrierCode.{u}).el
        (level := 0) (contextualCode h Γ) =
      (fun _ : Γ => carrierCode.{u}) := rfl

def encodeSection {Γ : Type (u + 2)} (value : Γ → ZFSet.{u}) :
    ZFSetContextualInterpretation.Section (fun _ : Γ => carrierCode.{u}) :=
  fun γ => encode (value γ)

theorem decodeSection_encodeSection {Γ : Type (u + 2)} (value : Γ → ZFSet.{u}) :
    (fun γ => carrierEquiv (encodeSection value γ)) = value := by
  funext γ
  exact decode_encode (value γ)

theorem encodeSection_substitution {Γ Δ : Type (u + 2)}
    (θ : Δ → Γ) (value : Γ → ZFSet.{u}) :
    (fun δ => encodeSection value (θ δ)) = encodeSection (value ∘ θ) := rfl

/-- The term is typed by decoding the actual contextual level-zero code. -/
def codedSection (h : CofinalInaccessibles.{u + 1}) {Γ : Type (u + 2)}
    (value : Γ → ZFSet.{u}) :
    ZFSetContextualInterpretation.codedCwf.Tm Γ
      ((ZFSetContextualUniverseInterpretation.hierarchy h carrierCode.{u}).el
        (level := 0) (contextualCode h Γ)) := encodeSection value

theorem decode_coded_union {Γ : Type (u + 2)} (value : Γ → ZFSet.{u}) (γ : Γ) :
    carrierEquiv (carrierUnion (encodeSection value γ)) = ZFSet.sUnion (value γ) := by
  change carrierEquiv (carrierUnion (encode (value γ))) = _
  rw [decode_union, decode_encode]

theorem decode_coded_power {Γ : Type (u + 2)} (value : Γ → ZFSet.{u}) (γ : Γ) :
    carrierEquiv (carrierPower (encodeSection value γ)) = ZFSet.powerset (value γ) := by
  change carrierEquiv (carrierPower (encode (value γ))) = _
  rw [decode_power, decode_encode]

theorem coded_membership {Γ : Type (u + 2)} (first second : Γ → ZFSet.{u}) (γ : Γ) :
    (encodeSection first γ).1 ∈ (encodeSection second γ).1 ↔ first γ ∈ second γ :=
  lift_mem_lift

#print axioms carrierAtZero
#print axioms decodedCarrier
#print axioms contextualCode_decoding
#print axioms decodeSection_encodeSection
#print axioms encodeSection_substitution
#print axioms codedSection
#print axioms decode_coded_union
#print axioms decode_coded_power
#print axioms coded_membership

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.ZFSetLiftedCarrierInterpretation
