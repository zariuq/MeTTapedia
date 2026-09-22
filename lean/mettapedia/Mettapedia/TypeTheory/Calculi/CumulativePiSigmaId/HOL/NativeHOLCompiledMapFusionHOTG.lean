import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLCompiledMapFusionUniverse
import Mettapedia.Logic.HOL.Embedding.ZFSetHOLTraceTermInterpretation

/-!
# The compiled fusion proof specialized to actual HOTG set operations

One universe higher, the trace-coded HOL set carrier is literally the element
carrier of the uniform-list model.  This identifies the recursively coded
simple fragment by set equality, not merely by an external equivalence.
Consequently the exact compiled map-fusion proof can be instantiated with the
actual powerset and least-universe operations of the set model and consumed by
dependent identity elimination.

The universe shift is essential: no same-level set can code the entire ambient
set carrier.
-/

open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLCompiledMapFusionHOTG

open Mettapedia.Logic
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetUniverseClosure ZFSetUniverseLift ZFSetLiftedUniverseClosure

namespace Uniform

open HOL.UniformListInduction
open ZFSetUniformListTraceTypeInterpretation

end Uniform

namespace SetTrace

open ZFSetHenkinInterpretation ZFSetUniverseInterpretation
open ZFSetHOLTraceTypeInterpretation ZFSetHOLTraceTermInterpretation

end SetTrace

universe u

/-- The set-theory simple types embedded in the uniform-list signature. -/
def embedSetType : HOL.Ty Unit → HOL.Ty HOL.UniformListInduction.BaseSort
  | .prop => .prop
  | .base _ => .base .element
  | .arr domain codomain => .arr (embedSetType domain) (embedSetType codomain)

/-- The full trace-coded set/HOL fragment and the uniform-list fragment use
literally the same set code after embedding their type indices. -/
theorem typeCode_agreement (type : HOL.Ty Unit) :
    ZFSetUniformListTraceTypeInterpretation.typeCode carrierCode.{u}
        (embedSetType type) =
      ZFSetHOLTraceTypeInterpretation.typeCode.{u} type := by
  induction type with
  | prop => rfl
  | base => rfl
  | arr domain codomain domainHypothesis codomainHypothesis =>
      simp only [embedSetType, ZFSetUniformListTraceTypeInterpretation.typeCode,
        ZFSetHOLTraceTypeInterpretation.typeCode, domainHypothesis,
        codomainHypothesis]

@[simp] theorem embedSetType_set :
    embedSetType ZFSetHenkinInterpretation.set =
      HOL.UniformListInduction.element := rfl

@[simp] theorem embedSetType_mapping :
    embedSetType ZFSetHenkinInterpretation.mapping =
      HOL.UniformListInduction.mapping := rfl

/-- The actual higher-ambient powerset constant, viewed as a map on list
elements. The type checks by the literal code agreement above. -/
noncomputable def powerMap :
    ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.mapping :=
  ZFSetHOLTraceTermInterpretation.constants ZFSetHenkinInterpretation.Symbol.power

/-- The actual shifted least-universe operation, viewed through the same
literal function code. -/
noncomputable def universeMap (h : CofinalInaccessibles.{u}) :
    ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.mapping :=
  ZFSetHOLTraceTermInterpretation.universeConstants h
    ZFSetUniverseInterpretation.UniverseSymbol.universe

theorem decode_powerMap
    (x : ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.element) :
    carrierEquiv
        (ZFSetUniformListTraceTypeInterpretation.app powerMap x) =
      ZFSet.powerset (carrierEquiv x) := by
  change carrierEquiv
      (ZFSetHOLTraceTypeInterpretation.app
        (ZFSetHOLTraceTermInterpretation.constants
          ZFSetHenkinInterpretation.Symbol.power) x) = _
  rw [ZFSetHOLTraceTermInterpretation.constants,
    ZFSetHOLTraceTypeInterpretation.app_lam, decode_power]

theorem decode_universeMap (h : CofinalInaccessibles.{u})
    (x : ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.element) :
    carrierEquiv
        (ZFSetUniformListTraceTypeInterpretation.app (universeMap h) x) =
      univOf h (carrierEquiv x) := by
  change carrierEquiv
      (ZFSetHOLTraceTypeInterpretation.app
        (ZFSetHOLTraceTermInterpretation.universeConstants h
          ZFSetUniverseInterpretation.UniverseSymbol.universe) x) = _
  rw [ZFSetHOLTraceTermInterpretation.universeConstants,
    ZFSetHOLTraceTypeInterpretation.app_lam, decode_universe]

/-- The proof value comes from the exact compiled source proof, instantiated
with two actual set operations and an arbitrary list of encoded lower sets. -/
noncomputable def hotgFusionProofValue (h : CofinalInaccessibles.{u})
    (xs : ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.sequence) :=
  NativeHOLCompiledMapFusionTrace.compiledFusionProofValue
    (universeMap h) powerMap xs

/-- Dependent identity elimination consumes that same specialized compiler
value at the concrete endpoint motive. -/
noncomputable def hotgConsumedEndpoint (h : CofinalInaccessibles.{u})
    (xs : ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.sequence) :=
  NativeHOLCompiledMapFusionTrace.compiledConsumedEndpoint
    (universeMap h) powerMap xs

theorem hotgConsumedEndpoint_value (h : CofinalInaccessibles.{u})
    (xs : ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.sequence) :
    (hotgConsumedEndpoint h xs).1 =
      (NativeHOLCompiledMapFusionTrace.compiledFusionIdentityPoint
        (universeMap h) powerMap xs).1.1.2.1 :=
  NativeHOLCompiledMapFusionTrace.compiledConsumedEndpoint_value
    (universeMap h) powerMap xs

/-- With a separately stated larger-ambient tower assumption, this concrete
HOTG-specialized proof value is small in its bottom universe. -/
theorem hotgFusionProofValue_small (lower : CofinalInaccessibles.{u})
    (upper : CofinalInaccessibles.{u + 1})
    (xs : ZFSetUniformListTraceTypeInterpretation.Value carrierCode.{u}
      HOL.UniformListInduction.sequence) :
    (hotgFusionProofValue lower xs).1 ∈
      ZFSetInterpretation.universeSet upper
        (ZFSetIndexedClosure.seed carrierCode.{u}) 0 :=
  NativeHOLCompiledMapFusionUniverse.compiledFusionProofValue_small upper
    (universeMap lower) powerMap xs

/-- The literal agreement necessarily uses a genuine universe shift. -/
theorem no_same_level_full_set_code :
    ¬ ∃ code : ZFSet.{u}, Nonempty (Elements code ≃ ZFSet.{u}) :=
  no_same_level_carrier_code

#print axioms typeCode_agreement
#print axioms decode_powerMap
#print axioms decode_universeMap
#print axioms hotgFusionProofValue
#print axioms hotgConsumedEndpoint_value
#print axioms hotgFusionProofValue_small
#print axioms no_same_level_full_set_code

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLCompiledMapFusionHOTG
