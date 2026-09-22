import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.HOL.NativeHOLCompiledMapFusionTrace
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Models.ZFSetTraceUniverseInterpretation

/-!
# Universe bounds for the compiled map-fusion crossing

The exact native proof section and its dependent identity consumer already
live in the trace-coded set model.  This file connects that crossing to the
existing internal universe tower under its explicit cofinal-inaccessibles
assumption.  Source simple types, proof families, the compiled proof value,
and the concrete endpoint motive are small in the seeded bottom universe.

The finite-universe control is retained: closure under the elementary set
operations and containment of every individual list do not by themselves
make the whole list type small.
-/

open Mettapedia.TypeTheory.UniverseLevel
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false


namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLCompiledMapFusionUniverse

open Mettapedia.Logic HOL.UniformListInduction
open Mettapedia.Logic.HOL.Embedding
open ZFSetDependentProducts (Elements)
open ZFSetUniverseClosure ZFSetInterpretation
open ZFSetUniformListTraceTypeInterpretation
open ZFSetUniformListTraceProofBridge
open NativeHOLTraceLeibnizCompilerSemantics
open NativeHOLCompiledMapFusionTrace

universe u

noncomputable abbrev integrationSeed (a : ZFSet.{u}) : ZFSet.{u} :=
  ZFSetIndexedClosure.seed a

/-- Every simple type used by the uniform list theory has an actual code at
every level of the seeded trace universe tower. -/
theorem sourceType_small (h : CofinalInaccessibles.{u}) (a : ZFSet.{u})
    (level : Nat) (type : HOL.Ty BaseSort) :
    typeCode a type ∈ universeSet h (integrationSeed a) level := by
  apply typeCode_mem (universeSet_closed h (integrationSeed a) level)
  · exact universeSet_mono h (integrationSeed a) (Nat.zero_le level)
      (ZFSetIndexedClosure.seed_contains_parameter h a)
  · exact ZFSetTraceUniverseInterpretation.indices_mem_level h a level

/-- Every proof-hypothesis family in the compiler's semantic telescope is a
bottom-universe code. -/
theorem proofContextFamily_small (h : CofinalInaccessibles.{u}) (a : ZFSet.{u})
    (delta : List (HOL.Formula Symbol [])) (index : Fin delta.length)
    (environment : (proofContext a delta).Environment) :
    (proofContext a delta).family index environment ∈
      universeSet h (integrationSeed a) 0 := by
  rw [proofContext_family]
  exact ZFSetTraceUniverseInterpretation.truthCode_mem h (integrationSeed a) 0 _

/-- The conclusion family of the exact open compiler output is small at each
semantic environment, independently of whether that environment satisfies
the theory assumptions. -/
theorem openConclusion_small (h : CofinalInaccessibles.{u}) (a : ZFSet.{u})
    (environment : (proofContext a (theory (Γ := []))).Environment) :
    ZFSetTraceProofDecoding.truthCode
        (formulaMeaning (HOL.UniformListMapFusion.mapFusion (Γ := []))
          (proofContext a (theory (Γ := [])))
          (fun _ => (ZFSetUniformListTraceTermInterpretation.emptyValuation :
            ZFSetUniformListTraceTermInterpretation.Valuation a [])) environment) ∈
      universeSet h (integrationSeed a) 0 :=
  ZFSetTraceUniverseInterpretation.truthCode_mem h (integrationSeed a) 0 _

/-- The retained set value denoted by the compiler's exact open output is
itself an element of the bottom universe. -/
theorem openNativeProofValue_small (h : CofinalInaccessibles.{u}) (a : ZFSet.{u})
    (environment : (proofContext a (theory (Γ := []))).Environment) :
    (openNativeProofSection a environment).1 ∈
      universeSet h (integrationSeed a) 0 :=
  (universeSet_closed h (integrationSeed a) 0).transitive _
    (openConclusion_small h a environment)
    (openNativeProofSection a environment).2

theorem fusionTruthFibre_small (h : CofinalInaccessibles.{u}) (a : ZFSet.{u})
    (f g : Value a mapping) (xs : Value a sequence) :
    truthFibre fusionBody (fusionValuation f g xs) ∈
      universeSet h (integrationSeed a) 0 := by
  unfold truthFibre
  exact ZFSetTraceUniverseInterpretation.truthCode_mem h (integrationSeed a) 0 _

/-- The contextual identity family inhabited by the compiled fusion proof is
literally the same small set as its source truth fibre. -/
theorem compiledIdentityFamily_small (h : CofinalInaccessibles.{u})
    (a : ZFSet.{u}) (f g : Value a mapping) (xs : Value a sequence) :
    ZFSetContextualIdentity.identityFamily (sequenceFamily a)
        (beforeSection f g xs) (afterSection f g xs) PUnit.unit ∈
      universeSet h (integrationSeed a) 0 := by
  rw [← fusion_fibre_identity]
  exact fusionTruthFibre_small h a f g xs

/-- The proof value obtained from the actual compiler output, after all three
universal eliminations, belongs to that bottom universe. -/
theorem compiledFusionProofValue_small (h : CofinalInaccessibles.{u})
    {a : ZFSet.{u}} (f g : Value a mapping) (xs : Value a sequence) :
    (compiledFusionProofValue f g xs).1 ∈
      universeSet h (integrationSeed a) 0 :=
  (universeSet_closed h (integrationSeed a) 0).transitive _
    (fusionTruthFibre_small h a f g xs) (compiledFusionProofValue f g xs).2

/-- The concrete endpoint motive used to test dependent identity elimination
is also a bottom-universe code. -/
theorem compiledEndpointMotive_small (h : CofinalInaccessibles.{u})
    {a : ZFSet.{u}} (f g : Value a mapping) (xs : Value a sequence) :
    endpointMotive (compiledFusionIdentityPoint f g xs) ∈
      universeSet h (integrationSeed a) 0 := by
  apply (universeSet_closed h (integrationSeed a) 0).singleton_mem
  exact (universeSet_closed h (integrationSeed a) 0).transitive _
    (sourceType_small h a 0 sequence)
    (compiledFusionIdentityPoint f g xs).1.1.2.2

/-- The value returned by dependent `J` for the endpoint motive remains in
the same bottom universe. -/
theorem compiledConsumedEndpoint_small (h : CofinalInaccessibles.{u})
    {a : ZFSet.{u}} (f g : Value a mapping) (xs : Value a sequence) :
    (compiledConsumedEndpoint f g xs).1 ∈
      universeSet h (integrationSeed a) 0 := by
  rw [compiledConsumedEndpoint_value]
  exact (universeSet_closed h (integrationSeed a) 0).transitive _
    (sourceType_small h a 0 sequence)
    (compiledFusionIdentityPoint f g xs).1.1.2.2

/-- Elementary closure plus containment of every encoded list is not enough
to justify the list type's universe membership. -/
theorem finiteClosure_does_not_supply_list_smallness :
    ∃ U a : ZFSet.{u}, Closed U ∧ a ∈ U ∧
      ZFSetList.listCode a ⊆ U ∧ ZFSetList.listCode a ∉ U :=
  ZFSetListClosure.closed_does_not_imply_list_closed

#print axioms sourceType_small
#print axioms proofContextFamily_small
#print axioms openNativeProofValue_small
#print axioms fusionTruthFibre_small
#print axioms compiledIdentityFamily_small
#print axioms compiledFusionProofValue_small
#print axioms compiledEndpointMotive_small
#print axioms compiledConsumedEndpoint_small
#print axioms finiteClosure_does_not_supply_list_smallness

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeHOLCompiledMapFusionUniverse
