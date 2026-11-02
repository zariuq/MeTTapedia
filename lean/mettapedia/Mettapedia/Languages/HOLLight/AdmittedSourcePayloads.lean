import Mettapedia.Languages.HOLLight.RecursiveSpaceTypeInstantiation
import Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

/-!
# Source payload types extracted from admitted constructor fields

The registered source type syntax represents every simple HOL field type.
Reversing the admitted inventory's ordered fields therefore supplies the
existing predicate-handler payload encoding without a per-signature table.
The six source-law instances use the existing checked replay suffix.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.AdmittedSourcePayloads

open Mettapedia.Logic Mettapedia.Languages.OpenTheory Mettapedia.TypeTheory
open Mettapedia.GSLT.LanguageDef
open IndexedPolynomial.Description

def sourceFields (fields : List (List (HOL.Ty AtomicTy))) : List (List Ty) :=
  fields.map (List.map ReverseTranslation.reverseTy)

theorem sourceFields_toHOL (fields : List (List (HOL.Ty AtomicTy))) :
    (sourceFields fields).map (List.map Ty.toHOL) = fields := by
  simp [sourceFields, List.map_map, Function.comp_def, ReverseTranslation.toHOL_reverseTy]

def payload (fields : List (List (HOL.Ty AtomicTy))) : Ty :=
  RecursiveSpaceTypeInstantiation.constructorPayload (sourceFields fields)

theorem payload_toHOL (fields : List (List (HOL.Ty AtomicTy))) :
    (payload fields).toHOL = HOL.FiniteConstructorEncoding.payloadType fields := by
  rw [payload, RecursiveSpaceTypeInstantiation.constructorPayload_toHOL, sourceFields_toHOL]

def targetOperations (operations : RecursiveSpaceSourceReadback.Operations) (parameter : Name)
    (fields : List (List (HOL.Ty AtomicTy))) : RecursiveSpaceSourceReadback.Operations :=
  RecursiveSpaceTypeInstantiation.Operations.instantiate operations
    (RecursiveSpaceTypeInstantiation.effectiveTypes [(parameter, payload fields)])

structure Instance (policy : AxiomPolicy) [DecidablePred policy]
    (before : ProofExecution.Registered.State) (operations : RecursiveSpaceSourceReadback.Operations)
    (parameter : Name) (fields : List (List (HOL.Ty AtomicTy))) where
  source : RecursiveSpaceTypeInstantiation.Result policy before operations [(parameter, payload fields)]
  payloadExact : (targetOperations operations parameter fields).payload = payload fields

theorem Instance.payload_toHOL {policy : AxiomPolicy} [DecidablePred policy]
    {before : ProofExecution.Registered.State} {operations : RecursiveSpaceSourceReadback.Operations}
    {parameter : Name} {fields : List (List (HOL.Ty AtomicTy))}
    (result : Instance policy before operations parameter fields) :
    (targetOperations operations parameter fields).payload.toHOL =
      HOL.FiniteConstructorEncoding.payloadType fields :=
  (congrArg Ty.toHOL result.payloadExact).trans (AdmittedSourcePayloads.payload_toHOL fields)

def instantiate? (policy : AxiomPolicy) [DecidablePred policy]
    (before : ProofExecution.Registered.State) (operations : RecursiveSpaceSourceReadback.Operations)
    (indices : RecursiveSpaceSourceReadback.CacheIndices) (parameter : Name)
    (fields : List (List (HOL.Ty AtomicTy))) : Option (Instance policy before operations parameter fields) := do
  let source ← RecursiveSpaceTypeInstantiation.instantiate? policy before operations indices [(parameter, payload fields)]
  if same : Ty.same (targetOperations operations parameter fields).payload (payload fields) = true then
    pure ⟨source, (Ty.same_eq_true_iff _ _).mp same⟩
  else none

universe u
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
    {context : List I.SortCode}

def fields (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : HOL.IndexedContainerPositionTerms.Reading I
      (IndexedPositiveContainer.Unindexed.liftRegistry source I) Symbol) : List (List (HOL.Ty AtomicTy)) :=
  (AdmittedContainerHOL.codes block registered).map reading.fields

def admittedPayload (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : HOL.IndexedContainerPositionTerms.Reading I
      (IndexedPositiveContainer.Unindexed.liftRegistry source I) Symbol) : Ty :=
  payload (fields block registered reading)

theorem admittedPayload_toHOL (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : HOL.IndexedContainerPositionTerms.Reading I
      (IndexedPositiveContainer.Unindexed.liftRegistry source I) Symbol) :
    (admittedPayload block registered reading).toHOL =
      HOL.FiniteConstructorEncoding.payloadType ((AdmittedContainerHOL.codes block registered).map reading.fields) :=
  payload_toHOL _

def instantiateAdmitted? (policy : AxiomPolicy) [DecidablePred policy]
    (before : ProofExecution.Registered.State) (operations : RecursiveSpaceSourceReadback.Operations)
    (indices : RecursiveSpaceSourceReadback.CacheIndices) (parameter : Name)
    (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : HOL.IndexedContainerPositionTerms.Reading I
      (IndexedPositiveContainer.Unindexed.liftRegistry source I) Symbol) :=
  instantiate? policy before operations indices parameter (fields block registered reading)

#print axioms sourceFields_toHOL
#print axioms payload_toHOL
#print axioms admittedPayload_toHOL
#print axioms instantiateAdmitted?

end Mettapedia.Languages.HOLLight.AdmittedSourcePayloads
