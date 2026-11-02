import Mettapedia.GSLT.LanguageDef.PositiveInductiveBlockBridge
import Mettapedia.TypeTheory.IndexedPositiveContainer
import Mettapedia.Logic.HOL.IndexedContainerFieldProofs

/-!
# HOL constructor proof production from admitted positive blocks

The existing registered-code embedding retains source declaration order and
the selected container meanings. The resulting code list supplies the shared
HOL field, result and position compilers. Primitive HOL readings and their
retained field evidence are explicit inputs to the proof-producing route.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.IndexedContainerPositionTerms
open Mettapedia.TypeTheory.IndexedPolynomial.Description
open Mettapedia.TypeTheory
universe u v w
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
  {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ : Ctx Base}

def codes (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered) :
    List (IndexedPositiveContainer.Code I (IndexedPositiveContainer.Unindexed.liftRegistry source I) parameterCount context) :=
  List.ofFn (IndexedPositiveContainer.Unindexed.blockCode block registered)

def sourceOccurrence (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const)
    (occurrence : Fin ((codes block registered).map reading.fields).length) : Fin block.constructors.length :=
  ⟨occurrence.val, by simpa only [List.length_map, codes, List.length_ofFn] using occurrence.isLt⟩

theorem codeAt_source (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const)
    (occurrence : Fin ((codes block registered).map reading.fields).length) :
    codeAt reading (codes block registered) occurrence =
      IndexedPositiveContainer.Unindexed.blockCode block registered (sourceOccurrence block registered reading occurrence) := by
  simp only [codeAt, codes, sourceOccurrence, List.get_eq_getElem, List.getElem_ofFn]

def inventory (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) : IndexedConstructorGuards.ConstructorPrograms Const Γ :=
  guards.constructors (codes block registered) rho numeral

theorem inventory_arity (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number) :
    (inventory block registered guards rho numeral).fields.length = block.constructors.length := by
  simp only [inventory, FieldGuards.constructors, List.length_map, codes, List.length_ofFn]

theorem source_name (block : PositiveInductiveBlock.Admitted source I parameterCount context)
    (registered : block.WellRegistered)
    (reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const)
    (occurrence : Fin ((codes block registered).map reading.fields).length) :
    (block.constructors.get (sourceOccurrence block registered reading occurrence)).name =
      (block.constructors.map (·.name))[occurrence.val]'(by
        simpa only [List.length_map, sourceOccurrence] using (sourceOccurrence block registered reading occurrence).isLt) := by
  simp only [List.get_eq_getElem, List.getElem_map, sourceOccurrence]

def payloadProof {assumptions : List (Formula Const Γ)}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading (codes block registered) occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading (codes block registered) occurrence) rho arguments) :
    ProofSyntax Const assumptions
      (ConstructorDataPredicates.guard (codes block registered |>.map reading.fields)
        (inventory block registered guards rho numeral).allowed
        (payloadTerm reading (codes block registered) occurrence arguments)) :=
  guards.payloadProof (codes block registered) rho numeral occurrence arguments evidence

def resultProof {assumptions : List (Formula Const Γ)}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : FiniteConstructorEncoding.Arguments Const Γ (reading.fields (codeAt reading (codes block registered) occurrence)))
    (evidence : guards.Evidence assumptions (codeAt reading (codes block registered) occurrence) rho arguments) :
    ProofSyntax Const assumptions ((inventory block registered guards rho numeral).resultGuard
      (payloadTerm reading (codes block registered) occurrence arguments)
      (reading.indexTerm (codeAt reading (codes block registered) occurrence) rho arguments)) :=
  guards.resultGuardProof (codes block registered) rho numeral occurrence arguments evidence

#print axioms codeAt_source
#print axioms resultProof
end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
