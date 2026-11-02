import Mettapedia.GSLT.LanguageDef.AdmittedSourceCasePremises
import Mettapedia.Logic.HOL.IndexedContainerPayloadContexts

/-!
# Payload contexts from the actual scoped constructor cases

The original first case premise supplies every data and registered-shape
guard. Its constructor-frame assignment restricts to the ambient variables.
Those proofs realize the structurally generated payload context without
assuming the desired constructor case or discarding its remaining premises.
Recursive membership remains in the separate original child condition.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL

open Mettapedia.Logic.HOL Mettapedia.TypeTheory
open IndexedContainerPositionTerms IndexedPolynomial.Description FiniteConstructorEncoding PredicateContexts
universe u v w
variable {I : Interface.{u}} {source : PositiveInductiveBlock.Registry} {parameterCount : Nat}
    {context : List I.SortCode} {Base : Type v} {Const : Ty Base → Type w} {Γ Ξ : Ctx Base}
    (block : PositiveInductiveBlock.Admitted source I parameterCount context) (registered : block.WellRegistered)
    {reading : Reading I (IndexedPositiveContainer.Unindexed.liftRegistry source I) Const}
    (guards : FieldGuards reading)
    (rho : Subst Const (context.map reading.indices.sort ++ reading.indices.parameters) Γ)
    (numeral : Nat → Term Const Γ reading.number)
    {space : Ty Base}
    (constructorCode : Term Const Γ (reading.number ⇒
      payloadType ((codes block registered).map reading.fields) ⇒ (reading.number ⇒ space) ⇒ space))
    (zero : ClosedTerm Const reading.number) (successor : ClosedTerm Const (reading.number ⇒ reading.number))
    (bottomCode : Term Const Γ space) (predicate : Term Const Γ (space ⇒ .prop))
    (assumptions : List (Formula Const Γ))

private theorem comp_assoc {Ω Φ : Ctx Base}
    (last : Subst Const Ω Ξ) (middle : Subst Const Φ Ω) (first : Subst Const Γ Φ) :
    @Eq (Subst Const Γ Ξ) (Subst.comp last (Subst.comp middle first))
      (Subst.comp (Subst.comp last middle) first) := by
  funext type index
  exact subst_comp last middle (first index)

def scopedSourcePayloadRealizer
    (base : Telescope Const Γ)
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence)))
    (baseRealizer :
      let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
      base.Realizes (Subst.comp images (Subst.ofRename signature.constructorRenaming))
        (scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
          bottomCode predicate assumptions images occurrence arguments)) :
    let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
    (guards.payloadTelescope (codeAt reading (codes block registered) occurrence) base rho).Realizes
      (FieldGuards.payloadAssignment (codeAt reading (codes block registered) occurrence)
        (Subst.comp images (Subst.ofRename signature.constructorRenaming)) arguments)
      (scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
        bottomCode predicate assumptions images occurrence arguments) := by
  let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
  let scope : Subst Const Γ signature.constructorContext := Subst.ofRename signature.constructorRenaming
  let fields := scopedSourceFieldEvidence block registered guards rho numeral constructorCode zero successor
    bottomCode predicate assumptions images occurrence arguments
  let evidence := guards.castEvidence (codeAt reading (codes block registered) occurrence)
    (comp_assoc images scope rho) arguments fields
  exact fun {type} index => guards.realizePayload (codeAt reading (codes block registered) occurrence) base rho
    (Subst.comp images scope) arguments baseRealizer evidence index

theorem scopedSourcePayloadRealizer_free
    (base : Telescope Const Γ)
    (images : Subst Const
      (recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode).constructorContext Ξ)
    (occurrence : Fin ((codes block registered).map reading.fields).length)
    (arguments : Arguments Const Ξ (reading.fields (codeAt reading (codes block registered) occurrence)))
    (baseRealizer :
      let signature := recursiveSignature block registered (guards := guards) rho numeral zero successor bottomCode constructorCode
      base.Realizes (Subst.comp images (Subst.ofRename signature.constructorRenaming))
        (scopedSourceCaseAssumptions block registered guards rho numeral constructorCode zero successor
          bottomCode predicate assumptions images occurrence arguments))
    (baseFree : ∀ {type} (index : Var Γ type), (baseRealizer index).FunctionExtensionalityFree) :
    ∀ {type} (index : Var (FieldGuards.payloadScope (reading := reading)
        (codeAt reading (codes block registered) occurrence) Γ) type),
      (scopedSourcePayloadRealizer block registered guards rho numeral constructorCode zero successor
        bottomCode predicate assumptions base images occurrence arguments baseRealizer index).FunctionExtensionalityFree := by
  unfold scopedSourcePayloadRealizer
  apply guards.realizePayload_free
  · exact baseFree
  · apply guards.castEvidence_free
    exact scopedSourceFieldEvidence_free block registered guards rho numeral constructorCode zero successor
      bottomCode predicate assumptions images occurrence arguments

#print axioms scopedSourcePayloadRealizer_free

end Mettapedia.GSLT.LanguageDef.AdmittedContainerHOL
