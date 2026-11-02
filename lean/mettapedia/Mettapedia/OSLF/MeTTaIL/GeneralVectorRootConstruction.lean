import Mettapedia.OSLF.MeTTaIL.GeneralVectorRootReadout
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInstantiation
import Mettapedia.OSLF.MeTTaIL.GeneralVectorInstanceAgreement

/-! Construct actual scoped root-firing witnesses from typed ordinary
constructor/vector instances. The authored admitted binding specification is
retained, including occurrence metadata; no inferred replacement is assumed.
-/

set_option autoImplicit false
set_option maxHeartbeats 5000000

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching GeneralScopedMatch
open Mettapedia.GSLT.LanguageDef.WellSorted

theorem vector_rootFiring_construct {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index : Nat} {bindings : Bindings}
    {source target : Pattern}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (admitted : admittedFor rule spec = true)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (premiseFree : rule.premises = [])
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (defined : Defined bindings rule.left.freeFvarNames)
    (typed : CapturesTyped environment.language environment.free bound rule.typeContext bindings)
    (sourceTyped : OpenPatternWellSorted environment.language environment.free bound type source)
    (targetTyped : OpenPatternWellSorted environment.language environment.free bound type target)
    (input : applyBindings bindings rule.left = source)
    (output : applyBindings bindings rule.right = target) :
    ∃ trace captured, GeneralPremise.RootFiring environment bound type source index trace captured captured [] target := by
  have dependencies : ∀ name ∈ rule.left.freeFvarNames, dependencies? spec name = some [] := by
    intro name member
    obtain ⟨body, found⟩ := defined name member
    obtain ⟨expected, declaredType, _⟩ := typed (name, body) (raw_lookup_member found)
    exact dependencies_empty_of_admitted admitted zero declaredType
  obtain ⟨raw, matched, compatible, _, _⟩ := vector_match_instance bindings leftShape defined
  rw [input] at matched
  obtain ⟨captured, matching, read⟩ := binderFree_scoped_of_matchRel_admitted (initial := []) admitted
    (GeneralRuleBindingInference.vector_binderFree leftShape) (NameCoherent.left rule) dependencies
    matched compatible sourceTyped.2.2.2 sourceTyped.2.2.1 (by intro _ member; cases member)
  have capturedTyped := read.typed_admitted typed admitted zero
  have roots := read.rootValues typed
  have rightDefined : GeneralPremise.BoundNames captured rule.right.freeFvarNames :=
    fun name member => GeneralPremise.matching_bound_names matching name (rightBound name member)
  have rightDependencies : ∀ name ∈ rule.right.freeFvarNames, dependencies? spec name = some [] :=
    fun name member => dependencies name (rightBound name member)
  have reduct := vector_instantiation_exact
    (operation := ScopedReflectiveExecution.binderOperation environment.reflection rule)
    admitted rightShape (NameCoherent.right rule) rightDefined roots read rightDependencies
  rw [output] at reduct
  obtain ⟨trace, traced⟩ := GeneralScopedMatchMachine.matches_trace matching
  exact ⟨trace, captured, .fire declared specified admitted sourceTyped traced capturedTyped
    (premiseFree ▸ .nil) reduct targetTyped⟩

theorem vector_rootFiring_target {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {index : Nat} {bindings : Bindings}
    {source target : Pattern} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : ScopedRuleMatching.Assignment} {history : List GeneralPremise.Event}
    (declared : environment.language.rewrites[index]? = some rule)
    (specified : GeneralPremise.specification? environment index = some spec)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (leftShape : VectorFirstOrder rule.left) (rightShape : VectorFirstOrder rule.right)
    (premiseFree : rule.premises = [])
    (rightBound : ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames)
    (input : applyBindings bindings rule.left = source)
    (firing : GeneralPremise.RootFiring environment bound type source index trace captured completed history target) :
    completed = captured ∧ history = [] ∧ target = applyBindings bindings rule.right := by
  obtain ⟨sameCaptures, emptyHistory, sourceRead, targetRead⟩ := vector_rootFiring_readout declared specified zero
    leftShape (GeneralRuleBindingInference.vector_binderFree rightShape) premiseFree firing
  refine ⟨sameCaptures, emptyHistory, ?_⟩
  exact targetRead.symm.trans (vector_rule_output_unique leftShape rightShape rightBound
    (ordinary captured) bindings (sourceRead.trans input.symm))

#print axioms vector_rootFiring_construct
#print axioms vector_rootFiring_target

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
