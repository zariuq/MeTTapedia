import Mettapedia.OSLF.MeTTaIL.GeneralVectorInputQuery

/-! Read-only two-argument provider queries preserve their matched
assignment. Actual root firings read both rule sides and the provider row
through one ordinary substitution.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

theorem two_input_row_readout {environment : Environment} {context : Context}
    {relation : String} {firstSchema secondSchema : Pattern} {firstType secondType : TypeExpr}
    {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (empty : environment.dynamic = DynamicProvider.empty)
    (signature : signature? environment.provider relation 2 = some ⟨relation, [firstType, secondType], [.input, .input]⟩)
    (query : TracedQuery environment context relation [firstSchema, secondSchema] initial rowIndex final origins) :
    final = initial ∧ ∃ first second,
      environment.provider.rows[rowIndex]? = some ⟨relation, [first, second]⟩ ∧
      instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0 initial firstSchema = some first ∧
      instantiateAt? context.rule context.spec context.bound.length (context.site 1) [] 0 initial secondSchema = some second := by
  change Interpreted.TracedQuery ordinaryInterpretation _ _ _ _ _ _ _ _ at query
  cases query with
  | @row rowIndex row actualSignature final origins present declared typed held finalTyped =>
    have same := Option.some.inj (declared.symm.trans signature)
    subst actualSignature
    obtain ⟨relation', values⟩ := row
    cases held with
    | input firstRead tail =>
      cases tail with
      | input secondRead tail =>
        cases tail
        have relationSame : relation' = relation := typed.1
        subst relation'
        exact ⟨rfl, _, _, present, firstRead, secondRead⟩
  | dynamicRow registered declared resolved source present typed held finalTyped =>
    simp only [empty, DynamicProvider.empty] at source

end Mettapedia.OSLF.MeTTaIL.GeneralPremise

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax Match RuleBinding ScopedRuleMatching GeneralScopedMatch

theorem vector_two_input_root_readout {environment : GeneralPremise.Environment} {bound : List TypeExpr}
    {type firstType secondType : TypeExpr} {rule : RewriteRule} {spec : RuleBindingSpec} {ordinal : Nat}
    {source target : Pattern} {relation firstName secondName : String}
    {trace : List GeneralScopedMatchMachine.BagChoice} {captured completed : ScopedRuleMatching.Assignment}
    {history : List GeneralPremise.Event}
    (selected : environment.language.rewrites[ordinal]? = some rule)
    (specified : GeneralPremise.specification? environment ordinal = some spec)
    (zero : GeneralPremise.checkZeroDependencies spec = true)
    (leftShape : VectorFirstOrder rule.left) (rightShape : binderFree rule.right = true)
    (premise : rule.premises = [.relationQuery relation [.fvar firstName, .fvar secondName]])
    (empty : environment.dynamic = GeneralPremise.DynamicProvider.empty)
    (signature : GeneralPremise.signature? environment.provider relation 2 =
      some ⟨relation, [firstType, secondType], [.input, .input]⟩)
    (firing : GeneralPremise.RootFiring environment bound type source ordinal trace captured completed history target) :
    ∃ (bindings : Bindings) (rowIndex : Nat),
      applyBindings bindings rule.left = source ∧ applyBindings bindings rule.right = target ∧
      environment.provider.rows[rowIndex]? = some ⟨relation,
        [applyBindings bindings (.fvar firstName), applyBindings bindings (.fvar secondName)]⟩ := by
  cases firing with
  | fire actualDeclared actualSpecified admitted sourceTyped matching typed premises reduct targetTyped =>
    have sameRule := Option.some.inj (actualDeclared.symm.trans selected)
    subst sameRule
    have sameSpec := Option.some.inj (actualSpecified.symm.trans specified)
    subst sameSpec
    have roots := typed.rootValues zero
    have sourceRead := vector_matching_readout leftShape matching.matching (fun _ _ found => found) roots
    rw [premise] at premises
    cases premises with
    | cons head tail =>
      cases tail
      cases head with
      | query queried =>
        obtain ⟨same, first, second, present, firstInput, secondInput⟩ :=
          GeneralPremise.two_input_row_readout empty signature queried
        rw [same] at reduct
        have firstRead := binderFree_instantiation_readout (by rfl) roots firstInput
        have secondRead := binderFree_instantiation_readout (by rfl) roots secondInput
        have targetRead := binderFree_instantiation_readout rightShape roots reduct
        rw [← firstRead, ← secondRead] at present
        exact ⟨ordinary captured, _, sourceRead, targetRead, present⟩

#print axioms GeneralPremise.two_input_row_readout
#print axioms vector_two_input_root_readout

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
