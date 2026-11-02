import Mettapedia.OSLF.MeTTaIL.GeneralPremiseSemantics

/-! Static two-input/one-output queries retain their exact provider row,
input instantiations and output matching evidence. An empty dynamic
provider cannot supply an alternative unrecorded row.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralPremise

open Syntax RuleBinding ScopedRuleMatching

theorem two_input_output_row_readout {environment : Environment} {context : Context}
    {relation : String} {firstSchema secondSchema outputSchema : Pattern}
    {firstType secondType outputType : TypeExpr} {initial final : Assignment} {rowIndex : Nat}
    {origins : List (Nat × List GeneralScopedMatchMachine.BagChoice)}
    (empty : environment.dynamic = DynamicProvider.empty)
    (signature : signature? environment.provider relation 3 =
      some ⟨relation, [firstType, secondType, outputType], [.input, .input, .output]⟩)
    (query : TracedQuery environment context relation [firstSchema, secondSchema, outputSchema] initial rowIndex final origins) :
    ∃ first second output,
      environment.provider.rows[rowIndex]? = some ⟨relation, [first, second, output]⟩ ∧
      instantiateAt? context.rule context.spec context.bound.length (context.site 0) [] 0 initial firstSchema = some first ∧
      instantiateAt? context.rule context.spec context.bound.length (context.site 1) [] 0 initial secondSchema = some second ∧
      GeneralScopedMatch.Matches context.rule context.spec context.bound.length (context.site 2) [] 0 initial outputSchema output final := by
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
        cases tail with
        | output outputMatch tail =>
          cases tail
          have relationSame : relation' = relation := typed.1
          subst relation'
          exact ⟨_, _, _, present, firstRead, secondRead, outputMatch.matching⟩
  | dynamicRow registered declared resolved source present typed held finalTyped =>
    simp only [empty, DynamicProvider.empty] at source

#print axioms two_input_output_row_readout

end Mettapedia.OSLF.MeTTaIL.GeneralPremise
