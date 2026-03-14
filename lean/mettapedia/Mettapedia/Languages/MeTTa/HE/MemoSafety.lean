import MeTTailCore

/-!
# HE Memo Safety Classification

Concrete instantiation of the generic `MeTTaIL.EffectSafety` framework for the
current HE rewrite system.

This does not change execution. It demonstrates that the existing premise and
transition metadata are rich enough to distinguish:

- deterministic read-only rules (`MC_Grounded`)
- nondeterministic read-only rules (`MC_Equation`)
- oracle-style rules that are not memo-safe (`MC_Collapse`)
-/

namespace Mettapedia.Languages.MeTTa.HE.MemoSafety

open MeTTailCore.MeTTaIL.Syntax
open MeTTailCore.MeTTaIL.EffectSafety

def heRelationEffectClass : RelationEffectProfile
  | "isEmpty" => some .pureStructural
  | "isError" => some .pureStructural
  | "changedToEmpty" => some .pureStructural
  | "changedToError" => some .pureStructural
  | "metaType" => some .pureStructural
  | "typeMatchesMetaOrAtom" => some .pureStructural
  | "typeNotMatchesMetaOrAtom" => some .pureStructural
  | "needsTypeCast" => some .pureStructural
  | "needsInterpExpr" => some .pureStructural
  | "notExpression" => some .pureStructural
  | "isExecutable" => some .pureStructural
  | "notExecutable" => some .pureStructural
  | "funcArgTypes" => some .pureStructural
  | "parseSwitchMinimalCall" => some .pureStructural
  | "selectSwitchResult" => some .pureStructural
  | "isReducible" => some .pureStructural
  | "isNotReducible" => some .pureStructural
  | "parseAssertCall" => some .pureStructural
  | "assertMatchesTrue" => some .pureStructural
  | "assertNotTrue" => some .pureStructural
  | "mkAssertError" => some .pureStructural
  | "parseCaseCall" => some .pureStructural
  | "parseSuperpose" => some .pureStructural
  | "isSuperpose_empty" => some .pureStructural
  | "parseMatchCall" => some .pureStructural
  | "parseUnifyCall" => some .pureStructural
  | "localMatch" => some .pureStructural
  | "localNoMatch" => some .pureStructural
  | "parseCollapseCall" => some .pureStructural
  | "noTypeAtAll" => some .readOnlyLookup
  | "typeOfRaw" => some .readOnlyLookup
  | "typeOf" => some .readOnlyLookup
  | "applicableFuncTypeRaw" => some .readOnlyLookup
  | "applicableFuncType" => some .readOnlyLookup
  | "applicableFuncTypeHas" => some .readOnlyLookup
  | "needsTupleInterp" => some .readOnlyLookup
  | "eqQueryHas" => some .readOnlyLookup
  | "noEqQuery" => some .readOnlyLookup
  | "groundedCallResult" => some .readOnlyLookup
  | "spaceQueryNoMatch" => some .readOnlyLookup
  | "eqQueryRaw" => some .nondeterministicReadOnly
  | "eqQueryResult" => some .nondeterministicReadOnly
  | "spaceQueryMatch" => some .nondeterministicReadOnly
  | "collapseBind" => some .oracleIO
  | _ => none

def heTransitionEffectClass : TransitionEffectProfile
  | "emit_done" => some .pureStructural
  | "propagate_error" => some .pureStructural
  | "recurse_state" => some .pureStructural
  | "spawn_eval_args" => some .pureStructural
  | "emit_call" => some .pureStructural
  | "resolve_call" => some .pureStructural
  | "emit_return" => some .pureStructural
  | "advance_state" => some .pureStructural
  | _ => none

private def summaryForPremises
    (premises : List Premise)
    (transitionEffect : EffectClass := .pureStructural) :
    Option RuleEffectSummary := do
  let premiseEffect ← premisesEffectClass? heRelationEffectClass premises
  pure { premiseEffect := premiseEffect, transitionEffect := transitionEffect }

private def mcGroundedPremises : List Premise :=
  [ .relationQuery "groundedCallResult" [.fvar "space", .fvar "atom", .fvar "result"] ]

private def mcEquationPremises : List Premise :=
  [ .relationQuery "eqQueryResult" [.fvar "space", .fvar "atom", .fvar "rhs"]
  , .relationQuery "notExecutable" [.fvar "atom"]
  ]

private def mcCollapsePremises : List Premise :=
  [ .relationQuery "notExecutable" [.fvar "atom"]
  , .relationQuery "parseCollapseCall" [.fvar "atom", .fvar "expr"]
  , .relationQuery "collapseBind" [.fvar "expr", .fvar "ty", .fvar "packed"]
  ]

/-- Public summary value for the current `collapseBind` oracle premise batch. -/
def collapseBindSummary : Option RuleEffectSummary :=
  summaryForPremises mcCollapsePremises

theorem collapseBind_effect_oracleIO :
    heRelationEffectClass "collapseBind" = some .oracleIO := rfl

theorem collapseBind_overallEffect_oracleIO :
    collapseBindSummary.map RuleEffectSummary.overallEffect =
      some .oracleIO := by
  decide

theorem collapseBind_memoization_inadmissible :
    collapseBindSummary.map
        (fun s => s.memoizationContractAdmissible) =
      some false := by
  decide

example : (summaryForPremises mcGroundedPremises).map RuleEffectSummary.overallEffect =
    some .readOnlyLookup := by
  decide

example : (summaryForPremises mcGroundedPremises).map (fun s => s.supportsMemoShape .scalar) =
    some true := by
  decide

example : (summaryForPremises mcEquationPremises).map RuleEffectSummary.overallEffect =
    some .nondeterministicReadOnly := by
  decide

example : (summaryForPremises mcEquationPremises).map (fun s => s.supportsMemoShape .scalar) =
    some false := by
  decide

example : (summaryForPremises mcEquationPremises).map (fun s => s.supportsMemoShape .outcomeSet) =
    some true := by
  decide

example : (summaryForPremises mcCollapsePremises).map RuleEffectSummary.overallEffect =
    some .oracleIO := by
  decide

example : (summaryForPremises mcCollapsePremises).map (fun s => s.memoizationContractAdmissible) =
    some false := by
  decide

end Mettapedia.Languages.MeTTa.HE.MemoSafety
