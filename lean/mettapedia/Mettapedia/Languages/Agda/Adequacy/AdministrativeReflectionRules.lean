import Mettapedia.Languages.Agda.Adequacy.AdministrativeReflectionData

/-!
# Source algebra for the administrative equality presentation

Prior rules reuse the checked twenty-four-family algebra at their original
premise positions. Each new case builds source equality from interpreted
children and an actual typed head equality. Empty and cons prefix equations
use raw observation equations without erasing their native histories.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection

open Mettapedia.OSLF.Binding
open Mettapedia.OSLF.Binding.FiniteRulePremiseLists
open Structural.AdministrativeStatics

def interpretRule {j : Judgment} (shape : RuleShape j)
    (ih : Evidence Interpretation (premises shape)) : Interpretation j := by
  cases shape <;> simp only [premises] at ih
  case prior shape =>
    exact ofPriorInterpretation (SpineReflection.interpretRule shape
      (fun position => toPriorInterpretation (priorPremiseEvidence ih position)))
  case spineRefl Γ A es B =>
    intro Δ ctx input observed
    let action := ih 0 Δ ctx input observed
    exact ⟨action.spine, action.spine, action.output, action.spineObserved, action.spineObserved,
      action.outputObserved, action.equality⟩
  case spineSymm Γ A es fs B =>
    intro Δ ctx input observed
    let equal := ih 0 Δ ctx input observed
    exact ⟨equal.second, equal.first, equal.output, equal.secondObserved, equal.firstObserved,
      equal.outputObserved, fun heads => .symm (equal.proof (.symm heads))⟩
  case spineTrans Γ A es fs gs B =>
    intro Δ ctx input observed
    let first := ih 0 Δ ctx input observed
    let second := ih 1 Δ ctx input observed
    exact ⟨first.first, second.second, first.output, first.firstObserved, second.secondObserved,
      first.outputObserved, fun heads => .trans (first.proof heads)
        (second.at first.secondObserved second.secondObserved first.outputObserved (.trans (.symm heads) heads))⟩
  case spineCons Γ A B u v es fs C =>
    intro Δ ctx input observed
    let parts := Observation.piView A B observed
    let arguments := ih 0 Δ ctx
    let tails := ih 1 Δ ctx (parts.body.instantiate arguments.left)
      (Observation.typeBody_instantiate B parts.body_eq arguments.leftObserved)
    exact ⟨.apply arguments.left :: tails.first, .apply arguments.right :: tails.second, tails.output,
      Observation.cons_of_some (Observation.apply_of_some arguments.leftObserved) tails.firstObserved,
      Observation.cons_of_some (Observation.apply_of_some arguments.rightObserved) tails.secondObserved,
      tails.outputObserved,
      fun heads => tails.proof (.appCong (parts.result_eq ▸ heads) (arguments.atType parts.domain_eq))⟩
  case spineAppend Γ A es fs B gs hs C =>
    intro Δ ctx input observed
    let first := ih 0 Δ ctx input observed
    let second := ih 1 Δ ctx first.output first.outputObserved
    refine ⟨first.first ++ second.first, first.second ++ second.second, second.output,
      Observation.append_of_some first.firstObserved second.firstObserved,
      Observation.append_of_some first.secondObserved second.secondObserved, second.outputObserved, ?_⟩
    intro f g heads
    simpa only [StaticSpecification.Term.applySpine_append] using second.proof (first.proof heads)
  case spineInputConversion Γ A' A es fs B =>
    intro Δ ctx input observed
    let types := ih 0 Δ ctx
    let spines := ih 1 Δ ctx types.right types.rightObserved
    exact ⟨spines.first, spines.second, spines.output, spines.firstObserved, spines.secondObserved,
      spines.outputObserved, fun heads => spines.proof (.conv heads (types.at observed types.rightObserved))⟩
  case spineOutputConversion Γ A es fs B B' =>
    intro Δ ctx input observed
    let spines := ih 0 Δ ctx input observed
    let types := ih 1 Δ ctx
    exact ⟨spines.first, spines.second, types.right, spines.firstObserved, spines.secondObserved,
      types.rightObserved, fun heads => .conv (spines.proof heads) (types.at spines.outputObserved types.rightObserved)⟩
  case appendEmpty Γ A es B =>
    intro Δ ctx input observed
    let action := ih 0 Δ ctx input observed
    exact ⟨action.spine, action.spine, action.output, action.spineObserved,
      (observe_empty_prefix es).symm.trans action.spineObserved, action.outputObserved, action.equality⟩
  case appendCons Γ A u es fs B =>
    intro Δ ctx input observed
    let action := ih 0 Δ ctx input observed
    exact ⟨action.spine, action.spine, action.output, action.spineObserved,
      (observe_cons_prefix u es fs).symm.trans action.spineObserved, action.outputObserved, action.equality⟩
  case eliminationCongruence Γ f g A es fs B =>
    intro Δ ctx
    let heads := ih 0 Δ ctx
    let spines := ih 1 Δ ctx heads.typeValue heads.typeObserved
    exact ⟨heads.left.applySpine spines.first, heads.right.applySpine spines.second, spines.output,
      Observation.eliminate_of_some heads.leftObserved spines.firstObserved,
      Observation.eliminate_of_some heads.rightObserved spines.secondObserved,
      spines.outputObserved, spines.proof heads.proof⟩
  case emptyElimination Γ f A =>
    intro Δ ctx
    let head := ih 0 Δ ctx
    exact ⟨head.value, head.value, head.typeValue,
      (Observation.eliminate_nil f).trans head.observed, head.observed, head.typeObserved, .refl head.proof⟩
  case nestedElimination Γ f A es B fs C =>
    intro Δ ctx
    let head := ih 0 Δ ctx
    let first := ih 1 Δ ctx head.typeValue head.typeObserved
    let second := ih 2 Δ ctx first.output first.outputObserved
    refine ⟨(head.value.applySpine first.spine).applySpine second.spine,
      head.value.applySpine (first.spine ++ second.spine), second.output,
      Observation.eliminate_of_some (Observation.eliminate_of_some head.observed first.spineObserved) second.spineObserved,
      Observation.eliminate_of_some head.observed (Observation.append_of_some first.spineObserved second.spineObserved),
      second.outputObserved, ?_⟩
    simpa only [StaticSpecification.Term.applySpine_append] using
      StaticSpecification.TermEq.refl (second.proof (first.proof head.proof))

end Mettapedia.Languages.Agda.StaticAdequacy.AdministrativeReflection
