import Mettapedia.Logic.HOL.SetCodeOperators
import Mettapedia.Logic.HOL.Embedding.ZFSetTotalProjectionInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProductProofInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofDecoding

/-!
# The closed set-code operators have the existing actual set meanings

The eight lambda bodies are compared to the independently defined trace,
pairing, total projection and truth-code operations. The projection comparison
retains the specified empty-default interpretation of the selector.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetCodeOperatorsInterpretation
open SetCodeOperators SetPairingProofs
open ZFSetHenkinInterpretation (carrier mapping)
open ZFSetPairingProofInterpretation (core epsilon model)
open Mettapedia.SetTheory
universe u

noncomputable def meaning {type : Ty Unit} : Operator type → Ty.denote.{0,u+1} carrier.{u} type
  | .product => ZFSetTraceProducts.tracePiSet
  | .sum => ZFSetDependentProducts.sigmaSet
  | .abstraction => fun domain function => ZFSetTraceProducts.traceLam (ZFSetDependentProducts.graph domain function)
  | .application => ZFSetTraceProducts.traceApp
  | .pair => ZFSet.pair
  | .first => ZFSetOrderedPair.first
  | .second => ZFSetOrderedPair.second
  | .truth => fun proposition => ZFSetTraceProofDecoding.truthCode proposition.down

theorem body_meaning {type : Ty Unit} (operator : Operator type) :
    model.{u}.denote (body core epsilon operator) (fun index => nomatch index) = meaning operator := by
  let emptyValuation : model.{u}.Valuation [] := fun index => nomatch index
  cases operator with
  | product =>
    funext domain family
    exact ZFSetTraceProductProofInterpretation.product_value (.var (.vs .vz)) (.var .vz)
      (model.extend (σ := mapping) (model.extend (σ := object) emptyValuation domain) family)
  | sum =>
    funext domain family
    exact ZFSetTraceProofInterpretation.sum_value (.var (.vs .vz)) (.var .vz)
      (model.extend (σ := mapping) (model.extend (σ := object) emptyValuation domain) family)
  | abstraction =>
    funext domain function
    exact ZFSetTraceProofInterpretation.abstraction_value (.var (.vs .vz)) (.var .vz)
      (model.extend (σ := mapping) (model.extend (σ := object) emptyValuation domain) function)
  | application =>
    funext relation point
    exact ZFSetTraceProofInterpretation.application_value (.var (.vs .vz)) (.var .vz)
      (model.extend (σ := object) (model.extend (σ := object) emptyValuation relation) point)
  | pair =>
    funext first second
    exact ZFSetPairingProofInterpretation.ordered_value (.var (.vs .vz)) (.var .vz)
      (model.extend (σ := object) (model.extend (σ := object) emptyValuation first) second)
  | first =>
    funext point
    exact (ZFSetTotalProjectionInterpretation.projections_agree (.var .vz)
      (model.extend (σ := object) emptyValuation point)).1
  | second =>
    funext point
    exact (ZFSetTotalProjectionInterpretation.projections_agree (.var .vz)
      (model.extend (σ := object) emptyValuation point)).2
  | truth =>
    funext proposition
    change ZFSet.sep (fun _ => proposition.down) (ZFSet.powerset (∅ : ZFSet.{u})) =
      ZFSet.sep (fun _ => proposition.down) {∅}
    apply ZFSet.ext
    intro point
    rw [ZFSet.mem_sep,ZFSet.mem_powerset,ZFSet.mem_sep,ZFSet.mem_singleton]
    constructor
    · rintro ⟨included,holds⟩
      refine ⟨?_,holds⟩
      apply ZFSet.ext
      intro value
      constructor
      · intro present
        exact False.elim (ZFSet.notMem_empty value (included present))
      · intro present
        exact False.elim (ZFSet.notMem_empty value present)
    · rintro ⟨rfl,holds⟩
      exact ⟨ZFSet.empty_subset _,holds⟩

end Mettapedia.Logic.HOL.Embedding.ZFSetCodeOperatorsInterpretation
