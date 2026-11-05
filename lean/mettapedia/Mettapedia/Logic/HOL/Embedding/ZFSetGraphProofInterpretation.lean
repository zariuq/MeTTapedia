import Mettapedia.Logic.HOL.SetGraphProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetDependentProducts

/-!
# Comparing retained graph syntax with actual set-coded graphs

The comparison holds at every typed context and valuation. It uses the
previously proved denotation of the constructed ordered pair. Retained proof
production remains separate from this semantic comparison.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetGraphProofInterpretation
open ZFSetHenkinInterpretation (ChoiceSymbol replacement)
open ZFSetPairingProofInterpretation SetGraphProofs
open ZFSetPairingProofInterpretation (core epsilon model value)
universe u
variable {Γ : Ctx Unit}

noncomputable def functionValue (function : Term ChoiceSymbol Γ (SetPairingProofs.object ⇒ SetPairingProofs.object))
    (valuation : model.{u}.Valuation Γ) : ZFSet.{u} → ZFSet.{u} := model.denote function valuation

theorem graph_value (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (function : Term ChoiceSymbol Γ (SetPairingProofs.object ⇒ SetPairingProofs.object))
    (valuation : model.{u}.Valuation Γ) :
    value (SetGraphProofs.graph core epsilon domain function) valuation =
      ZFSetDependentProducts.graph (value domain valuation) (functionValue function valuation) := by
  change replacement (value domain valuation)
      (fun point => value (SetPairingProofs.ordered core epsilon (.var .vz)
        (.app (HOL.weaken function) (.var .vz))) (model.extend (σ := SetPairingProofs.object) valuation point)) =
    replacement (value domain valuation) (fun point => ZFSet.pair point (functionValue function valuation point))
  apply congrArg (replacement (value domain valuation))
  funext point
  rw [ordered_value]
  change ZFSet.pair point ((model.denote (HOL.weaken function)
      (model.extend (σ := SetPairingProofs.object) valuation point)) point) =
    ZFSet.pair point (functionValue function valuation point)
  exact congrArg (ZFSet.pair point) (congrFun
    (Soundness.denote_weaken (σ := SetPairingProofs.object) model function valuation point) point)

theorem graph_membership (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (function : Term ChoiceSymbol Γ (SetPairingProofs.object ⇒ SetPairingProofs.object))
    (point result : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value (SetPairingProofs.ordered core epsilon point result) valuation ∈
      value (SetGraphProofs.graph core epsilon domain function) valuation ↔
      value point valuation ∈ value domain valuation ∧
        functionValue function valuation (value point valuation) = value result valuation := by
  rw [ordered_value,graph_value,ZFSetDependentProducts.pair_mem_graph]

end Mettapedia.Logic.HOL.Embedding.ZFSetGraphProofInterpretation

