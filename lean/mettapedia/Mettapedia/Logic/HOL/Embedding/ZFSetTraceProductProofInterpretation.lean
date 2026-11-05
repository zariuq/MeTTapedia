import Mettapedia.Logic.HOL.SetTraceProductProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation

/-!
# Bounded trace products agree with the existing function-space model

The support bound excludes pairs outside the declared domain. Together with
typed application it characterizes exactly the earlier image of functional
graphs under tracing. The comparison is uniform in the context and valuation.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceProductProofInterpretation
open ZFSetHenkinInterpretation (ChoiceSymbol)
open ZFSetPairingProofInterpretation (core epsilon model value value_weaken value_newest)
open ZFSetGraphProofInterpretation (functionValue)
open ZFSetDependentProducts ZFSetTraceProducts
universe u

noncomputable def supportSet (domain : ZFSet.{u}) (family : ZFSet.{u} → ZFSet.{u}) : ZFSet.{u} :=
  sigmaSet domain (fun _ => ZFSet.sUnion (ZFSetDependentProducts.familyUnion domain family))

theorem tracePiSet_eq_bounded (domain : ZFSet.{u}) (family : ZFSet.{u} → ZFSet.{u}) :
    tracePiSet domain family =
      ZFSet.sep (fun relation => ∀ x ∈ domain, traceApp relation x ∈ family x)
        (ZFSet.powerset (supportSet domain family)) := by
  apply ZFSet.ext
  intro relation
  rw [ZFSet.mem_sep,ZFSet.mem_powerset]
  constructor
  · intro admitted
    refine ⟨?_,fun x hx => traceApp_mem ⟨relation,admitted⟩ ⟨x,hx⟩⟩
    obtain ⟨function,typed,rfl⟩ := mem_tracePiSet.mp admitted
    intro point present
    obtain ⟨x,y,z,pairPresent,inY,rfl⟩ := mem_traceLam.mp present
    have fields := ZFSet.pair_mem_prod.mp ((mem_piSet.mp typed).1.1 pairPresent)
    exact mem_sigmaSet.mpr ⟨x,fields.1,z,ZFSet.mem_sUnion.mpr ⟨y,fields.2,inY⟩,rfl⟩
  · rintro ⟨bounded,typed⟩
    let function : ZFSet.{u} → ZFSet.{u} := traceApp relation
    have functionTyped : graph domain function ∈ piSet domain family := graph_mem_piSet typed
    refine mem_tracePiSet.mpr ⟨graph domain function,functionTyped,?_⟩
    rw [traceLam_graph]
    apply ZFSet.ext
    intro point
    rw [mem_sigmaSet]
    constructor
    · rintro ⟨x,_,z,present,rfl⟩
      exact mem_traceApp.mp present
    · intro present
      obtain ⟨x,hx,z,_,equal⟩ := mem_sigmaSet.mp (bounded present)
      exact ⟨x,hx,z,mem_traceApp.mpr (equal ▸ present),equal⟩

variable {Γ : Ctx Unit}

theorem functionValue_weaken (function : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping)
    (valuation : model.{u}.Valuation Γ) (point : ZFSet.{u}) :
    functionValue (HOL.weaken function) (model.extend (σ := SetPairingProofs.object) valuation point) =
      functionValue function valuation :=
  Soundness.denote_weaken (σ := SetPairingProofs.object) model function valuation point

theorem values_value (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping) (valuation : model.{u}.Valuation Γ) :
    value (SetTraceProductProofs.values core domain family) valuation =
      ZFSet.sUnion (ZFSetDependentProducts.familyUnion (value domain valuation) (functionValue family valuation)) := rfl

theorem support_value (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping) (valuation : model.{u}.Valuation Γ) :
    value (SetTraceProductProofs.support core epsilon domain family) valuation =
      supportSet (value domain valuation) (functionValue family valuation) := by
  rw [SetTraceProductProofs.support,ZFSetTraceProofInterpretation.sum_value]
  apply congrArg (sigmaSet (value domain valuation))
  funext point
  exact value_weaken (SetTraceProductProofs.values core domain family) valuation point

theorem guard_meaning (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping)
    (relation : Term ChoiceSymbol Γ SetPairingProofs.object) (valuation : model.{u}.Valuation Γ) :
    (model.denote (SetTraceProductProofs.guard core epsilon domain family relation) valuation).down ↔
      ∀ point ∈ value domain valuation,
        traceApp (value relation valuation) point ∈ functionValue family valuation point := by
  constructor
  · intro holds point present
    have premise : value (.var .vz) (model.extend (σ := SetPairingProofs.object) valuation point) ∈
        value (HOL.weaken domain) (model.extend (σ := SetPairingProofs.object) valuation point) := by
      rw [value_newest,value_weaken]
      exact present
    have result := holds point trivial premise
    change value (SetTraceProofs.application core epsilon (HOL.weaken relation) (.var .vz))
      (model.extend (σ := SetPairingProofs.object) valuation point) ∈
        functionValue (HOL.weaken family) (model.extend (σ := SetPairingProofs.object) valuation point) point at result
    rw [ZFSetTraceProofInterpretation.application_value,value_weaken,value_newest,functionValue_weaken] at result
    exact result
  · intro holds point _ present
    change point ∈ value (HOL.weaken domain) (model.extend (σ := SetPairingProofs.object) valuation point) at present
    rw [value_weaken] at present
    change value (SetTraceProofs.application core epsilon (HOL.weaken relation) (.var .vz))
      (model.extend (σ := SetPairingProofs.object) valuation point) ∈
        functionValue (HOL.weaken family) (model.extend (σ := SetPairingProofs.object) valuation point) point
    rw [ZFSetTraceProofInterpretation.application_value,value_weaken,value_newest,functionValue_weaken]
    exact holds point present

theorem product_value (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping) (valuation : model.{u}.Valuation Γ) :
    value (SetTraceProductProofs.product core epsilon domain family) valuation =
      tracePiSet (value domain valuation) (functionValue family valuation) := by
  rw [tracePiSet_eq_bounded]
  change ZFSet.sep (fun relation : ZFSet.{u} =>
      (model.denote (SetTraceProductProofs.guard core epsilon (HOL.weaken domain) (HOL.weaken family) (.var .vz))
        (model.extend (σ := SetPairingProofs.object) valuation relation)).down)
    (ZFSet.powerset (value (SetTraceProductProofs.support core epsilon domain family) valuation)) = _
  rw [support_value]
  apply congrArg (fun predicate : ZFSet.{u} → Prop =>
    ZFSet.sep predicate (ZFSet.powerset (supportSet (value domain valuation) (functionValue family valuation))))
  funext relation
  apply propext
  have meaning := guard_meaning (HOL.weaken domain) (HOL.weaken family) (.var .vz)
    (model.extend (σ := SetPairingProofs.object) valuation relation)
  rw [value_weaken,value_newest,functionValue_weaken] at meaning
  exact meaning

theorem product_in_closed_universe (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping) (valuation : model.{u}.Valuation Γ)
    {universeSet : ZFSet.{u}} (closed : ZFSetUniverseClosure.Closed universeSet)
    (domainMember : value domain valuation ∈ universeSet)
    (familyMembers : ∀ point ∈ value domain valuation, functionValue family valuation point ∈ universeSet) :
    value (SetTraceProductProofs.product core epsilon domain family) valuation ∈ universeSet := by
  rw [product_value]
  exact closed.tracePiSet_mem domainMember _ familyMembers

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceProductProofInterpretation
