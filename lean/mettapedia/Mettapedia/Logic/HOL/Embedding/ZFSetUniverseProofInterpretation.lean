import Mettapedia.Logic.HOL.SetUniverseFormationProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProductProofInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseInterpretation

/-!
# Interpreting the primitive retained universe profile

The four formulas specialize to the existing universe profile. At every
valuation they are satisfied by an actual closed set. This interpretation
does not assert the existence of a nonempty closed universe or a cofinal
inaccessible hierarchy.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetUniverseProofInterpretation
open SetComprehensionProofs SetUniverseProofs
open ZFSetHenkinInterpretation (ChoiceSymbol mapping replacement)
open ZFSetPairingProofInterpretation (core epsilon model value value_weaken value_newest)
open ZFSetGraphProofInterpretation (functionValue)
open ZFSetTraceProductProofInterpretation (functionValue_weaken)
universe u
variable {Γ : Ctx Unit}

theorem existing_transitive (universeSet : ZFSetUniverseInterpretation.UniverseExpr Γ ZFSetHenkinInterpretation.set) :
    transitive ZFSetUniverseInterpretation.UniverseSymbol.core universeSet =
      ZFSetUniverseInterpretation.transitiveFormula universeSet := rfl

theorem existing_union (universeSet : ZFSetUniverseInterpretation.UniverseExpr Γ ZFSetHenkinInterpretation.set) :
    unaryClosed ZFSetUniverseInterpretation.UniverseSymbol.core universeSet (.const (.core .union)) =
      ZFSetUniverseInterpretation.unionClosedFormula universeSet := rfl

theorem existing_power (universeSet : ZFSetUniverseInterpretation.UniverseExpr Γ ZFSetHenkinInterpretation.set) :
    unaryClosed ZFSetUniverseInterpretation.UniverseSymbol.core universeSet (.const (.core .power)) =
      ZFSetUniverseInterpretation.powerClosedFormula universeSet := rfl

theorem existing_replacement (universeSet : ZFSetUniverseInterpretation.UniverseExpr Γ ZFSetHenkinInterpretation.set) :
    replacementClosed ZFSetUniverseInterpretation.UniverseSymbol.core universeSet =
      ZFSetUniverseInterpretation.replacementClosedFormula universeSet := rfl

theorem mapsInto_meaning (universeSet domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (function : Term ChoiceSymbol Γ mapping) (valuation : model.{u}.Valuation Γ) :
    (model.denote (mapsInto core universeSet domain function) valuation).down ↔
      ∀ point ∈ value domain valuation, functionValue function valuation point ∈ value universeSet valuation := by
  constructor
  · intro holds point present
    have premise : value (.var .vz) (model.extend (σ := SetPairingProofs.object) valuation point) ∈
        value (HOL.weaken domain) (model.extend (σ := SetPairingProofs.object) valuation point) := by
      rw [value_newest,value_weaken]
      exact present
    have result := holds point trivial premise
    change functionValue (HOL.weaken function) (model.extend (σ := SetPairingProofs.object) valuation point) point ∈
      value (HOL.weaken universeSet) (model.extend (σ := SetPairingProofs.object) valuation point) at result
    rw [functionValue_weaken,value_weaken] at result
    exact result
  · intro holds point _ present
    change point ∈ value (HOL.weaken domain) (model.extend (σ := SetPairingProofs.object) valuation point) at present
    rw [value_weaken] at present
    change functionValue (HOL.weaken function) (model.extend (σ := SetPairingProofs.object) valuation point) point ∈
      value (HOL.weaken universeSet) (model.extend (σ := SetPairingProofs.object) valuation point)
    rw [functionValue_weaken,value_weaken]
    exact holds point present

theorem transitive_valid (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) (transitivity : ZFSet.IsTransitive (value universeSet valuation)) :
    (model.denote (transitive core universeSet) valuation).down := by
  intro bound _ boundMember point _ pointMember
  change bound ∈ value (HOL.weaken universeSet) (model.extend (σ := SetPairingProofs.object) valuation bound) at boundMember
  rw [value_weaken] at boundMember
  change (show ZFSet.{u} from point) ∈ (show ZFSet.{u} from bound) at pointMember
  change point ∈ value (HOL.weaken (HOL.weaken universeSet))
    (model.extend (σ := SetPairingProofs.object) (model.extend (σ := SetPairingProofs.object) valuation bound) point)
  rw [value_weaken,value_weaken]
  exact transitivity bound boundMember pointMember

theorem unary_valid (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object)
    (operation : Term ChoiceSymbol Γ mapping) (valuation : model.{u}.Valuation Γ)
    (closed : ∀ point ∈ value universeSet valuation, functionValue operation valuation point ∈ value universeSet valuation) :
    (model.denote (unaryClosed core universeSet operation) valuation).down :=
  (mapsInto_meaning universeSet universeSet operation valuation).mpr closed

theorem replacement_valid (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ)
    (closed : ∀ domain ∈ value universeSet valuation, ∀ function : ZFSet.{u} → ZFSet.{u},
      (∀ point ∈ domain, function point ∈ value universeSet valuation) → replacement domain function ∈ value universeSet valuation) :
    (model.denote (replacementClosed core universeSet) valuation).down := by
  intro domain _ domainMember function _ body
  change domain ∈ value (HOL.weaken universeSet) (model.extend (σ := SetPairingProofs.object) valuation domain) at domainMember
  rw [value_weaken] at domainMember
  let firstValuation : model.{u}.Valuation (SetPairingProofs.object :: Γ) :=
    model.extend (σ := SetPairingProofs.object) valuation domain
  let secondValuation : model.{u}.Valuation (mapping :: SetPairingProofs.object :: Γ) :=
    model.extend (σ := mapping) firstValuation function
  have bodyMeaning := (mapsInto_meaning (HOL.weaken (HOL.weaken universeSet))
    (.var (.vs .vz)) (.var .vz) secondValuation).mp body
  change ∀ point ∈ (show ZFSet.{u} from domain),
    (show ZFSet.{u} → ZFSet.{u} from function) point ∈
      value (HOL.weaken (HOL.weaken universeSet)) secondValuation at bodyMeaning
  have universeValue : value (HOL.weaken (HOL.weaken universeSet)) secondValuation = value universeSet valuation :=
    (Soundness.denote_weaken (σ := mapping) model (HOL.weaken universeSet) firstValuation function).trans
      (value_weaken universeSet valuation domain)
  rw [universeValue] at bodyMeaning
  change replacement domain function ∈ value (HOL.weaken (HOL.weaken universeSet)) secondValuation
  rw [universeValue]
  exact closed domain domainMember function bodyMeaning

abbrev closureAssumptions (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object) : List (Formula ChoiceSymbol Γ) :=
  [transitive core universeSet,unaryClosed core universeSet (.const (core .union)),
    unaryClosed core universeSet (.const (core .power)),replacementClosed core universeSet]

abbrev basis (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object) : List (Formula ChoiceSymbol Γ) :=
  ZFSetTraceProofInterpretation.basis Γ ++ closureAssumptions universeSet

def laws (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object) : SetUniverseProofs.Laws core universeSet (basis universeSet) where
  transitive := .hyp ⟨7,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
  union := .hyp ⟨8,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
  power := .hyp ⟨9,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
  replacement := .hyp ⟨10,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩

def setLaws (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object) : SetTraceProofs.Laws core epsilon (basis universeSet) where
  pairing := {
    empty := .hyp ⟨0,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
    power := .hyp ⟨1,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
    separation := .hyp ⟨2,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
    replacement := .hyp ⟨3,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
    selection := .hyp ⟨4,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩ }
  union := .hyp ⟨5,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩
  extensionality := .hyp ⟨6,by simp [basis,closureAssumptions,ZFSetTraceProofInterpretation.basis,ZFSetPairingProofInterpretation.basis]⟩

theorem laws_free (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object) : (laws universeSet).Free :=
  ⟨trivial,trivial,trivial,trivial⟩

theorem setLaws_free (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object) : (setLaws universeSet).Free :=
  ⟨⟨trivial,trivial,trivial,trivial,trivial⟩,trivial,trivial⟩

theorem closureAssumptions_valid (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) (closed : ZFSetUniverseClosure.Closed (value universeSet valuation)) :
    Soundness.SatisfiesHyps model valuation (closureAssumptions universeSet) := by
  intro formula present
  simp only [closureAssumptions,List.mem_cons,List.not_mem_nil,or_false] at present
  rcases present with rfl | rfl | rfl | rfl
  · exact transitive_valid universeSet valuation closed.transitive
  · exact unary_valid universeSet (.const (core .union)) valuation (fun _ h => closed.union_mem h)
  · exact unary_valid universeSet (.const (core .power)) valuation (fun _ h => closed.power_mem h)
  · exact replacement_valid universeSet valuation (fun _ h => closed.replacement_mem h)

theorem basis_valid (universeSet : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) (closed : ZFSetUniverseClosure.Closed (value universeSet valuation)) :
    Soundness.SatisfiesHyps model valuation (basis universeSet) := by
  intro formula present
  rcases List.mem_append.mp present with basic | extra
  · exact ZFSetTraceProofInterpretation.basis_valid valuation formula basic
  · exact closureAssumptions_valid universeSet valuation closed formula extra

end Mettapedia.Logic.HOL.Embedding.ZFSetUniverseProofInterpretation
