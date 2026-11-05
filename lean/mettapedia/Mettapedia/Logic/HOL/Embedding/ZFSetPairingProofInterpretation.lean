import Mettapedia.Logic.HOL.SetPairingProofs
import Mettapedia.Logic.HOL.ConstantSubstitutionSemantics

/-!
# The retained pairing programs denote actual set pairs

The supplied empty, power, separation, image and selection laws are validated
in the existing actual-set model. Retained proof soundness then identifies
the constructed unordered pairs with Mathlib's unordered pairs, and their
Kuratowski construction with `ZFSet.pair`. No constructor or injectivity law
for those programs is a model premise.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation
open SetComprehensionProofs SetPairingProofs
open ZFSetHenkinInterpretation
universe u

abbrev core : Core ChoiceSymbol := ChoiceSymbol.core
def epsilon : ClosedTerm ChoiceSymbol (SelectionProofs.Selection SetPairingProofs.object) := .const .epsilon
noncomputable abbrev model : HenkinModel.{0,0,u+1} Unit ChoiceSymbol := choiceModel.{u}

abbrev basis (context : Ctx Unit) : List (Formula ChoiceSymbol context) :=
  [lawAt core emptyLaw, lawAt core powerLaw, lawAt core separationLaw,
   lawAt core replacementLaw, SelectionProofs.principle (weakenCtx context epsilon)]

def laws (context : Ctx Unit) : SetPairingProofs.Laws core epsilon (basis context) where
  empty := .hyp 0
  power := .hyp 1
  separation := .hyp 2
  replacement := .hyp 3
  selection := .hyp 4

theorem laws_free (context : Ctx Unit) : (laws context).Free := ⟨trivial,trivial,trivial,trivial,trivial⟩

theorem core_valid (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (valid : ZFSetHenkinInterpretation.model.{u}.models formula) :
    model.{u}.models (mapConst core formula) := by
  have preserved := HenkinModel.models_substConst_of_agreement (fun symbol => .const (.core symbol))
    ZFSetHenkinInterpretation.model.{u} model.{u} rfl HEq.rfl (fun _ => HEq.rfl) formula
  simpa only [HOL.substConst_constant_images] using preserved.mpr valid

theorem law_valid {Γ : Ctx Unit} (valuation : model.{u}.Valuation Γ)
    (formula : ClosedFormula ZFSetHenkinInterpretation.Symbol)
    (valid : ZFSetHenkinInterpretation.model.{u}.models formula) :
    (model.denote (lawAt core formula) valuation).down := by
  rw [lawAt_eq_weakenCtx, HenkinModel.denote_weakenCtx]
  exact core_valid formula valid

theorem basis_valid {Γ : Ctx Unit} (valuation : model.{u}.Valuation Γ) :
    Soundness.SatisfiesHyps model valuation (basis Γ) := by
  intro formula present
  simp only [basis, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl | rfl | rfl
  · exact law_valid valuation _ emptyLaw_valid
  · exact law_valid valuation _ powerLaw_valid
  · exact law_valid valuation _ separationLaw_valid
  · exact law_valid valuation _ replacementLaw_valid
  · simp only [weakenCtx_const, epsilon]
    intro predicate _ point _ holds
    change (predicate (epsilonSet predicate)).down
    exact epsilonSet_spec predicate holds

noncomputable def value {Γ : Ctx Unit} (term : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) : ZFSet.{u} := model.denote term valuation

theorem value_weaken {Γ : Ctx Unit} (term : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) (point : ZFSet.{u}) :
    value (HOL.weaken term) (model.extend (σ := SetPairingProofs.object) valuation point) =
      value term valuation := Soundness.denote_weaken (σ := SetPairingProofs.object) model term valuation point

theorem value_newest {Γ : Ctx Unit} (valuation : model.{u}.Valuation Γ) (point : ZFSet.{u}) :
    value (.var .vz) (model.extend (σ := SetPairingProofs.object) valuation point) = point := rfl

theorem unordered_membership {Γ : Ctx Unit}
    (left right point : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value point valuation ∈ value (unordered core epsilon left right) valuation ↔
      value point valuation = value left valuation ∨ value point valuation = value right valuation := by
  have proof := SetPairingProofs.membership core epsilon left right point (laws Γ)
  have holds := Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) (basis_valid valuation)
  exact ⟨holds.1,holds.2⟩

theorem unordered_value {Γ : Ctx Unit} (left right : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value (unordered core epsilon left right) valuation = {value left valuation, value right valuation} := by
  apply ZFSet.ext
  intro point
  have meaning := unordered_membership (HOL.weaken left) (HOL.weaken right) (.var .vz)
    (model.extend (σ := SetPairingProofs.object) valuation point)
  rw [← weaken_unordered, value_weaken, value_weaken, value_weaken] at meaning
  simpa only [ZFSet.mem_pair, value_newest] using meaning

theorem ordered_value {Γ : Ctx Unit} (left right : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value (ordered core epsilon left right) valuation = ZFSet.pair (value left valuation) (value right valuation) := by
  simp [ordered, unordered_value, ZFSet.pair]

end Mettapedia.Logic.HOL.Embedding.ZFSetPairingProofInterpretation
