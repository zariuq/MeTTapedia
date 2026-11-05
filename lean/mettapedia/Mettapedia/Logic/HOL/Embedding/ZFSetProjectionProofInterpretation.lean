import Mettapedia.Logic.HOL.SetSumProjectionProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation

/-!
# Guarded comparison of retained projections with the existing sum decoder

Constructor projections recover their actual fields at every valuation.
For an admitted dependent-sum value, the selected fields are typed and agree
with the existing canonical decoding equivalence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetProjectionProofInterpretation
open ZFSetHenkinInterpretation (ChoiceSymbol)
open ZFSetPairingProofInterpretation (core epsilon model value ordered_value)
open ZFSetGraphProofInterpretation (functionValue)
open SetPairProjectionProofs
universe u
variable {Γ : Ctx Unit}

theorem constructor_values (left right : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value (first core epsilon (SetPairingProofs.ordered core epsilon left right)) valuation = value left valuation ∧
    value (second core epsilon (SetPairingProofs.ordered core epsilon left right)) valuation = value right valuation := by
  have proof := SetPairProjectionProofs.beta core epsilon left right (ZFSetPairingProofInterpretation.laws Γ)
  have holds := Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) (ZFSetPairingProofInterpretation.basis_valid valuation)
  exact ⟨holds.1,holds.2⟩

theorem typed_values (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping)
    (pair : Term ChoiceSymbol Γ SetPairingProofs.object) (valuation : model.{u}.Valuation Γ)
    (admitted : value pair valuation ∈ ZFSetDependentProducts.sigmaSet (value domain valuation) (functionValue family valuation)) :
    value (first core epsilon pair) valuation ∈ value domain valuation ∧
    value (second core epsilon pair) valuation ∈ functionValue family valuation (value (first core epsilon pair) valuation) ∧
    ZFSet.pair (value (first core epsilon pair) valuation) (value (second core epsilon pair) valuation) = value pair valuation := by
  let laws := ZFSetTraceProofInterpretation.laws Γ
  let claim := SetComprehensionProofs.member core pair (SetDependentSumProofs.sum core epsilon domain family)
  have proof := ProofSyntax.impI
    (SetSumProjectionProofs.typedFields core epsilon domain family pair (laws.pairing.prepend claim)
      (laws.union.prepend claim) (.hyp 0))
  have holds := Soundness.extDerivation_sound proof.erase
    (model.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) (ZFSetTraceProofInterpretation.basis_valid valuation)
  have member : value pair valuation ∈ value (SetDependentSumProofs.sum core epsilon domain family) valuation :=
    (ZFSetTraceProofInterpretation.sum_value domain family valuation).symm ▸ admitted
  have fields := holds member
  exact ⟨fields.1,fields.2.1,(ordered_value _ _ valuation).symm.trans fields.2.2⟩

theorem agrees_with_sigmaEquiv (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping)
    (pair : Term ChoiceSymbol Γ SetPairingProofs.object) (valuation : model.{u}.Valuation Γ)
    (admitted : value pair valuation ∈ ZFSetDependentProducts.sigmaSet (value domain valuation) (functionValue family valuation)) :
    let decoded := ZFSetDependentProducts.sigmaEquiv (value domain valuation) (functionValue family valuation)
      ⟨value pair valuation,admitted⟩
    value (first core epsilon pair) valuation = decoded.1.1 ∧ value (second core epsilon pair) valuation = decoded.2.1 := by
  let equivalence := ZFSetDependentProducts.sigmaEquiv (value domain valuation) (functionValue family valuation)
  let input : ZFSetDependentProducts.Elements
      (ZFSetDependentProducts.sigmaSet (value domain valuation) (functionValue family valuation)) :=
    ⟨value pair valuation,admitted⟩
  have decodedPair := congrArg Subtype.val (equivalence.symm_apply_apply input)
  change ZFSet.pair (equivalence input).1.1 (equivalence input).2.1 = value pair valuation at decodedPair
  exact ZFSet.pair_inj.mp ((typed_values domain family pair valuation admitted).2.2.trans decodedPair.symm)

end Mettapedia.Logic.HOL.Embedding.ZFSetProjectionProofInterpretation

