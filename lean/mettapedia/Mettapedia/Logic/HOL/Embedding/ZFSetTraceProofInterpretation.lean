import Mettapedia.Logic.HOL.SetTraceProofs
import Mettapedia.Logic.HOL.Embedding.ZFSetGraphProofInterpretation
import Mettapedia.Logic.HOL.Embedding.ZFSetTraceProducts

/-!
# Actual meanings of retained sums and trace operations

The indexed-union sum denotes the existing set-coded dependent sum. Its
abstraction reading is the Aczel trace of the actual functional graph, and
application agrees with the previously defined total trace application.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation
open ZFSetHenkinInterpretation (ChoiceSymbol replacement mem_replacement)
open ZFSetPairingProofInterpretation (core epsilon model value value_weaken value_newest ordered_value)
open ZFSetGraphProofInterpretation (functionValue)
universe u
variable {Γ : Ctx Unit}

abbrev basis (context : Ctx Unit) : List (Formula ChoiceSymbol context) :=
  ZFSetPairingProofInterpretation.basis context ++
    [SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.unionLaw,
     SetComprehensionProofs.lawAt core ZFSetHenkinInterpretation.extensionality]

def laws (context : Ctx Unit) : SetTraceProofs.Laws core epsilon (basis context) where
  pairing := {
    empty := ProofSyntax.hyp (Δ := basis context) ⟨0,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩
    power := ProofSyntax.hyp (Δ := basis context) ⟨1,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩
    separation := ProofSyntax.hyp (Δ := basis context) ⟨2,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩
    replacement := ProofSyntax.hyp (Δ := basis context) ⟨3,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩
    selection := ProofSyntax.hyp (Δ := basis context) ⟨4,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩ }
  union := ProofSyntax.hyp (Δ := basis context) ⟨5,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩
  extensionality := ProofSyntax.hyp (Δ := basis context) ⟨6,by simp [basis,ZFSetPairingProofInterpretation.basis]⟩

theorem laws_free (context : Ctx Unit) : (laws context).Free :=
  ⟨⟨trivial,trivial,trivial,trivial,trivial⟩,trivial,trivial⟩

theorem basis_valid (valuation : model.{u}.Valuation Γ) :
    Soundness.SatisfiesHyps model valuation (basis Γ) := by
  intro formula present
  rcases List.mem_append.mp present with old | extra
  · exact ZFSetPairingProofInterpretation.basis_valid valuation formula old
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at extra
    rcases extra with rfl | rfl
    · exact ZFSetPairingProofInterpretation.law_valid valuation _ ZFSetHenkinInterpretation.unionLaw_valid
    · exact ZFSetPairingProofInterpretation.law_valid valuation _ ZFSetHenkinInterpretation.extensionality_valid

theorem pairImage_value (point fibre : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value (SetDependentSumProofs.pairImage core epsilon point fibre) valuation =
      replacement (value fibre valuation) (fun z => ZFSet.pair (value point valuation) z) := by
  change replacement (value fibre valuation) (fun z =>
      value (SetPairingProofs.ordered core epsilon (HOL.weaken point) (.var .vz))
        (model.extend (σ := SetPairingProofs.object) valuation z)) = _
  apply congrArg (replacement (value fibre valuation))
  funext z
  rw [ordered_value,value_weaken,value_newest]

theorem sum_value (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping)
    (valuation : model.{u}.Valuation Γ) :
    value (SetDependentSumProofs.sum core epsilon domain family) valuation =
      ZFSetDependentProducts.sigmaSet (value domain valuation) (functionValue family valuation) := by
  change ZFSet.sUnion (replacement (value domain valuation) (fun x =>
      value (SetDependentSumProofs.pairImage core epsilon (.var .vz)
        (.app (HOL.weaken family) (.var .vz)))
        (model.extend (σ := SetPairingProofs.object) valuation x))) = _
  have fibres : (fun x : ZFSet.{u} =>
      value (SetDependentSumProofs.pairImage core epsilon (.var .vz) (.app (HOL.weaken family) (.var .vz)))
        (model.extend (σ := SetPairingProofs.object) valuation x)) =
      (fun x => replacement (functionValue family valuation x) (fun z => ZFSet.pair x z)) := by
    funext x
    rw [pairImage_value,value_newest]
    apply congrArg (fun bound => replacement bound (fun z => ZFSet.pair x z))
    exact congrFun (Soundness.denote_weaken (σ := SetPairingProofs.object) model family valuation x) x
  rw [fibres]
  apply ZFSet.ext
  intro point
  rw [ZFSet.mem_sUnion,ZFSetDependentProducts.mem_sigmaSet]
  constructor
  · rintro ⟨fibre,selected,present⟩
    obtain ⟨x,hx,rfl⟩ := mem_replacement.mp selected
    obtain ⟨z,hz,same⟩ := mem_replacement.mp present
    exact ⟨x,hx,z,hz,same.symm⟩
  · rintro ⟨x,hx,z,hz,rfl⟩
    exact ⟨replacement (functionValue family valuation x) (fun z => ZFSet.pair x z),
      mem_replacement.mpr ⟨x,hx,rfl⟩,mem_replacement.mpr ⟨z,hz,rfl⟩⟩

theorem abstraction_value (domain : Term ChoiceSymbol Γ SetPairingProofs.object)
    (family : Term ChoiceSymbol Γ ZFSetHenkinInterpretation.mapping)
    (valuation : model.{u}.Valuation Γ) :
    value (SetTraceProofs.abstraction core epsilon domain family) valuation =
      ZFSetTraceProducts.traceLam (ZFSetDependentProducts.graph (value domain valuation) (functionValue family valuation)) :=
  (sum_value domain family valuation).trans (ZFSetTraceProducts.traceLam_graph _ _).symm

theorem application_value (relation point : Term ChoiceSymbol Γ SetPairingProofs.object)
    (valuation : model.{u}.Valuation Γ) :
    value (SetTraceProofs.application core epsilon relation point) valuation =
      ZFSetTraceProducts.traceApp (value relation valuation) (value point valuation) := by
  change ZFSet.sep (fun z =>
      value (SetPairingProofs.ordered core epsilon (HOL.weaken point) (.var .vz))
        (model.extend (σ := SetPairingProofs.object) valuation z) ∈
      value (HOL.weaken relation) (model.extend (σ := SetPairingProofs.object) valuation z))
      (ZFSet.sUnion (ZFSet.sUnion (value relation valuation))) =
    ZFSet.sep (fun z => ZFSet.pair (value point valuation) z ∈ value relation valuation)
      (ZFSet.sUnion (ZFSet.sUnion (value relation valuation)))
  apply congrArg (fun predicate : ZFSet.{u} → Prop =>
    ZFSet.sep predicate (ZFSet.sUnion (ZFSet.sUnion (value relation valuation))))
  funext z
  apply propext
  rw [ordered_value,value_weaken,value_newest,value_weaken]

end Mettapedia.Logic.HOL.Embedding.ZFSetTraceProofInterpretation

