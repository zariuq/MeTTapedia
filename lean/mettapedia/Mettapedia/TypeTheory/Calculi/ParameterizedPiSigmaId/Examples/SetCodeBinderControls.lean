import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TowerInterpretation.SetCodeReductionProofs
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeControls

/-!
# Receipts from a source variable through abstraction, application and beta

The earlier identity example now obtains its function receipt from the
generic variable and abstraction producers. Removing the context guard
fails in an actual model, despite the ordinary set hypotheses remaining true.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeBinderControls
open Mettapedia.Logic Mettapedia.Logic.HOL
open Presentation TypedEquality.Annotated
open TowerInterpretation CodedHOL
open SetComprehensionProofs
open SetCodeControls

abbrev originalBound : Fin 0 → ClosedTerm (CodedHOL.Symbol Nat) object := Fin.elim0

def bodyReceipt : ProofSyntax Constants (weakenHyps (σ := object) basis)
    (SetCode.expand (judgmentAt (.typing (.snoc .nil Source.carrier) (.var 0) Source.carrier)
      (AnnotatedCodedReading.lift originalBound))) :=
  SetCode.ContextProofs.variableJudgment (.snoc .nil Source.carrier) 0 (AnnotatedCodedReading.lift originalBound)

theorem bodyReceipt_free : bodyReceipt.FunctionExtensionalityFree :=
  SetCode.ContextProofs.variableJudgment_free (.snoc .nil Source.carrier) 0 (AnnotatedCodedReading.lift originalBound)

def abstractionReceipt : ProofSyntax Constants basis
    (SetCode.expand (judgmentAt (.typing .nil Source.identity Source.functionType) originalBound)) :=
  SetCode.AbstractionProofs.abstractionJudgment .nil Source.carrier (.var 0) Source.carrier originalBound sets bodyReceipt

theorem abstractionReceipt_free : abstractionReceipt.FunctionExtensionalityFree :=
  SetCode.AbstractionProofs.abstractionJudgment_free .nil Source.carrier (.var 0) Source.carrier originalBound sets bodyReceipt
    sets_free bodyReceipt_free

theorem abstractionReceipt_nodeCount : type_of%
    (SetCode.AbstractionProofs.abstractionJudgment_nodeCount
      (Head := Nat) (Γ := []) (Δ := basis) .nil Source.carrier (.var 0) Source.carrier originalBound sets bodyReceipt) :=
  SetCode.AbstractionProofs.abstractionJudgment_nodeCount
    (Head := Nat) (Γ := []) (Δ := basis) .nil Source.carrier (.var 0) Source.carrier originalBound sets bodyReceipt

def applicationReceipt : ProofSyntax Constants basis (SetCode.expand (judgmentAt Source.statement originalBound)) :=
  SetCode.TypingProofs.applicationJudgment .nil Source.identity Source.argument Source.carrier Source.carrier originalBound sets
    abstractionReceipt argumentJudgment

theorem applicationReceipt_free : applicationReceipt.FunctionExtensionalityFree :=
  SetCode.TypingProofs.applicationJudgment_free .nil Source.identity Source.argument Source.carrier Source.carrier originalBound sets
    abstractionReceipt argumentJudgment sets_free abstractionReceipt_free
    (SetCodeControls.closedJudgment_free argumentReceipt argumentReceipt_free)

def betaStatement : CStatement Nat := .equality .nil (.app Source.identity Source.argument)
  (CTm.inst0 Source.argument (.var 0)) (CTm.inst0 Source.argument Source.carrier)

theorem source_beta : CDerivable Source.church betaStatement :=
  .betaPi (.piForm Source.carrier_typed (by change 0 < 2; decide) Source.carrier_typed
    (by change 0 < 2; decide) rfl) (by change 0 < 2; decide) (.var 0) Source.argument_typed

def betaReceipt : ProofSyntax Constants basis (SetCode.expand (judgmentAt betaStatement originalBound)) :=
  SetCode.ReductionProofs.betaJudgment .nil Source.carrier (.var 0) Source.carrier Source.argument originalBound sets
    bodyReceipt argumentJudgment

theorem betaReceipt_free : betaReceipt.FunctionExtensionalityFree :=
  SetCode.ReductionProofs.betaJudgment_free .nil Source.carrier (.var 0) Source.carrier Source.argument originalBound sets
    bodyReceipt argumentJudgment sets_free bodyReceipt_free
    (SetCodeControls.closedJudgment_free argumentReceipt argumentReceipt_free)

theorem actual_application :
    (actualModel.denote (SetCode.expand (judgmentAt (Γ := []) Source.statement originalBound)) (fun index => nomatch index)).down :=
  Soundness.extDerivation_sound applicationReceipt.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) basis_valid

theorem actual_beta :
    (actualModel.denote (SetCode.expand (judgmentAt (Γ := []) betaStatement originalBound)) (fun index => nomatch index)).down :=
  Soundness.extDerivation_sound betaReceipt.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ index; nomatch index) basis_valid

noncomputable def emptyValuation : actualModel.Valuation [] := fun index => nomatch index
noncomputable def badValuation : actualModel.Valuation [object] :=
  actualModel.extend (σ := object) emptyValuation (ZFSet.powerset (∅ : ZFSet.{0}))

def unguardedVariable : Formula Constants [object] := member core (.var .vz) (HOL.weaken SetCodeControls.carrier)

theorem unguardedVariable_false : ¬ (actualModel.denote unguardedVariable badValuation).down := by
  intro present
  change (ZFSet.powerset (∅ : ZFSet.{0})) ∈
    (show ZFSet.{0} from actualModel.denote (HOL.weaken SetCodeControls.carrier) badValuation) at present
  have unchanged := Soundness.denote_weaken (σ := object) actualModel SetCodeControls.carrier emptyValuation
    (ZFSet.powerset (∅ : ZFSet.{0}))
  have moved := (congrArg (fun value : ZFSet.{0} => ZFSet.powerset (∅ : ZFSet.{0}) ∈ value) unchanged).mp present
  change ZFSet.powerset (∅ : ZFSet.{0}) ∈
    ZFSet.sep (fun _ => (∅ : ZFSet.{0}) = ∅) (ZFSet.powerset ∅) at moved
  exact ZFSet.mem_irrefl _ (ZFSet.mem_sep.mp moved).1

theorem raisedBasis_valid : Soundness.SatisfiesHyps actualModel badValuation (weakenHyps (σ := object) basis) := by
  intro formula present
  obtain ⟨original,admitted,rfl⟩ := List.mem_map.mp present
  have unchanged := Soundness.denote_weaken (σ := object) actualModel original emptyValuation
    (ZFSet.powerset (∅ : ZFSet.{0}))
  exact (congrArg ULift.down unchanged).mpr (basis_valid original admitted)

theorem noUnguardedVariable : ¬ Nonempty (ProofSyntax Constants (weakenHyps (σ := object) basis) unguardedVariable) := by
  rintro ⟨proof⟩
  exact unguardedVariable_false (Soundness.extDerivation_sound (ρ := badValuation) proof.erase
    (actualModel.functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
    (by intro _ _; trivial) raisedBasis_valid)

#eval bodyReceipt.nodeCount

end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Examples.SetCodeBinderControls
