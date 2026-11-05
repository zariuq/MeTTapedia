import Mettapedia.Logic.HOL.ConstructorArgumentRecoveryInternalization
import Mettapedia.Logic.HOL.ProofSyntaxHypothesisSubstitution
import Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredConstructorRecoveryControls

/-!
# Reusing the universal stored-payload law with its original admission guard

The constructor comparison cites one recovery statement at both admitted
inputs. A retained hypothesis substitution discharges that statement using
the recovery proof from the same three primitive providers. This establishes
logical reuse; it does not establish native DAG sharing or a cost improvement.

The existing recursive-space model also separates guarded recovery from an
unguarded variant: permitting bottom as a stored field would require it to
be an encoded field, which it is not.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredRecoveryReuseControls

open Mettapedia.Logic Mettapedia.Logic.HOL
open FiniteConstructorEncoding ConstructorArgumentMap
open FiniteConstructorFieldEmbeddingControls (Base N A E Number Element Space)
open VectorTreeSuccessorFixture
open IndexedVectorTreeStoredConstructorRecoveryControls (numbers bottom domain constructor)

def lower := VectorTreePayloadMaps.lowerProgram given
def raise := VectorTreePayloadMaps.raiseProgram given
def statement : ClosedFormula Const := recoveryStatement lower raise domain

def originalRecovery : Recovery premises lower raise domain :=
  IndexedVectorTreeStoredConstructorRecovery.recovery given onlyTrue numbers zero one successor numeral bottom
    (.hyp ⟨0,by simp [premises]⟩) (.hyp ⟨1,by simp [premises]⟩) (.hyp ⟨2,by simp [premises]⟩)

theorem originalRecovery_free : Recovery.Free originalRecovery := by
  apply IndexedVectorTreeStoredConstructorRecovery.recovery_free
  all_goals trivial

def lawProof : ProofSyntax Const premises statement := recoveryLaw lower raise domain originalRecovery

theorem lawProof_free : lawProof.FunctionExtensionalityFree :=
  recoveryLaw_free lower raise domain originalRecovery originalRecovery_free

def reusedRecovery : Recovery (statement :: premises) lower raise domain :=
  recoveryOfLaw lower raise domain (.hyp 0)

theorem reusedRecovery_free : Recovery.Free reusedRecovery :=
  recoveryOfLaw_free (premises := statement :: premises) lower raise domain (.hyp 0) (by trivial)

def fieldLawViaStatement : ProofSyntax Const (statement :: premises)
    (GuardedConstructorProjections.fieldInjective constructor domain) :=
  ConstructorArgumentMap.fieldInjective given.raw lower raise domain
    (.hyp ⟨3,by simp [premises]⟩) reusedRecovery

theorem fieldLawViaStatement_free : fieldLawViaStatement.FunctionExtensionalityFree :=
  ConstructorArgumentMap.fieldInjective_free given.raw lower raise domain _ reusedRecovery
    True.intro reusedRecovery_free

private def discharge : ProofSyntax.HypothesisSubstitution (statement :: premises) premises :=
  Fin.cases lawProof (fun occurrence => .hyp occurrence)

private theorem discharge_free (occurrence : Fin (statement :: premises).length) :
    (discharge occurrence).FunctionExtensionalityFree := by
  refine Fin.cases ?_ (fun _ => ?_) occurrence
  · exact lawProof_free
  · trivial

def dischargedFieldLaw : ProofSyntax Const premises
    (GuardedConstructorProjections.fieldInjective constructor domain) :=
  ProofSyntax.substituteHypotheses discharge fieldLawViaStatement

theorem dischargedFieldLaw_free : dischargedFieldLaw.FunctionExtensionalityFree :=
  ProofSyntax.substituteHypotheses_free discharge fieldLawViaStatement fieldLawViaStatement_free discharge_free

theorem dischargedFieldLaw_holds :
    (model.denote (GuardedConstructorProjections.fieldInjective constructor domain) values).down :=
  Soundness.extDerivation_sound dischargedFieldLaw.erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) assumptions_realizable

private def hypothesisCount (occurrence : Nat) : ProofSyntax.Tree Const → Nat
  | .node _ observation count children =>
      (if observation.hypothesisOccurrence = some occurrence then 1 else 0) +
        (List.ofFn (fun index : Fin count => hypothesisCount occurrence (children index))).sum

theorem both_inputs_cite_the_recovery_statement : hypothesisCount 3 fieldLawViaStatement.observe = 2 := by
  decide +kernel

def changedDomain : ClosedTerm Const (GuardedConstructorProjections.Admission N E (N ⇒ E)) :=
  .lam (.lam (.lam .top))

def changedStatement : ClosedFormula Const := recoveryStatement decode encode changedDomain

theorem changed_domain_admits_bottom :
    (model.denote (GuardedConstructorProjections.admitted changedDomain zero bottom given.children) values).down := by
  trivial

theorem changed_guard_recovery_refused : ¬ (model.denote changedStatement values).down := by
  intro claimed
  have hypotheses : Soundness.SatisfiesHyps model values [changedStatement] := by
    intro formula member
    obtain rfl := List.mem_singleton.mp member
    exact claimed
  have specialized := Soundness.extDerivation_sound (M := model) (ρ := values)
    (specializeRecoveryLaw (assumptions := [changedStatement]) decode encode changedDomain zero bottom given.children (.hyp 0)).erase
    (model.functionsRespectEqv_of_fullDomains full) (fun _ => trivial) hypotheses
  have impossible := model.eq_of_eqv_of_fullDomains full (specialized changed_domain_admits_bottom)
  exact FiniteConstructorFieldEmbeddingControls.encoded_not_bottom
    (model.denote decode values (model.denote bottom values)) impossible

#print axioms lawProof_free
#print axioms reusedRecovery_free
#print axioms fieldLawViaStatement_free
#print axioms dischargedFieldLaw_free
#print axioms dischargedFieldLaw_holds
#print axioms both_inputs_cite_the_recovery_statement
#print axioms changed_domain_admits_bottom
#print axioms changed_guard_recovery_refused

end Mettapedia.GSLT.LanguageDef.IndexedVectorTreeStoredRecoveryReuseControls
