import Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower.RawInferenceMILWorkload

/-!
# Executable native materialization of checked learned relation proofs

Raw proofs are reconstructed by recursion over their submitted nodes and
ordered children. The learned relation interpretation selects its actual
stored rule by executable lookup; no classical selection is used to construct
the hypothesis. Its equality with the existing proof-relevant interpretation
is a separate theorem. Native formation still requires the independently
formed quotation leaves and ambient context.

The supported semantic vocabulary is the existing mother/father/chain
calculus. The generic reconstruction below does not assign meanings to new
learned rules. No runtime, native rule package or source syntax is changed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
namespace MILNativeMaterialization

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceProofRelevantSemanticExtension
open Presentation MILCheckedNativePrograms MILLearnedProofRelevantAdmission

mutual

/-- Reconstruct the submitted checked tree without selecting an existential
witness. Only the raw syntax and executable instantiation are inspected. -/
def reconstruct {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (proof : RawProof) (accepted : checkRaw definition goal proof = true) :
    { derivation : Derivation definition goal // derivation.erase = proof } := by
  cases proof with
  | node ruleInstance children =>
      simp only [checkRaw] at accepted
      cases instantiated : instantiateRule? definition ruleInstance with
      | none => simp only [instantiated, Bool.false_eq_true] at accepted
      | some result =>
          rcases result with ⟨premises, conclusion⟩
          simp only [instantiated, Bool.and_eq_true, decide_eq_true_eq] at accepted
          rcases accepted with ⟨rfl, checkedChildren⟩
          obtain ⟨derived, erases⟩ := reconstructChildren children checkedChildren
          exact ⟨.byRule ruleInstance
            (instantiateRule?_eq_some_iff_application.mp instantiated) derived,
            congrArg (RawProof.node ruleInstance) erases⟩
termination_by sizeOf proof

/-- Ordered premise occurrences remain ordered in the reconstructed tree. -/
def reconstructChildren {definition : ValidatedCalculusLanguageDef} {premises : List Pattern}
    (proofs : List RawProof) (accepted : checkRawChildren definition premises proofs = true) :
    { derivations : DerivationList definition premises // derivations.erase = proofs } := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => exact ⟨.nil, rfl⟩
      | cons _ _ => simp only [checkRawChildren, Bool.false_eq_true] at accepted
  | cons premise premises =>
      cases proofs with
      | nil => simp only [checkRawChildren, Bool.false_eq_true] at accepted
      | cons proof proofs =>
          simp only [checkRawChildren, Bool.and_eq_true] at accepted
          obtain ⟨head, headErases⟩ := reconstruct proof accepted.1
          obtain ⟨tail, tailErases⟩ := reconstructChildren proofs accepted.2
          exact ⟨.cons head tail, congrArg₂ List.cons headErases tailErases⟩
termination_by sizeOf proofs

end

mutual

/-- Fixed raw rule instances determine the typed proof tree, including its
ordered premise indices; application evidence itself is proposition-valued. -/
theorem erase_injective {definition : ValidatedCalculusLanguageDef} {goal : Pattern}
    (first second : Derivation definition goal) (same : first.erase = second.erase) :
    first = second := by
  match first, second with
  | .byRule instanceFirst applicationFirst childrenFirst,
      .byRule instanceSecond applicationSecond childrenSecond =>
          obtain ⟨sameInstance, sameChildren⟩ := RawProof.node.inj same
          cases sameInstance
          have firstInstantiated := instantiateRule?_eq_some_iff_application.mpr applicationFirst
          have secondInstantiated := instantiateRule?_eq_some_iff_application.mpr applicationSecond
          have samePremises := congrArg Prod.fst
            (Option.some.inj (firstInstantiated.symm.trans secondInstantiated))
          cases samePremises
          have sameChildren := eraseChildren_injective childrenFirst childrenSecond sameChildren
          cases sameChildren
          rfl
termination_by structural first

theorem eraseChildren_injective {definition : ValidatedCalculusLanguageDef} {premises : List Pattern}
    (first second : DerivationList definition premises) (same : first.erase = second.erase) :
    first = second := by
  match first, second with
  | .nil, .nil => rfl
  | .cons head tail, .cons head' tail' =>
          obtain ⟨heads, tails⟩ := List.cons.inj same
          have heads := erase_injective head head' heads
          have tails := eraseChildren_injective tail tail' tails
          cases heads
          cases tails
          rfl
termination_by structural first

end

private theorem no_base_application {ruleInstance : RuleInstance} {premises : List Pattern}
    {conclusion : Pattern} : ¬ RuleApplication MILCheckedChain.base ruleInstance premises conclusion := by
  rintro ⟨rule, lookup, _, _, _, _⟩
  have empty : MILCheckedChain.base.1.rules = [] := rfl
  unfold CalculusLanguageDef.lookupRule? at lookup
  rw [empty] at lookup
  cases lookup

/-- The exact learned rule is data from lookup, not a witness extracted from
the proposition-valued rule-application premise. -/
def semantics : CalculusLanguageSemantics MILCheckedChain.learned.target Meaning where
  ruleMeaning {ruleInstance premises conclusion} application evidence := by
    cases lookup : MILCheckedChain.learned.target.1.lookupRule? ruleInstance.ruleId with
    | none =>
        exact False.elim (by
          rcases application with ⟨rule, found, _, _, _, _⟩
          rw [lookup] at found
          cases found)
    | some rule =>
        exact learnedSemantics.addedRuleMeaning rule (by
          change rule ∈ MILCheckedChain.learned.target.1.rules
          exact List.mem_of_find?_eq_some lookup)
          ruleInstance premises conclusion lookup application evidence

/-- Executable lookup realizes the independently authored semantics exactly. -/
theorem semantics_eq : semantics = learnedSemantics.targetSemantics := by
  unfold semantics SemanticExtension.targetSemantics
  congr 1
  funext ruleInstance premises conclusion application evidence
  have absent : ¬ RuleApplication MILCheckedChain.base ruleInstance premises conclusion :=
    no_base_application
  unfold SemanticExtension.targetRuleMeaning
  rw [dif_neg absent]

variable {n : Nat} {context : Tower.Ctx n}

/-- Check and materialize the submitted proof by executable structural
reconstruction, rule interpretation and native constructor quotation. -/
def materialize? (quotation : HostedQuotation context) (source target : Pattern)
    (raw : RawProof) : Option (Tower.Tm n) :=
  if accepted : checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw = true then
    let checked := (reconstruct raw accepted).val
    let evidence : Reach source target := semantics.interpret checked
    some (IntrinsicMILHypothesis.quoteHypothesis quotation.toTypedVocabularyQuotation
      evidence.toIntrinsic.hypothesis)
  else none

theorem materialize_isSome (quotation : HostedQuotation context) (source target : Pattern)
    (raw : RawProof) :
    (materialize? quotation source target raw).isSome =
      checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw := by
  unfold materialize?
  split
  · simp_all only [Option.isSome_some]
  · rename_i rejected
    cases checked : checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw with
    | false => rfl
    | true => exact False.elim (rejected checked)

/-- Every existing exact-erasure artifact agrees with the executable output.
Thus a different derivation of the same endpoint cannot replace this tree. -/
theorem materialize_checked
    {quotation : HostedQuotation context} {source target : Pattern} {raw : RawProof}
    (program : CheckedRawNativeProgram quotation source target raw) :
    materialize? quotation source target raw = some program.toChecked.nativeTerm.code := by
  have accepted : checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw = true := by
    rw [← program.erases]
    exact checkRaw_erase program.checked
  have same : (reconstruct raw accepted).val = program.checked :=
    erase_injective _ _ ((reconstruct raw accepted).property.trans program.erases.symm)
  simp only [materialize?, dif_pos accepted, same, semantics_eq]
  rfl

/-- On an explicitly supplied derivation, materialization computes the exact
constructor quotation of its executable interpretation. -/
theorem materialize_derivation (quotation : HostedQuotation context)
    {source target : Pattern}
    (derivation : Derivation MILCheckedChain.learned.target (MILCheckedChain.relates source target)) :
    materialize? quotation source target derivation.erase =
      some (IntrinsicMILHypothesis.quoteHypothesis quotation.toTypedVocabularyQuotation
        (semantics.interpret derivation).toIntrinsic.hypothesis) := by
  have accepted := checkRaw_erase derivation
  have same : (reconstruct derivation.erase accepted).val = derivation :=
    erase_injective _ _ (reconstruct derivation.erase accepted).property
  simp only [materialize?, dif_pos accepted, same]

/-- Successful materialization is exactly the existing exact-erasure native
artifact relation, with no search for a replacement proof. -/
theorem materialize_eq_some_iff (quotation : HostedQuotation context)
    (source target : Pattern) (raw : RawProof) (term : Tower.Tm n) :
    materialize? quotation source target raw = some term ↔
      ∃ program : CheckedRawNativeProgram quotation source target raw,
        program.toChecked.nativeTerm.code = term := by
  constructor
  · intro result
    have accepted : checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw = true := by
      rw [← materialize_isSome quotation source target raw, result]
      rfl
    let program : CheckedRawNativeProgram quotation source target raw :=
      ⟨(reconstruct raw accepted).val, (reconstruct raw accepted).property⟩
    exact ⟨program, Option.some.inj ((materialize_checked program).symm.trans result)⟩
  · rintro ⟨program, rfl⟩
    exact materialize_checked program

theorem materialize_eq_none_iff (quotation : HostedQuotation context)
    (source target : Pattern) (raw : RawProof) :
    materialize? quotation source target raw = none ↔
      checkRaw MILCheckedChain.learned.target (MILCheckedChain.relates source target) raw = false := by
  rw [← materialize_isSome quotation source target raw]
  cases materialize? quotation source target raw <;> simp only [Option.isSome, reduceCtorEq]

/-- The materialized term carries the same proof-relevant relational meaning
as the exact retained checker tree, not merely a Boolean reachability result. -/
theorem materialize_meaning {quotation : HostedQuotation context}
    {source target : Pattern} {raw : RawProof} {term : Tower.Tm n}
    (result : materialize? quotation source target raw = some term) :
    ∃ program : CheckedRawNativeProgram quotation source target raw,
      program.toChecked.nativeTerm.code = term ∧
      Nonempty (Reach source target) ∧
      Nonempty (program.toChecked.intrinsicProgram.denotation.evidence source target) := by
  obtain ⟨program, same⟩ := (materialize_eq_some_iff quotation source target raw term).mp result
  exact ⟨program, same, ⟨program.toChecked.relationalEvidence⟩, ⟨program.toChecked.nativeEvidence⟩⟩

/-- Refined admission is derived from separately checked quotation leaves and
a formed context, not from raw typing or the materializer's return tag. -/
theorem materialize_judgment {quotation : HostedQuotation context}
    (leaves : FormationSensitiveMIL.QuotationTyping quotation.toTypedVocabularyQuotation)
    (formed : FormationSensitive.ContextFormation IntrinsicMILHypothesis.rules context)
    {source target : Pattern} {raw : RawProof} {term : Tower.Tm n}
    (result : materialize? quotation source target raw = some term) :
    FormationSensitive.Judgment IntrinsicMILHypothesis.rules context term
      (quotation.hypothesisType () ()).code := by
  obtain ⟨program, rfl⟩ := (materialize_eq_some_iff quotation source target raw term).mp result
  exact RawInferenceMILWorkload.native_judgment_of_quotation program leaves formed

#print axioms reconstruct
#print axioms reconstructChildren
#print axioms erase_injective
#print axioms semantics
#print axioms semantics_eq
#print axioms materialize?
#print axioms materialize_isSome
#print axioms materialize_checked
#print axioms materialize_derivation
#print axioms materialize_eq_some_iff
#print axioms materialize_eq_none_iff
#print axioms materialize_meaning
#print axioms materialize_judgment

end MILNativeMaterialization
end Mettapedia.Languages.MeTTa.TypeTheory.CumulativeTower
