import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-! # Executable materialization of checked inference proofs -/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceChecker

open Mettapedia.OSLF.MeTTaIL.Syntax

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

/-- Run the structural checker and retain the exact derivation of the submitted tree. -/
def materializeProof? (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (raw : RawProof) : Option { proof : Derivation definition goal // proof.erase = raw } :=
  if checked : checkRaw definition goal raw = true then some (reconstruct raw checked)
  else none

theorem materializeProof?_eq_some {definition : ValidatedCalculusLanguageDef}
    {goal : Pattern} {raw : RawProof} (checked : checkRaw definition goal raw = true) :
    materializeProof? definition goal raw = some (reconstruct raw checked) := by
  simp [materializeProof?, checked]

theorem materializeProof?_isSome (definition : ValidatedCalculusLanguageDef) (goal : Pattern)
    (raw : RawProof) : (materializeProof? definition goal raw).isSome = checkRaw definition goal raw := by
  cases checked : checkRaw definition goal raw <;> simp [materializeProof?, checked]

end Mettapedia.GSLT.LanguageDef.InferenceChecker
