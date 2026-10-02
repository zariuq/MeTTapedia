import Mettapedia.GSLT.LanguageDef.InferenceChecker

/-!
# Computed leaves in the shared inference checker

A computation may replace a replay subtree only after its returned judgments
are proved derivable in the same admitted definition. Ordinary nodes continue
to use `instantiateRule?`, including its ordered premises and side conditions.
The resulting mixed checker has exactly the original derivability scope.

This is a certificate compression boundary, not an additional inference axiom.
The computation's proof is erased during execution; full replay witnesses are
needed only in the correctness argument. A computation returning `none` means
that this certificate supplies no evidence, not that the goal is underivable.
The model does not establish correspondence with a particular C implementation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.InferenceChecker

/-- Qualification is indexed by the actual definition, rather than a name or
correspondence identifier. Every emitted judgment needs a derivation. -/
structure QualifiedComputation (definition : ValidatedCalculusLanguageDef)
    (Query : Type) where
  evaluate : Query → Option Pattern
  sound : ∀ query goal, evaluate query = some goal →
    Nonempty (Derivation definition goal)

/-- Replay trees and computed leaves can occur beneath the same rule node. -/
inductive CompactProof (Query : Type) where
  | replay : RawProof → CompactProof Query
  | computed : Query → CompactProof Query
  | node : RuleInstance → List (CompactProof Query) → CompactProof Query

mutual

def check {Query : Type} (definition : ValidatedCalculusLanguageDef)
    (evaluate : Query → Option Pattern) : Pattern → CompactProof Query → Bool
  | goal, .replay proof => checkRaw definition goal proof
  | goal, .computed query => decide (evaluate query = some goal)
  | goal, .node ruleInstance children =>
      match instantiateRule? definition ruleInstance with
      | none => false
      | some (premises, conclusion) =>
          decide (conclusion = goal) && checkChildren definition evaluate premises children
termination_by _ proof => sizeOf proof
decreasing_by all_goals (simp only [CompactProof.node.sizeOf_spec]; omega)

def checkChildren {Query : Type} (definition : ValidatedCalculusLanguageDef)
    (evaluate : Query → Option Pattern) :
    List Pattern → List (CompactProof Query) → Bool
  | [], [] => true
  | premise :: premises, child :: children =>
      check definition evaluate premise child &&
        checkChildren definition evaluate premises children
  | _, _ => false
termination_by _ proofs => sizeOf proofs
decreasing_by all_goals (simp only [List.cons.sizeOf_spec]; omega)

end

mutual

theorem check_sound {Query : Type} {definition : ValidatedCalculusLanguageDef}
    (computation : QualifiedComputation definition Query)
    {goal : Pattern} {proof : CompactProof Query}
    (accepted : check definition computation.evaluate goal proof = true) :
    Nonempty (Derivation definition goal) := by
  cases proof with
  | replay raw => exact checkRaw_soundness (by simpa only [check] using accepted)
  | computed query =>
      exact computation.sound query goal (by simpa only [check, decide_eq_true_eq] using accepted)
  | node ruleInstance children =>
      simp only [check] at accepted
      cases application : instantiateRule? definition ruleInstance with
      | none => simp [application] at accepted
      | some result =>
          obtain ⟨premises, conclusion⟩ := result
          simp only [application, Bool.and_eq_true, decide_eq_true_eq] at accepted
          obtain ⟨rfl, childrenAccepted⟩ := accepted
          obtain ⟨derivations⟩ := checkChildren_sound computation childrenAccepted
          exact ⟨.byRule ruleInstance
            (instantiateRule?_eq_some_iff_application.mp application) derivations⟩
termination_by sizeOf proof
decreasing_by all_goals (subst_vars; simp only [CompactProof.node.sizeOf_spec]; omega)

theorem checkChildren_sound {Query : Type} {definition : ValidatedCalculusLanguageDef}
    (computation : QualifiedComputation definition Query)
    {premises : List Pattern} {proofs : List (CompactProof Query)}
    (accepted : checkChildren definition computation.evaluate premises proofs = true) :
    Nonempty (DerivationList definition premises) := by
  cases premises with
  | nil =>
      cases proofs with
      | nil => exact ⟨.nil⟩
      | cons _ _ => simp [checkChildren] at accepted
  | cons premise premises =>
      cases proofs with
      | nil => simp [checkChildren] at accepted
      | cons proof proofs =>
          simp only [checkChildren, Bool.and_eq_true] at accepted
          obtain ⟨head, tail⟩ := accepted
          obtain ⟨headDerivation⟩ := check_sound computation head
          obtain ⟨tailDerivations⟩ := checkChildren_sound computation tail
          exact ⟨.cons headDerivation tailDerivations⟩
termination_by sizeOf proofs
decreasing_by all_goals (subst_vars; simp only [List.cons.sizeOf_spec]; omega)

end

/-- Computed leaves introduce no new judgments, even deep inside a proof. -/
theorem accepted_has_replay {Query : Type} {definition : ValidatedCalculusLanguageDef}
    (computation : QualifiedComputation definition Query)
    {goal : Pattern} {proof : CompactProof Query}
    (accepted : check definition computation.evaluate goal proof = true) :
    ∃ raw, checkRaw definition goal raw = true := by
  obtain ⟨derivation⟩ := check_sound computation accepted
  exact ⟨derivation.erase, checkRaw_erase derivation⟩

/-- Scope equivalence does not claim equality of compressed and expanded
proof objects or preservation of the size of a replay witness. -/
theorem accepted_iff_replay {Query : Type} {definition : ValidatedCalculusLanguageDef}
    (computation : QualifiedComputation definition Query) (goal : Pattern) :
    (∃ proof, check definition computation.evaluate goal proof = true) ↔
      ∃ raw, checkRaw definition goal raw = true := by
  constructor
  · rintro ⟨proof, accepted⟩
    exact accepted_has_replay computation accepted
  · rintro ⟨raw, accepted⟩
    exact ⟨.replay raw, by simpa only [check] using accepted⟩

/-- A rule-package mutation changing an emitted judgment's derivability
invalidates qualification, even if operation names and output bytes agree. -/
theorem unqualified_of_extra_output {Query : Type}
    (definition : ValidatedCalculusLanguageDef) (evaluate : Query → Option Pattern)
    {query : Query} {goal : Pattern} (emitted : evaluate query = some goal)
    (noReplay : ¬ ∃ raw, checkRaw definition goal raw = true) :
    ¬ ∃ computation : QualifiedComputation definition Query,
      computation.evaluate = evaluate := by
  rintro ⟨computation, same⟩
  have accepted : check definition computation.evaluate goal (.computed query) = true := by
    simp only [check, same, emitted, decide_true]
  exact noReplay (accepted_has_replay computation accepted)

/-- A computation failure cannot be interpreted as a successful leaf. -/
theorem absent_output_rejects {Query : Type} (definition : ValidatedCalculusLanguageDef)
    (evaluate : Query → Option Pattern) {query : Query}
    (absent : evaluate query = none) (goal : Pattern) :
    check definition evaluate goal (.computed query) = false := by
  simp [check, absent]

end Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves
