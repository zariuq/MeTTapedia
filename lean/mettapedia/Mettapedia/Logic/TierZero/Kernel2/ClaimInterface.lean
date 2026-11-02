import Mettapedia.Logic.TierZero.Kernel2.Claims
import Mettapedia.Logic.TierZero.ProofInterface

/-!
# A checked claim's proof-use interface

The generic proof analysis is lifted through the claim's actual child
translation. Selected hypothesis positions are classified by source origin:
judgment premise occurrence, local declaration occurrence, or cited-term
occurrence. Equal judgments at different source positions remain distinct.

The interface is inferred from the proof and root. It is not inferred from
the free variables of the conclusion. `verdict_interface` proves that deriving
the selected source hypotheses in any target context suffices for the claim's
goal there.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2

open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.ProofInterface

variable {R : Type}

inductive HypothesisOrigin where
  | judgment (premisePosition : Nat)
  | localDecl (localPosition : Nat)
  | term (termPosition : Nat)
  deriving DecidableEq, Repr

namespace Claim

/-- Classify one position in `cbHyps` back into the authored claim. Judgment
hypotheses retain their positions in the complete premise list, including side
conditions between them. -/
def originAt (claim : Claim R) (position : Nat) : Option HypothesisOrigin :=
  if _judgment : position < claim.nJ then
    (judgPositions claim.hyps)[position]?.map HypothesisOrigin.judgment
  else if _localSlot : position < claim.nJ + claim.nL then
    some (.localDecl (position - claim.nJ))
  else if _term : position < claim.nJ + claim.nL + claim.terms.length then
    some (.term (position - claim.nJ - claim.nL))
  else none

def originSet (claim : Claim R) (position : Nat) : Finset HypothesisOrigin :=
  match claim.originAt position with
  | some origin => {origin}
  | none => ∅

def usedOrigins (claim : Claim R) (used : Used) : Finset HypothesisOrigin :=
  used.biUnion claim.originSet

structure InferredInterface where
  used : Used
  origins : Finset HypothesisOrigin
  deriving DecidableEq

/-- Run the proof-use analysis on the exact proof and root read by the claim
checker. -/
def inferUsed (claim : Claim R) : Option Used := do
  let hypotheses ← claim.cbHyps
  let translated ← claim.translate
  ProofInterface.infer hypotheses.length translated.1 translated.2

def inferredInterface (claim : Claim R) : Option InferredInterface := do
  let used ← claim.inferUsed
  pure ⟨used, claim.usedOrigins used⟩

theorem originAt_exists (claim : Claim R) {position : Nat}
    (within : position < claim.nJ + claim.nL + claim.terms.length) :
    ∃ origin, claim.originAt position = some origin := by
  by_cases judgment : position < claim.nJ
  · have sourceWithin : position < (judgPositions claim.hyps).length := by
      rw [judgPositions, length_judgPositionsFrom]
      exact judgment
    exact ⟨.judgment (judgPositions claim.hyps)[position], by
      simp [originAt, judgment, List.getElem?_eq_getElem sourceWithin]⟩
  · by_cases localSlot : position < claim.nJ + claim.nL
    · exact ⟨.localDecl (position - claim.nJ), by
        simp [originAt, judgment, localSlot]⟩
    · exact ⟨.term (position - claim.nJ - claim.nL), by
        simp [originAt, judgment, localSlot, within]⟩

theorem inferUsed_bounded {claim : Claim R} {hypotheses : List Tm} {used : Used}
    (hypothesesRead : claim.cbHyps = some hypotheses)
    (inferred : claim.inferUsed = some used) :
    Bounded hypotheses.length used := by
  unfold inferUsed at inferred
  rw [hypothesesRead] at inferred
  cases translated : claim.translate with
  | none => simp [translated] at inferred
  | some result =>
      obtain ⟨proof, root⟩ := result
      simp only [translated] at inferred
      exact ProofInterface.infer_bounded inferred

theorem inferUsed_origin {claim : Claim R} {hypotheses : List Tm} {used : Used}
    (hypothesesRead : claim.cbHyps = some hypotheses)
    (inferred : claim.inferUsed = some used) {position : Nat}
    (selected : position ∈ used) :
    ∃ origin, claim.originAt position = some origin ∧ origin ∈ claim.usedOrigins used := by
  have bounded := inferUsed_bounded hypothesesRead inferred position selected
  have total : hypotheses.length = claim.nJ + claim.nL + claim.terms.length :=
    Claim.length_cbHyps hypothesesRead
  have positionWithin : position < claim.nJ + claim.nL + claim.terms.length := by
    rw [← total]
    exact bounded
  obtain ⟨origin, originRead⟩ := claim.originAt_exists positionWithin
  refine ⟨origin, originRead, ?_⟩
  exact Finset.mem_biUnion.mpr ⟨position, selected, by
    simp [originSet, originRead]⟩

/-- **The exact checked-proof interface is sufficient.** This is stable under
an arbitrary target context: each selected source hypothesis may itself be
derived there, after which the checked goal follows by cut. -/
theorem verdict_interface {env : Env R} {determined : EnvDetermined env}
    {claim : Claim R} {target : List Tm} (accepted : claim.verdict env determined = true) :
    ∃ hypotheses goal proof root used,
      claim.cbHyps = some hypotheses ∧ claim.goal = some goal ∧
      claim.translate = some (proof, root) ∧ claim.inferUsed = some used ∧
      claim.inferredInterface = some ⟨used, claim.usedOrigins used⟩ ∧
      Supports (P := presOf env claim.frame) hypotheses target used goal := by
  unfold Claim.verdict at accepted
  simp only [Bool.and_eq_true] at accepted
  obtain ⟨_, checked⟩ := accepted
  cases hypothesesRead : claim.cbHyps with
  | none => simp [hypothesesRead] at checked
  | some hypotheses =>
      cases goalRead : claim.goal with
      | none => simp [hypothesesRead, goalRead] at checked
      | some goal =>
          cases translated : claim.translate with
          | none => simp [hypothesesRead, goalRead, translated] at checked
          | some result =>
              obtain ⟨proof, root⟩ := result
              simp only [hypothesesRead, goalRead, translated] at checked
              obtain ⟨used, inferred, sufficient⟩ :=
                ProofInterface.checkCB_interface (matcherOf env claim.frame determined)
                  (target := target) checked
              have inferredClaim : claim.inferUsed = some used := by
                unfold Claim.inferUsed
                rw [hypothesesRead]
                rw [translated]
                exact inferred
              refine ⟨hypotheses, goal, proof, root, used, rfl, rfl,
                rfl, inferredClaim, ?_, sufficient⟩
              · unfold Claim.inferredInterface
                rw [inferredClaim]
                rfl

end Claim
end Mettapedia.Logic.TierZero.Kernel2
