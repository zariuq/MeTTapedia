import Mettapedia.Logic.TierZero.Kernel2.ClaimInterface
import Mettapedia.Logic.TierZero.Kernel2.Declared

/-!
# Proof interfaces survive permitted contextual substitution

`InstFacts` and `runDisc` are the existing Kernel2 conditions that make a
claim proof stable when its formals are instantiated and its dummy names are
carried freshly into another frame. Under precisely those conditions, the
proof graph has the same inferred interface, and its substituted selected
hypotheses suffice for the substituted conclusion.

The result does not erase a selected hypothesis. A caller may cut it only by
providing a derivation in the target context.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Kernel2.ClaimInterfaceSubstitution

open Mettapedia.Logic.TierZero
open Mettapedia.Logic.TierZero.ChildBound
open Mettapedia.Logic.TierZero.ProofInterface
open Mettapedia.Logic.TierZero.Kernel2
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

variable {R : Type}

theorem infer_map_invariant {Rule : Type} (operation : Tm → Tm)
    (hypotheses : List Tm) (proof : List (Rule × List Kid)) (root : Kid) :
    infer (hypotheses.map operation).length proof root =
      infer hypotheses.length proof root := by
  rw [List.length_map]

/-- A successful source run becomes a successful target-frame check under the
existing declared substitution conditions. -/
theorem checkCB_subst (env : Env R) (determined : EnvDetermined env)
    (noNames : EnvNoFv env) {sourceFrame targetFrame : Frame}
    {arguments : List Tm} {rename : Nat → Nat} {freshening : Subst Nat Tm}
    {claimHyps : List Premise} {variableCount : Nat}
    (facts : InstFacts sourceFrame targetFrame arguments rename freshening claimHyps)
    {hypotheses done : List Tm} {proof : List (R × List Kid)} {root : Kid} {goal : Tm}
    (ran : runT env sourceFrame hypotheses [] proof = some done)
    (discipline : runDisc env sourceFrame arguments.length variableCount freshening
      claimHyps hypotheses [] proof = true)
    (rootFound : lookupT hypotheses done root = some goal) :
    checkCB (matcherOf env targetFrame determined)
      (hypotheses.map (substN arguments rename)) proof root
      (substN arguments rename goal) = true := by
  have carried := runT_subst env noNames facts hypotheses [] proof done ran discipline
  simp only [List.map_nil] at carried
  rw [Claim.checkCB_eq_runT, carried]
  have rootCarried := lookupT_substN arguments rename hypotheses done root
  rw [rootFound] at rootCarried
  simpa only [Option.map_some, decide_eq_true_eq] using rootCarried

/-- **Contextual substitution and cut preserve the inferred interface.** Any
target context deriving the selected substituted hypotheses derives the
substituted goal. -/
theorem interface_subst_cut (env : Env R) (determined : EnvDetermined env)
    (noNames : EnvNoFv env) {sourceFrame targetFrame : Frame}
    {arguments : List Tm} {rename : Nat → Nat} {freshening : Subst Nat Tm}
    {claimHyps : List Premise} {variableCount : Nat}
    (facts : InstFacts sourceFrame targetFrame arguments rename freshening claimHyps)
    {hypotheses done target : List Tm} {proof : List (R × List Kid)}
    {root : Kid} {goal : Tm}
    (ran : runT env sourceFrame hypotheses [] proof = some done)
    (discipline : runDisc env sourceFrame arguments.length variableCount freshening
      claimHyps hypotheses [] proof = true)
    (rootFound : lookupT hypotheses done root = some goal) :
    ∃ used, infer hypotheses.length proof root = some used ∧
      Supports (P := presOf env targetFrame)
        (hypotheses.map (substN arguments rename)) target used
        (substN arguments rename goal) := by
  have accepted := checkCB_subst env determined noNames facts ran discipline rootFound
  obtain ⟨used, inferred, supported⟩ :=
    checkCB_interface (matcherOf env targetFrame determined) (target := target) accepted
  rw [List.length_map] at inferred
  exact ⟨used, inferred, supported⟩

/-- The selected substituted occurrences themselves give a concrete target
context for the carried proof. -/
theorem selected_subst (env : Env R) (determined : EnvDetermined env)
    (noNames : EnvNoFv env) {sourceFrame targetFrame : Frame}
    {arguments : List Tm} {rename : Nat → Nat} {freshening : Subst Nat Tm}
    {claimHyps : List Premise} {variableCount : Nat}
    (facts : InstFacts sourceFrame targetFrame arguments rename freshening claimHyps)
    {hypotheses done : List Tm} {proof : List (R × List Kid)}
    {root : Kid} {goal : Tm}
    (ran : runT env sourceFrame hypotheses [] proof = some done)
    (discipline : runDisc env sourceFrame arguments.length variableCount freshening
      claimHyps hypotheses [] proof = true)
    (rootFound : lookupT hypotheses done root = some goal) :
    ∃ used, infer hypotheses.length proof root = some used ∧
      Derivable (presOf env targetFrame)
        (select (P := presOf env targetFrame) used
          (hypotheses.map (substN arguments rename)))
        (substN arguments rename goal) := by
  have accepted := checkCB_subst env determined noNames facts ran discipline rootFound
  obtain ⟨used, inferred, derivation⟩ :=
    checkCB_selected (matcherOf env targetFrame determined) accepted
  rw [List.length_map] at inferred
  exact ⟨used, inferred, derivation⟩

end Mettapedia.Logic.TierZero.Kernel2.ClaimInterfaceSubstitution
