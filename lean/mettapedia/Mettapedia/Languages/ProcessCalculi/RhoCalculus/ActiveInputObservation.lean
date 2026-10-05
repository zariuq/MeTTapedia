import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-!
# Active public input observations of the authored rho semantics

The observer asks whether a process is ready to receive on a supplied
subject. It inspects neither the suspended handler nor quotation contents.
The canonical observation is exactly membership of an actual input in a
header frontier, including its actual channel.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Canonical HeaderInversion CanonicalStepperCompleteness

def HasInput (channel process : Pattern) : Prop :=
  ∃ body, .apply "PInput" [canonicalize channel, .lambda none body] ∈
    bagSplice (canonicalize process)

theorem canonical_congr {channel first second : Pattern}
    (equal : canonicalize first = canonicalize second) :
    HasInput channel first ↔ HasInput channel second := by
  unfold HasInput
  rw [equal]

private theorem input_mem_collapsed (channel body : Pattern) (patterns : List Pattern)
    (nonbags : ∀ pattern ∈ patterns, ∀ elements,
      pattern ≠ .collection .hashBag elements none) :
    .apply "PInput" [channel, .lambda none body] ∈ bagSplice (collapseBag patterns) ↔
      .apply "PInput" [channel, .lambda none body] ∈ patterns := by
  cases patterns with
  | nil => simp [collapseBag, bagSplice]
  | cons first rest =>
      cases rest with
      | nil =>
          rw [collapseBag, bagSplice_eq_singleton_of_not_bag (nonbags first (by simp))]
      | cons second rest => rfl

/-- Canonical equations do not invent a receiver in a concrete frontier,
and do not turn a suspended handler into an active receiver. -/
theorem frontier_iff (channel : Pattern) (heads : List Header) :
    HasInput channel (parallel heads) ↔
      ∃ subject body, .input subject body ∈ heads ∧
        canonicalize subject = canonicalize channel := by
  have nonbags : ∀ pattern ∈ sortPatterns (heads.map (fun head => canonicalize head.pattern)),
      ∀ elements, pattern ≠ .collection .hashBag elements none := by
    intro pattern member
    have original := (sortPatterns_perm (heads.map (fun head => canonicalize head.pattern))).mem_iff.mpr member
    obtain ⟨head, _, rfl⟩ := List.mem_map.mp original
    intro elements
    exact head.canonical_nonbag elements none
  unfold HasInput
  change (∃ body, .apply "PInput" [canonicalize channel, .lambda none body] ∈
    bagSplice (canonicalParallel heads)) ↔ _
  rw [canonicalParallel_eq]
  constructor
  · rintro ⟨body, member⟩
    have sorted := (input_mem_collapsed _ _ _ nonbags).mp member
    have original := (sortPatterns_perm (heads.map (fun head => canonicalize head.pattern))).mem_iff.mpr sorted
    obtain ⟨head, inHeads, equal⟩ := List.mem_map.mp original
    cases head with
    | input subject handler =>
        have facts : canonicalize subject = canonicalize channel ∧ canonicalize handler = body := by
          simpa only [Header.pattern, canonicalize_input, Pattern.apply.injEq, List.cons.injEq,
            Pattern.lambda.injEq, and_true, true_and] using equal
        exact ⟨subject, handler, inHeads, facts.1⟩
    | output subject datum => simp [Header.pattern, canonicalize_output] at equal
  · rintro ⟨subject, body, member, equal⟩
    refine ⟨canonicalize body, (input_mem_collapsed _ _ _ nonbags).mpr ?_⟩
    apply (sortPatterns_perm (heads.map (fun head => canonicalize head.pattern))).mem_iff.mp
    apply List.mem_map.mpr
    refine ⟨.input subject body, member, ?_⟩
    simp only [Header.pattern, canonicalize_input, equal]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveInputObservation
