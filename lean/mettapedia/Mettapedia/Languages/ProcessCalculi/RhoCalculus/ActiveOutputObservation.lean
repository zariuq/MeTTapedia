import Mettapedia.Languages.ProcessCalculi.RhoCalculus.HeaderInversion

/-!
# Public output observations of the authored rho semantics

The observer inspects an active output subject after canonical equations.
It does not descend into an input continuation or quoted code. For a header
frontier this observation is exactly membership of an original output
occurrence with the same canonical subject. Neither sorting nor wrapper
collapse creates an output that was absent from the frontier.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveOutputObservation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Canonical HeaderInversion CanonicalStepperCompleteness

/-- An active output on this subject, without observations inside guards
or quotation. Canonicalization makes the predicate equation invariant. -/
def HasOutput (channel process : Pattern) : Prop :=
  ∃ payload, .apply "POutput" [canonicalize channel, payload] ∈
    bagSplice (canonicalize process)

theorem canonical_congr {channel first second : Pattern}
    (equal : canonicalize first = canonicalize second) :
    HasOutput channel first ↔ HasOutput channel second := by
  unfold HasOutput
  rw [equal]

private theorem output_mem_collapsed (channel payload : Pattern) (patterns : List Pattern)
    (nonbags : ∀ pattern ∈ patterns, ∀ elements,
      pattern ≠ .collection .hashBag elements none) :
    .apply "POutput" [channel, payload] ∈ bagSplice (collapseBag patterns) ↔
      .apply "POutput" [channel, payload] ∈ patterns := by
  cases patterns with
  | nil => simp [collapseBag, bagSplice]
  | cons first rest =>
      cases rest with
      | nil =>
          rw [collapseBag, bagSplice_eq_singleton_of_not_bag (nonbags first (by simp))]
      | cons second rest => rfl

/-- Canonical equations preserve exactly the active output occurrences
of a concrete header frontier. -/
theorem frontier_iff (channel : Pattern) (heads : List Header) :
    HasOutput channel (parallel heads) ↔
      ∃ subject payload, .output subject payload ∈ heads ∧
        canonicalize subject = canonicalize channel := by
  have nonbags : ∀ pattern ∈ sortPatterns (heads.map (fun head => canonicalize head.pattern)),
      ∀ elements, pattern ≠ .collection .hashBag elements none := by
    intro pattern member
    have original := (sortPatterns_perm (heads.map (fun head => canonicalize head.pattern))).mem_iff.mpr member
    obtain ⟨head, _, rfl⟩ := List.mem_map.mp original
    intro elements
    exact head.canonical_nonbag elements none
  unfold HasOutput
  change (∃ payload, .apply "POutput" [canonicalize channel, payload] ∈
    bagSplice (canonicalParallel heads)) ↔ _
  rw [canonicalParallel_eq]
  constructor
  · rintro ⟨payload, member⟩
    have sorted := (output_mem_collapsed _ _ _ nonbags).mp member
    have original := (sortPatterns_perm (heads.map (fun head => canonicalize head.pattern))).mem_iff.mpr sorted
    obtain ⟨head, inHeads, equal⟩ := List.mem_map.mp original
    cases head with
    | input subject body =>
        simp [Header.pattern, canonicalize_input] at equal
    | output subject datum =>
        have subjectEq : canonicalize subject = canonicalize channel := by
          have facts : canonicalize subject = canonicalize channel ∧
              canonicalize datum = payload := by
            simpa only [Header.pattern, canonicalize_output, Pattern.apply.injEq,
              List.cons.injEq, and_true, true_and] using equal
          exact facts.1
        exact ⟨subject, datum, inHeads, subjectEq⟩
  · rintro ⟨subject, payload, member, equal⟩
    refine ⟨canonicalize payload, (output_mem_collapsed _ _ _ nonbags).mpr ?_⟩
    apply (sortPatterns_perm (heads.map (fun head => canonicalize head.pattern))).mem_iff.mp
    apply List.mem_map.mpr
    refine ⟨.output subject payload, member, ?_⟩
    simp only [Header.pattern, canonicalize_output, equal]

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ActiveOutputObservation
