import Mettapedia.Computability.HaltingGate

/-!
# The boundary of maximal sound recognition

For an undecidable eligibility property, every computable sound recognizer
misses an eligible input and has a strictly larger computable sound extension.
The extension adds one missed input. This is an existence theorem, not an
algorithm for finding that input and not an optimization policy.

The observation-specific corollary uses the existing halting-gate theorem.
Its hypotheses matter: it does not say that a decidable syntactic fragment
cannot have a complete recognizer, or that a fixed abstract domain cannot
have a best analysis. Nor does recognition imply a compiler or a speedup.
-/

set_option autoImplicit false

namespace Mettapedia.Computability.SoundRecognitionBoundary

universe u v

variable {Program : Type u} [Primcodable Program]

/-- A total computable sound recognizer of an undecidable property misses
at least one eligible input. -/
theorem exists_missed_eligible
    {eligible accepted : Set Program}
    (undecidable : ¬ ComputablePred (· ∈ eligible))
    (computable : ComputablePred (· ∈ accepted))
    (sound : accepted ⊆ eligible) :
    ∃ program, program ∈ eligible ∧ program ∉ accepted := by
  classical
  by_contra noneMissed
  apply undecidable
  apply computable.of_eq
  intro program
  constructor
  · exact fun member => sound member
  · intro member
    by_contra rejected
    exact noneMissed ⟨program, member, rejected⟩

/-- Extending a computable recognizer by one fixed input remains computable. -/
theorem computable_insert
    {accepted : Set Program}
    (computable : ComputablePred (· ∈ accepted)) (program : Program) :
    ComputablePred (· ∈ insert program accepted) := by
  classical
  have equality : ComputablePred (fun input : Program => input = program) :=
    (Primrec.eq.comp Primrec.id (Primrec.const program)).computablePred
  exact ((Primrec.or.to_comp.comp equality.decide computable.decide).of_eq
    (fun input => by simp [Set.mem_insert_iff])).computablePred

/-- No computable sound recognizer of an undecidable property is maximal
under inclusion among all computable sound recognizers. -/
theorem exists_strict_sound_extension
    {eligible accepted : Set Program}
    (undecidable : ¬ ComputablePred (· ∈ eligible))
    (computable : ComputablePred (· ∈ accepted))
    (sound : accepted ⊆ eligible) :
    ∃ extended : Set Program,
      ComputablePred (· ∈ extended) ∧ accepted ⊂ extended ∧ extended ⊆ eligible := by
  obtain ⟨program, eligibleProgram, missed⟩ :=
    exists_missed_eligible undecidable computable sound
  refine ⟨insert program accepted, computable_insert computable program, ?_, ?_⟩
  · refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_insert _ _, ?_⟩
    intro equal
    have member : program ∈ insert program accepted := by simp
    rw [← equal] at member
    exact missed member
  · intro input member
    rcases Set.mem_insert_iff.mp member with equal | previous
    · exact equal ▸ eligibleProgram
    · exact sound previous

/-- A nontrivial observation-invariant property with a halting gate has no
inclusion-maximal computable sound recognizer. Supplying the gate is the
language-specific obligation; it is not assumed for arbitrary observations. -/
theorem observation_property_has_strict_extension
    {Observation : Type v} {observe : Program → Observation}
    (halting : HaltingGate observe)
    {eligible accepted : Set Program}
    (invariant : ObservationInvariant observe eligible)
    (nontrivial : eligible.Nonempty ∧ eligibleᶜ.Nonempty)
    (computable : ComputablePred (· ∈ accepted))
    (sound : accepted ⊆ eligible) :
    ∃ extended : Set Program,
      ComputablePred (· ∈ extended) ∧ accepted ⊂ extended ∧ extended ⊆ eligible :=
  exists_strict_sound_extension (halting.not_computable invariant nontrivial)
    computable sound

/-- Concrete negative case: no total computable sound recognizer of codes
halting on a fixed input is maximal. -/
theorem halting_recognizer_has_strict_extension
    (input : ℕ) {accepted : Set Nat.Partrec.Code}
    (computable : ComputablePred (· ∈ accepted))
    (sound : ∀ program ∈ accepted, (program.eval input).Dom) :
    ∃ extended : Set Nat.Partrec.Code,
      ComputablePred (· ∈ extended) ∧ accepted ⊂ extended ∧
      ∀ program ∈ extended, (program.eval input).Dom :=
  exists_strict_sound_extension (ComputablePred.halting_problem input)
    computable sound

end Mettapedia.Computability.SoundRecognitionBoundary

#print axioms Mettapedia.Computability.SoundRecognitionBoundary.exists_strict_sound_extension
#print axioms Mettapedia.Computability.SoundRecognitionBoundary.observation_property_has_strict_extension
#print axioms Mettapedia.Computability.SoundRecognitionBoundary.halting_recognizer_has_strict_extension
