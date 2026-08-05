import Mathlib.Tactic

/-!
# Optimal continual learning: equivalence classes and perfect memory

Knoblauch, Husain, and Diethe, *Optimal Continual Learning has Perfect Memory
and is NP-hard* (2020, arXiv:2006.05188), Definition 8 and Lemma 3, define the
class of a parameter as the intersection of all admissible solution sets that
contain it.  Lemma 3 then treats these classes as the equivalence classes of
identical task-set membership.

The displayed definition supplies only one implication: every member of the
intersection belongs to every solution set containing the parameter.  It does
not imply the converse.  A two-point, two-set fixture below refutes the first
claim of Lemma 3 as stated.

The repaired construction uses equality of membership signatures across the
entire admissible family.  It is an equivalence relation, its classes are
equal or disjoint, and every admissible solution set contains either a whole
class or none of it.  The source intersection agrees with the repaired class
when the admissible family is closed under complement.

Finally, one stored representative from every surviving repaired class is
proved sufficient to answer every admissible task-intersection query.  This
is the set-theoretic, finite-observation content of the paper's perfect-memory
argument.  No theorem here claims the paper's NP-hardness result; that requires
a separate encoding and complexity-preserving reduction.
-/

namespace Mettapedia.MachineLearning.ContinualLearning

namespace OptimalContinualLearning

universe uParameter

variable {Parameter : Type uParameter}

/-- Definition 8 as displayed: the intersection of every admissible solution
set containing `parameter`, written as its membership predicate. -/
def sourceIntersectionClass
    (family : Set (Set Parameter))
    (parameter : Parameter) : Set Parameter :=
  {candidate |
    ∀ solution ∈ family, parameter ∈ solution → candidate ∈ solution}

theorem sourceIntersectionClass_self
    (family : Set (Set Parameter))
    (parameter : Parameter) :
    parameter ∈ sourceIntersectionClass family parameter := by
  intro solution _ parameter_mem
  exact parameter_mem

/-- Repaired relation: two parameters have the same membership signature
across all admissible solution sets. -/
def MembershipEquivalent
    (family : Set (Set Parameter))
    (first second : Parameter) : Prop :=
  ∀ solution ∈ family, first ∈ solution ↔ second ∈ solution

theorem membershipEquivalent_refl
    (family : Set (Set Parameter))
    (parameter : Parameter) :
    MembershipEquivalent family parameter parameter := by
  intro solution _
  rfl

theorem membershipEquivalent_symm
    {family : Set (Set Parameter)}
    {first second : Parameter}
    (equivalent : MembershipEquivalent family first second) :
    MembershipEquivalent family second first := by
  intro solution solution_mem
  exact (equivalent solution solution_mem).symm

theorem membershipEquivalent_trans
    {family : Set (Set Parameter)}
    {first second third : Parameter}
    (first_second : MembershipEquivalent family first second)
    (second_third : MembershipEquivalent family second third) :
    MembershipEquivalent family first third := by
  intro solution solution_mem
  exact (first_second solution solution_mem).trans
    (second_third solution solution_mem)

/-- The genuine equivalence class induced by the task-family signature. -/
def membershipClass
    (family : Set (Set Parameter))
    (parameter : Parameter) : Set Parameter :=
  {candidate | MembershipEquivalent family parameter candidate}

theorem membershipClass_self
    (family : Set (Set Parameter))
    (parameter : Parameter) :
    parameter ∈ membershipClass family parameter :=
  membershipEquivalent_refl family parameter

theorem mem_membershipClass_iff_class_eq
    (family : Set (Set Parameter))
    (first second : Parameter) :
    second ∈ membershipClass family first ↔
      membershipClass family second = membershipClass family first := by
  constructor
  · intro first_second
    apply Set.ext
    intro candidate
    constructor
    · intro second_candidate
      exact membershipEquivalent_trans
        first_second second_candidate
    · intro first_candidate
      exact membershipEquivalent_trans
        (membershipEquivalent_symm first_second) first_candidate
  · intro classes_equal
    rw [← classes_equal]
    exact membershipClass_self family second

theorem membershipClasses_disjoint_of_not_equivalent
    {family : Set (Set Parameter)}
    {first second : Parameter}
    (notEquivalent : ¬ MembershipEquivalent family first second) :
    Disjoint (membershipClass family first)
      (membershipClass family second) := by
  refine Set.disjoint_left.2 ?_
  intro candidate first_candidate second_candidate
  apply notEquivalent
  exact membershipEquivalent_trans first_candidate
    (membershipEquivalent_symm second_candidate)

/-- Every admissible solution set is saturated by repaired equivalence
classes. -/
theorem membershipClass_subset_or_disjoint
    (family : Set (Set Parameter))
    (parameter : Parameter)
    (solution : Set Parameter)
    (solution_mem : solution ∈ family) :
    membershipClass family parameter ⊆ solution ∨
      Disjoint (membershipClass family parameter) solution := by
  by_cases parameter_mem : parameter ∈ solution
  · left
    intro candidate equivalent
    exact (equivalent solution solution_mem).mp parameter_mem
  · right
    refine Set.disjoint_left.2 ?_
    intro candidate equivalent candidate_mem
    exact parameter_mem ((equivalent solution solution_mem).mpr candidate_mem)

/-- Complement closure is exactly the extra separation property needed to
turn the source's one-way intersection into the repaired equivalence class. -/
def ComplementClosed (family : Set (Set Parameter)) : Prop :=
  ∀ solution ∈ family, solutionᶜ ∈ family

theorem sourceIntersectionClass_eq_membershipClass_of_complementClosed
    {family : Set (Set Parameter)}
    (closed : ComplementClosed family)
    (parameter : Parameter) :
    sourceIntersectionClass family parameter =
      membershipClass family parameter := by
  apply Set.ext
  intro candidate
  constructor
  · intro sourceMember solution solution_mem
    constructor
    · intro parameter_mem
      exact sourceMember solution solution_mem parameter_mem
    · intro candidate_mem
      by_contra parameter_not_mem
      have parameter_complement : parameter ∈ solutionᶜ := parameter_not_mem
      have candidate_complement : candidate ∈ solutionᶜ :=
        sourceMember solutionᶜ (closed solution solution_mem)
          parameter_complement
      exact candidate_complement candidate_mem
  · intro equivalent solution solution_mem parameter_mem
    exact (equivalent solution solution_mem).mp parameter_mem

/-! ## Counterexample to the displayed source definition -/

/-- Two admissible sets on two parameters: the full set and `{true}`. -/
def asymmetricFamily : Set (Set Bool) :=
  {Set.univ, {true}}

theorem true_mem_sourceIntersectionClass_false :
    true ∈ sourceIntersectionClass asymmetricFamily false := by
  intro solution solution_mem false_mem
  simp [asymmetricFamily] at solution_mem
  rcases solution_mem with rfl | rfl
  · simp
  · simp at false_mem

theorem false_not_mem_sourceIntersectionClass_true :
    false ∉ sourceIntersectionClass asymmetricFamily true := by
  intro false_member
  have singleton_mem : ({true} : Set Bool) ∈ asymmetricFamily := by
    simp [asymmetricFamily]
  have := false_member ({true} : Set Bool) singleton_mem (by simp)
  simp at this

/-- The first bullet of source Lemma 3 fails for Definition 8 as displayed:
membership in the one-way intersection need not imply equality of classes. -/
theorem source_Lemma3_first_claim_counterexample :
    true ∈ sourceIntersectionClass asymmetricFamily false ∧
      sourceIntersectionClass asymmetricFamily false ≠
        sourceIntersectionClass asymmetricFamily true := by
  constructor
  · exact true_mem_sourceIntersectionClass_false
  · intro classes_equal
    have false_self :=
      sourceIntersectionClass_self asymmetricFamily false
    rw [classes_equal] at false_self
    exact false_not_mem_sourceIntersectionClass_true false_self

theorem asymmetricFamily_not_complementClosed :
    ¬ ComplementClosed asymmetricFamily := by
  intro closed
  have full_mem : (Set.univ : Set Bool) ∈ asymmetricFamily := by
    simp [asymmetricFamily]
  have complement_mem := closed Set.univ full_mem
  simp only [asymmetricFamily, Set.mem_insert_iff,
    Set.mem_singleton_iff] at complement_mem
  rcases complement_mem with complement_univ | complement_singleton
  · have point := Set.ext_iff.mp complement_univ true
    simp at point
  · have point := Set.ext_iff.mp complement_singleton true
    simp at point

/-! ## Representative memory as a task-intersection oracle -/

/-- `memory` stores a representative of every equivalence class still
represented in `remaining`. -/
def RepresentsEveryRemainingClass
    (family : Set (Set Parameter))
    (remaining memory : Set Parameter) : Prop :=
  ∀ parameter ∈ remaining,
    ∃ representative ∈ memory,
      MembershipEquivalent family parameter representative

/-- One representative per surviving class is sufficient to answer whether
any admissible solution set intersects the surviving optimal set. -/
theorem representativeMemory_is_intersectionOracle
    {family : Set (Set Parameter)}
    {remaining memory : Set Parameter}
    (memory_subset : memory ⊆ remaining)
    (represents : RepresentsEveryRemainingClass family remaining memory)
    (solution : Set Parameter)
    (solution_mem : solution ∈ family) :
    (memory ∩ solution).Nonempty ↔
      (remaining ∩ solution).Nonempty := by
  constructor
  · rintro ⟨parameter, memory_mem, solution_parameter⟩
    exact ⟨parameter, memory_subset memory_mem, solution_parameter⟩
  · rintro ⟨parameter, remaining_mem, solution_parameter⟩
    obtain ⟨representative, memory_representative, equivalent⟩ :=
      represents parameter remaining_mem
    exact ⟨representative, memory_representative,
      (equivalent solution solution_mem).mp solution_parameter⟩

/-- Missing the `true` equivalence class makes `{false}` fail the task
intersection query for the admissible set `{true}`. -/
theorem singleton_memory_fails_intersectionOracle :
    ¬ ((({false} : Set Bool) ∩ ({true} : Set Bool)).Nonempty ↔
      ((Set.univ : Set Bool) ∩ ({true} : Set Bool)).Nonempty) := by
  simp

theorem singleton_memory_does_not_represent_every_class :
    ¬ RepresentsEveryRemainingClass asymmetricFamily
      (Set.univ : Set Bool) ({false} : Set Bool) := by
  intro represents
  obtain ⟨representative, representative_mem, equivalent⟩ :=
    represents true (by simp)
  have representative_false : representative = false := by
    simpa using representative_mem
  subst representative
  have singleton_mem : ({true} : Set Bool) ∈ asymmetricFamily := by
    simp [asymmetricFamily]
  have same_membership := equivalent ({true} : Set Bool) singleton_mem
  simp at same_membership

#print axioms mem_membershipClass_iff_class_eq
#print axioms membershipClasses_disjoint_of_not_equivalent
#print axioms membershipClass_subset_or_disjoint
#print axioms sourceIntersectionClass_eq_membershipClass_of_complementClosed
#print axioms source_Lemma3_first_claim_counterexample
#print axioms representativeMemory_is_intersectionOracle
#print axioms singleton_memory_does_not_represent_every_class

end OptimalContinualLearning

end Mettapedia.MachineLearning.ContinualLearning
