import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalChecks

/-!
# Certain and possible occurrence regions determine exact counts

At a principal answer the matching region is a lower bound for every model.
An occurrence belongs to the possible region when its matching equation is
consistent with the existing store. These regions retain physical occurrence
identities, including duplicate-valued occurrences.

An exact count is entailed precisely when the lower and upper regions coincide
and have that count. The result needs neither an independence assumption on
occurrences nor enumeration of simultaneous matching combinations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalCheckRegions

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO}

noncomputable def possibleRegion (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (world : Finset O) (pattern : T) : Finset O := by
  classical
  exact world.filter fun occurrence => A.Consistent (problem ++ [(pattern, label occurrence)])

theorem possible_member_iff (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (world : Finset O) (pattern : T) (occurrence : O) :
    occurrence ∈ possibleRegion A problem label world pattern ↔
      occurrence ∈ world ∧ ∃ assignment,
        A.Models assignment problem ∧ A.Solves assignment (pattern, label occurrence) := by
  classical
  simp only [possibleRegion, Finset.mem_filter, SubstitutionAction.Consistent,
    SubstitutionAction.models_append, SubstitutionAction.models_cons,
    SubstitutionAction.models_nil, and_true]

theorem region_subset_possible (A : SubstitutionAction T S) {problem : EquationStore T}
    (label : O → T) (world : Finset O) (pattern : T) {assignment : S}
    (solved : A.Models assignment problem) :
    Check.matches A assignment label world pattern ⊆ possibleRegion A problem label world pattern := by
  classical
  intro occurrence member
  obtain ⟨present, same⟩ := Finset.mem_filter.mp member
  exact (possible_member_iff A problem label world pattern occurrence).mpr
    ⟨present, assignment, solved, same⟩

theorem principal_region_subset (A : SubstitutionAction T S)
    {problem : EquationStore T} {answer : S} {observed : List T}
    (principal : A.PrincipalOn problem answer observed)
    (label : O → T) (world : Finset O) (pattern : T)
    (argument : pattern ∈ observed)
    (values : ∀ occurrence ∈ world, label occurrence ∈ observed)
    {assignment : S} (solved : A.Models assignment problem) :
    Check.matches A answer label world pattern ⊆ Check.matches A assignment label world pattern := by
  classical
  obtain ⟨residual, factors⟩ := principal.factors assignment solved
  intro occurrence member
  obtain ⟨present, same⟩ := Finset.mem_filter.mp member
  have preserved := A.preserves residual same
  have result : A.E (A.apply assignment pattern) (A.apply assignment (label occurrence)) :=
    A.equivalence.trans (factors pattern argument)
      (A.equivalence.trans (by simpa only [A.apply_compose] using preserved)
        (A.equivalence.symm (factors (label occurrence) (values occurrence present))))
  exact Finset.mem_filter.mpr ⟨present, result⟩

theorem count_iff_regions (A : SubstitutionAction T S)
    {problem : EquationStore T} {answer : S} {observed : List T}
    (principal : A.PrincipalOn problem answer observed)
    (label : O → T) (world : Finset O) (pattern : T) (number : Nat)
    (argument : pattern ∈ observed)
    (values : ∀ occurrence ∈ world, label occurrence ∈ observed) :
    A.Entails problem (fun assignment => (Check.count pattern number).Holds A assignment label world) ↔
      (Check.matches A answer label world pattern).card = number ∧
        possibleRegion A problem label world pattern = Check.matches A answer label world pattern := by
  classical
  constructor
  · intro entailed
    have baseline : (Check.matches A answer label world pattern).card = number := entailed answer principal.sound
    refine ⟨baseline, Finset.Subset.antisymm ?_ (region_subset_possible A label world pattern principal.sound)⟩
    intro occurrence member
    obtain ⟨present, assignment, solved, same⟩ :=
      (possible_member_iff A problem label world pattern occurrence).mp member
    have lower := principal_region_subset A principal label world pattern argument values solved
    have equalRegions : Check.matches A answer label world pattern = Check.matches A assignment label world pattern :=
      Finset.eq_of_subset_of_card_le lower (by
        have size : (Check.matches A assignment label world pattern).card = number := entailed assignment solved
        omega)
    rw [equalRegions]
    exact Finset.mem_filter.mpr ⟨present, same⟩
  · rintro ⟨baseline, samePossible⟩ assignment solved
    have lower := principal_region_subset A principal label world pattern argument values solved
    have upper := region_subset_possible A label world pattern solved
    rw [samePossible] at upper
    have equalRegions := Finset.Subset.antisymm upper lower
    change (Check.matches A assignment label world pattern).card = number
    rw [equalRegions]
    exact baseline

theorem absent_iff_possible_empty (A : SubstitutionAction T S) (problem : EquationStore T)
    (label : O → T) (world : Finset O) (pattern : T) :
    A.Entails problem (fun assignment => (Check.absent pattern).Holds A assignment label world) ↔
      possibleRegion A problem label world pattern = ∅ := by
  classical
  constructor
  · intro absent
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro occurrence member
    obtain ⟨present, assignment, solved, same⟩ :=
      (possible_member_iff A problem label world pattern occurrence).mp member
    exact absent assignment solved occurrence present same
  · intro empty assignment solved occurrence present same
    have member := (possible_member_iff A problem label world pattern occurrence).mpr
      ⟨present, assignment, solved, same⟩
    rw [empty] at member
    exact Finset.notMem_empty occurrence member

theorem equal_iff_principal_answer (A : SubstitutionAction T S)
    {problem : EquationStore T} {answer : S} {observed : List T}
    (principal : A.PrincipalOn problem answer observed)
    (left right : T) (leftRetained : left ∈ observed) (rightRetained : right ∈ observed) :
    A.Entails problem (fun assignment => A.Solves assignment (left, right)) ↔ A.Solves answer (left, right) := by
  constructor
  · exact fun entailed => entailed answer principal.sound
  · intro same assignment solved
    obtain ⟨residual, factors⟩ := principal.factors assignment solved
    exact A.equivalence.trans (factors left leftRetained)
      (A.equivalence.trans (by simpa only [SubstitutionAction.Solves, A.apply_compose] using A.preserves residual same)
        (A.equivalence.symm (factors right rightRetained)))

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.PrincipalCheckRegions
