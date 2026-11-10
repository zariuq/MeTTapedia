import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.SuperpositionHigherOrder

/-!
# Eventual coverage is distinct from sound finite enumeration reports

An enumeration may be sound and never claim completion while reporting
nothing forever. Eventual coverage states the missing per-solution progress
property directly. It permits infinite complete sets without requiring a
finite finished stage. It does not assert that an arbitrary scheduler is fair.
-/
set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
namespace UnificationEnumerationProgress
universe u v
variable {T : Type u} {S : Type v} (A : SubstitutionAction T S) (K : EquationStore T)

def EventuallyCovers (enumeration : Superposition.UnifierEnumeration A K) : Prop :=
  ∀ σ, A.Models σ K → ∃ n u, u ∈ (enumeration.report n).answers ∧ Superposition.Factors A σ u

def silent : Superposition.UnifierEnumeration A K where
  report := fun _ => Search.Outcome.unknown
  sound := by intro n u member; exact False.elim (Multiset.notMem_zero u member)
  complete := by intro n completed; cases completed

theorem silent_not_eventually_covering (solvable : A.Consistent K) : ¬ EventuallyCovers A K (silent A K) := by
  rintro covering
  obtain ⟨σ, solved⟩ := solvable
  obtain ⟨n, u, member, _⟩ := covering σ solved
  exact Multiset.notMem_zero u member

theorem eventual_cover_returns_something (enumeration : Superposition.UnifierEnumeration A K)
    (covering : EventuallyCovers A K enumeration) (solvable : A.Consistent K) :
    ∃ n, (enumeration.report n).answers ≠ 0 := by
  obtain ⟨σ, solved⟩ := solvable
  obtain ⟨n, u, member, _⟩ := covering σ solved
  refine ⟨n, ?_⟩
  intro empty
  rw [empty] at member
  exact Multiset.notMem_zero u member
end UnificationEnumerationProgress
end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
