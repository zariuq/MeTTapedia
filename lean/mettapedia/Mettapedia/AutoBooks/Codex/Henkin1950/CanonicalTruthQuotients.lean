import Mettapedia.AutoBooks.Codex.Henkin1950.RepresentativeIndependence

namespace Mettapedia.AutoBooks.Codex.Henkin1950

open Mettapedia.Logic.HOL

/-!
Quotient-class quantifier clauses for Henkin's canonical truth relation.

`CanonicalTruth.lean` states the first universal and existential clauses over
closed-term instances. `RepresentativeIndependence.lean` then proves that the
truth relation is independent of the choice of realizing representatives. This
file combines those two layers to state the quantifier clauses directly over
Henkin's quotient-class domains.
-/

/-- The universal clause for canonical truth stated directly over quotient
classes rather than chosen closed representatives. -/
theorem holds_all_iff_forall_class_extensions
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    Holds T ν (.all φ) ↔
      ∀ c : TermClass T σ, Holds T (ClassAssignment.extend ν c) φ := by
  constructor
  · intro hForall c
    exact holds_all_specialize_representative hT ν hForall c
  · intro hClasses
    rw [holds_all_iff_forall_closed_instances hT hAll ν φ]
    intro t
    let c : TermClass T σ := classOf (T := T) t
    have hc : Holds T (ClassAssignment.extend ν c) φ := hClasses c
    have hRealizes :
        RepresentativeAssignment.Realizes T
          (RepresentativeAssignment.extend
            (ClassAssignment.chooseRepresentatives ν) t)
          (ClassAssignment.extend ν c) := by
      intro τ v
      cases v with
      | vz =>
          change classOf (T := T) t = c
          simp [c]
      | vs v =>
          change classOf (T := T) (ClassAssignment.chooseRepresentatives ν v) = ν v
          simp [ClassAssignment.chooseRepresentatives]
    have hMem :
        closeFormula
          (RepresentativeAssignment.extend
            (ClassAssignment.chooseRepresentatives ν) t) φ ∈ T :=
      (holds_iff_closeFormula_of_realizes
        hT hEx hAll hRealizes φ).mp hc
    simpa [closeBody, instantiate_subst_lift] using hMem

/-- The existential clause for canonical truth stated directly over quotient
classes rather than chosen closed representatives. -/
theorem holds_ex_iff_exists_class_witness
    {T : ClosedTheorySet}
    (hT : CompleteConsistentTheory T)
    (hEx : ExistentialWitnessClosed T)
    (hAll : UniversalCounterexampleClosed T)
    (ν : ClassAssignment T Γ)
    {σ : HTy} (φ : Formula (σ :: Γ)) :
    Holds T ν (.ex φ) ↔
      ∃ c : TermClass T σ, Holds T (ClassAssignment.extend ν c) φ := by
  constructor
  · intro hExists
    rcases (holds_ex_iff_exists_closed_witness hT hEx ν φ).mp hExists with ⟨t, ht⟩
    let c : TermClass T σ := classOf (T := T) t
    have hRealizes :
        RepresentativeAssignment.Realizes T
          (RepresentativeAssignment.extend
            (ClassAssignment.chooseRepresentatives ν) t)
          (ClassAssignment.extend ν c) := by
      intro τ v
      cases v with
      | vz =>
          change classOf (T := T) t = c
          simp [c]
      | vs v =>
          change classOf (T := T) (ClassAssignment.chooseRepresentatives ν v) = ν v
          simp [ClassAssignment.chooseRepresentatives]
    have hMem :
        closeFormula
          (RepresentativeAssignment.extend
            (ClassAssignment.chooseRepresentatives ν) t) φ ∈ T := by
      simpa [closeBody, instantiate_subst_lift] using ht
    exact ⟨c,
      (holds_iff_closeFormula_of_realizes
        hT hEx hAll hRealizes φ).mpr hMem⟩
  · rintro ⟨c, hc⟩
    exact holds_ex_of_class_witness hT ν c hc

end Mettapedia.AutoBooks.Codex.Henkin1950
