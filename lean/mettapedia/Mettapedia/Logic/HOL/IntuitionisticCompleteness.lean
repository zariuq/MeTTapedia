import Mettapedia.Logic.HOL.CanonicalModel

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/-!
# Internal Intuitionistic Completeness Milestone

This file packages the current canonical-world / cumulative-Henkin machinery into
an honest internal completeness theorem:

- finite closed assumptions over the cumulative Henkin language,
- closed conclusion over the cumulative Henkin language,
- validity in all canonical worlds that contain the cumulative Henkin axioms,
- if and only if finite-context provability from those assumptions together with
  the cumulative Henkin axiom family.

This is not yet the final original-signature HOL completeness theorem. It is the
internal cumulative-Henkin milestone on the way there.
-/

/-- Validity in all canonical worlds containing the cumulative Henkin axioms. -/
def CanonicalHenkinValidFrom
    (Δ : List (ClosedFormula (HInf Base Const)))
    (φ : ClosedFormula (HInf Base Const)) : Prop :=
  ∀ W : World Base Const,
    HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier →
    W ∈ contextDenote (Base := Base) (Const := Const) Δ
      (emptyClosedSubst Base Const) →
    W ∈ denoteFormula (Base := Base) (Const := Const) φ
      (emptyClosedSubst Base Const)

@[simp] theorem mem_denoteFormula_empty_iff
    {W : World Base Const}
    {φ : ClosedFormula (HInf Base Const)} :
    W ∈ denoteFormula (Base := Base) (Const := Const) φ
      (emptyClosedSubst Base Const) ↔
      φ ∈ W.carrier := by
  rw [mem_denoteFormula_iff]
  simp [subst_emptyClosedSubst]

@[simp] theorem mem_contextDenote_empty_iff
    {W : World Base Const}
    {Δ : List (ClosedFormula (HInf Base Const))} :
    W ∈ contextDenote (Base := Base) (Const := Const) Δ
      (emptyClosedSubst Base Const) ↔
      ∀ φ : ClosedFormula (HInf Base Const),
        φ ∈ Δ → φ ∈ W.carrier := by
  constructor
  · intro h φ hφ
    exact (mem_denoteFormula_empty_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := φ)).1 <|
      (mem_contextDenote_iff
        (Base := Base)
        (Const := Const)
        (W := W)
        (Δ := Δ)
        (σs := emptyClosedSubst Base Const)).1 h φ hφ
  · intro h
    apply (mem_contextDenote_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (Δ := Δ)
      (σs := emptyClosedSubst Base Const)).2
    intro φ hφ
    exact (mem_denoteFormula_empty_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (φ := φ)).2 <|
      h φ hφ

theorem liftBase_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    ClosedTheorySet.Provable
      (Const := HInf Base Const)
      (fun ψ =>
        ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
          ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
      (liftBaseClosedFormula (Base := Base) (Const := Const) φ) := by
  refine ClosedTheorySet.provable_of_closedTheory
    (Const := HInf Base Const)
    (T := fun ψ =>
      ψ ∈ Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)) ∨
        ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
    (Δ := Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)))
    ?_
    ?_
  · intro ψ hψ
    exact Or.inl hψ
  · simpa only
      [HenkinConstInfinity.liftBaseClosedFormula, Mettapedia.Logic.HOL.mapClosedFormula] using
      (ExtDerivation.closedTheory_mapConst
        (Base := Base)
        (Const := Const)
        (Const' := HInf Base Const)
        (f := HenkinConstInfinity.base)
        (Δ := Δ)
        (φ := φ)
        hProv)

theorem canonicalHenkinValidFrom_of_provable
    {Δ : List (ClosedFormula (HInf Base Const))}
    {φ : ClosedFormula (HInf Base Const)}
    (hProv :
      ClosedTheorySet.Provable
        (Const := HInf Base Const)
        (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
        φ) :
    CanonicalHenkinValidFrom (Base := Base) (Const := Const) Δ φ := by
  intro W hHenkin hΔ
  apply (mem_denoteFormula_empty_iff
    (Base := Base)
    (Const := Const)
    (W := W)
    (φ := φ)).2
  apply W.mem_of_provable
  rcases hProv with ⟨Γ, hΓ, hDeriv⟩
  exact ClosedTheorySet.provable_of_closedTheory
    (Const := HInf Base Const)
    (T := W.carrier)
    (Δ := Γ)
    (hΔ := by
      intro ψ hψ
      rcases hΓ ψ hψ with hψ | hψ
      · exact (mem_contextDenote_empty_iff
          (Base := Base)
          (Const := Const)
          (W := W)
          (Δ := Δ)).1 hΔ ψ hψ
      · exact hHenkin hψ)
    hDeriv

theorem provable_of_canonicalHenkinValidFrom
    {Δ : List (ClosedFormula (HInf Base Const))}
    {φ : ClosedFormula (HInf Base Const)}
    (hValid : CanonicalHenkinValidFrom (Base := Base) (Const := Const) Δ φ) :
    ClosedTheorySet.Provable
      (Const := HInf Base Const)
      (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
      φ := by
  classical
  by_contra hNot
  rcases exists_canonical_counterworld_of_list_notProvable
      (Base := Base)
      (Const := Const)
      (Δ := Δ)
      (φ := φ)
      hNot with
    ⟨W, hWΔ, hWHenkin, hWNotφ⟩
  have hΔ :
      W ∈ contextDenote (Base := Base) (Const := Const) Δ
        (emptyClosedSubst Base Const) := by
    exact (mem_contextDenote_empty_iff
      (Base := Base)
      (Const := Const)
      (W := W)
      (Δ := Δ)).2 <|
      by
        intro ψ hψ
        exact (mem_denoteFormula_empty_iff
          (Base := Base)
          (Const := Const)
          (W := W)
          (φ := ψ)).1 <|
          hWΔ hψ
  exact hWNotφ (hValid W hWHenkin hΔ)

theorem canonicalHenkinValidFrom_iff_provable
    {Δ : List (ClosedFormula (HInf Base Const))}
    {φ : ClosedFormula (HInf Base Const)} :
    CanonicalHenkinValidFrom (Base := Base) (Const := Const) Δ φ ↔
      ClosedTheorySet.Provable
        (Const := HInf Base Const)
        (fun ψ => ψ ∈ Δ ∨ ψ ∈ HenkinAxioms (Base := Base) (Const := Const))
        φ := by
  constructor
  · exact provable_of_canonicalHenkinValidFrom (Base := Base) (Const := Const)
  · exact canonicalHenkinValidFrom_of_provable (Base := Base) (Const := Const)

theorem liftBase_canonicalHenkinValidFrom_of_provable
    {Δ : List (ClosedFormula Const)}
    {φ : ClosedFormula Const}
    (hProv : ExtDerivation Const Δ φ) :
    CanonicalHenkinValidFrom
      (Base := Base)
      (Const := Const)
      (Δ.map (liftBaseClosedFormula (Base := Base) (Const := Const)))
      (liftBaseClosedFormula (Base := Base) (Const := Const) φ) :=
  canonicalHenkinValidFrom_of_provable
    (Base := Base)
    (Const := Const)
    (liftBase_provable (Base := Base) (Const := Const) hProv)

end HenkinConstInfinity

end Mettapedia.Logic.HOL
