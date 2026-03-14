import Mettapedia.Logic.HOL.CanonicalExtension
import Mettapedia.Logic.HOL.CanonicalKripke
import Mettapedia.Logic.HOL.HenkinAxiomsInfinity

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace HenkinConstInfinity

/-- The cumulative Henkin axiom family is preserved when adding one extra closed formula. -/
theorem henkinAxioms_subset_insert
    {φ : ClosedFormula (HInf Base Const)}
    {T : ClosedTheorySet (HInf Base Const)}
    (hHenkin : HenkinAxioms (Base := Base) (Const := Const) ⊆ T) :
    HenkinAxioms (Base := Base) (Const := Const) ⊆ insert φ T := by
  intro ψ hψ
  exact by simp [hHenkin hψ]

/--
For worlds over the cumulative Henkin language that already contain the cumulative
Henkin axiom family, the canonical implication forcing clause is equivalent to
membership of the implication formula itself.
-/
theorem forcesImp_iff_mem
    {W : ClosedTheorySet.World (HInf Base Const)}
    (hHenkin : HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier)
    {φ ψ : ClosedFormula (HInf Base Const)} :
    ClosedTheorySet.World.ForcesImp (Const := HInf Base Const) W φ ψ ↔
      (.imp φ ψ : ClosedFormula (HInf Base Const)) ∈ W.carrier := by
  constructor
  · intro hForces
    by_contra hImp
    have hNotProv :
        ¬ClosedTheorySet.Provable
          (Const := HInf Base Const)
          (insert φ W.carrier)
          ψ :=
      ClosedTheorySet.not_provable_insert_of_imp_not_mem
        (Const := HInf Base Const)
        (W := W)
        hImp
    rcases exists_world_separating_of_notProvable
        (Base := Base)
        (Const := Const)
        (T := insert φ W.carrier)
        (φ := ψ)
        (henkinAxioms_subset_insert
          (Base := Base)
          (Const := Const)
          (φ := φ)
          hHenkin)
        hNotProv with
      ⟨V, hExt, _, hOmit⟩
    have hWV : W ≤ V := by
      intro ξ hξ
      exact hExt (by simp [hξ])
    have hφV : φ ∈ V.carrier := by
      exact hExt (by simp)
    have hψV : ψ ∈ V.carrier :=
      hForces hWV hφV
    exact hOmit hψV
  · intro hImp
    exact ClosedTheorySet.World.imp_mem_implies_forcesImp
      (Const := HInf Base Const)
      hImp

/--
For worlds over the cumulative Henkin language that already contain the cumulative
Henkin axiom family, the canonical negation forcing clause is equivalent to
membership of the negation formula itself.
-/
theorem forcesNot_iff_mem
    {W : ClosedTheorySet.World (HInf Base Const)}
    (hHenkin : HenkinAxioms (Base := Base) (Const := Const) ⊆ W.carrier)
    {φ : ClosedFormula (HInf Base Const)} :
    ClosedTheorySet.World.ForcesNot (Const := HInf Base Const) W φ ↔
      (.not φ : ClosedFormula (HInf Base Const)) ∈ W.carrier := by
  constructor
  · intro hForces
    by_contra hNot
    have hCons :
        ClosedTheorySet.Consistent
          (Const := HInf Base Const)
          (insert φ W.carrier) :=
      ClosedTheorySet.consistent_insert_of_not_not_mem
        (Const := HInf Base Const)
        (W := W)
        hNot
    have hConsUnion :
        ClosedTheorySet.Consistent
          (Const := HInf Base Const)
          (insert φ W.carrier ∪ HenkinAxioms (Base := Base) (Const := Const)) := by
      simpa [Set.union_eq_left.2 (henkinAxioms_subset_insert
        (Base := Base)
        (Const := Const)
        (φ := φ)
        hHenkin)] using hCons
    rcases exists_world_of_consistent_with_henkinAxioms
        (Base := Base)
        (Const := Const)
        (T := insert φ W.carrier)
        hConsUnion with
      ⟨V, hExt, _⟩
    have hWV : W ≤ V := by
      intro ξ hξ
      exact hExt (by simp [hξ])
    have hφV : φ ∈ V.carrier := by
      exact hExt (by simp)
    exact hForces hWV hφV
  · intro hNot
    exact ClosedTheorySet.World.not_mem_implies_forcesNot
      (Const := HInf Base Const)
      hNot

end HenkinConstInfinity

end Mettapedia.Logic.HOL
