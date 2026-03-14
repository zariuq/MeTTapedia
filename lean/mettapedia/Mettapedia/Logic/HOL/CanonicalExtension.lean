import Mettapedia.Logic.HOL.CanonicalTheory

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

abbrev ClosedTheorySetWith (Const : Ty Base → Type v) := ClosedTheorySet Const

namespace ClosedTheorySet

theorem provable_imp_of_insert {T : ClosedTheorySet Const}
    {φ ψ : ClosedFormula Const}
    (h : Provable (Const := Const) (insert φ T) ψ) :
    Provable (Const := Const) T (.imp φ ψ) := by
  rcases h with ⟨Γ, hΓ, hψ⟩
  let Γ' : ClosedTheory Const := Γ.filter (fun ξ => ξ ≠ φ)
  have hmono :
      ClosedTheory.Provable (Const := Const) (φ :: Γ') ψ := by
    refine ExtDerivation.mono ?_ hψ
    intro ξ hξ
    by_cases hEq : ξ = φ
    · subst hEq
      simp
    · simp [Γ', List.mem_filter, hξ, hEq]
  refine ⟨Γ', ?_, ExtDerivation.impI hmono⟩
  intro ξ hξ
  have hξΓ : ξ ∈ Γ := (List.mem_filter.mp hξ).1
  have hξNe : ξ ≠ φ := by
    intro hEq
    have hξNeBool : decide (ξ ≠ φ) = true := (List.mem_filter.mp hξ).2
    simp [hEq] at hξNeBool
  have hξInsert : ξ ∈ insert φ T := hΓ ξ hξΓ
  simp at hξInsert
  rcases hξInsert with hEq | hξT
  · exact False.elim (hξNe hEq)
  · exact hξT

theorem not_provable_insert_of_imp_not_mem
    {W : ClosedTheorySet.World Const}
    {φ ψ : ClosedFormula Const}
    (hImp : (.imp φ ψ : ClosedFormula Const) ∉ W.carrier) :
    ¬Provable (Const := Const) (insert φ W.carrier) ψ := by
  intro hψ
  have hImpProv : Provable (Const := Const) W.carrier (.imp φ ψ) :=
    provable_imp_of_insert (Const := Const) hψ
  exact hImp (W.mem_of_provable hImpProv)

theorem consistent_insert_of_imp_not_mem
    {W : ClosedTheorySet.World Const}
    {φ ψ : ClosedFormula Const}
    (hImp : (.imp φ ψ : ClosedFormula Const) ∉ W.carrier) :
    Consistent (Const := Const) (insert φ W.carrier) := by
  intro hInconsistent
  have hψ : Provable (Const := Const) (insert φ W.carrier) ψ := by
    exact provable_mp
      (Const := Const)
      (φ := (.bot : ClosedFormula Const))
      (ψ := ψ)
      (provable_of_closedTheory
        (Const := Const)
        (T := insert φ W.carrier)
        (Δ := [])
        (hΔ := by intro ξ hξ; cases hξ)
        (hφ := ClosedTheory.Provable.bot_imp (Δ := []) (Const := Const) (φ := ψ)))
      hInconsistent
  exact (not_provable_insert_of_imp_not_mem (Const := Const) (W := W) hImp) hψ

theorem provable_not_of_imp_bot {T : ClosedTheorySet Const}
    {φ : ClosedFormula Const}
    (h : Provable (Const := Const) T (.imp φ (.bot : ClosedFormula Const))) :
    Provable (Const := Const) T (.not φ) := by
  have hLift :
      Provable (Const := Const) T
        (.imp (.imp φ (.bot : ClosedFormula Const)) (.not φ)) := by
    refine provable_of_closedTheory (Const := Const) (T := T) (Δ := []) ?_ ?_
    · intro ξ hξ
      cases hξ
    · refine ExtDerivation.impI ?_
      refine ExtDerivation.notI ?_
      exact
        ExtDerivation.impE
          (ExtDerivation.hyp
            (Δ := [φ, (.imp φ (.bot : ClosedFormula Const))])
            (φ := (.imp φ (.bot : ClosedFormula Const)))
            (by simp))
          (ExtDerivation.hyp
            (Δ := [φ, (.imp φ (.bot : ClosedFormula Const))])
            (φ := φ)
            (by simp))
  exact provable_mp (Const := Const) hLift h

theorem consistent_insert_of_not_not_mem
    {W : ClosedTheorySet.World Const}
    {φ : ClosedFormula Const}
    (hNot : (.not φ : ClosedFormula Const) ∉ W.carrier) :
    Consistent (Const := Const) (insert φ W.carrier) := by
  intro hInconsistent
  have hBot : Provable (Const := Const) (insert φ W.carrier) (.bot : ClosedFormula Const) :=
    hInconsistent
  have hImpBot : Provable (Const := Const) W.carrier (.imp φ (.bot : ClosedFormula Const)) :=
    provable_imp_of_insert (Const := Const) (φ := φ) (ψ := (.bot : ClosedFormula Const)) hBot
  have hNotProv : Provable (Const := Const) W.carrier (.not φ) :=
    provable_not_of_imp_bot (Const := Const) (φ := φ) hImpBot
  exact hNot (W.mem_of_provable hNotProv)

end ClosedTheorySet

end Mettapedia.Logic.HOL
