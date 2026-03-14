import Mathlib.Order.PrimeSeparator
import Mettapedia.Logic.HOL.LindenbaumSet

namespace Mettapedia.Logic.HOL

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

namespace ClosedTheory

/-- Iterated implication from a finite list of closed assumptions to a closed conclusion. -/
def iterImp (Γ : ClosedTheory Const) (φ : ClosedFormula Const) : ClosedFormula Const :=
  match Γ with
  | [] => φ
  | ψ :: Γ => iterImp Γ (.imp ψ φ)

theorem provable_iterImp :
    Provable (Const := Const) Γ φ →
      Provable (Const := Const) [] (iterImp (Const := Const) Γ φ) := by
  intro h
  induction Γ generalizing φ with
  | nil =>
      simpa [iterImp] using h
  | cons ψ Γ ih =>
      have h' : Provable (Const := Const) Γ (.imp ψ φ) := .impI h
      simpa [iterImp] using ih h'

end ClosedTheory

namespace ClosedTheorySet

namespace ProvablyEquivalent.LindenbaumSet

variable {T : ClosedTheorySet Const}

theorem top_mem_filter
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)} :
    (⊤ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F :=
  Order.PFilter.top_mem

theorem mem_of_himp_mem
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    {a b : ProvablyEquivalent.LindenbaumSet (Const := Const) T}
    (hImp : a ⇨ b ∈ F) (ha : a ∈ F) :
    b ∈ F := by
  have hInf : a ⊓ (a ⇨ b) ∈ F := Order.PFilter.inf_mem ha hImp
  exact Order.PFilter.mem_of_le inf_himp_le hInf

theorem mem_of_iterImp_mem
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    {Γ : ClosedTheory Const} {φ : ClosedFormula Const}
    (hImp :
      (⟦ClosedTheory.iterImp (Const := Const) Γ φ⟧ :
        ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F)
    (hΓ :
      ∀ {ξ : ClosedFormula Const},
        ξ ∈ Γ →
          (⟦ξ⟧ :
            ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F) :
    (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F := by
  induction Γ generalizing φ with
  | nil =>
      simpa [ClosedTheory.iterImp] using hImp
  | cons ψ Γ ih =>
      have hImpψ :
          (⟦(.imp ψ φ)⟧ :
            ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F :=
        ih hImp (by
          intro ξ hξ
          exact hΓ (by simp [hξ]))
      have hψ :
          (⟦ψ⟧ :
            ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F :=
        hΓ (by simp)
      exact mem_of_himp_mem (T := T) hImpψ hψ

theorem mem_of_closedTheoryProvable
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    {Γ : ClosedTheory Const} {φ : ClosedFormula Const}
    (hΓ :
      ∀ {ξ : ClosedFormula Const},
        ξ ∈ Γ →
          (⟦ξ⟧ :
            ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F)
    (hφ : ClosedTheory.Provable (Const := Const) Γ φ) :
    (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F := by
  have hIterProv :
      ClosedTheorySet.Provable (Const := Const) T
        (ClosedTheory.iterImp (Const := Const) Γ φ) :=
    ClosedTheorySet.provable_of_closedTheory
      (Const := Const) (T := T) (Δ := [])
      (hΔ := by intro ξ hξ; cases hξ)
      (hφ := ClosedTheory.provable_iterImp (Const := Const) hφ)
  have hIterTop :
      (⟦ClosedTheory.iterImp (Const := Const) Γ φ⟧ :
        ProvablyEquivalent.LindenbaumSet (Const := Const) T) = ⊤ := by
    exact (ProvablyEquivalent.LindenbaumSet.provable_iff_eq_top
      (Const := Const) (T := T)
      (φ := ClosedTheory.iterImp (Const := Const) Γ φ)).1 hIterProv
  have hIterMem :
      (⟦ClosedTheory.iterImp (Const := Const) Γ φ⟧ :
        ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F := by
    exact hIterTop ▸ top_mem_filter (Const := Const) (T := T) (F := F)
  exact mem_of_iterImp_mem (Const := Const) (T := T) hIterMem hΓ

theorem mem_all_of_bot_mem
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    {a : ProvablyEquivalent.LindenbaumSet (Const := Const) T}
    (hBot : (⊥ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F) :
    a ∈ F :=
  Order.PFilter.mem_of_le bot_le hBot

end LindenbaumSet

end ProvablyEquivalent

/-- The preimage of a Lindenbaum-set prime filter gives a candidate closed theory. -/
def carrierOfPFilter (T : ClosedTheorySet Const)
    (F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)) :
    ClosedTheorySet Const :=
  fun φ => (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F

theorem mem_carrierOfPFilter_iff
    {T : ClosedTheorySet Const}
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    {φ : ClosedFormula Const} :
    φ ∈ carrierOfPFilter (Const := Const) T F ↔
      (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F :=
  Iff.rfl

theorem carrierOfPFilter_extends
    {T : ClosedTheorySet Const}
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)} :
    ∀ {φ : ClosedFormula Const}, φ ∈ T → φ ∈ carrierOfPFilter (Const := Const) T F := by
  intro φ hφ
  have hProv : Provable (Const := Const) T φ := provable_of_mem (Const := Const) hφ
  have hEqTop :
      (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) = ⊤ :=
    (ProvablyEquivalent.LindenbaumSet.provable_iff_eq_top
      (Const := Const) (T := T) (φ := φ)).1 hProv
  change (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F
  exact hEqTop ▸
    ProvablyEquivalent.LindenbaumSet.top_mem_filter
      (Const := Const) (T := T) (F := F)

theorem carrierOfPFilter_deductivelyClosed
    {T : ClosedTheorySet Const}
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)} :
    DeductivelyClosed (Const := Const) (carrierOfPFilter (Const := Const) T F) := by
  intro φ hφ
  rcases hφ with ⟨Γ, hΓ, hProv⟩
  exact ProvablyEquivalent.LindenbaumSet.mem_of_closedTheoryProvable
    (Const := Const) (T := T) (F := F)
    (hΓ := by
      intro ξ hξ
      exact hΓ ξ hξ)
    hProv

theorem carrierOfPrimePFilter_prime_or
    {T : ClosedTheorySet Const}
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    (hPrime : Order.PFilter.IsPrime F) :
    ∀ {φ ψ : ClosedFormula Const},
      (.or φ ψ : ClosedFormula Const) ∈ carrierOfPFilter (Const := Const) T F →
        φ ∈ carrierOfPFilter (Const := Const) T F ∨
          ψ ∈ carrierOfPFilter (Const := Const) T F := by
  intro φ ψ hOr
  have hSup :
      ((⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ⊔
          ⟦ψ⟧) ∈ F := by
    simpa [carrierOfPFilter,
      ProvablyEquivalent.LindenbaumSet.sup_def] using hOr
  by_cases hφ :
      (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F
  · exact Or.inl hφ
  · have hIdeal :
        (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈
          hPrime.compl_ideal.toIdeal := hφ
    by_cases hψ :
        (⟦ψ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F
    · exact Or.inr hψ
    · have hSupIdeal :
          ((⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ⊔
              ⟦ψ⟧) ∈ hPrime.compl_ideal.toIdeal := by
          exact hPrime.compl_ideal.toIdeal.sup_mem hIdeal hψ
      exact False.elim (hSupIdeal hSup)

theorem carrierOfPFilter_consistent_of_omits
    {T : ClosedTheorySet Const}
    {F : Order.PFilter (ProvablyEquivalent.LindenbaumSet (Const := Const) T)}
    {φ : ClosedFormula Const}
    (hOmit : φ ∉ carrierOfPFilter (Const := Const) T F) :
    Consistent (Const := Const) (carrierOfPFilter (Const := Const) T F) := by
  intro hInconsistent
  have hBot :
      (.bot : ClosedFormula Const) ∈ carrierOfPFilter (Const := Const) T F :=
    carrierOfPFilter_deductivelyClosed (Const := Const) (T := T) (F := F) hInconsistent
  have hAny :
      (⟦φ⟧ : ProvablyEquivalent.LindenbaumSet (Const := Const) T) ∈ F :=
    ProvablyEquivalent.LindenbaumSet.mem_all_of_bot_mem
      (Const := Const) (T := T) (F := F) (a := ⟦φ⟧) hBot
  exact hOmit hAny

theorem exists_prime_extension_separating
    {T : ClosedTheorySet Const} {φ : ClosedFormula Const}
    (hNot : ¬Provable (Const := Const) T φ) :
    ∃ U : ClosedTheorySet Const,
      (∀ {ψ : ClosedFormula Const}, ψ ∈ T → ψ ∈ U) ∧
      DeductivelyClosed (Const := Const) U ∧
      Consistent (Const := Const) U ∧
      (∀ {ψ χ : ClosedFormula Const}, (.or ψ χ : ClosedFormula Const) ∈ U → ψ ∈ U ∨ χ ∈ U) ∧
      φ ∉ U := by
  let A := ProvablyEquivalent.LindenbaumSet (Const := Const) T
  let x : A := ⟦φ⟧
  have hxNeTop : x ≠ (⊤ : A) := by
    intro hEq
    exact hNot ((ProvablyEquivalent.LindenbaumSet.provable_iff_eq_top
      (Const := Const) (T := T) (φ := φ)).2 hEq)
  have hDisjoint :
      Disjoint (((Order.PFilter.principal (⊤ : A)) : Order.PFilter A) : Set A)
        (Order.Ideal.principal x) := by
    refine Set.disjoint_left.2 ?_
    intro y hyF hyI
    have hyTop : (⊤ : A) ≤ y := (Order.PFilter.mem_principal).1 hyF
    have hyx : y ≤ x := Order.Ideal.mem_principal.1 hyI
    exact hxNeTop (top_le_iff.mp (le_trans hyTop hyx))
  obtain ⟨J, hJPrime, hJContains, hJDisjoint⟩ :=
    DistribLattice.prime_ideal_of_disjoint_filter_ideal
      (F := Order.PFilter.principal (⊤ : A))
      (I := Order.Ideal.principal x)
      hDisjoint
  let P : Order.Ideal.PrimePair A := Order.Ideal.IsPrime.toPrimePair hJPrime
  let F : Order.PFilter A := P.F
  let U : ClosedTheorySet Const := carrierOfPFilter (Const := Const) T F
  have hxJ : x ∈ J := (Order.Ideal.principal_le_iff).1 hJContains
  have hOmit : φ ∉ U := by
    intro hφ
    exact (Set.disjoint_left.1 P.disjoint) (by simpa [P] using hxJ) hφ
  refine ⟨U, ?_, carrierOfPFilter_deductivelyClosed (Const := Const) (T := T) (F := F),
    carrierOfPFilter_consistent_of_omits (Const := Const) (T := T) (F := F) hOmit,
    carrierOfPrimePFilter_prime_or (Const := Const) (T := T)
      (F := F) (hPrime := Order.Ideal.PrimePair.F_isPrime P),
    hOmit⟩
  exact carrierOfPFilter_extends (Const := Const) (T := T) (F := F)

theorem exists_prime_extension_of_consistent
    {T : ClosedTheorySet Const}
    (hCons : Consistent (Const := Const) T) :
    ∃ U : ClosedTheorySet Const,
      (∀ {ψ : ClosedFormula Const}, ψ ∈ T → ψ ∈ U) ∧
      DeductivelyClosed (Const := Const) U ∧
      Consistent (Const := Const) U ∧
      (∀ {ψ χ : ClosedFormula Const}, (.or ψ χ : ClosedFormula Const) ∈ U → ψ ∈ U ∨ χ ∈ U) := by
  rcases exists_prime_extension_separating
      (Const := Const) (T := T) (φ := (.bot : ClosedFormula Const)) hCons
    with ⟨U, hExt, hClosed, hUCons, hPrime, hBotOmit⟩
  exact ⟨U, hExt, hClosed, hUCons, hPrime⟩

end ClosedTheorySet

end Mettapedia.Logic.HOL
