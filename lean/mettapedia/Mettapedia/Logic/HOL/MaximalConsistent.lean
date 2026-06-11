import Mettapedia.Logic.HOL.WitnessedExtension
import Mathlib.Order.Zorn

/-!
# Maximal consistent extensions (Lindenbaum)

A consistent closed theory extends to a **maximal** consistent one (Zorn's lemma,
with chain unions consistent by finite character).  A maximal consistent theory is
deductively closed, **complete** (`χ ∈ M ∨ ¬χ ∈ M`), and prime — exactly the
ingredients the classical canonical `World` needs beyond witnessing.
-/

namespace Mettapedia.Logic.HOL

open ClosedTheorySet

universe u v

variable {Base : Type u} {Const : Ty Base → Type v}

/-! ## Two propositional `Provable` helpers -/

/-- `(χ → ⊥) ⊢ ¬χ`, lifted to theories. -/
theorem provable_not_of_imp_bot {T : ClosedTheorySet Const} {χ : ClosedFormula Const}
    (h : Provable (Const := Const) T (Term.imp χ .bot)) :
    Provable (Const := Const) T (.not χ) := by
  rcases h with ⟨Γ, hΓ, d⟩
  exact ⟨Γ, hΓ, not_of_imp_bot d⟩

/-- Disjunctive syllogism: `φ ∨ ψ` and `¬φ` give `ψ`. -/
theorem provable_or_elim_left {T : ClosedTheorySet Const} {φ ψ : ClosedFormula Const}
    (hor : Provable (Const := Const) T (.or φ ψ))
    (hnφ : Provable (Const := Const) T (.not φ)) :
    Provable (Const := Const) T ψ := by
  rcases hor with ⟨Γ₁, hΓ₁, dor⟩
  rcases hnφ with ⟨Γ₂, hΓ₂, dnφ⟩
  refine ⟨Γ₁ ++ Γ₂, ?_, ?_⟩
  · intro ξ hξ
    rcases List.mem_append.mp hξ with h | h
    · exact hΓ₁ ξ h
    · exact hΓ₂ ξ h
  · have dor' : ExtDerivation Const (Γ₁ ++ Γ₂) (.or φ ψ) :=
      ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inl hξ)) dor
    have dnφ' : ExtDerivation Const (Γ₁ ++ Γ₂) (.not φ) :=
      ExtDerivation.mono (by intro ξ hξ; exact List.mem_append.mpr (.inr hξ)) dnφ
    refine ExtDerivation.orE dor' ?_ ?_
    · apply ExtDerivation.botE
      exact ExtDerivation.notE
        (ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) dnφ')
        (ExtDerivation.hyp List.mem_cons_self)
    · exact ExtDerivation.hyp List.mem_cons_self

/-! ## Chain unions are consistent -/

/-- A finite list of formulas drawn from the union of a nonempty chain already lies
inside a single member of the chain. -/
theorem chain_finite_subset {c : Set (ClosedTheorySet Const)}
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty) :
    ∀ (Γ : List (ClosedFormula Const)), (∀ ψ ∈ Γ, ψ ∈ ⋃₀ c) →
      ∃ T ∈ c, ∀ ψ ∈ Γ, ψ ∈ T
  | [], _ => by
      obtain ⟨T, hT⟩ := hne
      exact ⟨T, hT, by intro ψ hψ; cases hψ⟩
  | a :: Γ, hΓ => by
      obtain ⟨T, hTc, hT⟩ :=
        chain_finite_subset hc hne Γ (fun ψ hψ => hΓ ψ (List.mem_cons_of_mem _ hψ))
      obtain ⟨Ta, hTac, haTa⟩ := Set.mem_sUnion.mp (hΓ a List.mem_cons_self)
      rcases eq_or_ne T Ta with rfl | hne'
      · exact ⟨T, hTc, fun ψ hψ => by
          rcases List.mem_cons.mp hψ with rfl | h
          · exact haTa
          · exact hT ψ h⟩
      · rcases hc hTc hTac hne' with hle | hle
        · exact ⟨Ta, hTac, fun ψ hψ => by
            rcases List.mem_cons.mp hψ with rfl | h
            · exact haTa
            · exact hle (hT ψ h)⟩
        · exact ⟨T, hTc, fun ψ hψ => by
            rcases List.mem_cons.mp hψ with rfl | h
            · exact hle haTa
            · exact hT ψ h⟩

theorem sUnion_consistent {c : Set (ClosedTheorySet Const)}
    (hc : IsChain (· ⊆ ·) c) (hne : c.Nonempty)
    (hcons : ∀ T ∈ c, Consistent (Const := Const) T) :
    Consistent (Const := Const) (⋃₀ c) := by
  intro hbot
  rcases hbot with ⟨Γ, hΓ, d⟩
  obtain ⟨T, hTc, hT⟩ := chain_finite_subset hc hne Γ hΓ
  exact hcons T hTc ⟨Γ, hT, d⟩

/-! ## Existence of a maximal consistent extension and its properties -/

/-- **Lindenbaum.**  Every consistent theory extends to a maximal consistent one. -/
theorem exists_maximal_consistent_extension {H : ClosedTheorySet Const}
    (hH : Consistent (Const := Const) H) :
    ∃ M : ClosedTheorySet Const, H ⊆ M ∧ Consistent (Const := Const) M ∧
      (∀ a : ClosedTheorySet Const, Consistent (Const := Const) a → M ⊆ a → a ⊆ M) := by
  obtain ⟨M, hHM, hMax⟩ :=
    zorn_subset_nonempty {T' | Consistent (Const := Const) T'}
      (fun c hcS hchain hne =>
        ⟨⋃₀ c, sUnion_consistent hchain hne (fun T hT => hcS hT),
          fun s hs => Set.subset_sUnion_of_mem hs⟩)
      H hH
  exact ⟨M, hHM, hMax.1, fun a ha hMa => hMax.2 ha hMa⟩

variable {M : ClosedTheorySet Const}

/-- A maximal consistent theory is deductively closed. -/
theorem maximal_deductivelyClosed (hM : Consistent (Const := Const) M)
    (hmax : ∀ a : ClosedTheorySet Const, Consistent (Const := Const) a → M ⊆ a → a ⊆ M) :
    DeductivelyClosed (Const := Const) M := by
  intro φ hφ
  by_contra hφM
  have hIncon : Inconsistent (Const := Const) (insert φ M) := by
    by_contra hc
    have hsub : insert φ M ⊆ M := hmax _ hc (Set.subset_insert _ _)
    exact hφM (hsub (Set.mem_insert _ _))
  exact hM (provable_mp (provable_imp_of_insert hIncon) hφ)

/-- A maximal consistent theory is complete. -/
theorem maximal_complete
    (hmax : ∀ a : ClosedTheorySet Const, Consistent (Const := Const) a → M ⊆ a → a ⊆ M)
    (hClosed : DeductivelyClosed (Const := Const) M) (χ : ClosedFormula Const) :
    χ ∈ M ∨ (.not χ : ClosedFormula Const) ∈ M := by
  by_cases hc : Consistent (Const := Const) (insert χ M)
  · left
    exact (hmax _ hc (Set.subset_insert _ _)) (Set.mem_insert _ _)
  · right
    have hIncon : Inconsistent (Const := Const) (insert χ M) := not_not.mp hc
    exact hClosed (provable_not_of_imp_bot (provable_imp_of_insert hIncon))

/-- **Henkin co-witnessing (single step).**  Dual to `consistent_addWitness`: for a
fresh parameter `c`, adjoining the counterexample `¬φ[c]` preserves consistency
whenever `∀x. ¬¬φ` is underivable.  Intuitionistically valid — a refutation would,
by fresh generalization, derive exactly the underivable `∀x. ¬¬φ`.  This is the
dual saturation step that makes failed universals witnessed. -/
theorem consistent_addCounterexample {T : ClosedTheorySet Const}
    {σ : Ty Base} {φ : Formula Const [σ]} (c : Const σ)
    (hT : ∀ ψ ∈ T, NoConstOccurrence c ψ)
    (hφ : NoConstOccurrence c φ)
    (hUnderiv : ¬ Provable (Const := Const) T (.all (.not (.not φ)))) :
    Consistent (Const := Const)
      (insert (.not (instantiate (Base := Base) (.const c) φ)) T) := by
  intro hbot
  apply hUnderiv
  have h1 : Provable (Const := Const) T
      (Term.imp (.not (instantiate (Base := Base) (.const c) φ)) .bot) :=
    provable_imp_of_insert hbot
  have h2 : Provable (Const := Const) T
      (.not (.not (instantiate (Base := Base) (.const c) φ))) :=
    provable_not_of_imp_bot h1
  exact ClosedTheorySet.provable_all_intro_fresh c hT
    (NoConstOccurrence.not (NoConstOccurrence.not hφ)) h2

/-- **Classical ∀ from EM + double negation.**  From the constant-free universal
excluded middle `∀x.(φ∨¬φ)` and `∀x.¬¬φ`, one derives `∀x.φ` — the key classical
move, realized by fresh generalization (`allI_fresh`) at a parameter `c` absent
from `φ` (hence from both hypotheses, which are universally quantified). -/
theorem emdne_all {σ : Ty Base} (φ : Formula Const [σ]) (c : Const σ)
    (hc : NoConstOccurrence c φ) :
    ExtDerivation Const
      [(.all (.or φ (.not φ)) : ClosedFormula Const), .all (.not (.not φ))]
      (.all φ) := by
  apply ExtDerivation.allI_fresh c
  · intro ψ hψ
    rcases List.mem_cons.mp hψ with rfl | hψ'
    · exact NoConstOccurrence.all (NoConstOccurrence.or hc (NoConstOccurrence.not hc))
    · rcases List.mem_cons.mp hψ' with rfl | hψ''
      · exact NoConstOccurrence.all (NoConstOccurrence.not (NoConstOccurrence.not hc))
      · cases hψ''
  · exact hc
  · have hEM : ExtDerivation Const
        [(.all (.or φ (.not φ)) : ClosedFormula Const), .all (.not (.not φ))]
        (.or (instantiate (Base := Base) (.const c) φ)
             (.not (instantiate (Base := Base) (.const c) φ))) :=
      ExtDerivation.allE (Base := Base) (.const c) (ExtDerivation.hyp List.mem_cons_self)
    have hDNE : ExtDerivation Const
        [(.all (.or φ (.not φ)) : ClosedFormula Const), .all (.not (.not φ))]
        (.not (.not (instantiate (Base := Base) (.const c) φ))) :=
      ExtDerivation.allE (Base := Base) (.const c)
        (ExtDerivation.hyp (φ := .all (.not (.not φ))) (List.mem_cons_of_mem _ List.mem_cons_self))
    refine ExtDerivation.orE hEM ?_ ?_
    · exact ExtDerivation.hyp List.mem_cons_self
    · apply ExtDerivation.botE
      exact ExtDerivation.notE
        (ExtDerivation.mono (by intro ξ hξ; exact List.mem_cons_of_mem _ hξ) hDNE)
        (ExtDerivation.hyp List.mem_cons_self)

/-- A complete deductively-closed theory is prime. -/
theorem maximal_prime_or (hClosed : DeductivelyClosed (Const := Const) M)
    (hComplete : ∀ χ : ClosedFormula Const, χ ∈ M ∨ (.not χ : ClosedFormula Const) ∈ M)
    {φ ψ : ClosedFormula Const} (h : (.or φ ψ : ClosedFormula Const) ∈ M) :
    φ ∈ M ∨ ψ ∈ M := by
  rcases hComplete φ with hφ | hnφ
  · exact Or.inl hφ
  · exact Or.inr (hClosed (provable_or_elim_left (provable_of_mem h) (provable_of_mem hnφ)))

end Mettapedia.Logic.HOL
