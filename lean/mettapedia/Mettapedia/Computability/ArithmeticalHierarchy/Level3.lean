import Mathlib.Computability.Partrec
import Mettapedia.Computability.ArithmeticalHierarchy.Basic

/-!
# Arithmetical Hierarchy Level 3 (Σ⁰₃, Π⁰₃, Δ⁰₃)

Extension to level 3 of the arithmetical hierarchy for computability of Choquet value functions.

## Main Definitions

* `Sigma03Predicate P`: Predicate P is Σ⁰₃ (∃m ∀k ∃j, approx(n,m,k,j) = true)
* `Pi03Predicate P`: Predicate P is Π⁰₃ (∀m ∃k ∀j, approx(n,m,k,j) = true)  
* `Delta03Predicate P`: Predicate P is Δ⁰₃ (both Σ⁰₃ and Π⁰₃)

## References

- Hutter (2024). "Universal Artificial Intelligence", Chapter 6, Definition 6.2
- Wyeth & Hutter (2025). "Value Under Ignorance", Section 5 (Δ⁰₃-computability)
-/

namespace Mettapedia.Computability.ArithmeticalHierarchy

open Classical

/-! ## Σ⁰₃ Predicates -/

/-- A Σ⁰₃ predicate: P(n) ↔ ∃m ∀k ∃j, approx(n,m,k,j) = true

    Three quantifier alternations: ∃∀∃
-/
structure Sigma03Predicate (P : ℕ → Prop) where
  /-- Computable approximation with 3 parameters -/
  approx : ℕ → ℕ → ℕ → ℕ → Bool
  /-- Approximation is computable -/
  approx_computable : Computable (fun ((n, m), k, j) => approx n m k j)
  /-- Characterization with ∃∀∃ quantifiers -/
  converges : ∀ n, P n ↔ ∃ m, ∀ k, ∃ j, approx n m k j = true

namespace Sigma03Predicate

variable {P : ℕ → Prop}

theorem mem_iff_exists_forall_exists (h : Sigma03Predicate P) (n : ℕ) :
    P n ↔ ∃ m, ∀ k, ∃ j, h.approx n m k j = true :=
  h.converges n

end Sigma03Predicate

/-! ## Π⁰₃ Predicates -/

/-- A Π⁰₃ predicate: P(n) ↔ ∀m ∃k ∀j, approx(n,m,k,j) = true

    Three quantifier alternations: ∀∃∀
-/
structure Pi03Predicate (P : ℕ → Prop) where
  approx : ℕ → ℕ → ℕ → ℕ → Bool
  approx_computable : Computable (fun ((n, m), k, j) => approx n m k j)
  converges : ∀ n, P n ↔ ∀ m, ∃ k, ∀ j, approx n m k j = true

namespace Pi03Predicate

variable {P : ℕ → Prop}

theorem mem_iff_forall_exists_forall (h : Pi03Predicate P) (n : ℕ) :
    P n ↔ ∀ m, ∃ k, ∀ j, h.approx n m k j = true :=
  h.converges n

end Pi03Predicate

/-! ## Δ⁰₃ Predicates -/

/-- A Δ⁰₃ predicate: both Σ⁰₃ and Π⁰₃ -/
structure Delta03Predicate (P : ℕ → Prop) where
  sigma : Sigma03Predicate P
  pi : Pi03Predicate P

namespace Delta03Predicate

variable {P : ℕ → Prop}

theorem mem_iff_sigma (h : Delta03Predicate P) (n : ℕ) :
    P n ↔ ∃ m, ∀ k, ∃ j, h.sigma.approx n m k j = true :=
  h.sigma.converges n

theorem mem_iff_pi (h : Delta03Predicate P) (n : ℕ) :
    P n ↔ ∀ m, ∃ k, ∀ j, h.pi.approx n m k j = true :=
  h.pi.converges n

end Delta03Predicate

/-! ## Complement Relationships -/

/-- Complement of Σ⁰₃ is Π⁰₃ -/
def sigma03_complement_pi03 {P : ℕ → Prop} (h : Sigma03Predicate P) :
    Pi03Predicate (fun n => ¬P n) := {
  approx := fun n m k j => !h.approx n m k j
  approx_computable := by
    exact bool_not_computable.comp h.approx_computable
  converges := fun n => by
    simp [h.converges n]
}

/-- Complement of Π⁰₃ is Σ⁰₃ -/
def pi03_complement_sigma03 {P : ℕ → Prop} (h : Pi03Predicate P) :
    Sigma03Predicate (fun n => ¬P n) := {
  approx := fun n m k j => !h.approx n m k j
  approx_computable := by
    exact bool_not_computable.comp h.approx_computable
  converges := fun n => by
    simp [h.converges n]
}

end Mettapedia.Computability.ArithmeticalHierarchy
