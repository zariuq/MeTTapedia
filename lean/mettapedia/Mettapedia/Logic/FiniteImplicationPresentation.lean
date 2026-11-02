import Mettapedia.Logic.FiniteHornClosureCharacterization
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Card

/-! A finite explicit implication table presents every closure response on
a finite carrier. Rule premises are finite sets; execution still uses the
independently defined derivation trees. This construction claims existence,
not a small basis or an efficient way to discover unknown responses. -/

set_option autoImplicit false

namespace Mettapedia.Logic.FiniteHornClosureCharacterization

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def implicationTable (response : Set A → Set A) : Finset (Finset A × A) := by
  classical
  exact Finset.univ.filter fun entry => entry.2 ∈ response (entry.1 : Set A)

def checkedImplicationTable (response : Set A → Set A)
    [DecidablePred (fun entry : Finset A × A => entry.2 ∈ response (entry.1 : Set A))] :
    Finset (Finset A × A) :=
  Finset.univ.filter fun entry => entry.2 ∈ response (entry.1 : Set A)

omit [DecidableEq A] in
theorem checkedImplicationTable_eq (response : Set A → Set A)
    [DecidablePred (fun entry : Finset A × A => entry.2 ∈ response (entry.1 : Set A))] :
    checkedImplicationTable response = implicationTable response := by
  classical
  ext entry
  simp [checkedImplicationTable, implicationTable]

omit [DecidableEq A] in
theorem implicationTable_size_bound (response : Set A → Set A) :
    (implicationTable response).card ≤ 2 ^ Fintype.card A * Fintype.card A := by
  classical
  have bounded := Finset.card_filter_le (Finset.univ : Finset (Finset A × A))
    (fun entry => entry.2 ∈ response (entry.1 : Set A))
  simpa [implicationTable, Fintype.card_prod] using bounded

def tableRules (table : Finset (Finset A × A)) (premises : List A) (atom : A) : Prop :=
  (premises.toFinset, atom) ∈ table

theorem tableRules_exact (response : Set A → Set A) (premises : List A) (atom : A) :
    tableRules (implicationTable response) premises atom ↔ rulesOf response premises atom := by
  classical
  simp [tableRules, implicationTable, rulesOf]

theorem implicationTable_realizes (response : Set A → Set A) (laws : ClosureLaws response)
    (seed : Set A) (atom : A) :
    FinitaryClosure.close (tableRules (implicationTable response)) (· ∈ seed) atom ↔ atom ∈ response seed := by
  have rulesEqual : tableRules (implicationTable response) = rulesOf response := by
    funext premises conclusion
    exact propext (tableRules_exact response premises conclusion)
  rw [rulesEqual]
  exact Set.ext_iff.mp (close_rulesOf_eq response laws (finite_support response) seed) atom

theorem finite_table_characterization (response : Set A → Set A) :
    ClosureLaws response ↔ ∃ table : Finset (Finset A × A), ∀ seed atom,
      atom ∈ response seed ↔ FinitaryClosure.close (tableRules table) (· ∈ seed) atom := by
  constructor
  · intro laws
    exact ⟨implicationTable response, fun seed atom => (implicationTable_realizes response laws seed atom).symm⟩
  · rintro ⟨table, realization⟩
    exact (finite_horn_characterization response).mpr ⟨tableRules table, realization⟩

end Mettapedia.Logic.FiniteHornClosureCharacterization
