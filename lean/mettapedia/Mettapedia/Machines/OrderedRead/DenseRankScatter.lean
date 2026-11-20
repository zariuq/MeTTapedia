import Mettapedia.Machines.OrderedRead.ComparisonLowerBound

/-!
# Dense supplied ranks permit noncomparison ordered delivery

In the direct-addressing model a slot read or write costs one unit. Each
occurrence supplies its distinct rank in a dense finite interval. Scatter
writes the occurrence position to that rank's slot; reading slots in order
returns the inverse permutation. The operation count is linear, including
initializing the slots. No pairwise comparison discovers the order.

This does not assume that sparse native ranks fit a small array. It records
why a comparison-only lower bound cannot forbid all ordered access paths.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.OrderedRead.DenseRankScatter

open ComparisonLowerBound (Input)

def scatter {number : Nat} (ranks : Input number) :
    List (Fin number) → (Fin number → Option (Fin number)) × Nat
  | [] => (fun _ => none, 0)
  | position :: rest =>
      let stored := scatter ranks rest
      (Function.update stored.1 (ranks position) (some position), stored.2 + 1)

theorem scatter_writes {number : Nat} (ranks : Input number) (positions : List (Fin number)) :
    (scatter ranks positions).2 = positions.length := by
  induction positions with
  | nil => rfl
  | cons position rest ih => simp [scatter, ih]

theorem scatter_retains_occurrence {number : Nat} (ranks : Input number)
    (positions : List (Fin number)) (position : Fin number) (present : position ∈ positions) :
    (scatter ranks positions).1 (ranks position) = some position := by
  induction positions with
  | nil => contradiction
  | cons first rest ih =>
      by_cases same : position = first
      · subst position
        simp [scatter]
      · have other : ranks position ≠ ranks first := fun equal => same (ranks.injective equal)
        have later : position ∈ rest := (List.mem_cons.mp present).resolve_left same
        simpa [scatter, Function.update_of_ne other] using ih later

def deliver {number : Nat} (ranks : Input number) : List (Option (Fin number)) :=
  List.ofFn fun rank => (scatter ranks (List.finRange number)).1 rank

theorem dense_rank_delivery_exact {number : Nat} (ranks : Input number) :
    deliver ranks = List.ofFn (fun rank => some (ranks.symm rank)) := by
  apply congrArg List.ofFn
  funext rank
  have position := scatter_retains_occurrence ranks (List.finRange number) (ranks.symm rank) (by simp)
  simpa using position

/-- Initialization, reading each supplied rank, scattering it, and reading the
output slots. This is a direct-addressing tariff, not a native benchmark. -/
def chargedWork {number : Nat} (ranks : Input number) : Nat :=
  number + (List.finRange number).length + (scatter ranks (List.finRange number)).2 + number

theorem direct_addressing_work_is_linear {number : Nat} (ranks : Input number) :
    chargedWork ranks = 4 * number := by
  simp [chargedWork, scatter_writes]
  omega

theorem every_dense_rank_problem_has_an_execution (number : Nat) :
    ∀ ranks : Input number,
      ∃ output, output = deliver ranks ∧
        output = List.ofFn (fun rank => some (ranks.symm rank)) ∧ chargedWork ranks = 4 * number := by
  intro ranks
  exact ⟨deliver ranks, rfl, dense_rank_delivery_exact ranks, direct_addressing_work_is_linear ranks⟩

end Mettapedia.Machines.OrderedRead.DenseRankScatter
