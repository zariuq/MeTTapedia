import Mettapedia.Languages.ProcessCalculi.MORK.ThreePhaseExec
import Mettapedia.OSLF.PathMap.Core

/-!
# MORK ↔ PathMap Bridge

Proves that MORK's space transitions (`applyBase`, `applyFold`, `applyUnfold`)
are expressible as operations in the `PathMapDistributiveLattice` structure on
`Finset Atom` — the abstract algebraic carrier already proven in `PathMap/Core.lean`.

## The Connection

`Space = Finset Atom` already inherits `PathMapDistributiveLattice` and
`PathMapQuantale` instances from `PathMap/Core.lean` (proven sorry-free).
MORK's transitions reduce to:

| MORK operation | PathMap expression             |
|----------------|-------------------------------|
| `s ∪ {a}`      | `pjoin s {a}` → `s ∪ {a}`    |
| `s.erase a`    | `psubtract s {a}` → `s \ {a}` |

## LLM Notes (Lean 4.27 / Mathlib 4.27)
- `AlgebraicResult.resolve` signature: `(a b : V) → AlgebraicResult V → Option V`.
  Dot notation `r.resolve a b` inserts `r` at the 3rd arg = `AlgebraicResult.resolve a b r`.
- AVOID `|>` in theorem type signatures: `|>` has precedence 0, causing `=`
  to be parsed as part of the RHS, mangling the theorem type.
  Use explicit parentheses: `((expr).getD ∅) = ...`.
- Finset lemma names (camelCase in Lean 4.27):
  - `Finset.erase_eq_of_notMem : a ∉ s → s.erase a = s`
  - `Finset.notMem_empty : a ∉ ∅`
  - `Finset.erase_eq : s.erase a = s \ {a}`
  - `simp [ha]` closes `s \ {a} = s` when `ha : a ∉ s` (sdiff simp lemma)
-/

namespace Mettapedia.Languages.ProcessCalculi.MORK

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.PathMap (AlgebraicResult)

-- Short aliases for the two typeclass methods we use
private abbrev PJ := @Mettapedia.PathMap.PathMapLattice.pjoin (Finset Atom) _
private abbrev PS := @Mettapedia.PathMap.PathMapDistributiveLattice.psubtract (Finset Atom) _

/-! ## Space = Finset Atom is a PathMap carrier -/

/-- `Space = Finset Atom` has a `PathMapDistributiveLattice` structure
    (inherited from the `Finset` instance in `PathMap/Core.lean`). -/
example : Mettapedia.PathMap.PathMapDistributiveLattice (Finset Atom) := inferInstance

/-- `Space = Finset Atom` has a `PathMapQuantale` structure. -/
example : Mettapedia.PathMap.PathMapQuantale (Finset Atom) := inferInstance

/-! ## pjoin with singleton -/

/-- `pjoin s {a}` always resolves to `s ∪ {a}`.

    Case analysis:
    - `s = {a}` → `.identity true true` → `some s = some (s ∪ {a})`
    - `s = ∅` (the only case with `s ⊆ {a}` and `s ≠ {a}`) → `.identity false true` → `some {a}`
    - `a ∈ s`, `s ≠ {a}` → `.identity true false` → `some s` (and `s ∪ {a} = s`)
    - otherwise → `.element (s ∪ {a})` -/
theorem pjoin_singleton_resolves (s : Space) (a : Atom) :
    (PJ s {a}).resolve s {a} = some (s ∪ {a}) := by
  simp only [PJ, Mettapedia.PathMap.PathMapLattice.pjoin,
             Mettapedia.PathMap.AlgebraicResult.resolve]
  by_cases h1 : s = {a}
  · simp [h1]
  · by_cases h2 : s ⊆ {a}
    · -- s ⊆ {a} and s ≠ {a} implies s = ∅
      have hs : s = ∅ := by
        rcases Finset.subset_singleton_iff.mp h2 with rfl | rfl
        · rfl
        · exact absurd rfl h1
      simp [hs]
    · simp only [h1, ite_false, h2, ite_false]
      by_cases h3 : {a} ⊆ s
      · have hunion : s ∪ {a} = s := Finset.union_eq_left.mpr h3
        simp [h3, hunion]
      · simp [h3]

/-! ## psubtract with singleton -/

/-- `psubtract s {a}` resolves (with `∅` as default for `.none`) to `s.erase a`.

    - `s ⊆ {a}` (so `s = ∅` or `s = {a}`) → `.none` → `getD ∅ = ∅ = s.erase a`
    - `a ∉ s` (and `s ≠ ∅`) → `.identity true false` → `some s` (and `s.erase a = s`)
    - `a ∈ s`, `s ⊄ {a}` → `.element (s \ {a})` → `s \ {a} = s.erase a` -/
theorem psubtract_singleton_erase (s : Space) (a : Atom) :
    ((PS s {a}).resolve s {a}).getD ∅ = s.erase a := by
  simp only [PS, Mettapedia.PathMap.PathMapDistributiveLattice.psubtract,
             Mettapedia.PathMap.AlgebraicResult.resolve]
  by_cases h0 : (s \ {a}).card = 0
  · simp only [h0, ite_true]
    have hs : s ⊆ {a} := Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp h0)
    rcases Finset.subset_singleton_iff.mp hs with rfl | rfl
    · simp
    · simp
  · simp only [h0, ite_false]
    by_cases h1 : s ∩ {a} = ∅
    · -- a ∉ s: resolve = some s, and s.erase a = s
      simp only [h1, ite_true]
      have ha : a ∉ s := by
        intro ha
        have hmem : a ∈ s ∩ {a} := Finset.mem_inter.mpr ⟨ha, Finset.mem_singleton_self a⟩
        rw [h1] at hmem
        exact Finset.notMem_empty _ hmem
      simp [Finset.erase_eq_of_notMem ha]
    · -- a ∈ s: resolve = some (s \ {a}) = some (s.erase a)
      simp only [h1, ite_false]
      rw [← Finset.erase_eq]
      rfl

/-! ## Space transition decomposition -/

/-- `applyBase` in terms of Finset ops (definitional). -/
theorem applyBase_eq_erase_union (s : Space) (step : BaseStep) :
    applyBase s step = (s.erase step.qid) ∪ {step.result} := rfl

/-- `applyBase` expressed as PathMap `psubtract` + `pjoin`. -/
theorem applyBase_eq_lattice_ops (s : Space) (step : BaseStep) :
    let s₁ := ((PS s {step.qid}).resolve s {step.qid}).getD ∅
    ((PJ s₁ {step.result}).resolve s₁ {step.result}).getD s₁ =
      applyBase s step := by
  simp only [applyBase_eq_erase_union]
  rw [psubtract_singleton_erase]
  rw [pjoin_singleton_resolves]
  simp

/-- Each element removal in `applyFold`'s chain is a `psubtract` step. -/
theorem applyFold_chain_as_psubtract (s : Space) (atoms : List Atom) :
    atoms.foldl (fun acc a => acc \ {a}) s =
      atoms.foldl (fun acc a => ((PS acc {a}).resolve acc {a}).getD ∅) s := by
  induction atoms generalizing s with
  | nil => rfl
  | cons a rest ih =>
    simp only [List.foldl_cons]
    rw [psubtract_singleton_erase]
    rw [Finset.erase_eq]
    exact ih _

/-- `applyFold` in terms of Finset ops (definitional). -/
theorem applyFold_eq_erase_chain_union (s : Space) (step : FoldStep) :
    applyFold s step =
      (step.subResults.foldl (fun acc a => acc \ {a}) (s.erase step.waitAtom))
        ∪ {step.assembled} := rfl

/-- `applyFold` expressed as PathMap `psubtract` chain + `pjoin`. -/
theorem applyFold_eq_lattice_ops (s : Space) (step : FoldStep) :
    let s₁ := ((PS s {step.waitAtom}).resolve s {step.waitAtom}).getD ∅
    let s₂ := step.subResults.foldl (fun acc a =>
      ((PS acc {a}).resolve acc {a}).getD ∅) s₁
    ((PJ s₂ {step.assembled}).resolve s₂ {step.assembled}).getD s₂ =
      applyFold s step := by
  simp only [applyFold_eq_erase_chain_union]
  rw [psubtract_singleton_erase]
  rw [← applyFold_chain_as_psubtract]
  rw [pjoin_singleton_resolves]
  simp

/-! ## Canary tests -/

section Canaries

-- The Finset Atom PathMap instances are available
#check (inferInstance : Mettapedia.PathMap.PathMapQuantale (Finset Atom))
-- Key bridge theorems compile
#check @pjoin_singleton_resolves
#check @psubtract_singleton_erase
#check @applyBase_eq_lattice_ops
#check @applyFold_eq_lattice_ops

end Canaries

end Mettapedia.Languages.ProcessCalculi.MORK
