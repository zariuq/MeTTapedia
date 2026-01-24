import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.GlobalizationInterface
import Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core

namespace Mettapedia.ProbabilityTheory.KnuthSkilling.Additive

open Classical

/-!
# K&S Representation Theorem: Globalization (constructing the global `Θ`)

This file contains the globalization construction packaged as `RepresentationGlobalization`,
together with the main instance `representationGlobalization_of_KSSeparationStrict`.

The short "public API" theorems (representation theorem statement + convenience wrappers) live in:
`Mettapedia/ProbabilityTheory/KnuthSkilling/Additive/Proofs/GridInduction/Main.lean`.

## Main Results

1. **`RepresentationGlobalization`**: Class packaging the existence of Θ : α → ℝ
2. **`representationGlobalization_of_KSSeparationStrict`**: Instance construction
3. **`representationGlobalization_of_KSSeparation_of_denselyOrdered`**: Convenience instance (density ⇒ strict separation)

## Proof Architecture

### Induction Machinery (from `Core/`)
- `extend_grid_rep_with_atom_of_KSSeparationStrict`: B-empty extension step
- `newAtomCommutes_of_KSSeparation`: Global commutativity → NewAtomCommutes
- `bEmptyExtensionExtra_of_KSSeparationStrict`: Full hypothesis bundle auto-construction

### Globalization ("Triple Family Trick")
For any x ≠ ident:
1. Choose reference atom `a` with `ident < a`
2. Build 2-atom family F₂ = {a, x} with MultiGridRep R₂
3. Define Θ(x) := R₂.Θ_grid ⟨x, mem_proof⟩

**Well-definedness**: Use 3-atom families to show independence of reference atom.
**Order preservation**: Build 3-atom family {ref, a, b}, use R.strictMono.
**Additivity**: Build 3-atom family {ref, x, y}, use path independence via `DeltaSpec_unique`.

## References

- Knuth & Skilling, "Foundations of Inference" Appendix A
- Goertzel, "Foundations of Inference: New Proofs" (2026 note)

## Identity-Optional Architecture (Future Work)

The current implementation uses identity (`ident`) extensively for:
1. Reference atom selection: `ident < a`
2. Positivity tests: `x > ident`
3. Normalization: `Θ ident = 0`
4. Grid membership: `ident_mem_kGrid`

**Future refactoring** could use the parametric infrastructure from `MultiGrid.lean`:
- `AtomFamily_param` with `IsPositive (atoms i)` instead of `ident < atoms i`
- `mu_param` with explicit base element instead of `ident`
- `kGrid_param` using `mu_param`

This would enable representation theorems for ordered semigroups without identity,
normalizing to an arbitrary "anchor element" instead of `ident`.

See `MultiGrid.lean` section "Identity-Free Grid Definitions" for the parametric API.
-/

section WithIdentity

open KnuthSkillingAlgebraBase
open KnuthSkillingAlgebra

/-!
### Separation-driven Globalization Instance

The globalization is fully proven using the "triple family trick":
- For any `x > ident`, pick reference `a > ident` and extend {a} → {a,x}
- Define Θ(x) from the extended grid representation
- Well-definedness: 3-atom families {a₁,a₂,x} show independence of reference choice
- Path independence (`DeltaSpec_unique`) establishes additivity
-/

variable {α : Type*} [KnuthSkillingAlgebraBase α] [KSSeparation α]

/-- GridComm holds for any family when we have global commutativity from KSSeparation. -/
lemma gridComm_of_KSSeparation (F : AtomFamily α k) : GridComm F := ⟨by
  intro r s
  have hcomm :=
    Mettapedia.ProbabilityTheory.KnuthSkilling.Additive.Proofs.GridInduction.Core.separationImpliesCommutative_of_KSSeparation
      (α := α)
  exact hcomm (mu F r) (mu F s)⟩

/-- GridBridge follows from GridComm. -/
lemma gridBridge_of_KSSeparation (F : AtomFamily α k) (_hk : k ≥ 1) : GridBridge F :=
  gridBridge_of_gridComm (gridComm_of_KSSeparation F)

/-- **Globalization Instance**: With `[KSSeparationStrict α]`, the globalization holds.

**Proof**: Uses the triple family trick:
1. For any `x > ident`, pick reference `a > ident` and extend {a} → {a,x}
2. Define Θ(x) := chooseδ for x in the 2-atom grid
3. Well-definedness: 3-atom families {a,x,y} show path independence via `DeltaSpec_unique`
4. Order preservation: `MultiGridRep.strictMono` on containing grids
5. Additivity: Path independence across extension orderings -/
instance representationGlobalization_of_KSSeparationStrict [KSSeparationStrict α] :
    RepresentationGlobalization α where
  exists_Theta := by
    classical
    -- Handle trivial algebra case
    by_cases htriv : ∀ x : α, x = ident
    · -- Trivial: Θ = 0
      refine ⟨fun _ => 0, ?_, rfl, fun _ _ => ?_⟩
      · intro a b; simp [htriv a, htriv b]
      · simp
    · -- Non-trivial: use triple family trick
      push_neg at htriv
      -- Get a reference atom a₀ > ident
      obtain ⟨a₀, ha₀_ne⟩ := htriv
      have ha₀ : ident < a₀ := lt_of_le_of_ne (ident_le a₀) (Ne.symm ha₀_ne)
      -- Build base representation
      let R₁ := oneTypeRep a₀ ha₀
      let F₁ := singletonAtomFamily a₀ ha₀
      let R₁_multi := R₁.toMulti a₀ ha₀
      have h₁ : (1 : ℕ) ≥ 1 := le_refl 1
      have H₁ : GridComm F₁ := gridComm_of_k_eq_one
      have IH₁ : GridBridge F₁ := gridBridge_of_k_eq_one

      -- ═══════════════════════════════════════════════════════════════════════════
      -- EXTENSION MACHINERY (builds 2-atom families for any element)
      -- ═══════════════════════════════════════════════════════════════════════════

      -- Build 2-atom extension: F₁ = {a₀} → F₂ = {a₀, x}
      have h_ext2 : ∀ (x : α) (hx : ident < x),
          ∃ (F₂ : AtomFamily α 2) (R₂ : MultiGridRep F₂),
            F₂.atoms ⟨0, by decide⟩ = a₀ ∧
            F₂.atoms ⟨1, by decide⟩ = x ∧
            (∀ r_old : Multi 1, ∀ t : ℕ,
              R₂.Θ_grid ⟨mu F₂ (joinMulti r_old t), mu_mem_kGrid F₂ (joinMulti r_old t)⟩ =
              R₁_multi.Θ_grid ⟨mu F₁ r_old, mu_mem_kGrid F₁ r_old⟩ + (t : ℝ) * chooseδ h₁ R₁_multi x hx) := by
        intro x hx
        have h_ext := extend_grid_rep_with_atom_of_KSSeparationStrict
          (α := α) (hk := h₁) (R := R₁_multi) (F := F₁) (d := x) (hd := hx) (IH := IH₁) (H := H₁)
        obtain ⟨F₂, hF₂_old, hF₂_new, R₂_exists⟩ := h_ext
        obtain ⟨R₂, hR₂_extends⟩ := R₂_exists
        refine ⟨F₂, R₂, ?_, ?_, ?_⟩
        · have h0 := hF₂_old ⟨0, by decide⟩
          simp only [F₁, singletonAtomFamily] at h0 ⊢
          exact h0
        · exact hF₂_new
        · exact hR₂_extends

      -- Helper: x is on the grid of {a₀, x} via unitMulti
      have h_x_on_grid2 : ∀ (F₂ : AtomFamily α 2) (x : α),
          F₂.atoms ⟨1, by decide⟩ = x → x ∈ kGrid F₂ := by
        intro F₂ x hF₂x
        use unitMulti ⟨1, by decide⟩ 1
        rw [mu_unitMulti, hF₂x, iterate_op_one]

      -- Extract representation via Classical.choose
      let getF₂ (x : α) (hx : ident < x) : AtomFamily α 2 :=
        Classical.choose (h_ext2 x hx)
      let getR₂ (x : α) (hx : ident < x) : MultiGridRep (getF₂ x hx) :=
        Classical.choose (Classical.choose_spec (h_ext2 x hx))
      have getF₂_spec (x : α) (hx : ident < x) :
          (getF₂ x hx).atoms ⟨0, by decide⟩ = a₀ ∧
          (getF₂ x hx).atoms ⟨1, by decide⟩ = x := by
        have h := Classical.choose_spec (Classical.choose_spec (h_ext2 x hx))
        exact ⟨h.1, h.2.1⟩
      have getR₂_extends_spec (x : α) (hx : ident < x) :
          ∀ r_old : Multi 1, ∀ t : ℕ,
            (getR₂ x hx).Θ_grid ⟨mu (getF₂ x hx) (joinMulti r_old t),
                                 mu_mem_kGrid (getF₂ x hx) (joinMulti r_old t)⟩ =
            R₁_multi.Θ_grid ⟨mu F₁ r_old, mu_mem_kGrid F₁ r_old⟩ +
              (t : ℝ) * chooseδ h₁ R₁_multi x hx := by
        have h := Classical.choose_spec (Classical.choose_spec (h_ext2 x hx))
        exact h.2.2

      -- ═══════════════════════════════════════════════════════════════════════════
      -- DEFINE GLOBAL Θ
      -- ═══════════════════════════════════════════════════════════════════════════

      let Θ : α → ℝ := fun x =>
        if hx_eq : x = ident then 0
        else
          have hx : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx_eq)
          let F₂ := getF₂ x hx
          let R₂ := getR₂ x hx
          have hF₂x : F₂.atoms ⟨1, by decide⟩ = x := (getF₂_spec x hx).2
          let hx_mem : x ∈ kGrid F₂ := h_x_on_grid2 F₂ x hF₂x
          R₂.Θ_grid ⟨x, hx_mem⟩

      -- ═══════════════════════════════════════════════════════════════════════════
      -- KEY LEMMA: Θ(x) equals chooseδ
      -- ═══════════════════════════════════════════════════════════════════════════

      have hΘ_eq_chooseδ : ∀ (x : α) (hx : ident < x),
          Θ x = chooseδ h₁ R₁_multi x hx := by
        intro x hx
        simp only [Θ, dif_neg (ne_of_gt hx)]
        -- Use ext_value_eq_chooseδ for path independence
        have hF_old := (getF₂_spec x hx).1
        have hF_new := (getF₂_spec x hx).2
        have hR_extends : ∀ (r : Multi 1) (t : ℕ),
            (getR₂ x hx).Θ_grid ⟨mu (getF₂ x hx) (joinMulti r t), mu_mem_kGrid (getF₂ x hx) (joinMulti r t)⟩ =
            R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ + (t : ℝ) * chooseδ h₁ R₁_multi x hx :=
          getR₂_extends_spec x hx
        have hF_old' : ∀ i : Fin 1, (getF₂ x hx).atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F₁.atoms i := by
          intro i; fin_cases i
          simp only [F₁, singletonAtomFamily]
          exact hF_old
        have hF_new' : (getF₂ x hx).atoms ⟨1, Nat.lt_succ_self 1⟩ = x := hF_new
        -- By ext_value_eq_chooseδ, the new atom gets value chooseδ
        have h_ext_val := ext_value_eq_chooseδ h₁ R₁_multi IH₁ H₁ x hx (getR₂ x hx) hF_old' hF_new' hR_extends
        -- mu F' (unitMulti k 1) = d when F'.atoms k = d
        have h_mu_eq_x : mu (getF₂ x hx) (unitMulti ⟨1, Nat.lt_succ_self 1⟩ 1) = x := by
          rw [mu_unitMulti, hF_new', iterate_op_one]
        have h_mem : x ∈ kGrid (getF₂ x hx) := h_x_on_grid2 _ x hF_new
        -- Show the subtype equality
        have h_eq : (⟨x, h_mem⟩ : {y // y ∈ kGrid (getF₂ x hx)}) =
                    ⟨mu (getF₂ x hx) (unitMulti ⟨1, Nat.lt_succ_self 1⟩ 1), mu_mem_kGrid _ _⟩ := by
          simp only [h_mu_eq_x]
        rw [h_eq]
        exact h_ext_val

      -- ═══════════════════════════════════════════════════════════════════════════
      -- PROVE PROPERTIES
      -- ═══════════════════════════════════════════════════════════════════════════

      use Θ
      refine ⟨?order, ?ident_zero, ?additivity⟩

      -- Property 1: Θ(ident) = 0
      case ident_zero => simp only [Θ, dif_pos rfl]

      -- Property 2: Order preservation (x ≤ y ↔ Θ(x) ≤ Θ(y))
      -- Uses the 3-atom family trick: build {a₀, y, x} to compare Θ values
      case order =>
        intro x y
        constructor
        · -- Forward: x ≤ y → Θ(x) ≤ Θ(y)
          intro hxy
          by_cases hx_eq : x = ident
          · -- x = ident: Θ(x) = 0, need 0 ≤ Θ(y)
            have hΘx : Θ x = 0 := by simp only [Θ, hx_eq, dif_pos rfl]
            rw [hΘx]
            by_cases hy_eq : y = ident
            · have hΘy : Θ y = 0 := by simp only [Θ, hy_eq, dif_pos rfl]
              rw [hΘy]
            · -- y ≠ ident: Θ(y) > 0
              -- 0 ≤ Θ(y) because ident < y and R₂ is strictly monotone
              have hy_pos : ident < y := lt_of_le_of_ne (ident_le y) (Ne.symm hy_eq)
              let F₂ := getF₂ y hy_pos
              let R₂ := getR₂ y hy_pos
              have hF₂y : F₂.atoms ⟨1, by decide⟩ = y := (getF₂_spec y hy_pos).2
              have hy_mem : y ∈ kGrid F₂ := h_x_on_grid2 F₂ y hF₂y
              have h_ident_mem : ident ∈ kGrid F₂ := ident_mem_kGrid (F := F₂)
              have h0 : R₂.Θ_grid ⟨ident, h_ident_mem⟩ = 0 := R₂.ident_eq_zero
              have h1 : R₂.Θ_grid ⟨ident, h_ident_mem⟩ < R₂.Θ_grid ⟨y, hy_mem⟩ :=
                R₂.strictMono (show (⟨ident, h_ident_mem⟩ : {x // x ∈ kGrid F₂}) < ⟨y, hy_mem⟩ from hy_pos)
              -- Connect Θ y to R₂.Θ_grid value
              have hΘy_eq : Θ y = R₂.Θ_grid ⟨y, hy_mem⟩ := by
                simp only [Θ, dif_neg (ne_of_gt hy_pos)]
                rfl
              rw [hΘy_eq]
              linarith
          · by_cases hy_eq : y = ident
            · rw [hy_eq] at hxy
              have : x = ident := le_antisymm hxy (ident_le x)
              exact absurd this hx_eq
            · -- Both x ≠ ident and y ≠ ident
              have hx_pos : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx_eq)
              have hy_pos : ident < y := lt_of_le_of_ne (ident_le y) (Ne.symm hy_eq)
              by_cases hxy_lt : x < y
              · -- Strict case: x < y → Θ(x) < Θ(y) via 3-atom family trick
                apply le_of_lt
                -- Build F₃ = {a₀, y, x} by extending {a₀, y} with x
                let F₂_y := getF₂ y hy_pos
                let R₂_y := getR₂ y hy_pos
                have hF₂_y_1 : F₂_y.atoms ⟨1, by decide⟩ = y := (getF₂_spec y hy_pos).2
                have h₂ : 2 ≥ 1 := by omega
                have IH₂ : GridBridge F₂_y := gridBridge_of_KSSeparation F₂_y h₂
                have H₂ : GridComm F₂_y := gridComm_of_KSSeparation F₂_y
                -- Extend {a₀, y} with x
                have h_ext_x := extend_grid_rep_with_atom_of_KSSeparationStrict
                  (α := α) (hk := h₂) (R := R₂_y) (F := F₂_y) (d := x) (hd := hx_pos) (IH := IH₂) (H := H₂)
                obtain ⟨F₃, hF₃_old, hF₃_new, R₃_exists⟩ := h_ext_x
                obtain ⟨R₃, hR₃_extends⟩ := R₃_exists
                -- x and y are on F₃
                have hF₃_1 : F₃.atoms ⟨1, by omega⟩ = y := by
                  have h1 := hF₃_old ⟨1, by decide⟩
                  rw [h1, hF₂_y_1]
                have hF₃_2 : F₃.atoms ⟨2, by omega⟩ = x := hF₃_new
                have hy_mem₃ : y ∈ kGrid F₃ := by
                  use unitMulti ⟨1, by omega⟩ 1; rw [mu_unitMulti, hF₃_1, iterate_op_one]
                have hx_mem₃ : x ∈ kGrid F₃ := by
                  use unitMulti ⟨2, by omega⟩ 1; rw [mu_unitMulti, hF₃_2, iterate_op_one]
                have hy_mem₂ : y ∈ kGrid F₂_y := h_x_on_grid2 F₂_y y hF₂_y_1
                -- R₃.strictMono: x < y → R₃.Θ_grid(x) < R₃.Θ_grid(y)
                have h_strict : R₃.Θ_grid ⟨x, hx_mem₃⟩ < R₃.Θ_grid ⟨y, hy_mem₃⟩ :=
                  R₃.strictMono hxy_lt
                -- Show R₃.Θ_grid(y) = Θ(y) (y is on old grid, t=0 in extension formula)
                have hR₃_y : R₃.Θ_grid ⟨y, hy_mem₃⟩ = R₂_y.Θ_grid ⟨y, hy_mem₂⟩ := by
                  have hy_join : (unitMulti ⟨1, by omega⟩ 1 : Multi 3) =
                      joinMulti (unitMulti ⟨1, by decide⟩ 1 : Multi 2) 0 := by
                    funext i; by_cases hi : i.val < 2
                    · simp only [joinMulti, unitMulti, hi, dite_true]
                      by_cases hi1 : i.val = 1
                      · simp only [Fin.ext_iff, hi1]
                      · have hi0 : i.val = 0 := by omega
                        simp only [Fin.ext_iff, hi0]
                    · simp only [joinMulti, unitMulti]; have hi2 : i.val = 2 := by omega
                      simp only [hi2, Fin.ext_iff]; decide
                  have hext := hR₃_extends (unitMulti ⟨1, by decide⟩ 1) 0
                  simp only [Nat.cast_zero, zero_mul, add_zero] at hext
                  have hmu_y₃ : mu F₃ (joinMulti (unitMulti ⟨1, by decide⟩ 1) 0) = y := by
                    rw [← hy_join, mu_unitMulti, hF₃_1, iterate_op_one]
                  have hmu_y₂ : mu F₂_y (unitMulti ⟨1, by decide⟩ 1) = y := by
                    rw [mu_unitMulti, hF₂_y_1, iterate_op_one]
                  -- Use Subtype.val_injective pattern
                  have h_lhs : R₃.Θ_grid ⟨y, hy_mem₃⟩ = R₃.Θ_grid ⟨mu F₃ (joinMulti (unitMulti ⟨1, by decide⟩ 1) 0), mu_mem_kGrid F₃ _⟩ := by
                    congr 1; exact Subtype.ext hmu_y₃.symm
                  have h_rhs : R₂_y.Θ_grid ⟨y, hy_mem₂⟩ = R₂_y.Θ_grid ⟨mu F₂_y (unitMulti ⟨1, by decide⟩ 1), mu_mem_kGrid F₂_y _⟩ := by
                    congr 1; exact Subtype.ext hmu_y₂.symm
                  rw [h_lhs, h_rhs]; exact hext
                have hΘ_y_def : Θ y = R₂_y.Θ_grid ⟨y, hy_mem₂⟩ := by
                  simp only [Θ, dif_neg (ne_of_gt hy_pos)]; rfl
                -- Show Θ(x) ≤ R₃.Θ_grid(x) via δ-monotonicity
                have hΘ_x_le : Θ x ≤ R₃.Θ_grid ⟨x, hx_mem₃⟩ := by
                  rw [hΘ_eq_chooseδ x hx_pos]
                  -- R₃.Θ_grid(x) = chooseδ h₂ R₂_y x hx_pos
                  have hR₃_x_eq : R₃.Θ_grid ⟨x, hx_mem₃⟩ = chooseδ h₂ R₂_y x hx_pos := by
                    have hext := hR₃_extends (fun _ => 0) 1
                    simp only [mu_zero, R₂_y.ident_eq_zero, zero_add] at hext
                    -- mu F₃ (joinMulti 0 1) = F₃.atoms[2]^1 ⊕ (F₃.atoms[1]^0 ⊕ F₃.atoms[0]^0)
                    -- = x ⊕ ident ⊕ ident = x (using left fold)
                    have hmu_x : mu F₃ (joinMulti (fun _ => 0) 1) = x := by
                      -- Express mu using unitMulti
                      have hjoineq : (joinMulti (fun (_ : Fin 2) => 0) 1 : Multi 3) = unitMulti ⟨2, by omega⟩ 1 := by
                        funext i; simp only [joinMulti, unitMulti, Fin.ext_iff]
                        by_cases hi : i.val < 2
                        · simp only [hi, dite_true]
                          split_ifs with h <;> omega
                        · simp only [hi, dite_false]
                          split_ifs with h <;> omega
                      rw [hjoineq, mu_unitMulti, hF₃_2, iterate_op_one]
                    have h_eq_subtype : (⟨x, hx_mem₃⟩ : kGrid F₃) = ⟨mu F₃ (joinMulti (fun _ => 0) 1), mu_mem_kGrid F₃ _⟩ := by
                      exact Subtype.ext hmu_x.symm
                    simp only [Nat.cast_one, one_mul] at hext
                    rw [h_eq_subtype]; exact hext
                  rw [hR₃_x_eq]
                  -- Apply chooseδ_monotone_family
                  have hF₂y_old : ∀ i : Fin 1,
                      F₂_y.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F₁.atoms i := by
                    intro i; have h0 := (getF₂_spec y hy_pos).1
                    fin_cases i; simp [F₁, singletonAtomFamily] at h0 ⊢; exact h0
                  have hF₂y_new : F₂_y.atoms ⟨1, Nat.lt_succ_self 1⟩ = y := (getF₂_spec y hy_pos).2
                  have hR₂y_extends : ∀ r : Multi 1,
                      R₂_y.Θ_grid ⟨mu F₂_y (joinMulti r 0), mu_mem_kGrid F₂_y (joinMulti r 0)⟩ =
                      R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ := by
                    intro r; have h := getR₂_extends_spec y hy_pos r 0
                    simp only [Nat.cast_zero, zero_mul, add_zero] at h; exact h
                  exact chooseδ_monotone_family h₁ R₁_multi IH₁ H₁ y hy_pos R₂_y
                    hF₂y_old hF₂y_new hR₂y_extends h₂ IH₂ H₂ x hx_pos
                -- Chain: Θ(x) ≤ R₃.Θ(x) < R₃.Θ(y) = Θ(y)
                calc Θ x ≤ R₃.Θ_grid ⟨x, hx_mem₃⟩ := hΘ_x_le
                  _ < R₃.Θ_grid ⟨y, hy_mem₃⟩ := h_strict
                  _ = R₂_y.Θ_grid ⟨y, hy_mem₂⟩ := hR₃_y
                  _ = Θ y := hΘ_y_def.symm
              · -- x ≥ y, combined with x ≤ y gives x = y
                have hxy_eq : x = y := le_antisymm hxy (le_of_not_gt hxy_lt)
                simp only [hxy_eq]; exact le_refl _
        · -- Backward: Θ(x) ≤ Θ(y) → x ≤ y (contrapositive via symmetric argument)
          intro hΘxy
          by_cases hx_eq : x = ident
          · rw [hx_eq]; exact ident_le y
          · by_cases hy_eq : y = ident
            · simp only [Θ, hy_eq, dif_pos rfl, dif_neg hx_eq] at hΘxy
              have hx_pos : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx_eq)
              let F₂ := getF₂ x hx_pos
              let R₂ := getR₂ x hx_pos
              have hF₂x : F₂.atoms ⟨1, by decide⟩ = x := (getF₂_spec x hx_pos).2
              have hx_mem : x ∈ kGrid F₂ := h_x_on_grid2 F₂ x hF₂x
              have h_ident_mem : ident ∈ kGrid F₂ := ident_mem_kGrid (F := F₂)
              have h0 : R₂.Θ_grid ⟨ident, h_ident_mem⟩ = 0 := R₂.ident_eq_zero
              have h1 : R₂.Θ_grid ⟨ident, h_ident_mem⟩ < R₂.Θ_grid ⟨x, hx_mem⟩ :=
                R₂.strictMono (show (⟨ident, h_ident_mem⟩ : {x // x ∈ kGrid F₂}) < ⟨x, hx_mem⟩ from hx_pos)
              linarith
            · -- Both x ≠ ident and y ≠ ident: contrapositive
              have hx_pos : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx_eq)
              have hy_pos : ident < y := lt_of_le_of_ne (ident_le y) (Ne.symm hy_eq)
              by_contra h_not_le; push_neg at h_not_le
              -- h_not_le : y < x, but Θ(x) ≤ Θ(y)
              -- Build F₃ = {a₀, x, y} by extending {a₀, x} with y (mirror of forward)
              let F₂_x := getF₂ x hx_pos
              let R₂_x := getR₂ x hx_pos
              have hF₂_x_1 : F₂_x.atoms ⟨1, by decide⟩ = x := (getF₂_spec x hx_pos).2
              have h₂ : 2 ≥ 1 := by omega
              have IH₂ : GridBridge F₂_x := gridBridge_of_KSSeparation F₂_x h₂
              have H₂ : GridComm F₂_x := gridComm_of_KSSeparation F₂_x
              have h_ext_y := extend_grid_rep_with_atom_of_KSSeparationStrict
                (α := α) (hk := h₂) (R := R₂_x) (F := F₂_x) (d := y) (hd := hy_pos) (IH := IH₂) (H := H₂)
              obtain ⟨F₃, hF₃_old, hF₃_new, R₃_exists⟩ := h_ext_y
              obtain ⟨R₃, hR₃_extends⟩ := R₃_exists
              have hF₃_1 : F₃.atoms ⟨1, by omega⟩ = x := by
                have h1 := hF₃_old ⟨1, by decide⟩
                rw [h1, hF₂_x_1]
              have hF₃_2 : F₃.atoms ⟨2, by omega⟩ = y := hF₃_new
              have hx_mem₃ : x ∈ kGrid F₃ := by
                use unitMulti ⟨1, by omega⟩ 1; rw [mu_unitMulti, hF₃_1, iterate_op_one]
              have hy_mem₃ : y ∈ kGrid F₃ := by
                use unitMulti ⟨2, by omega⟩ 1; rw [mu_unitMulti, hF₃_2, iterate_op_one]
              have hx_mem₂ : x ∈ kGrid F₂_x := h_x_on_grid2 F₂_x x hF₂_x_1
              have h_strict : R₃.Θ_grid ⟨y, hy_mem₃⟩ < R₃.Θ_grid ⟨x, hx_mem₃⟩ := R₃.strictMono h_not_le
              -- R₃.Θ_grid(x) = Θ(x) (x on old grid)
              have hR₃_x : R₃.Θ_grid ⟨x, hx_mem₃⟩ = R₂_x.Θ_grid ⟨x, hx_mem₂⟩ := by
                have hx_join : (unitMulti ⟨1, by omega⟩ 1 : Multi 3) =
                    joinMulti (unitMulti ⟨1, by decide⟩ 1 : Multi 2) 0 := by
                  funext i; fin_cases i <;> simp [joinMulti, unitMulti]
                have hext := hR₃_extends (unitMulti ⟨1, by decide⟩ 1) 0
                simp only [Nat.cast_zero, zero_mul, add_zero] at hext
                have hmu_x₃ : mu F₃ (joinMulti (unitMulti ⟨1, by decide⟩ 1) 0) = x := by
                  rw [← hx_join, mu_unitMulti, hF₃_1, iterate_op_one]
                have hmu_x₂ : mu F₂_x (unitMulti ⟨1, by decide⟩ 1) = x := by
                  rw [mu_unitMulti, hF₂_x_1, iterate_op_one]
                -- Use Subtype.val_injective pattern like forward direction
                have h_lhs : R₃.Θ_grid ⟨x, hx_mem₃⟩ = R₃.Θ_grid ⟨mu F₃ (joinMulti (unitMulti ⟨1, by decide⟩ 1) 0), mu_mem_kGrid F₃ _⟩ := by
                  congr 1; exact Subtype.ext hmu_x₃.symm
                have h_rhs : R₂_x.Θ_grid ⟨x, hx_mem₂⟩ = R₂_x.Θ_grid ⟨mu F₂_x (unitMulti ⟨1, by decide⟩ 1), mu_mem_kGrid F₂_x _⟩ := by
                  congr 1; exact Subtype.ext hmu_x₂.symm
                rw [h_lhs, h_rhs]; exact hext
              have hΘ_x_def : Θ x = R₂_x.Θ_grid ⟨x, hx_mem₂⟩ := by
                simp only [Θ, dif_neg (ne_of_gt hx_pos)]; rfl
              -- Θ(y) ≤ R₃.Θ_grid(y) via δ-monotonicity
              have hΘ_y_le : Θ y ≤ R₃.Θ_grid ⟨y, hy_mem₃⟩ := by
                rw [hΘ_eq_chooseδ y hy_pos]
                have hR₃_y_eq : R₃.Θ_grid ⟨y, hy_mem₃⟩ = chooseδ h₂ R₂_x y hy_pos := by
                  have hext := hR₃_extends (fun _ => 0) 1
                  simp only [mu_zero, R₂_x.ident_eq_zero, zero_add] at hext
                  have hmu_y : mu F₃ (joinMulti (fun _ => 0) 1) = y := by
                    -- Express using unitMulti like forward direction
                    have hjoineq : (joinMulti (fun (_ : Fin 2) => 0) 1 : Multi 3) = unitMulti ⟨2, by omega⟩ 1 := by
                      funext i; fin_cases i <;> simp [joinMulti, unitMulti]
                    rw [hjoineq, mu_unitMulti, hF₃_2, iterate_op_one]
                  simp only [Nat.cast_one, one_mul] at hext
                  have h_eq_subtype : (⟨y, hy_mem₃⟩ : kGrid F₃) = ⟨mu F₃ (joinMulti (fun _ => 0) 1), mu_mem_kGrid F₃ _⟩ := by
                    exact Subtype.ext hmu_y.symm
                  rw [h_eq_subtype]; exact hext
                rw [hR₃_y_eq]
                have hF₂x_old : ∀ i : Fin 1,
                    F₂_x.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F₁.atoms i := by
                  intro i; have h0 := (getF₂_spec x hx_pos).1
                  fin_cases i; simp [F₁, singletonAtomFamily] at h0 ⊢; exact h0
                have hF₂x_new : F₂_x.atoms ⟨1, Nat.lt_succ_self 1⟩ = x := (getF₂_spec x hx_pos).2
                have hR₂x_extends : ∀ r : Multi 1,
                    R₂_x.Θ_grid ⟨mu F₂_x (joinMulti r 0), mu_mem_kGrid F₂_x (joinMulti r 0)⟩ =
                    R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ := by
                  intro r; have h := getR₂_extends_spec x hx_pos r 0
                  simp only [Nat.cast_zero, zero_mul, add_zero] at h; exact h
                exact chooseδ_monotone_family h₁ R₁_multi IH₁ H₁ x hx_pos R₂_x
                  hF₂x_old hF₂x_new hR₂x_extends h₂ IH₂ H₂ y hy_pos
              -- Chain: Θ(y) ≤ R₃.Θ(y) < R₃.Θ(x) = Θ(x), contradicting Θ(x) ≤ Θ(y)
              have h_Θy_lt_Θx : Θ y < Θ x := calc
                Θ y ≤ R₃.Θ_grid ⟨y, hy_mem₃⟩ := hΘ_y_le
                _ < R₃.Θ_grid ⟨x, hx_mem₃⟩ := h_strict
                _ = R₂_x.Θ_grid ⟨x, hx_mem₂⟩ := hR₃_x
                _ = Θ x := hΘ_x_def.symm
              linarith

      -- Property 3: Additivity (Θ(x ⊕ y) = Θ(x) + Θ(y))
      -- Uses 3-atom family {a₀, x, y} and R₃.add property
      case additivity =>
        intro x y
        by_cases hx_eq : x = ident
        · simp only [Θ, hx_eq, dif_pos rfl, op_ident_left, zero_add]
        · by_cases hy_eq : y = ident
          · simp only [Θ, hy_eq, dif_pos rfl, op_ident_right, add_zero]
          · have hx_pos : ident < x := lt_of_le_of_ne (ident_le x) (Ne.symm hx_eq)
            have hy_pos : ident < y := lt_of_le_of_ne (ident_le y) (Ne.symm hy_eq)
            have hxy_pos : ident < op x y := by
              have h1 : op ident y = y := op_ident_left y
              have h2 : ident < op ident y := by rw [h1]; exact hy_pos
              have h3 : op ident y < op x y := op_strictMono_left y hx_pos
              exact lt_trans h2 h3
            -- Build 3-atom family {a₀, x, y} to access R₃.add
            let F₂_x := getF₂ x hx_pos
            let R₂_x := getR₂ x hx_pos
            have hF₂_x_1 : F₂_x.atoms ⟨1, by decide⟩ = x := (getF₂_spec x hx_pos).2
            have h₂ : 2 ≥ 1 := by omega
            have IH₂ : GridBridge F₂_x := gridBridge_of_KSSeparation F₂_x h₂
            have H₂ : GridComm F₂_x := gridComm_of_KSSeparation F₂_x
            have h_ext_y := extend_grid_rep_with_atom_of_KSSeparationStrict
              (α := α) (hk := h₂) (R := R₂_x) (F := F₂_x) (d := y) (hd := hy_pos) (IH := IH₂) (H := H₂)
            obtain ⟨F₃, hF₃_old, hF₃_new, R₃_exists⟩ := h_ext_y
            obtain ⟨R₃, hR₃_extends⟩ := R₃_exists
            have hF₃_1 : F₃.atoms ⟨1, by omega⟩ = x := by
              have h1 := hF₃_old ⟨1, by decide⟩
              rw [h1, hF₂_x_1]
            have hF₃_2 : F₃.atoms ⟨2, by omega⟩ = y := hF₃_new
            -- x, y, and x⊕y are all on F₃ grid
            have H₃ : GridComm F₃ := gridComm_of_KSSeparation F₃
            have hx_mem₂ : x ∈ kGrid F₂_x := h_x_on_grid2 F₂_x x hF₂_x_1
            have hx_mem₃ : x ∈ kGrid F₃ := by
              use unitMulti ⟨1, by omega⟩ 1; rw [mu_unitMulti, hF₃_1, iterate_op_one]
            have hy_mem₃ : y ∈ kGrid F₃ := by
              use unitMulti ⟨2, by omega⟩ 1; rw [mu_unitMulti, hF₃_2, iterate_op_one]
            -- x⊕y = mu F₃ (unitMulti 1 1 + unitMulti 2 1)
            let r_x : Multi 3 := unitMulti ⟨1, by omega⟩ 1
            let r_y : Multi 3 := unitMulti ⟨2, by omega⟩ 1
            let r_xy : Multi 3 := fun i => r_x i + r_y i
            have hmu_x : mu F₃ r_x = x := by rw [mu_unitMulti, hF₃_1, iterate_op_one]
            have hmu_y : mu F₃ r_y = y := by rw [mu_unitMulti, hF₃_2, iterate_op_one]
            have hmu_xy : mu F₃ r_xy = op x y := by
              have h_grid_add := mu_add_of_comm H₃ r_x r_y
              -- r_xy = r_x + r_y by definition (Pi.add)
              have h_eq : r_xy = r_x + r_y := rfl
              rw [h_eq, h_grid_add, hmu_x, hmu_y]
            have hxy_mem₃ : op x y ∈ kGrid F₃ := by
              use r_xy; exact hmu_xy.symm
            -- R₃.add gives the key equation
            have h_R₃_add : R₃.Θ_grid ⟨mu F₃ r_xy, mu_mem_kGrid F₃ r_xy⟩ =
                R₃.Θ_grid ⟨mu F₃ r_x, mu_mem_kGrid F₃ r_x⟩ +
                R₃.Θ_grid ⟨mu F₃ r_y, mu_mem_kGrid F₃ r_y⟩ := R₃.add r_x r_y
            -- Connect to global Θ values
            -- Θ(x) = R₃.Θ_grid(x) (x on old grid of F₃)
            have hR₃_x_eq : R₃.Θ_grid ⟨x, hx_mem₃⟩ = R₂_x.Θ_grid ⟨x, hx_mem₂⟩ := by
              have hx_join : r_x = joinMulti (unitMulti ⟨1, by decide⟩ 1 : Multi 2) 0 := by
                funext i; fin_cases i <;> simp [r_x, joinMulti, unitMulti]
              have hext := hR₃_extends (unitMulti ⟨1, by decide⟩ 1) 0
              simp only [Nat.cast_zero, zero_mul, add_zero] at hext
              have hmu_x₃ : mu F₃ (joinMulti (unitMulti ⟨1, by decide⟩ 1) 0) = x := by
                rw [← hx_join, hmu_x]
              have hmu_x₂ : mu F₂_x (unitMulti ⟨1, by decide⟩ 1) = x := by
                rw [mu_unitMulti, hF₂_x_1, iterate_op_one]
              -- Use Subtype.ext to handle dependent type rewrites
              have h_lhs : R₃.Θ_grid ⟨x, hx_mem₃⟩ =
                  R₃.Θ_grid ⟨mu F₃ (joinMulti (unitMulti ⟨1, by decide⟩ 1) 0), mu_mem_kGrid F₃ _⟩ := by
                congr 1; exact Subtype.ext hmu_x₃.symm
              have h_rhs : R₂_x.Θ_grid ⟨x, hx_mem₂⟩ =
                  R₂_x.Θ_grid ⟨mu F₂_x (unitMulti ⟨1, by decide⟩ 1), mu_mem_kGrid F₂_x _⟩ := by
                congr 1; exact Subtype.ext hmu_x₂.symm
              rw [h_lhs, h_rhs]; exact hext
            have hΘ_x_eq : Θ x = R₂_x.Θ_grid ⟨x, hx_mem₂⟩ := by
              simp only [Θ, dif_neg (ne_of_gt hx_pos)]; rfl
            have hΘx_R₃ : Θ x = R₃.Θ_grid ⟨x, hx_mem₃⟩ := by rw [hΘ_x_eq, hR₃_x_eq]
            -- Θ(y) = R₃.Θ_grid(y) = chooseδ h₂ R₂_x y hy_pos
            have hR₃_y_eq : R₃.Θ_grid ⟨y, hy_mem₃⟩ = chooseδ h₂ R₂_x y hy_pos := by
              have hext := hR₃_extends (fun _ => 0) 1
              simp only [mu_zero, R₂_x.ident_eq_zero, zero_add, Nat.cast_one, one_mul] at hext
              -- joinMulti (fun _ => 0) 1 = unitMulti ⟨2, _⟩ 1 for Multi 3
              have hy_join : (joinMulti (fun _ => 0) 1 : Multi 3) = unitMulti ⟨2, by omega⟩ 1 := by
                funext i; fin_cases i <;> simp [joinMulti, unitMulti]
              have hmu_y₃ : mu F₃ (joinMulti (fun _ => 0) 1) = y := by
                rw [hy_join, mu_unitMulti, hF₃_2, iterate_op_one]
              -- Use Subtype.ext to handle dependent type
              have h_lhs : R₃.Θ_grid ⟨y, hy_mem₃⟩ =
                  R₃.Θ_grid ⟨mu F₃ (joinMulti (fun _ => 0) 1), mu_mem_kGrid F₃ _⟩ := by
                congr 1; exact Subtype.ext hmu_y₃.symm
              rw [h_lhs, hext]
            have hΘ_y_eq : Θ y = chooseδ h₁ R₁_multi y hy_pos := hΘ_eq_chooseδ y hy_pos
            -- Helper lemmas for F₁ → F₂_x embedding (used by both hΘy_le_R₃ and path independence)
            have hF₂x_old : ∀ i : Fin 1,
                F₂_x.atoms ⟨i.val, Nat.lt_succ_of_lt i.is_lt⟩ = F₁.atoms i := by
              intro i; have h0 := (getF₂_spec x hx_pos).1
              fin_cases i; simp [F₁, singletonAtomFamily] at h0 ⊢; exact h0
            have hF₂x_new : F₂_x.atoms ⟨1, Nat.lt_succ_self 1⟩ = x := (getF₂_spec x hx_pos).2
            have hR₂x_extends : ∀ r : Multi 1,
                R₂_x.Θ_grid ⟨mu F₂_x (joinMulti r 0), mu_mem_kGrid F₂_x (joinMulti r 0)⟩ =
                R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ := by
              intro r; have h := getR₂_extends_spec x hx_pos r 0
              simp only [Nat.cast_zero, zero_mul, add_zero] at h; exact h
            -- By δ-monotonicity, Θ(y) ≤ R₃.Θ_grid(y)
            have hΘy_le_R₃ : Θ y ≤ R₃.Θ_grid ⟨y, hy_mem₃⟩ := by
              rw [hΘ_y_eq, hR₃_y_eq]
              exact chooseδ_monotone_family h₁ R₁_multi IH₁ H₁ x hx_pos R₂_x
                hF₂x_old hF₂x_new hR₂x_extends h₂ IH₂ H₂ y hy_pos
            -- ═══════════════════════════════════════════════════════════════════════
            -- PATH INDEPENDENCE: chooseδ h₁ R₁_multi y = chooseδ h₂ R₂_x y
            -- (K&S Appendix A path independence, cf. Goertzel v2 analysis)
            -- ═══════════════════════════════════════════════════════════════════════
            -- Key insight: chooseδ h₂ R₂_x y hy_pos satisfies DeltaSpec F₁ R₁_multi y hy_pos
            -- because F₁-witnesses embed into F₂_x-witnesses with preserved statistics.
            -- By DeltaSpec_unique, this equals chooseδ h₁ R₁_multi y hy_pos.
            have hδ_path_indep_y : chooseδ h₁ R₁_multi y hy_pos = chooseδ h₂ R₂_x y hy_pos := by
              -- Show chooseδ h₂ R₂_x y hy_pos satisfies DeltaSpec F₁ R₁_multi y hy_pos
              have h_spec_at_base : DeltaSpec F₁ R₁_multi y hy_pos (chooseδ h₂ R₂_x y hy_pos) := by
                -- Get the DeltaSpec that chooseδ h₂ satisfies at F₂_x level
                have h_spec₂ := chooseδ_spec h₂ R₂_x IH₂ H₂ y hy_pos
                -- Helper: μ is preserved under embedding (joinMulti r 0)
                have h_mu_embed : ∀ r : Multi 1, mu F₂_x (joinMulti r 0) = mu F₁ r := by
                  intro r
                  have h := mu_extend_last_of_old_new F₁ x hx_pos F₂_x hF₂x_old hF₂x_new r 0
                  simp only [iterate_op_zero, op_ident_right] at h
                  exact h
                -- Helper: statistics preserved under embedding
                have h_stat_embed : ∀ r u (hu : 0 < u),
                    separationStatistic R₂_x (joinMulti r 0) u hu =
                    separationStatistic R₁_multi r u hu := by
                  intro r u hu
                  simp only [separationStatistic]
                  have h := hR₂x_extends r
                  rw [h]
                -- Build DeltaSpec at F₁ level
                refine ⟨?hA, ?hC, ?hB⟩
                -- A-bound: For F₁-A-witnesses, their statistics ≤ chooseδ h₂
                case hA =>
                  intro r u hu hrA
                  -- hrA : r ∈ extensionSetA F₁ y u, i.e., mu F₁ r < y^u
                  have hrA' : joinMulti r 0 ∈ extensionSetA F₂_x y u := by
                    simp only [extensionSetA, Set.mem_setOf_eq]
                    rw [h_mu_embed]; exact hrA
                  -- By h_spec₂.1: separationStatistic R₂_x (joinMulti r 0) u hu ≤ chooseδ h₂
                  have h := h_spec₂.1 (joinMulti r 0) u hu hrA'
                  rw [h_stat_embed] at h
                  exact h
                -- C-bound: chooseδ h₂ ≤ statistics of F₁-C-witnesses
                case hC =>
                  intro r u hu hrC
                  have hrC' : joinMulti r 0 ∈ extensionSetC F₂_x y u := by
                    simp only [extensionSetC, Set.mem_setOf_eq]
                    rw [h_mu_embed]; exact hrC
                  have h := h_spec₂.2.1 (joinMulti r 0) u hu hrC'
                  rw [h_stat_embed] at h
                  exact h
                -- B-bound: statistics of F₁-B-witnesses = chooseδ h₂
                case hB =>
                  intro r u hu hrB
                  have hrB' : joinMulti r 0 ∈ extensionSetB F₂_x y u := by
                    simp only [extensionSetB, Set.mem_setOf_eq]
                    rw [h_mu_embed]; exact hrB
                  have h := h_spec₂.2.2 (joinMulti r 0) u hu hrB'
                  rw [h_stat_embed] at h
                  exact h
              -- By DeltaSpec_unique, both values are equal
              have h_spec₁ := chooseδ_spec h₁ R₁_multi IH₁ H₁ y hy_pos
              exact DeltaSpec_unique h₁ R₁_multi IH₁ H₁ y hy_pos h_spec₁ h_spec_at_base
            -- Now we have Θ(y) = R₃.Θ_grid(y)
            have hΘy_R₃ : Θ y = R₃.Θ_grid ⟨y, hy_mem₃⟩ := by
              rw [hΘ_y_eq, hR₃_y_eq, hδ_path_indep_y]
            -- ═══════════════════════════════════════════════════════════════════════
            -- ADDITIVITY via R₃.add
            -- ═══════════════════════════════════════════════════════════════════════
            -- We have: Θ(x) = R₃.Θ_grid(x), Θ(y) = R₃.Θ_grid(y)
            -- By R₃.add: R₃.Θ_grid(op x y) = R₃.Θ_grid(x) + R₃.Θ_grid(y) = Θ(x) + Θ(y)
            -- We need: Θ(op x y) = R₃.Θ_grid(op x y)
            -- Rewrite h_R₃_add using the mu equalities
            have h_R₃_xy : R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ =
                R₃.Θ_grid ⟨x, hx_mem₃⟩ + R₃.Θ_grid ⟨y, hy_mem₃⟩ := by
              -- Use Subtype.ext to connect mu values to x, y, op x y
              have h_lhs : R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ =
                  R₃.Θ_grid ⟨mu F₃ r_xy, mu_mem_kGrid F₃ r_xy⟩ := by
                congr 1; exact Subtype.ext hmu_xy.symm
              have h_rhs_x : R₃.Θ_grid ⟨x, hx_mem₃⟩ =
                  R₃.Θ_grid ⟨mu F₃ r_x, mu_mem_kGrid F₃ r_x⟩ := by
                congr 1; exact Subtype.ext hmu_x.symm
              have h_rhs_y : R₃.Θ_grid ⟨y, hy_mem₃⟩ =
                  R₃.Θ_grid ⟨mu F₃ r_y, mu_mem_kGrid F₃ r_y⟩ := by
                congr 1; exact Subtype.ext hmu_y.symm
              rw [h_lhs, h_rhs_x, h_rhs_y, ← h_R₃_add]
            -- Path independence for op x y: Θ(op x y) = R₃.Θ_grid(op x y)
            -- This follows from the same argument as for y
            have hδ_path_indep_xy : chooseδ h₁ R₁_multi (op x y) hxy_pos =
                R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := by
              -- R₃.Θ_grid(op x y) = R₃.Θ_grid(x) + R₃.Θ_grid(y) by h_R₃_xy
              -- = Θ(x) + Θ(y) by hΘx_R₃ and hΘy_R₃
              -- = chooseδ h₁ x + chooseδ h₁ y by hΘ_eq_chooseδ
              -- We need to show chooseδ h₁ (op x y) equals this sum
              -- This is the additivity of chooseδ at base level!
              -- Key: R₃.Θ_grid(op x y) satisfies DeltaSpec F₁ R₁_multi (op x y) hxy_pos
              have h_spec_at_base : DeltaSpec F₁ R₁_multi (op x y) hxy_pos
                  (R₃.Θ_grid ⟨op x y, hxy_mem₃⟩) := by
                -- R₃.Θ_grid(op x y) = Θ(x) + Θ(y) = chooseδ h₁ x + chooseδ h₁ y
                have h_val : R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ =
                    chooseδ h₁ R₁_multi x hx_pos + chooseδ h₁ R₁_multi y hy_pos := by
                  rw [h_R₃_xy, ← hΘx_R₃, ← hΘy_R₃]
                  simp only [hΘ_eq_chooseδ x hx_pos, hΘ_eq_chooseδ y hy_pos]
                -- Get DeltaSpec for chooseδ h₂ R₂_x (op x y) from h_ext_y extended again
                -- Actually, we need DeltaSpec for (op x y) which is on the F₃ grid
                -- The value R₃.Θ_grid(op x y) is determined by R₃.add from grid values
                -- We use that this equals Θ(x) + Θ(y) = δ_x + δ_y
                -- And show δ_x + δ_y satisfies DeltaSpec F₁ for (op x y)
                -- F₁-witnesses for (op x y) embed into F₃ with additive statistics
                have h_mu_embed₃ : ∀ r : Multi 1, mu F₃ (joinMulti (joinMulti r 0) 0) = mu F₁ r := by
                  intro r
                  have h1 := mu_extend_last_of_old_new F₁ x hx_pos F₂_x hF₂x_old hF₂x_new r 0
                  simp only [iterate_op_zero, op_ident_right] at h1
                  have h2 := mu_extend_last_of_old_new F₂_x y hy_pos F₃ hF₃_old hF₃_new (joinMulti r 0) 0
                  simp only [iterate_op_zero, op_ident_right] at h2
                  rw [h2, h1]
                have h_stat_embed₃ : ∀ r u (hu : 0 < u),
                    separationStatistic R₃ (joinMulti (joinMulti r 0) 0) u hu =
                    separationStatistic R₁_multi r u hu := by
                  intro r u hu
                  simp only [separationStatistic]
                  have h1 := hR₃_extends (joinMulti r 0) 0
                  simp only [Nat.cast_zero, zero_mul, add_zero] at h1
                  have h2 := hR₂x_extends r
                  rw [h1, h2]
                -- Now use the DeltaSpec at the R₃ level for (op x y)
                -- (op x y) = mu F₃ r_xy, so R₃.Θ_grid(op x y) has a natural spec
                -- But we need DeltaSpec at F₁ level for (op x y)
                -- Use that all F₁ witnesses embed and statistics preserved
                refine ⟨?hA, ?hC, ?hB⟩
                case hA =>
                  intro r u hu hrA
                  -- hrA : mu F₁ r < (op x y)^u
                  have h_embed := h_mu_embed₃ r
                  have h_stat := h_stat_embed₃ r u hu
                  -- Define membership proofs explicitly
                  have hr_mem₃ : mu F₁ r ∈ kGrid F₃ := ⟨joinMulti (joinMulti r 0) 0, h_embed.symm⟩
                  have hxyu_mem₃ : iterate_op (op x y) u ∈ kGrid F₃ := by
                    use scaleMult u r_xy; rw [mu_scale_eq_iterate_of_comm H₃, hmu_xy]
                  -- By strict monotonicity: mu F₁ r < iterate_op (op x y) u →
                  -- R₃.Θ_grid(mu F₁ r) < R₃.Θ_grid(iterate_op (op x y) u)
                  have h_strict : R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ <
                      R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ :=
                    R₃.strictMono.lt_iff_lt.mpr hrA
                  -- R₃.Θ_grid(iterate_op (op x y) u) = u * R₃.Θ_grid(op x y) via R₃.scale
                  have h_power : R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ =
                      u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := by
                    have h_mu_power : mu F₃ (scaleMult u r_xy) = iterate_op (op x y) u := by
                      rw [mu_scale_eq_iterate_of_comm H₃, hmu_xy]
                    have h_Θ_power := Theta_scaleMult R₃ r_xy u
                    have h_eq : (⟨iterate_op (op x y) u, hxyu_mem₃⟩ : kGrid F₃) =
                        ⟨mu F₃ (scaleMult u r_xy), mu_mem_kGrid F₃ _⟩ :=
                      Subtype.ext h_mu_power.symm
                    rw [h_eq, h_Θ_power]
                    have h_base : (⟨mu F₃ r_xy, mu_mem_kGrid F₃ r_xy⟩ : kGrid F₃) =
                        ⟨op x y, hxy_mem₃⟩ := Subtype.ext hmu_xy
                    rw [h_base]
                  -- R₃.Θ_grid ⟨mu F₃ (embed r), ...⟩ = R₁_multi.Θ_grid ⟨mu F₁ r, ...⟩ via embedding
                  have h_Θ_embed : R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ =
                      R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ := by
                    have h1 := hR₃_extends (joinMulti r 0) 0
                    simp only [Nat.cast_zero, zero_mul, add_zero] at h1
                    have h2 := hR₂x_extends r
                    simp only [h1, h2]
                  -- Also: R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ = R₃.Θ_grid ⟨mu F₃ (embed r), ...⟩
                  have h_Θ_r : R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ =
                      R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ := by
                    congr 1; exact Subtype.ext h_embed.symm
                  -- Goal: separationStatistic R₁_multi r u hu ≤ h_val
                  simp only [separationStatistic]
                  -- Use h_stat: separationStatistic R₃ (embed r) = separationStatistic R₁_multi r
                  simp only [separationStatistic] at h_stat
                  rw [← h_Θ_embed]
                  have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu
                  have h_lt : R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ <
                      R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ * u := by
                    calc R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩
                        = R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ := h_Θ_r.symm
                      _ < R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ := h_strict
                      _ = u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := h_power
                      _ = R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ * u := mul_comm _ _
                  linarith [(div_lt_iff₀ hu_pos).mpr h_lt]
                case hC =>
                  intro r u hu hrC
                  -- hrC : iterate_op (op x y) u < mu F₁ r
                  have h_embed := h_mu_embed₃ r
                  have h_stat := h_stat_embed₃ r u hu
                  -- Define membership proofs explicitly
                  have hr_mem₃ : mu F₁ r ∈ kGrid F₃ := ⟨joinMulti (joinMulti r 0) 0, h_embed.symm⟩
                  have hxyu_mem₃ : iterate_op (op x y) u ∈ kGrid F₃ := by
                    use scaleMult u r_xy; rw [mu_scale_eq_iterate_of_comm H₃, hmu_xy]
                  -- By strict monotonicity: iterate_op < mu F₁ r
                  have h_strict : R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ <
                      R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ :=
                    R₃.strictMono.lt_iff_lt.mpr hrC
                  -- R₃.Θ_grid(iterate_op (op x y) u) = u * R₃.Θ_grid(op x y)
                  have h_power : R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ =
                      u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := by
                    have h_mu_power : mu F₃ (scaleMult u r_xy) = iterate_op (op x y) u := by
                      rw [mu_scale_eq_iterate_of_comm H₃, hmu_xy]
                    have h_Θ_power := Theta_scaleMult R₃ r_xy u
                    have h_eq : (⟨iterate_op (op x y) u, hxyu_mem₃⟩ : kGrid F₃) =
                        ⟨mu F₃ (scaleMult u r_xy), mu_mem_kGrid F₃ _⟩ :=
                      Subtype.ext h_mu_power.symm
                    rw [h_eq, h_Θ_power]
                    have h_base : (⟨mu F₃ r_xy, mu_mem_kGrid F₃ r_xy⟩ : kGrid F₃) =
                        ⟨op x y, hxy_mem₃⟩ := Subtype.ext hmu_xy
                    rw [h_base]
                  -- R₃.Θ_grid ⟨mu F₃ (embed r), ...⟩ = R₁_multi.Θ_grid ⟨mu F₁ r, ...⟩ via embedding
                  have h_Θ_embed : R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ =
                      R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ := by
                    have h1 := hR₃_extends (joinMulti r 0) 0
                    simp only [Nat.cast_zero, zero_mul, add_zero] at h1
                    have h2 := hR₂x_extends r
                    simp only [h1, h2]
                  -- R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ = R₃.Θ_grid ⟨mu F₃ (embed r), ...⟩
                  have h_Θ_r : R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ =
                      R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ := by
                    congr 1; exact Subtype.ext h_embed.symm
                  simp only [separationStatistic]
                  simp only [separationStatistic] at h_stat
                  rw [← h_Θ_embed]
                  have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu
                  have h_gt : R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ * u <
                      R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ := by
                    calc R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ * u
                        = u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := mul_comm _ _
                      _ = R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ := h_power.symm
                      _ < R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ := h_strict
                      _ = R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ := h_Θ_r
                  linarith [(lt_div_iff₀ hu_pos).mpr h_gt]
                case hB =>
                  intro r u hu hrB
                  -- hrB : mu F₁ r = iterate_op (op x y) u
                  have h_embed := h_mu_embed₃ r
                  have h_stat := h_stat_embed₃ r u hu
                  -- Define membership proofs explicitly
                  have hr_mem₃ : mu F₁ r ∈ kGrid F₃ := ⟨joinMulti (joinMulti r 0) 0, h_embed.symm⟩
                  have hxyu_mem₃ : iterate_op (op x y) u ∈ kGrid F₃ := by
                    use scaleMult u r_xy; rw [mu_scale_eq_iterate_of_comm H₃, hmu_xy]
                  -- mu F₁ r = iterate_op (op x y) u implies Θ values equal
                  have h_Θ_eq : R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ =
                      R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ := by
                    congr 1; exact Subtype.ext hrB
                  -- R₃.Θ_grid(iterate_op (op x y) u) = u * R₃.Θ_grid(op x y)
                  have h_power : R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ =
                      u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := by
                    have h_mu_power : mu F₃ (scaleMult u r_xy) = iterate_op (op x y) u := by
                      rw [mu_scale_eq_iterate_of_comm H₃, hmu_xy]
                    have h_Θ_power := Theta_scaleMult R₃ r_xy u
                    have h_eq : (⟨iterate_op (op x y) u, hxyu_mem₃⟩ : kGrid F₃) =
                        ⟨mu F₃ (scaleMult u r_xy), mu_mem_kGrid F₃ _⟩ :=
                      Subtype.ext h_mu_power.symm
                    rw [h_eq, h_Θ_power]
                    have h_base : (⟨mu F₃ r_xy, mu_mem_kGrid F₃ r_xy⟩ : kGrid F₃) =
                        ⟨op x y, hxy_mem₃⟩ := Subtype.ext hmu_xy
                    rw [h_base]
                  -- R₃.Θ_grid ⟨mu F₃ (embed r), ...⟩ = R₁_multi.Θ_grid ⟨mu F₁ r, ...⟩ via embedding
                  have h_Θ_embed : R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ =
                      R₁_multi.Θ_grid ⟨mu F₁ r, mu_mem_kGrid F₁ r⟩ := by
                    have h1 := hR₃_extends (joinMulti r 0) 0
                    simp only [Nat.cast_zero, zero_mul, add_zero] at h1
                    have h2 := hR₂x_extends r
                    simp only [h1, h2]
                  -- R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ = R₃.Θ_grid ⟨mu F₃ (embed r), ...⟩
                  have h_Θ_r : R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ =
                      R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ := by
                    congr 1; exact Subtype.ext h_embed.symm
                  simp only [separationStatistic]
                  simp only [separationStatistic] at h_stat
                  rw [← h_Θ_embed]
                  -- Goal: R₃.Θ_grid(embed r) / u = h_val
                  have h_val_eq : R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩ =
                      u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := by
                    calc R₃.Θ_grid ⟨mu F₃ (joinMulti (joinMulti r 0) 0), mu_mem_kGrid F₃ _⟩
                        = R₃.Θ_grid ⟨mu F₁ r, hr_mem₃⟩ := h_Θ_r.symm
                      _ = R₃.Θ_grid ⟨iterate_op (op x y) u, hxyu_mem₃⟩ := h_Θ_eq
                      _ = u * R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := h_power
                  rw [h_val_eq]
                  have hu_pos : (0 : ℝ) < u := Nat.cast_pos.mpr hu
                  field_simp
              -- By DeltaSpec_unique
              have h_spec₁ := chooseδ_spec h₁ R₁_multi IH₁ H₁ (op x y) hxy_pos
              exact DeltaSpec_unique h₁ R₁_multi IH₁ H₁ (op x y) hxy_pos h_spec₁ h_spec_at_base
            -- Final: Θ(op x y) = Θ(x) + Θ(y)
            have hΘ_xy_eq : Θ (op x y) = chooseδ h₁ R₁_multi (op x y) hxy_pos := hΘ_eq_chooseδ (op x y) hxy_pos
            calc Θ (op x y) = chooseδ h₁ R₁_multi (op x y) hxy_pos := hΘ_xy_eq
              _ = R₃.Θ_grid ⟨op x y, hxy_mem₃⟩ := hδ_path_indep_xy
              _ = R₃.Θ_grid ⟨x, hx_mem₃⟩ + R₃.Θ_grid ⟨y, hy_mem₃⟩ := h_R₃_xy
              _ = Θ x + Θ y := by rw [← hΘx_R₃, ← hΘy_R₃]

/-- **Globalization Instance with Density**: Alternative using `[KSSeparation α] [DenselyOrdered α]`. -/
instance representationGlobalization_of_KSSeparation_of_denselyOrdered [DenselyOrdered α] :
    RepresentationGlobalization α := by
  letI : KSSeparationStrict α := KSSeparation.toKSSeparationStrict_of_denselyOrdered
  exact representationGlobalization_of_KSSeparationStrict

end WithIdentity

end Mettapedia.ProbabilityTheory.KnuthSkilling.Additive
