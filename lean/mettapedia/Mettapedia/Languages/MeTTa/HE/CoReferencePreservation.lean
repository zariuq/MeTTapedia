import Mettapedia.Languages.MeTTa.HE.BagSupportBridge
import Mathlib.Data.List.Basic

/-!
# Co-Reference Preservation Under Canonical Storage

Formalizes the **injectivity requirement** for variable canonicalization:
an injective renaming preserves co-reference (shared variables stay shared)
and distinctness (different variables stay different).

## Key Results

- `VarRenaming.Injective` — the formal requirement
- `VarRenaming.distinct_preserved` — distinct vars stay distinct
- `VarRenaming.apply_var_injective` — renamed vars are injective images
- `VarRenaming.apply_id` — identity is no-op
- `VarRenaming.apply_comp` — composition law

## Connection to CeTTa

- `term_universe.c`: `TermUniverseCanonMap` assigns fresh ordinals → injective
- `table_store.c`: `TableVarMap` assigns fresh ordinals → injective
- Injectivity guarantees co-reference preservation without traversing the atom tree
-/

namespace Mettapedia.Languages.MeTTa.HE

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

/-! ## §1: Variable renaming -/

/-- A **variable renaming**: maps variable names to new names. -/
structure VarRenaming where
  rename : String → String

/-- A renaming is **injective**: distinct names map to distinct names.
    This is THE co-reference preservation requirement. -/
def VarRenaming.Injective (r : VarRenaming) : Prop :=
  Function.Injective r.rename

/-- **Distinct preservation**: different variable names stay different. -/
theorem VarRenaming.distinct_preserved (r : VarRenaming) (hr : r.Injective)
    {v₁ v₂ : String} (hne : v₁ ≠ v₂) :
    r.rename v₁ ≠ r.rename v₂ :=
  fun h => hne (hr h)

/-- **Co-reference preservation (at variable level)**: same name → same renamed name.
    This is trivially true (it's a function), but stating it makes the contract explicit:
    every occurrence of `$x` maps to `rename("x")`, guaranteed by function application. -/
theorem VarRenaming.coref_preserved (r : VarRenaming) (v : String) :
    r.rename v = r.rename v := rfl

/-- Together, `coref_preserved` + `distinct_preserved` say:
    an injective renaming is a **faithful encoding** of variable identity.
    Two positions share a variable iff their renamed positions share a variable. -/
theorem VarRenaming.faithful_iff (r : VarRenaming) (hr : r.Injective)
    (v₁ v₂ : String) :
    v₁ = v₂ ↔ r.rename v₁ = r.rename v₂ :=
  ⟨fun h => h ▸ rfl, fun h => hr h⟩

/-! ## §2: Atom-level renaming (fuel-bounded for nested inductive) -/

/-- Apply a renaming to all variables in an atom. Fuel-bounded. -/
def VarRenaming.applyAtom (r : VarRenaming) (atom : Atom) (fuel : Nat := 100) : Atom :=
  match fuel with
  | 0 => atom
  | n + 1 =>
    match atom with
    | .var v => .var (r.rename v)
    | .expression es => .expression (es.map (r.applyAtom · n))
    | a => a

/-- Renaming a variable atom gives the renamed variable. -/
@[simp]
theorem VarRenaming.apply_var (r : VarRenaming) (v : String) (fuel : Nat) :
    r.applyAtom (.var v) (fuel + 1) = .var (r.rename v) := rfl

/-- Renaming a symbol is a no-op. -/
@[simp]
theorem VarRenaming.apply_symbol (r : VarRenaming) (s : String) (fuel : Nat) :
    r.applyAtom (.symbol s) (fuel + 1) = .symbol s := rfl

/-- Renaming a grounded value is a no-op. -/
@[simp]
theorem VarRenaming.apply_grounded (r : VarRenaming) (g : GroundedValue) (fuel : Nat) :
    r.applyAtom (.grounded g) (fuel + 1) = .grounded g := rfl

/-- Renaming preserves variable injectivity at the atom level:
    if `applyAtom r a₁ = applyAtom r a₂` and both are variables and r is injective,
    then `a₁ = a₂`. -/
theorem VarRenaming.apply_var_injective (r : VarRenaming) (hr : r.Injective)
    (v₁ v₂ : String) (fuel : Nat)
    (h : r.applyAtom (.var v₁) (fuel + 1) = r.applyAtom (.var v₂) (fuel + 1)) :
    v₁ = v₂ := by
  simp [applyAtom] at h
  exact hr h

/-! ## §3: Algebraic laws -/

/-- Identity renaming is a no-op (at any fuel ≥ 1). -/
theorem VarRenaming.apply_id_var (v : String) (fuel : Nat) :
    (VarRenaming.mk id).applyAtom (.var v) (fuel + 1) = .var v := rfl

/-- Composition of renamings on variables = renaming by composition. -/
theorem VarRenaming.apply_comp_var (r₁ r₂ : VarRenaming) (v : String) (fuel : Nat) :
    r₂.applyAtom (r₁.applyAtom (.var v) (fuel + 1)) (fuel + 1) =
    (VarRenaming.mk (r₂.rename ∘ r₁.rename)).applyAtom (.var v) (fuel + 1) := rfl

/-- Composition of injective renamings is injective. -/
theorem VarRenaming.comp_injective (r₁ r₂ : VarRenaming)
    (h₁ : r₁.Injective) (h₂ : r₂.Injective) :
    (VarRenaming.mk (r₂.rename ∘ r₁.rename)).Injective := by
  intro a b hab
  exact h₁ (h₂ hab)

/-! ## §4: applyAtom injectivity -/

/-- `applyAtom` with injective renaming is injective on atoms. -/
theorem VarRenaming.applyAtom_injective (r : VarRenaming) (hr : r.Injective)
    (fuel : Nat) : Function.Injective (r.applyAtom · (fuel + 1)) := by
  intro a₁ a₂ h
  induction fuel generalizing a₁ a₂ with
  | zero =>
    -- fuel+1 = 1, so applyAtom unfolds one level
    match a₁, a₂ with
    | .var v₁, .var v₂ => simp [applyAtom] at h; exact congrArg Atom.var (hr h)
    | .symbol s₁, .symbol s₂ => simp [applyAtom] at h; exact congrArg Atom.symbol h
    | .grounded g₁, .grounded g₂ => simp [applyAtom] at h; exact congrArg Atom.grounded h
    | .expression es₁, .expression es₂ =>
      simp [applyAtom] at h
      exact congrArg Atom.expression h
    | .var _, .symbol _ => simp [applyAtom] at h
    | .var _, .grounded _ => simp [applyAtom] at h
    | .var _, .expression _ => simp [applyAtom] at h
    | .symbol _, .var _ => simp [applyAtom] at h
    | .symbol _, .grounded _ => simp [applyAtom] at h
    | .symbol _, .expression _ => simp [applyAtom] at h
    | .grounded _, .var _ => simp [applyAtom] at h
    | .grounded _, .symbol _ => simp [applyAtom] at h
    | .grounded _, .expression _ => simp [applyAtom] at h
    | .expression _, .var _ => simp [applyAtom] at h
    | .expression _, .symbol _ => simp [applyAtom] at h
    | .expression _, .grounded _ => simp [applyAtom] at h
  | succ n ih =>
    match a₁, a₂ with
    | .var v₁, .var v₂ => simp [applyAtom] at h; exact congrArg Atom.var (hr h)
    | .symbol s₁, .symbol s₂ => simp [applyAtom] at h; exact congrArg Atom.symbol h
    | .grounded g₁, .grounded g₂ => simp [applyAtom] at h; exact congrArg Atom.grounded h
    | .expression es₁, .expression es₂ =>
      simp [applyAtom] at h
      congr 1
      exact (List.map_injective_iff.mpr ih) h
    | .var _, .symbol _ => simp [applyAtom] at h
    | .var _, .grounded _ => simp [applyAtom] at h
    | .var _, .expression _ => simp [applyAtom] at h
    | .symbol _, .var _ => simp [applyAtom] at h
    | .symbol _, .grounded _ => simp [applyAtom] at h
    | .symbol _, .expression _ => simp [applyAtom] at h
    | .grounded _, .var _ => simp [applyAtom] at h
    | .grounded _, .symbol _ => simp [applyAtom] at h
    | .grounded _, .expression _ => simp [applyAtom] at h
    | .expression _, .var _ => simp [applyAtom] at h
    | .expression _, .symbol _ => simp [applyAtom] at h
    | .expression _, .grounded _ => simp [applyAtom] at h

/-- BEq compatibility: `(r(a) == r(b)) = (a == b)` for injective `r`. -/
theorem VarRenaming.applyAtom_beq_iff (r : VarRenaming) (hr : r.Injective)
    (a b : Atom) (fuel : Nat) :
    (r.applyAtom a (fuel + 1) == r.applyAtom b (fuel + 1)) = (a == b) := by
  have hinj := applyAtom_injective r hr fuel
  by_cases hab : a = b
  · subst hab; simp
  · have : r.applyAtom a (fuel + 1) ≠ r.applyAtom b (fuel + 1) :=
      fun h => hab (hinj h)
    simp [hab, this]

/-! ## §4a: Fuel-free atom renaming

`applyAtom` is fuel-bounded for termination. For specification purposes
(bisimulation proofs), we need a fuel-free version that always fully
traverses. Lean 4 accepts this via structural recursion on nested inductives. -/

/-- Fuel-free atom renaming. Unlike `applyAtom`, always fully traverses the atom tree. -/
def applyAtomTotal (r : VarRenaming) : Atom → Atom
  | .var v => .var (r.rename v)
  | .symbol s => .symbol s
  | .grounded g => .grounded g
  | .expression es => .expression (es.map (applyAtomTotal r))

private theorem sizeOf_mem_lt_expression (a : Atom) (es : List Atom) (ha : a ∈ es) :
    sizeOf a < sizeOf (Atom.expression es) := by
  rw [Atom.expression.sizeOf_spec]
  exact Nat.lt_of_lt_of_le (List.sizeOf_lt_of_mem ha) (Nat.le_add_left _ _)

/-- `applyAtomTotal` with injective renaming is injective. -/
noncomputable def applyAtomTotal_injective_aux (r : VarRenaming) (hr : r.Injective) :
    (a₁ : Atom) → ∀ a₂, applyAtomTotal r a₁ = applyAtomTotal r a₂ → a₁ = a₂ :=
  WellFounded.fix (measure (sizeOf (α := Atom))).wf fun a₁ ih a₂ h => by
    match a₁, a₂, h with
    | .var _, .var _, h => unfold applyAtomTotal at h; exact congrArg _ (hr (Atom.var.inj h))
    | .symbol _, .symbol _, h => unfold applyAtomTotal at h; exact h
    | .grounded _, .grounded _, h => unfold applyAtomTotal at h; exact h
    | .expression es₁, .expression es₂, h =>
      unfold applyAtomTotal at h; congr 1
      have hmap := Atom.expression.inj h
      have haux : ∀ (l₁ l₂ : List Atom),
          (∀ a, a ∈ l₁ → ∀ b, applyAtomTotal r a = applyAtomTotal r b → a = b) →
          l₁.map (applyAtomTotal r) = l₂.map (applyAtomTotal r) → l₁ = l₂ := by
        intro l₁; induction l₁ with
        | nil => intro l₂ _ hm; cases l₂ <;> simp_all [List.map]
        | cons x xs ihxs =>
          intro l₂ hmem hm; cases l₂ with
          | nil => simp [List.map] at hm
          | cons y ys =>
            simp [List.map] at hm; obtain ⟨hhd, htl⟩ := hm
            exact congrArg₂ List.cons
              (hmem x (List.mem_cons.mpr (.inl rfl)) y hhd)
              (ihxs ys (fun a ha => hmem a (List.mem_cons.mpr (.inr ha))) htl)
      exact haux es₁ es₂
        (fun a ha b hab => ih a
          (by show sizeOf a < sizeOf (Atom.expression es₁)
              exact sizeOf_mem_lt_expression a es₁ ha) b hab) hmap
    | .var _, .symbol _, h | .var _, .grounded _, h | .var _, .expression _, h
    | .symbol _, .var _, h | .symbol _, .grounded _, h | .symbol _, .expression _, h
    | .grounded _, .var _, h | .grounded _, .symbol _, h | .grounded _, .expression _, h
    | .expression _, .var _, h | .expression _, .symbol _, h | .expression _, .grounded _, h =>
      unfold applyAtomTotal at h; exact absurd h Atom.noConfusion

theorem applyAtomTotal_injective (r : VarRenaming) (hr : r.Injective) :
    Function.Injective (applyAtomTotal r) := applyAtomTotal_injective_aux r hr

/-- BEq compatibility for fuel-free renaming. -/
theorem applyAtomTotal_beq_iff (r : VarRenaming) (hr : r.Injective) (a b : Atom) :
    (applyAtomTotal r a == applyAtomTotal r b) = (a == b) := by
  by_cases hab : a = b
  · subst hab; simp
  · have : applyAtomTotal r a ≠ applyAtomTotal r b :=
      fun h => hab (applyAtomTotal_injective r hr h)
    simp [hab, this]

/-! ## §5: The CanonMap connection -/

/-- A `VarRenaming` lifts to a `CanonMap` on atoms (at fixed fuel). -/
def VarRenaming.toCanonMap (r : VarRenaming) (fuel : Nat := 100) : CanonMap where
  canon := fun a => r.applyAtom a fuel

/-- Injective renamings give injective CanonMaps on variable atoms. -/
theorem VarRenaming.canonMap_var_injective (r : VarRenaming) (hr : r.Injective)
    (fuel : Nat) (v₁ v₂ : String)
    (h : (r.toCanonMap (fuel + 1)).canon (.var v₁) = (r.toCanonMap (fuel + 1)).canon (.var v₂)) :
    v₁ = v₂ := by
  simp [toCanonMap, applyAtom] at h
  exact hr h

/-! ## §5: Interpretation

### What this gives CeTTa

The **faithful_iff** theorem is the complete characterization:
under an injective renaming, variable identity is preserved in both directions.

- `v₁ = v₂ → rename v₁ = rename v₂` (co-reference: same var stays same)
- `rename v₁ = rename v₂ → v₁ = v₂` (distinctness: different vars stay different)

CeTTa's `TermUniverseCanonMap` builds the renaming by assigning ordinals:
`map->len + 1` for each new variable. This is injective because each new
variable gets a strictly larger ordinal. Our theorem says: any such
injective map preserves the full variable-identity structure.

### The cache connection

`table_store_canonicalize_atom` uses `TableVarMap` — same pattern.
The variant table key is the canonicalized atom. `faithful_iff` says:
two queries have the same canonical key iff they have the same variable
structure. This is variant-equivalence, and it's what XSB calls
"variant-based tabling."

### The Fujita connection

A faithful (injective) canonicalization is a **reduced hyperstructure
quotient morphism**: it quotients by alpha-equivalence without collapsing
structurally distinct terms. `CanonMap.support_comm` (BagSupportBridge.lean)
says this quotient commutes with support projection. Here we prove the
quotient is faithful: it doesn't over-identify.
-/

end Mettapedia.Languages.MeTTa.HE
