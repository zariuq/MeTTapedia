import Mettapedia.GSLT.LanguageDef.BooleanAlgebraIdentitySemanticBasis
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Finite cell profiles in atomless Boolean algebras

Quantifier elimination for atomless Boolean algebras rests on one concrete
extension property.  A valuation of finitely many variables partitions the
unit into Venn cells.  After adding one variable, every old nonzero cell may
remain wholly on either side or split into two nonzero pieces; an old zero
cell must remain zero on both sides.  Atomlessness is exactly what realizes
the two-nonzero case.

This module proves that extension property directly.  It does not yet name a
full first-order quantifier-elimination algorithm.  The finite profile and its
projection are explicit, and the constructed witness is a finite join of
cell-local choices.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension

open Mettapedia.Foundations.Gunk

universe u

/-- A Venn cell selects a polarity for every variable. -/
abbrev Cell (arity : Nat) := Fin arity -> Bool

/-- A finite profile records exactly which Venn cells are nonzero. -/
abbrev Profile (arity : Nat) := Cell arity -> Bool

/-- Add a new value at de Bruijn index zero. -/
def extendValuation {B : Type u} {arity : Nat}
    (value : B) (valuation : Fin arity -> B) : Fin (arity + 1) -> B :=
  Fin.cases value valuation

/-- Add the polarity of the new de Bruijn-zero variable to a cell. -/
def extendCell {arity : Nat} (polarity : Bool) (cell : Cell arity) :
    Cell (arity + 1) :=
  Fin.cases polarity cell

/-- The element selected by one Venn cell under a Boolean valuation. -/
def cellValue {B : Type u} [BooleanAlgebra B] :
    {arity : Nat} -> (Fin arity -> B) -> Cell arity -> B
  | 0, _valuation, _cell => ⊤
  | _arity + 1, valuation, cell =>
      (if cell 0 then valuation 0 else (valuation 0)ᶜ) ⊓
        cellValue (fun index => valuation index.succ)
          (fun index => cell index.succ)

@[simp] theorem cellValue_zero {B : Type u} [BooleanAlgebra B]
    (valuation : Fin 0 -> B) (cell : Cell 0) :
    cellValue valuation cell = ⊤ :=
  rfl

@[simp] theorem cellValue_extend_true
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (value : B) (valuation : Fin arity -> B) (cell : Cell arity) :
    cellValue (extendValuation value valuation) (extendCell true cell) =
      value ⊓ cellValue valuation cell := by
  rfl

@[simp] theorem cellValue_extend_false
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (value : B) (valuation : Fin arity -> B) (cell : Cell arity) :
    cellValue (extendValuation value valuation) (extendCell false cell) =
      valueᶜ ⊓ cellValue valuation cell := by
  rfl

/-- The two child cells induced by a new variable reassemble their parent. -/
theorem child_cells_sup_eq_parent
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (value : B) (valuation : Fin arity -> B) (cell : Cell arity) :
    cellValue (extendValuation value valuation) (extendCell true cell) ⊔
        cellValue (extendValuation value valuation) (extendCell false cell) =
      cellValue valuation cell := by
  rw [cellValue_extend_true, cellValue_extend_false]
  simpa only [inf_comm] using
    (sup_inf_inf_compl (x := cellValue valuation cell) (y := value))

/-- Every cell lies below each literal selected by that cell. -/
theorem cellValue_le_literal
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) (cell : Cell arity) (index : Fin arity) :
    cellValue valuation cell ≤
      if cell index then valuation index else (valuation index)ᶜ := by
  induction arity with
  | zero => exact Fin.elim0 index
  | succ arity inductionHypothesis =>
      refine Fin.cases ?_ (fun tailIndex => ?_) index
      · exact inf_le_left
      · exact le_trans inf_le_right
          (inductionHypothesis
            (fun i => valuation i.succ)
            (fun i => cell i.succ) tailIndex)

/-- Distinct Venn cells are disjoint in every Boolean algebra. -/
theorem distinct_cells_inf_eq_bot
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) {left right : Cell arity}
    (different : left ≠ right) :
    cellValue valuation left ⊓ cellValue valuation right = ⊥ := by
  classical
  have differsAt : ∃ index, left index ≠ right index := by
    by_contra noDifference
    apply different
    funext index
    exact Classical.byContradiction (fun atIndex =>
      noDifference ⟨index, atIndex⟩)
  obtain ⟨index, atIndex⟩ := differsAt
  apply bot_unique
  calc
    cellValue valuation left ⊓ cellValue valuation right ≤
        (if left index then valuation index else (valuation index)ᶜ) ⊓
          (if right index then valuation index else (valuation index)ᶜ) :=
      inf_le_inf (cellValue_le_literal valuation left index)
        (cellValue_le_literal valuation right index)
    _ ≤ ⊥ := by
      cases leftValue : left index <;>
        cases rightValue : right index <;>
        simp_all

/-! ## Profiles and their one-variable projection -/

/-- The exact nonzero-cell profile of a valuation. -/
noncomputable def profileOf
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) : Profile arity := by
  classical
  exact fun cell => decide (cellValue valuation cell ≠ ⊥)

@[simp] theorem profileOf_eq_true_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) (cell : Cell arity) :
    profileOf valuation cell = true <-> cellValue valuation cell ≠ ⊥ := by
  classical
  simp [profileOf]

@[simp] theorem profileOf_eq_false_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) (cell : Cell arity) :
    profileOf valuation cell = false <-> cellValue valuation cell = ⊥ := by
  classical
  simp [profileOf]

/-- Forget the newest polarity by joining its two cell-status bits. -/
def project {arity : Nat} (profile : Profile (arity + 1)) : Profile arity :=
  fun cell =>
    profile (extendCell true cell) || profile (extendCell false cell)

/-- A genuinely realized child profile always projects to the original
valuation's profile. -/
theorem profileOf_extend_projects
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (value : B) (valuation : Fin arity -> B) :
    project (profileOf (extendValuation value valuation)) =
      profileOf valuation := by
  classical
  funext cell
  rw [Bool.eq_iff_iff]
  simp only [project, Bool.or_eq_true, profileOf_eq_true_iff]
  rw [← child_cells_sup_eq_parent value valuation cell]
  simp only [ne_eq, sup_eq_bot_iff, not_and_or]

/-! ## Local atomless splitting -/

/-- A nonzero element of an atomless Boolean algebra splits into two
disjoint nonzero pieces whose join is the original element. -/
theorem exists_nonzero_complementary_split
    {B : Type u} [BooleanAlgebra B]
    (gunky : IsGunky B) {parent : B} (parentNonzero : parent ≠ ⊥) :
    ∃ left right : B,
      left ≠ ⊥ ∧ right ≠ ⊥ ∧
      left ⊓ right = ⊥ ∧ left ⊔ right = parent := by
  obtain ⟨left, leftNonzero, leftProper⟩ := gunky parent parentNonzero
  refine ⟨left, parent \ left, leftNonzero, ?_, ?_, ?_⟩
  · exact (sdiff_eq_bot_iff.not.mpr (not_le_of_gt leftProper))
  · rw [inf_sdiff_eq_bot_iff leftProper.le leftProper.le]
  · calc
      left ⊔ parent \ left = parent ⊓ left ⊔ parent \ left := by
        rw [inf_eq_right.mpr leftProper.le]
      _ = parent := sup_inf_sdiff parent left

/-! ## Realizing every compatible child profile -/

/-- Compatibility says that a proposed child profile forgets to the exact
profile of the already fixed parent valuation. -/
def Compatible
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) (child : Profile (arity + 1)) : Prop :=
  project child = profileOf valuation

private theorem parent_nonzero_of_child_true
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    {valuation : Fin arity -> B} {child : Profile (arity + 1)}
    (compatible : Compatible valuation child)
    (cell : Cell arity) (polarity : Bool)
    (childNonzero : child (extendCell polarity cell) = true) :
    cellValue valuation cell ≠ ⊥ := by
  have projected : project child cell = true := by
    cases polarity <;> simp [project, childNonzero]
  have parentProfile : profileOf valuation cell = true := by
    rw [← congrFun compatible cell]
    exact projected
  exact (profileOf_eq_true_iff valuation cell).mp parentProfile

/-- The cell-local part assigned to the new variable.  The only choice is
when both child polarities must be nonzero; atomlessness supplies a proper
part in that case. -/
noncomputable def selectedPart
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity) : B := by
  classical
  by_cases positive : child (extendCell true cell) = true
  · by_cases negative : child (extendCell false cell) = true
    · exact (gunky (cellValue valuation cell)
        (parent_nonzero_of_child_true compatible cell true positive)).choose
    · exact cellValue valuation cell
  · exact ⊥

private theorem selectedPart_both_true_spec
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity)
    (positive : child (extendCell true cell) = true)
    (negative : child (extendCell false cell) = true) :
    selectedPart gunky valuation child compatible cell ≠ ⊥ ∧
      selectedPart gunky valuation child compatible cell <
        cellValue valuation cell := by
  classical
  simp only [selectedPart, dif_pos positive, dif_pos negative]
  exact (gunky (cellValue valuation cell)
    (parent_nonzero_of_child_true compatible cell true positive)).choose_spec

theorem selectedPart_le_cell
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity) :
    selectedPart gunky valuation child compatible cell ≤
      cellValue valuation cell := by
  classical
  by_cases positive : child (extendCell true cell) = true
  · by_cases negative : child (extendCell false cell) = true
    · exact (selectedPart_both_true_spec gunky valuation child compatible
        cell positive negative).2.le
    · simp [selectedPart, positive, negative]
  · simp [selectedPart, positive]

theorem selectedPart_ne_bot_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity) :
    selectedPart gunky valuation child compatible cell ≠ ⊥ <->
      child (extendCell true cell) = true := by
  classical
  by_cases positive : child (extendCell true cell) = true
  · by_cases negative : child (extendCell false cell) = true
    · simp [positive,
        (selectedPart_both_true_spec gunky valuation child compatible
          cell positive negative).1]
    · have parentNonzero :=
        parent_nonzero_of_child_true compatible cell true positive
      simp [selectedPart, positive, negative, parentNonzero]
  · simp [selectedPart, positive]

theorem remainder_ne_bot_iff
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity) :
    cellValue valuation cell \
        selectedPart gunky valuation child compatible cell ≠ ⊥ <->
      child (extendCell false cell) = true := by
  classical
  by_cases positive : child (extendCell true cell) = true
  · by_cases negative : child (extendCell false cell) = true
    · have proper :=
        (selectedPart_both_true_spec gunky valuation child compatible
          cell positive negative).2
      simp only [negative, iff_true]
      exact sdiff_eq_bot_iff.not.mpr (not_le_of_gt proper)
    · simp [selectedPart, positive, negative]
  · by_cases negative : child (extendCell false cell) = true
    · have parentNonzero :=
        parent_nonzero_of_child_true compatible cell false negative
      simp [selectedPart, positive, negative, parentNonzero]
    · have projectedFalse : project child cell = false := by
        simp [project, positive, negative]
      have parentFalse : profileOf valuation cell = false := by
        rw [← congrFun compatible cell]
        exact projectedFalse
      have parentZero :=
        (profileOf_eq_false_iff valuation cell).mp parentFalse
      simp [selectedPart, positive, negative, parentZero]

/-- The global witness is the finite join of its independently selected
parts inside all parent cells. -/
noncomputable def witness
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) : B :=
  Finset.univ.sup (selectedPart gunky valuation child compatible)

/-- Intersecting the global witness with one parent cell recovers exactly
the part selected locally for that cell. -/
theorem witness_inf_cell
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity) :
    witness gunky valuation child compatible ⊓ cellValue valuation cell =
      selectedPart gunky valuation child compatible cell := by
  classical
  apply le_antisymm
  · rw [witness, Finset.sup_inf_distrib_right]
    apply Finset.sup_le
    intro other _member
    by_cases same : other = cell
    · subst same
      exact inf_le_left
    · rw [show selectedPart gunky valuation child compatible other ⊓
          cellValue valuation cell = ⊥ by
        apply bot_unique
        calc
          selectedPart gunky valuation child compatible other ⊓
              cellValue valuation cell ≤
            cellValue valuation other ⊓ cellValue valuation cell :=
              inf_le_inf_right _
                (selectedPart_le_cell gunky valuation child compatible other)
          _ = ⊥ := distinct_cells_inf_eq_bot valuation same]
      exact bot_le
  · apply le_inf
    · exact Finset.le_sup
        (f := fun other => selectedPart gunky valuation child compatible other)
        (Finset.mem_univ cell)
    · exact selectedPart_le_cell gunky valuation child compatible cell

private theorem cell_sdiff_witness_eq_remainder
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) (cell : Cell arity) :
    cellValue valuation cell \ witness gunky valuation child compatible =
      cellValue valuation cell \
        selectedPart gunky valuation child compatible cell := by
  rw [sdiff_eq_sdiff_iff_inf_eq_inf]
  rw [inf_comm, witness_inf_cell]
  exact (inf_eq_right.mpr
    (selectedPart_le_cell gunky valuation child compatible cell)).symm

/-- Every compatible finite child profile is realized by the explicit
atomless witness. -/
theorem profileOf_witness
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1))
    (compatible : Compatible valuation child) :
    profileOf (extendValuation
      (witness gunky valuation child compatible) valuation) = child := by
  classical
  funext extendedCell
  let polarity : Bool := extendedCell 0
  let parentCell : Cell arity := fun index => extendedCell index.succ
  have reconstruct : extendCell polarity parentCell = extendedCell := by
    funext index
    refine Fin.cases ?_ (fun _tailIndex => ?_) index
    · rfl
    · rfl
  rw [← reconstruct]
  cases polarity
  · rw [Bool.eq_iff_iff]
    simp only [profileOf_eq_true_iff, cellValue_extend_false]
    rw [inf_comm, ← sdiff_eq,
      cell_sdiff_witness_eq_remainder,
      remainder_ne_bot_iff]
  · rw [Bool.eq_iff_iff]
    simp only [profileOf_eq_true_iff, cellValue_extend_true]
    rw [witness_inf_cell, selectedPart_ne_bot_iff]

/-- Atomlessness makes the projection equation the exact criterion for
one-variable profile realizability. -/
theorem compatible_iff_exists_extension
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (gunky : IsGunky B) (valuation : Fin arity -> B)
    (child : Profile (arity + 1)) :
    Compatible valuation child <->
      ∃ value : B,
        profileOf (extendValuation value valuation) = child := by
  constructor
  · intro compatible
    exact ⟨witness gunky valuation child compatible,
      profileOf_witness gunky valuation child compatible⟩
  · rintro ⟨value, realized⟩
    unfold Compatible
    rw [← realized, profileOf_extend_projects]

/-- Negative canary: no value can realize a child profile whose projection
disagrees with the fixed parent valuation. -/
theorem no_extension_of_incompatible
    {B : Type u} [BooleanAlgebra B] {arity : Nat}
    (valuation : Fin arity -> B) (child : Profile (arity + 1))
    (incompatible : ¬ Compatible valuation child) :
    ¬ ∃ value : B,
      profileOf (extendValuation value valuation) = child := by
  rintro ⟨value, realized⟩
  apply incompatible
  unfold Compatible
  rw [← realized, profileOf_extend_projects]

#print axioms child_cells_sup_eq_parent
#print axioms distinct_cells_inf_eq_bot
#print axioms profileOf_extend_projects
#print axioms exists_nonzero_complementary_split
#print axioms selectedPart_ne_bot_iff
#print axioms remainder_ne_bot_iff
#print axioms witness_inf_cell
#print axioms profileOf_witness
#print axioms compatible_iff_exists_extension
#print axioms no_extension_of_incompatible

end Mettapedia.GSLT.LanguageDef.AtomlessBooleanProfileExtension
