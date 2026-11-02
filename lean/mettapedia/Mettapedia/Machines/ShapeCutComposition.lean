import Mettapedia.Machines.ShapeStore
import Mathlib.Data.PFunctor.Univariate.Basic
import Mathlib.Data.List.OfFn

/-!
# Composing changes of shape-store cuts

The polynomial of recursive skeletons has one position per hole. Its values
are exactly length-correct rows. Reassembly of all such rows is not injective:
the same term admits several cuts. Restricting to the image of a chosen cut
gives actual equivalences, and their composition agrees with the existing model's
reassembly followed by decomposition. No cost or runtime correspondence follows
from these representation laws alone.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeCutComposition

open ShapeStore

variable {α : Type}

/-- The hole interface of a recursive skeleton. This is not the signature's
k-th derivative: its positions can occur at several constructor depths. -/
abbrev skeletonPolynomial (α : Type) : PFunctor.{0, 0} where
  A := Skel α
  B := fun s => Fin s.holes

abbrev SizedRow (α : Type) := {r : Row α // r.2.length = r.1.holes}

/-- An indexed tuple of hole contents is exactly a length-correct list row. -/
def polynomialRowEquiv : skeletonPolynomial α (Tm α) ≃ SizedRow α where
  toFun := fun ⟨s, f⟩ => ⟨(s, List.ofFn f), List.length_ofFn⟩
  invFun := fun ⟨⟨s, ts⟩, h⟩ => ⟨s, fun i => ts.get ⟨i.val, by
    change ts.length = s.holes at h
    have hi : i.val < s.holes := i.isLt
    omega⟩⟩
  left_inv := by
    rintro ⟨s, f⟩
    dsimp only
    congr 1
    funext i
    exact List.get_ofFn f ⟨i.val, by rw [List.length_ofFn]; exact i.isLt⟩
  right_inv := by
    rintro ⟨⟨s, ts⟩, h⟩
    apply Subtype.ext
    dsimp only
    congr 1
    apply List.ext_getElem
    · exact List.length_ofFn.trans h.symm
    · intro i h₁ h₂
      exact List.getElem_ofFn h₁

theorem fill_exists (s : Skel α) (ts : List (Tm α)) (h : s.holes ≤ ts.length) :
    ∃ t rest, fill s ts = some (t, rest) := by
  induction s generalizing ts with
  | hole =>
    cases ts with
    | nil => simp [Skel.holes] at h
    | cons t ts => exact ⟨t, ts, rfl⟩
  | atom a => exact ⟨.atom a, ts, rfl⟩
  | node l r ihl ihr =>
    have hleft : l.holes ≤ ts.length := by simp only [Skel.holes] at h; omega
    obtain ⟨tl, mid, hl⟩ := ihl ts hleft
    have hlen := fill_length hl
    have hright : r.holes ≤ mid.length := by simp only [Skel.holes] at h; omega
    obtain ⟨tr, rest, hr⟩ := ihr mid hright
    exact ⟨.node tl tr, rest, by simp [fill, hl, hr]⟩

/-- Exact arity, not a choice of cut, suffices for total reassembly. -/
theorem reassemble_exists (r : SizedRow α) : ∃ t, reassemble r.val = some t := by
  obtain ⟨t, rest, hfill⟩ := fill_exists r.val.1 r.val.2 (le_of_eq r.property.symm)
  have hlen := fill_length hfill
  have hrest : rest = [] := by
    have := r.property
    cases rest with
    | nil => rfl
    | cons x xs => simp only [List.length_cons] at hlen; omega
  subst rest
  exact ⟨t, by simp [reassemble, hfill]⟩

theorem sized_of_reassemble {r : Row α} {t : Tm α} (h : reassemble r = some t) :
    r.2.length = r.1.holes := by
  unfold reassemble at h
  split at h
  · rename_i u hu
    simpa using fill_length hu
  · simp at h

/-- The exact image of a selected cut, excluding noncanonical encodings. -/
abbrev CanonicalRow (k : Cut α) := Set.range k.d

noncomputable def encodingEquiv (k : Cut α) : Tm α ≃ CanonicalRow k :=
  Equiv.ofInjective k.d k.injective

@[simp] theorem encodingEquiv_val (k : Cut α) (t : Tm α) :
    (encodingEquiv k t).val = k.d t := rfl

theorem reassemble_canonical (k : Cut α) (r : CanonicalRow k) :
    reassemble r.val = some ((encodingEquiv k).symm r) := by
  have h := k.sec ((encodingEquiv k).symm r)
  have he : k.d ((encodingEquiv k).symm r) = r.val :=
    Equiv.apply_ofInjective_symm k.injective r
  rwa [he] at h

theorem canonical_sized (k : Cut α) (r : CanonicalRow k) :
    r.val.2.length = r.val.1.holes := sized_of_reassemble (reassemble_canonical k r)

/-- A canonical stored row has a genuine polynomial tuple presentation. -/
noncomputable def canonicalExpansion (k : Cut α) (r : CanonicalRow k) :
    skeletonPolynomial α (Tm α) := polynomialRowEquiv.symm ⟨r.val, canonical_sized k r⟩

theorem canonicalExpansion_row (k : Cut α) (r : CanonicalRow k) :
    (polynomialRowEquiv (canonicalExpansion k r)).val = r.val := by
  exact congrArg Subtype.val (polynomialRowEquiv.apply_symm_apply
    ⟨r.val, canonical_sized k r⟩)

/-- Change of cut on canonical row representations. -/
noncomputable def recut (k₁ k₂ : Cut α) : CanonicalRow k₁ ≃ CanonicalRow k₂ :=
  (encodingEquiv k₁).symm.trans (encodingEquiv k₂)

@[simp] theorem recut_encoded (k₁ k₂ : Cut α) (t : Tm α) :
    recut k₁ k₂ (encodingEquiv k₁ t) = encodingEquiv k₂ t := by simp [recut]

theorem recut_via_reassembly (k₁ k₂ : Cut α) (r : CanonicalRow k₁) :
    (reassemble r.val).map k₂.d = some (recut k₁ k₂ r).val := by
  rw [reassemble_canonical]
  rfl

@[simp] theorem recut_identity (k : Cut α) (r : CanonicalRow k) : recut k k r = r := by
  simp [recut]

/-- Re-cutting through an intermediate representation has no semantic residue. -/
@[simp] theorem recut_composition (k₁ k₂ k₃ : Cut α) (r : CanonicalRow k₁) :
    recut k₂ k₃ (recut k₁ k₂ r) = recut k₁ k₃ r := by simp [recut]

theorem recut_reassemble (k₁ k₂ : Cut α) (r : CanonicalRow k₁) :
    reassemble (recut k₁ k₂ r).val = reassemble r.val := by
  rw [reassemble_canonical, reassemble_canonical]
  simp [recut]

theorem recut_match [DecidableEq α] (k₁ k₂ : Cut α) (p : Pat α) (r : CanonicalRow k₁) :
    matchRow p (recut k₁ k₂ r).val = matchRow p r.val := by
  rw [matchRow_of_reassemble p (reassemble_canonical k₂ _),
    matchRow_of_reassemble p (reassemble_canonical k₁ _)]
  simp [recut]

/-- The new equivalences implement the existing bag transfer, not a new operation. -/
theorem transfer_singleton (k₁ k₂ : Cut α) (r : CanonicalRow k₁) :
    transfer k₂ {r.val} = {(recut k₁ k₂ r).val} := by
  have hrow := Equiv.apply_ofInjective_symm k₁.injective r
  change k₁.d ((encodingEquiv k₁).symm r) = r.val at hrow
  calc
    transfer k₂ {r.val} = transfer k₂ (store k₁ {((encodingEquiv k₁).symm r)}) := by
      simp only [store, Multiset.map_singleton, hrow]
    _ = store k₂ {((encodingEquiv k₁).symm r)} := transfer_store k₁ k₂ _
    _ = {(recut k₁ k₂ r).val} := rfl

theorem transfer_composition (k₁ k₂ k₃ : Cut α) (S : Multiset (Row α)) :
    transfer k₃ (transfer k₂ (transfer k₁ S)) = transfer k₃ S := by
  simp [transfer, denote_store]

/-- Neither all well-sized rows nor all recursive skeletons give a unique cut. -/
theorem reassembly_not_injective :
    ¬ Function.Injective (reassemble (α := Unit)) := by
  intro h
  have bad := h (a₁ := (.hole, [.atom ()])) (a₂ := (.atom (), [])) rfl
  cases bad

example :
    (recut (rootCut : Cut String) noCut (encodingEquiv rootCut (.atom "a"))).val =
      (.atom "a", []) := by
  simp [noCut_d, Tm.toSkel]

#print axioms polynomialRowEquiv
#print axioms recut_via_reassembly
#print axioms recut_composition
#print axioms recut_match
#print axioms reassembly_not_injective

end Mettapedia.Machines.ShapeCutComposition
