import Mettapedia.Machines.PolynomialContexts
import Mettapedia.Machines.ShapeCutComposition
import Mettapedia.Machines.OrderedDissection
import Mettapedia.Machines.HybridShapeStore

/-!
# Composing shape-store cuts and ordered cursors

Joined entry point for polynomial context laws, canonical cuts, finite ordered
dissections and compact-plus-row bag semantics. The connection below executes
the dissection of a shape row and then uses the existing reassembler. It proves
that chunked traversal and a change of canonical cut preserve the same ground
term. DAG realizations, unifier universal properties, transducer compilation and
cut optimization are not supplied by this entry point.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ShapeCursorTheory

open ShapeStore ShapeCutComposition OrderedDissection

variable {α : Type}

abbrev RowCursor (α : Type) := Cursor (Skel.holes (α := α)) (Tm α) (Tm α)

def beginRow (r : SizedRow α) : RowCursor α := start (polynomialRowEquiv.symm r)

theorem beginRow_shape (r : SizedRow α) : (beginRow r).shape = r.val.1 := by
  rcases r with ⟨⟨s, ts⟩, h⟩
  rfl

theorem complete_beginRow (r : SizedRow α) : complete id (beginRow r) = r.val.2 := by
  have hr := polynomialRowEquiv.apply_symm_apply r
  cases hp : polynomialRowEquiv.symm r with
  | mk s f =>
    rw [hp] at hr
    unfold beginRow
    rw [hp, complete_start]
    exact congrArg (fun q : SizedRow α => q.val.2) hr

def readback (c : RowCursor α) : Option (Tm α) := reassemble (c.shape, complete id c)

theorem readback_seek (n : Nat) (r : SizedRow α) :
    readback (seek id n (beginRow r)) = reassemble r.val := by
  simp only [readback, seek_shape, complete_seek, beginRow_shape, complete_beginRow]

/-- Cut migration and cursor service can be chosen independently of ground-term readback. -/
theorem recut_cursor_readback (k₁ k₂ : Cut α) (r : CanonicalRow k₁) (n m : Nat) :
    readback (seek id n (beginRow ⟨r.val, canonical_sized k₁ r⟩)) =
      readback (seek id m (beginRow
        ⟨(recut k₁ k₂ r).val, canonical_sized k₂ (recut k₁ k₂ r)⟩)) := by
  rw [readback_seek, readback_seek, recut_reassemble]

/-- Three recursive holes need not be three positions of one binary constructor.
The higher-derivative claim needs the recursive term functor, not only its signature. -/
theorem nested_holes_not_root_positions :
    (Skel.node (.hole : Skel Unit) (.node .hole .hole)).holes = 3 ∧
      ¬ ∃ f : Fin 3 → Fin 2, Function.Injective f := by
  constructor
  · rfl
  · rintro ⟨f, hf⟩
    have hc := Fintype.card_le_of_injective f hf
    norm_num at hc

/-- Disjoint constructor alphabets do not make constraints sharing a variable
independently solvable. Modular algorithms must communicate the substitution. -/
theorem shared_variable_conflict :
    (∃ σ : Nat → Tm (Unit ⊕ Unit), σ 0 = .atom (.inl ())) ∧
    (∃ σ : Nat → Tm (Unit ⊕ Unit), σ 0 = .atom (.inr ())) ∧
    ¬ ∃ σ : Nat → Tm (Unit ⊕ Unit), σ 0 = .atom (.inl ()) ∧ σ 0 = .atom (.inr ()) := by
  refine ⟨⟨fun _ => .atom (.inl ()), rfl⟩, ⟨fun _ => .atom (.inr ()), rfl⟩, ?_⟩
  rintro ⟨σ, hl, hr⟩
  have h := hl.symm.trans hr
  cases h

example : ∃ σ : Nat → Tm (Unit ⊕ Unit), σ 0 = .atom (.inl ()) ∧ σ 1 = .atom (.inr ()) := by
  exact ⟨fun n => if n = 0 then .atom (.inl ()) else .atom (.inr ()), rfl, rfl⟩

#print axioms complete_beginRow
#print axioms readback_seek
#print axioms recut_cursor_readback
#print axioms nested_holes_not_root_positions
#print axioms shared_variable_conflict

end Mettapedia.Machines.ShapeCursorTheory
