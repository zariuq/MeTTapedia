import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.TypedPublicationSetControls

/-!
# Independent block coherence in the actual set-family model

The frame uses three extensions of `familiesCwf`, with each family reindexed
from the common base. Blocks are arbitrary varying families and may themselves
contain dependent pairs. The two exchanges are explicit tuple rearrangements,
with a universal reconstruction property, braid, and change-of-base laws.
Typed publication views retain their full family and section through the
comparison. No interpretation of arbitrary syntactic rewrite rules is assumed.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetFamilyCoherence

open Mettapedia.GSLT.Core.ContextualLadder
open Mettapedia.TypeTheory.ContextualTypedPublication

universe u

abbrev model := familiesCwf.{u}

variable {Γ Δ Observer : Type u} (A B C : Γ → Type u)

abbrev frame : Type u :=
  model.ext (model.ext (model.ext Γ A) (fun point => B point.1)) (fun point => C point.1.1)

def base (point : frame A B C) : Γ := point.1.1.1
def first (point : frame A B C) : A (base A B C point) := point.1.1.2
def second (point : frame A B C) : B (base A B C point) := point.1.2
def third (point : frame A B C) : C (base A B C point) := point.2

def assemble (substitution : Observer → Γ)
    (a : ∀ point, A (substitution point)) (b : ∀ point, B (substitution point))
    (c : ∀ point, C (substitution point)) : Observer → frame A B C :=
  fun point => ⟨⟨⟨substitution point, a point⟩, b point⟩, c point⟩

/-- A map to the actual iterated extension is exactly a common base map
and three sections. This keeps all points of each fibre. -/
def sectionsEquiv : (Observer → frame A B C) ≃
    Σ substitution : Observer → Γ,
      (∀ point, A (substitution point)) × (∀ point, B (substitution point)) × (∀ point, C (substitution point)) where
  toFun map := ⟨base A B C ∘ map,
    (fun point => first A B C (map point)), (fun point => second A B C (map point)),
    (fun point => third A B C (map point))⟩
  invFun data := assemble A B C data.1 data.2.1 data.2.2.1 data.2.2.2
  left_inv map := by
    funext point
    change ⟨⟨⟨(map point).1.1.1, (map point).1.1.2⟩, (map point).1.2⟩, (map point).2⟩ = map point
    rcases map point with ⟨⟨⟨origin, a⟩, b⟩, c⟩
    rfl
  right_inv data := by rcases data with ⟨substitution, a, b, c⟩; rfl

def swapFirst (point : frame A B C) : frame B A C :=
  ⟨⟨⟨base A B C point, second A B C point⟩, first A B C point⟩, third A B C point⟩

def swapLast (point : frame A B C) : frame A C B :=
  ⟨⟨⟨base A B C point, first A B C point⟩, third A B C point⟩, second A B C point⟩

def swapFirstEquiv : frame A B C ≃ frame B A C where
  toFun := swapFirst A B C
  invFun := swapFirst B A C
  left_inv point := by rcases point with ⟨⟨⟨origin, a⟩, b⟩, c⟩; rfl
  right_inv point := by rcases point with ⟨⟨⟨origin, b⟩, a⟩, c⟩; rfl

def swapLastEquiv : frame A B C ≃ frame A C B where
  toFun := swapLast A B C
  invFun := swapLast A C B
  left_inv point := by rcases point with ⟨⟨⟨origin, a⟩, b⟩, c⟩; rfl
  right_inv point := by rcases point with ⟨⟨⟨origin, a⟩, c⟩, b⟩; rfl

def leftRoute : frame A B C → frame C B A :=
  swapFirst B C A ∘ swapLast B A C ∘ swapFirst A B C

def rightRoute : frame A B C → frame C B A :=
  swapLast C A B ∘ swapFirst A C B ∘ swapLast A B C

theorem braid : leftRoute A B C = rightRoute A B C := rfl

def rebase (substitution : Δ → Γ) (point : frame (A ∘ substitution) (B ∘ substitution) (C ∘ substitution)) :
    frame A B C := ⟨⟨⟨substitution point.1.1.1, point.1.1.2⟩, point.1.2⟩, point.2⟩

theorem swapFirst_natural (substitution : Δ → Γ) :
    swapFirst A B C ∘ rebase A B C substitution =
      rebase B A C substitution ∘ swapFirst (A ∘ substitution) (B ∘ substitution) (C ∘ substitution) := rfl

theorem swapLast_natural (substitution : Δ → Γ) :
    swapLast A B C ∘ rebase A B C substitution =
      rebase A C B substitution ∘ swapLast (A ∘ substitution) (B ∘ substitution) (C ∘ substitution) := rfl

theorem view_braid (view : View model (frame C B A)) :
    view.reindex (leftRoute A B C) = view.reindex (rightRoute A B C) := congrArg view.reindex (braid A B C)

theorem license_braid (view : View model (frame C B A)) (substitution : Observer → frame A B C) :
    (view.reindex (leftRoute A B C)).At substitution ↔
      (view.reindex (rightRoute A B C)).At substitution := by rw [view_braid]

theorem readout_braid (view : View model (frame C B A)) (substitution : Observer → frame A B C)
    (licensed : (view.reindex (leftRoute A B C)).At substitution) :
    (view.reindex (leftRoute A B C)).readout substitution licensed =
      (view.reindex (rightRoute A B C)).readout substitution ((license_braid A B C view substitution).mp licensed) := rfl

namespace Controls

def Index (size : Nat) := Fin size
def DependentBlock (size : Nat) := Σ index : Fin size, Fin (index.val + 1)

abbrev Context := frame Index Index DependentBlock

def point : Context := ⟨⟨⟨2, ⟨0, by decide⟩⟩, ⟨1, by decide⟩⟩, ⟨⟨1, by decide⟩, ⟨0, by decide⟩⟩⟩

theorem nonconstant : ¬ ∃ carrier : Type, ∀ size, Index size = carrier := by
  rintro ⟨carrier, same⟩
  have zeroOne : Fin 0 = Fin 1 := (same 0).trans (same 1).symm
  exact Fin.elim0 (cast zeroOne.symm (⟨0, by decide⟩ : Fin 1))

theorem exchange_is_not_identity : swapFirst Index Index DependentBlock point ≠ point := by
  intro same
  have indices := congrArg (fun value : Context => value.1.1.2.val) same
  change (1 : Nat) = 0 at indices
  cases indices

theorem internal_dependency_retained :
    (swapFirst Index Index DependentBlock point).2 = point.2 := rfl

theorem empty_fibre : ¬ ∃ value : Context, base Index Index DependentBlock value = 0 := by
  rintro ⟨value, zero⟩
  exact Fin.elim0 (Fin.cast zero (first Index Index DependentBlock value))

def oldContext (value : Context) : SetControls.Context := ⟨value.1.1.1, value.1.1.2⟩

def indexView (size : Nat) : View model Context := (SetControls.view size).reindex oldContext

theorem learned_index_view (size : Nat) {Observer : Type} (substitution : Observer → Context)
    (solved : SetControls.frame.Models (oldContext ∘ substitution) (SetControls.information size)) :
    (indexView size).At substitution :=
  ((SetControls.view size).at_reindex_iff oldContext substitution).mpr
    (SetControls.source_license size (oldContext ∘ substitution) solved)

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetFamilyCoherence

#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetFamilyCoherence.sectionsEquiv
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetFamilyCoherence.readout_braid
#print axioms Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Interface.TypedPublication.SetFamilyCoherence.Controls.nonconstant
