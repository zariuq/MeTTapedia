import Mettapedia.CategoryTheory.FinitePowerset
import Mathlib.Data.PFunctor.Univariate.M
import Mathlib.Data.Fintype.EquivFin

/-!
# Coloured trees with finite branching at every action

The polynomial shape records a colour and a branch count for each action.
Its positions are the finite contiguous slots at each action. Actions are
arbitrary, so the complete position carrier need not be finite. The M-type
constructs the whole tree from compatible finite-depth approximations.

Raw successor sets forget slot multiplicity, while `child` retains the
actual occurrence at each supplied slot. Finite enumeration of an actual
coalgebra constructs an independent raw coiteration.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTree

universe a u v

variable (Actions : Type a) (Colours : Type u)

def polynomial : PFunctor.{max a u, a} where
  A := Colours × (Actions → Nat)
  B shape := (action : Actions) × Fin (shape.2 action)

abbrev Raw := PFunctor.M (polynomial Actions Colours)

variable {Actions Colours}

def root (tree : Raw Actions Colours) : Colours := (PFunctor.M.dest tree).1.1

def count (tree : Raw Actions Colours) (action : Actions) : Nat :=
  (PFunctor.M.dest tree).1.2 action

def child (tree : Raw Actions Colours) (action : Actions) (slot : Fin (count tree action)) :
    Raw Actions Colours := (PFunctor.M.dest tree).2 ⟨action, slot⟩

def step (tree : Raw Actions Colours) (action : Actions) : Finset (Raw Actions Colours) :=
  FinitePowerset.map (child tree action) Finset.univ

theorem mem_step (tree : Raw Actions Colours) (action : Actions)
    (next : Raw Actions Colours) :
    next ∈ step tree action ↔ ∃ slot, child tree action slot = next := by
  simp only [step, FinitePowerset.mem_map, Finset.mem_univ, true_and]

theorem child_mem_step (tree : Raw Actions Colours) (action : Actions)
    (slot : Fin (count tree action)) : child tree action slot ∈ step tree action :=
  (mem_step tree action _).2 ⟨slot, rfl⟩

def node (colour : Colours) (counts : Actions → Nat)
    (children : (action : Actions) → Fin (counts action) → Raw Actions Colours) :
    Raw Actions Colours :=
  PFunctor.M.mk ⟨⟨colour, counts⟩, fun slot => children slot.1 slot.2⟩

@[simp] theorem root_node (colour : Colours) (counts : Actions → Nat)
    (children : (action : Actions) → Fin (counts action) → Raw Actions Colours) :
    root (node colour counts children) = colour := rfl

@[simp] theorem count_node (colour : Colours) (counts : Actions → Nat)
    (children : (action : Actions) → Fin (counts action) → Raw Actions Colours)
    (action : Actions) : count (node colour counts children) action = counts action := rfl

@[simp] theorem child_node (colour : Colours) (counts : Actions → Nat)
    (children : (action : Actions) → Fin (counts action) → Raw Actions Colours)
    (action : Actions) (slot : Fin (counts action)) :
    child (node colour counts children) action slot = children action slot := rfl

@[simp] theorem step_node (colour : Colours) (counts : Actions → Nat)
    (children : (action : Actions) → Fin (counts action) → Raw Actions Colours)
    (action : Actions) :
    step (node colour counts children) action =
      FinitePowerset.map (children action) Finset.univ := rfl

def enumerate {States : Type v} (successors : Finset States) (slot : Fin successors.card) :
    States := (successors.equivFin.symm slot).val

theorem enumerate_mem {States : Type v} (successors : Finset States)
    (slot : Fin successors.card) : enumerate successors slot ∈ successors :=
  (successors.equivFin.symm slot).property

theorem enumerate_surjective {States : Type v} (successors : Finset States)
    (state : States) (member : state ∈ successors) :
    ∃ slot, enumerate successors slot = state := by
  refine ⟨successors.equivFin ⟨state, member⟩, ?_⟩
  exact congrArg Subtype.val (successors.equivFin.symm_apply_apply ⟨state, member⟩)

theorem enumerate_image {States : Type v} (successors : Finset States) :
    FinitePowerset.map (enumerate successors) Finset.univ = successors := by
  apply Finset.ext
  intro state
  rw [FinitePowerset.mem_map]
  constructor
  · rintro ⟨slot, _, rfl⟩
    exact enumerate_mem successors slot
  · intro member
    obtain ⟨slot, same⟩ := enumerate_surjective successors state member
    exact ⟨slot, Finset.mem_univ _, same⟩

def rawLayer {States : Type v} (successors : States → Actions → Finset States)
    (colour : States → Colours) (state : States) : (polynomial Actions Colours).Obj States :=
  ⟨⟨colour state, fun action => (successors state action).card⟩,
    fun slot => enumerate (successors state slot.1) slot.2⟩

def coiterateRaw {States : Type v} (successors : States → Actions → Finset States)
    (colour : States → Colours) (state : States) : Raw Actions Colours :=
  PFunctor.M.corec (rawLayer successors colour) state

theorem dest_coiterateRaw {States : Type v} (successors : States → Actions → Finset States)
    (colour : States → Colours) (state : States) :
    PFunctor.M.dest (coiterateRaw successors colour state) =
      ⟨⟨colour state, fun action => (successors state action).card⟩,
        fun slot => coiterateRaw successors colour
          (enumerate (successors state slot.1) slot.2)⟩ :=
  PFunctor.M.dest_corec (rawLayer successors colour) state

@[simp] theorem root_coiterateRaw {States : Type v}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (state : States) : root (coiterateRaw successors colour state) = colour state := by
  exact congrArg (fun layer => layer.1.1) (dest_coiterateRaw successors colour state)

@[simp] theorem count_coiterateRaw {States : Type v}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (state : States) (action : Actions) :
    count (coiterateRaw successors colour state) action = (successors state action).card := by
  exact congrArg (fun layer => layer.1.2 action) (dest_coiterateRaw successors colour state)

/-- The complete successor image, rather than one selected branch. -/
theorem step_coiterateRaw {States : Type v}
    (successors : States → Actions → Finset States) (colour : States → Colours)
    (state : States) (action : Actions) :
    step (coiterateRaw successors colour state) action =
      FinitePowerset.map (coiterateRaw successors colour) (successors state action) := by
  change FinitePowerset.map
    (fun slot => (PFunctor.M.dest (coiterateRaw successors colour state)).2 ⟨action, slot⟩)
    Finset.univ = _
  rw [dest_coiterateRaw]
  exact (FinitePowerset.map_compose (enumerate (successors state action))
    (coiterateRaw successors colour) Finset.univ).symm.trans
      (congrArg (FinitePowerset.map (coiterateRaw successors colour))
        (enumerate_image (successors state action)))

end Mettapedia.CategoryTheory.FiniteActionTree
