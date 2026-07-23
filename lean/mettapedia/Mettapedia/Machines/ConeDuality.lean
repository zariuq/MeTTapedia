import Mathlib.Logic.Relation
import Mathlib.Data.Set.Lattice
import Mathlib.Order.GaloisConnection.Basic

/-!
# Forward and backward cones over a production relation

A production system is a relation `r : α → α → Prop` on states/cells/facts
(`r x y` = "one step of production turns `x` into, or contributes to, `y`").
Two evaluation disciplines correspond to the two lightcones of `r`:

* **forward cone** (`forwardCone`): everything producible from a set of
  sources — data-driven, write-propagating, "wavefront" evaluation
  (write-space forward chaining). Characterized as a least fixed point /
  induction principle (`forwardCone_least`), i.e. the algebra side.
* **backward cone** (`backwardCone`): everything that can contribute to a
  set of goals — demand-driven evaluation. It is literally the forward cone
  of the reversed relation (`backwardCone_eq_forwardCone_swap`), i.e. the
  same construction run on the opposite category.

The two cones generate the two classical Galois connections of reachability
(existential image ⊣ universal preimage, and symmetrically), which are the
possibility/safety (◇/□) modal adjunctions; this is the order-theoretic
skeleton behind derived behavioral modalities on rewrite systems.

Finally `workCone X Y = forwardCone X ∩ backwardCone Y` is the "work
diamond": the region a demand-driven run over goals `Y` explores inside a
data-driven run from sources `X`, and
`forwardCone_inter_nonempty_iff` states the push/pull equivalence — running
writes forward from `X` and checking `Y` succeeds iff demanding backward
from `Y` meets `X`.

No project-specific axioms are introduced.
-/

namespace Mettapedia.Machines

open Relation Set

variable {α : Type*}

/-- Zero-or-more production steps. -/
abbrev Reaches (r : α → α → Prop) : α → α → Prop := Relation.ReflTransGen r

/-- Reversing reachability reverses the relation. -/
theorem reaches_swap {r : α → α → Prop} {a b : α} (h : Reaches r a b) :
    Reaches (Function.swap r) b a := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact Relation.ReflTransGen.head hstep ih

theorem reaches_swap_iff {r : α → α → Prop} {a b : α} :
    Reaches (Function.swap r) b a ↔ Reaches r a b := by
  constructor
  · intro h
    have := reaches_swap (r := Function.swap r) h
    simpa [Function.swap] using this
  · exact reaches_swap

/-- The forward (production) cone of a source set: everything reachable. -/
def forwardCone (r : α → α → Prop) (X : Set α) : Set α :=
  {y | ∃ x ∈ X, Reaches r x y}

/-- The backward (demand) cone of a goal set: everything that can reach it. -/
def backwardCone (r : α → α → Prop) (Y : Set α) : Set α :=
  {x | ∃ y ∈ Y, Reaches r x y}

@[simp] theorem mem_forwardCone {r : α → α → Prop} {X : Set α} {y : α} :
    y ∈ forwardCone r X ↔ ∃ x ∈ X, Reaches r x y := Iff.rfl

@[simp] theorem mem_backwardCone {r : α → α → Prop} {Y : Set α} {x : α} :
    x ∈ backwardCone r Y ↔ ∃ y ∈ Y, Reaches r x y := Iff.rfl

/-- Cone duality: demand is production in the opposite direction. -/
theorem backwardCone_eq_forwardCone_swap (r : α → α → Prop) (Y : Set α) :
    backwardCone r Y = forwardCone (Function.swap r) Y := by
  ext x
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, reaches_swap h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, reaches_swap_iff.mp h⟩

theorem subset_forwardCone (r : α → α → Prop) (X : Set α) :
    X ⊆ forwardCone r X :=
  fun x hx => ⟨x, hx, .refl⟩

theorem forwardCone_mono (r : α → α → Prop) {X X' : Set α} (h : X ⊆ X') :
    forwardCone r X ⊆ forwardCone r X' := by
  rintro y ⟨x, hx, hr⟩
  exact ⟨x, h hx, hr⟩

/-- The forward cone is closed under production. -/
theorem forwardCone_closed {r : α → α → Prop} {X : Set α} {x y : α}
    (hx : x ∈ forwardCone r X) (hstep : r x y) : y ∈ forwardCone r X := by
  obtain ⟨x₀, hx₀, hr⟩ := hx
  exact ⟨x₀, hx₀, hr.tail hstep⟩

/-- Least-fixed-point / induction principle: the forward cone is the least
set containing the sources and closed under production. This is the
Knaster–Tarski face of data-driven evaluation. -/
theorem forwardCone_least {r : α → α → Prop} {X S : Set α}
    (hX : X ⊆ S) (hcl : ∀ x ∈ S, ∀ y, r x y → y ∈ S) :
    forwardCone r X ⊆ S := by
  rintro y ⟨x, hx, hr⟩
  induction hr with
  | refl => exact hX hx
  | tail _ hstep ih => exact hcl _ ih _ hstep

/-! ## The two reachability adjunctions (the ◇ ⊣ □ pairs) -/

/-- Safety region: states all of whose reachable futures stay inside `Y`
(the universal preimage / weakest precondition of reachability). -/
def alwaysWithin (r : α → α → Prop) (Y : Set α) : Set α :=
  {x | ∀ y, Reaches r x y → y ∈ Y}

/-- Provenance region: states all of whose possible pasts lie inside `X`
(the universal image). -/
def onlyFrom (r : α → α → Prop) (X : Set α) : Set α :=
  {y | ∀ x, Reaches r x y → x ∈ X}

/-- Production ⊣ safety: pushing writes forward lands inside `Y` iff the
sources start in the safety region of `Y`. -/
theorem gc_forward (r : α → α → Prop) :
    GaloisConnection (forwardCone r) (alwaysWithin r) := by
  intro X Y
  constructor
  · intro h x hx y hxy
    exact h ⟨x, hx, hxy⟩
  · rintro h y ⟨x, hx, hxy⟩
    exact h hx y hxy

/-- Demand ⊣ provenance: pulling demand backward lands inside `X` iff the
goals lie in the provenance region of `X`. -/
theorem gc_backward (r : α → α → Prop) :
    GaloisConnection (backwardCone r) (onlyFrom r) := by
  intro Y X
  constructor
  · intro h y hy x hxy
    exact h ⟨y, hy, hxy⟩
  · rintro h x ⟨y, hy, hxy⟩
    exact h hy x hxy

/-! ## Wavefronts: the eager evaluation front, one step at a time -/

/-- One production step applied to a whole set. -/
def stepImage (r : α → α → Prop) (X : Set α) : Set α :=
  {y | ∃ x ∈ X, r x y}

/-- The `n`-step wavefront of eager, data-driven evaluation. -/
def wavefront (r : α → α → Prop) (X : Set α) : ℕ → Set α
  | 0 => X
  | n + 1 => wavefront r X n ∪ stepImage r (wavefront r X n)

theorem wavefront_mono_succ (r : α → α → Prop) (X : Set α) (n : ℕ) :
    wavefront r X n ⊆ wavefront r X (n + 1) :=
  Set.subset_union_left

theorem wavefront_subset_forwardCone (r : α → α → Prop) (X : Set α) :
    ∀ n, wavefront r X n ⊆ forwardCone r X := by
  intro n
  induction n with
  | zero => exact subset_forwardCone r X
  | succ n ih =>
    intro y hy
    rcases hy with hy | ⟨x, hx, hstep⟩
    · exact ih hy
    · exact forwardCone_closed (ih hx) hstep

/-- The forward cone is exactly the union of all finite wavefronts: eager
evaluation exhausts production in the limit. -/
theorem forwardCone_eq_iUnion_wavefront (r : α → α → Prop) (X : Set α) :
    forwardCone r X = ⋃ n, wavefront r X n := by
  ext y
  constructor
  · rintro ⟨x, hx, hr⟩
    induction hr with
    | refl => exact Set.mem_iUnion.mpr ⟨0, hx⟩
    | tail _ hstep ih =>
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ih
      exact Set.mem_iUnion.mpr ⟨n + 1, Or.inr ⟨_, hn, hstep⟩⟩
  · intro h
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp h
    exact wavefront_subset_forwardCone r X n hn

/-! ## The work diamond: what lazy evaluation explores -/

/-- The work cone between sources `X` and demands `Y`: reachable from the
sources AND relevant to the goals. Demand-driven evaluation confines its
exploration to this diamond. -/
def workCone (r : α → α → Prop) (X Y : Set α) : Set α :=
  forwardCone r X ∩ backwardCone r Y

theorem workCone_subset_forwardCone (r : α → α → Prop) (X Y : Set α) :
    workCone r X Y ⊆ forwardCone r X :=
  Set.inter_subset_left

theorem workCone_subset_backwardCone (r : α → α → Prop) (X Y : Set α) :
    workCone r X Y ⊆ backwardCone r Y :=
  Set.inter_subset_right

/-- Push/pull equivalence: propagating writes forward from `X` and testing
the goals is the same success condition as demanding backward from `Y` and
testing the sources. Data-driven and demand-driven evaluation answer the
same reachability question from opposite ends of the work diamond. -/
theorem forwardCone_inter_nonempty_iff (r : α → α → Prop) (X Y : Set α) :
    (forwardCone r X ∩ Y).Nonempty ↔ (X ∩ backwardCone r Y).Nonempty := by
  constructor
  · rintro ⟨z, ⟨x, hx, hxz⟩, hzY⟩
    exact ⟨x, hx, ⟨z, hzY, hxz⟩⟩
  · rintro ⟨x, hxX, ⟨y, hy, hxy⟩⟩
    exact ⟨y, ⟨x, hxX, hxy⟩, hy⟩

/-- Goal-meeting is equivalent to a nonempty work diamond containing a goal
point; in particular an empty work cone means demand-driven evaluation can
soundly refuse without exploring anything else. -/
theorem goal_reached_iff_workCone_meets_goal (r : α → α → Prop) (X Y : Set α) :
    (forwardCone r X ∩ Y).Nonempty ↔ (workCone r X Y ∩ Y).Nonempty := by
  constructor
  · rintro ⟨z, hz, hzY⟩
    exact ⟨z, ⟨hz, ⟨z, hzY, .refl⟩⟩, hzY⟩
  · rintro ⟨z, ⟨hzF, _⟩, hzY⟩
    exact ⟨z, hzF, hzY⟩

end Mettapedia.Machines
