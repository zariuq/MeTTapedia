import Mettapedia.Cybernetics.DistinctionCalculus.Basic

/-!
# Event grammar for the history calculus

`dcalculus_v2` §4: evolution, fork, merge and erasure form histories. This
module records that grammar as inductive data, the three elementary Livšic
loops, and the copy/merge Frobenius no-go. It is not a costed operational
semantics and it does not identify histories that share an input–output map.

The operational carrier for rewrite histories is `GSLT.Causality.Trace`.
Costs that vanish on closed paths live in `GSLT.Dynamics.CostExactness`.
d-calc `erase` deletes a node; Meredith's erasure forgets history. Rho
has no genuine delete, so its exactness test is the global loop law, not
the three local copy/erase loops.
-/

set_option autoImplicit false

universe u

namespace Mettapedia.Cybernetics.DistinctionCalculus.History

/-- Primitive events on a node set. -/
inductive Event (V : Type u) where
  | evolve (x : V)
  | fork (x : V)
  | merge (x y : V)
  | erase (x : V)
  deriving DecidableEq, Repr

/-- Histories as the free sequential/parallel algebra on events. Sharing is
not quotiented; a DAG presentation would identify more. -/
inductive Hist (V : Type u) where
  | empty
  | singleton (e : Event V)
  | seq (first second : Hist V)
  | par (first second : Hist V)
  deriving DecidableEq, Repr

variable {V : Type u}

/-- Fork then erase at the same node: `Δ_x ε_x`. -/
def forkErase (x : V) : Hist V :=
  .seq (.singleton (.fork x)) (.singleton (.erase x))

/-- Fork, evolve, erase the successor name. The successor is a separate
node argument because the event grammar does not include `T` as data. -/
def forkEvolveErase (x tx : V) : Hist V :=
  .seq (.singleton (.fork x))
    (.seq (.singleton (.evolve x)) (.singleton (.erase tx)))

/-- Fork both arguments, merge, erase the join name: `Δ_x Δ_y ⋆_{xy} ε_{x⋆y}`. -/
def forkMergeErase (x y xy : V) : Hist V :=
  .seq (.singleton (.fork x))
    (.seq (.singleton (.fork y))
      (.seq (.singleton (.merge x y)) (.singleton (.erase xy))))

/-- Diagonal copy on a cartesian product. -/
def diagonal {X : Type u} (x : X) : X × X := (x, x)

/-- The first Frobenius law with diagonal copy forces `m(x,y) = x`. -/
theorem frobenius_forces_left_projection {X : Type u} (m : X → X → X)
    (frobenius : ∀ x y, diagonal (m x y) = (x, m x y)) :
    ∀ x y, m x y = x := by
  intro x y
  exact congrArg Prod.fst (frobenius x y)

/-- The mirror Frobenius law forces `m(x,y) = y`. -/
theorem frobenius_forces_right_projection {X : Type u} (m : X → X → X)
    (mirror : ∀ x y, diagonal (m x y) = (m x y, y)) :
    ∀ x y, m x y = y := by
  intro x y
  exact congrArg Prod.snd (mirror x y)

/-- No merge on a type with two distinct points is Frobenius-compatible with
diagonal copy. `dcalculus_v2`, Proposition "Copy compatibility" (ii). -/
theorem no_frobenius_merge {X : Type u} (m : X → X → X)
    (frobenius : ∀ x y, diagonal (m x y) = (x, m x y))
    (mirror : ∀ x y, diagonal (m x y) = (m x y, y)) :
    ∀ x y : X, x = y := by
  intro x y
  calc
    x = m x y := (frobenius_forces_left_projection m frobenius x y).symm
    _ = y := frobenius_forces_right_projection m mirror x y

/-- Copy of a merge is the merge of the copies: naturality of the diagonal,
always true. `dcalculus_v2`, Proposition "Copy compatibility" (i). -/
theorem copy_of_merge {X : Type u} (m : X → X → X) (x y : X) :
    diagonal (m x y) =
      (fun p : (X × X) × (X × X) => (m p.1.1 p.2.1, m p.1.2 p.2.2))
        ((diagonal x, diagonal y)) :=
  rfl

end Mettapedia.Cybernetics.DistinctionCalculus.History
