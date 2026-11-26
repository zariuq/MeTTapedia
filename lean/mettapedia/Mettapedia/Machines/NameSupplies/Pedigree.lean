import Mettapedia.Machines.NameSupplies.Pools

/-!
# Positions in the spawn tree

A *pedigree* (Leiserson, Schardl and Sukha, *Deterministic parallel random-number generation for
dynamic-multithreading platforms*, PPoPP 2012) places a supply in the spawn tree: the root, and
below a position its children `0, 1, …` in the order they are split off.  A supply at position `π`
gives the names `(π, 0), (π, 1), …` (`Pedigree.draw`).

As a local discipline (`pedigreeDiscipline`), the parts of a fork are the next children of the
forking supply, and the successor of two holders that end together is the next child of the second.
Every fork and every join moves one level down the tree (`pedigree_piece_depth`,
`pedigree_join_depth`), so a supply that keeps forking reaches every depth
(`pedigree_kept_depth`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.NameSupplies

/-- A supply of the spawn tree: its position (the ranks of the splits from the root, the most
recent first), the names it has given and the children it has split off. -/
structure Pedigree where
  position : List ℕ
  given : ℕ
  children : ℕ
  deriving DecidableEq, Repr

namespace Pedigree

/-- The root of the spawn tree. -/
def root : Pedigree := ⟨[], 0, 0⟩

/-- The `i`-th next child of a supply. -/
def child (supply : Pedigree) (i : ℕ) : Pedigree := ⟨(supply.children + i) :: supply.position, 0, 0⟩

/-- The next name of a supply: its position and the number of names it gave before. -/
def draw (supply : Pedigree) : (List ℕ × ℕ) × Pedigree :=
  ((supply.position, supply.given), { supply with given := supply.given + 1 })

theorem child_depth (supply : Pedigree) (i : ℕ) :
    (supply.child i).position.length = supply.position.length + 1 := rfl

end Pedigree

/-- **The spawn-tree discipline.** -/
def pedigreeDiscipline : Discipline Pedigree (List ℕ × ℕ) where
  draw := Pedigree.draw
  piece supply _ i := supply.child i
  join _ second := second.child 0

theorem pedigree_piece_depth (supply : Pedigree) (parts i : ℕ) :
    (pedigreeDiscipline.piece supply parts i).position.length = supply.position.length + 1 := rfl

theorem pedigree_join_depth (first second : Pedigree) :
    (pedigreeDiscipline.join first second).position.length = second.position.length + 1 := rfl

/-- **A supply that keeps forking reaches every depth.** -/
theorem pedigree_kept_depth (k : ℕ) :
    (kept pedigreeDiscipline Pedigree.root k).position.length = k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [kept, pedigree_piece_depth, ih]

end Mettapedia.Machines.NameSupplies
