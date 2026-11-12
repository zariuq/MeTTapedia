import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.PatternSolverControls

/-!
# The occurs check is the null "no well-founded solution"

The store `X ≐ arr X gnd` is read in two models.

* **Well-founded terms.** Finite trees: no finite tree `T` satisfies `T = arr T gnd`
  (`FTree.no_loop`). In the codes of the solver the store `X par ≐ arr (X par) gnd` is refuted
  with the reason `noWellFoundedSolution` and has no solution (`well_founded_refutation`).
* **Rational trees.** Trees are labelings of paths (`ITree`), finite or infinite. The equation
  `T = arr T gnd` has exactly one solution (`loopTree_solves`, `loopTree_unique`), it is rational:
  it has finitely many distinct subtrees (`loopTree_rational`), and it is no finite tree
  (`loopTree_not_finite`). Reading the solver's codes in trees (`interp`), the same store is solved
  by sending `X` to the constant family at that tree (`rational_solution`), and every tree solution
  of the store sends `X`, at every parameter, to that tree (`rational_solution_unique`).

So the occurs check does not say "no solution": it says that every solution is a non-well-founded
tree. That is why its refutation carries its own reason, distinct from a clash. Every clash the
solver refutes (two different heads among the parameter, the ground type, a universe and an arrow,
`Refutes.clash`) has no solution in trees either (`clash_in_trees`): at the empty tree as the
parameter, the two sides already differ at the root.

Positive controls: the rational-tree solution and its uniqueness. Negative controls: no finite
solution; the clash `gnd ≐ arr gnd gnd` has no tree solution (`ground_arrow_in_trees`), nor does
`par ≐ gnd` (`parameter_ground_in_trees`), although its sides are solved by one tree at the
parameter `gndT`, because a tree solution must hold at every parameter.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels

namespace OccursNull

/-- The labels of tree nodes; `none` marks a path with no node. -/
inductive Label where
  | none : Label
  | par : Label
  | gnd : Label
  | sort (n : Nat) : Label
  | arr : Label
  deriving DecidableEq, Repr

/-- A tree, finite or infinite: the label at each path (`false` goes left, `true` right). -/
abbrev ITree := List Bool → Label

/-- The tree `arr A B`. -/
def arrT (A B : ITree) : ITree
  | [] => .arr
  | false :: p => A p
  | true :: p => B p

/-- A leaf. -/
def leaf (l : Label) : ITree
  | [] => l
  | _ :: _ => .none

/-- The ground leaf. -/
abbrev gndT : ITree := leaf .gnd

/-- The empty tree. -/
def emptyT : ITree := fun _ => .none

/-- The subtree at a path. -/
def subtree (t : ITree) (p : List Bool) : ITree := fun q => t (p ++ q)

/-! ## Finite trees: the well-founded model -/

/-- Finite trees over the same labels. -/
inductive FTree where
  | par : FTree
  | gnd : FTree
  | arr (A B : FTree) : FTree
  deriving DecidableEq, Repr

def FTree.size : FTree → Nat
  | par => 1
  | gnd => 1
  | arr A B => A.size + B.size + 1

/-- **No finite tree solves `T = arr T gnd`.** -/
theorem FTree.no_loop (T : FTree) : T ≠ .arr T .gnd := by
  intro h
  have := congrArg FTree.size h
  simp only [FTree.size] at this
  omega

/-- The tree of a finite tree. -/
def FTree.toITree : FTree → ITree
  | par => leaf .par
  | gnd => leaf .gnd
  | arr A B => arrT A.toITree B.toITree

/-- A finite tree has no node below its size. -/
theorem FTree.toITree_deep : ∀ (T : FTree) (p : List Bool), T.size ≤ p.length → T.toITree p = .none
  | par, [], h => by simp [FTree.size] at h
  | par, _ :: _, _ => rfl
  | gnd, [], h => by simp [FTree.size] at h
  | gnd, _ :: _, _ => rfl
  | arr _ _, [], h => by simp [FTree.size] at h
  | arr A _, false :: p, h => by
      simp only [FTree.size, List.length_cons] at h
      exact FTree.toITree_deep A p (by omega)
  | arr _ B, true :: p, h => by
      simp only [FTree.size, List.length_cons] at h
      exact FTree.toITree_deep B p (by omega)

/-! ## The rational solution -/

/-- **The solution of `T = arr T gnd`**: `arr` along the left spine, `gnd` at each right child. -/
def loopTree : ITree
  | [] => .arr
  | false :: p => loopTree p
  | [true] => .gnd
  | true :: _ :: _ => .none

theorem loopTree_solves : loopTree = arrT loopTree gndT := by
  funext p
  match p with
  | [] => rfl
  | false :: _ => rfl
  | [true] => rfl
  | true :: _ :: _ => rfl

/-- **The solution is unique.** -/
theorem loopTree_unique (T : ITree) (h : T = arrT T gndT) : T = loopTree := by
  funext p
  induction p with
  | nil => rw [h]; rfl
  | cons b p ih =>
      cases b with
      | false =>
          rw [h]
          exact ih
      | true =>
          rw [h]
          cases p with
          | nil => rfl
          | cons _ _ => rfl

/-- **The solution is rational**: each of its subtrees is one of three trees. -/
theorem loopTree_rational (p : List Bool) :
    subtree loopTree p = loopTree ∨ subtree loopTree p = gndT ∨ subtree loopTree p = emptyT := by
  induction p with
  | nil => exact Or.inl rfl
  | cons b p ih =>
      cases b with
      | false =>
          have same : subtree loopTree (false :: p) = subtree loopTree p := rfl
          rw [same]
          exact ih
      | true =>
          cases p with
          | nil =>
              refine Or.inr (Or.inl ?_)
              funext q
              match q with
              | [] => rfl
              | _ :: _ => rfl
          | cons _ _ =>
              refine Or.inr (Or.inr ?_)
              funext q
              rfl

theorem loopTree_spine (n : Nat) : loopTree (List.replicate n false) = .arr := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- **The solution is not well-founded**: it is the tree of no finite tree. -/
theorem loopTree_not_finite (T : FTree) : T.toITree ≠ loopTree := by
  intro h
  have deep := FTree.toITree_deep T (List.replicate T.size false) (by simp)
  rw [h, loopTree_spine] at deep
  cases deep

/-! ## The solver's store, read in trees -/

open CumulativeCodes

/-- Read a code in trees: the parameter as `P`, each unknown as a function of trees. -/
def interp (v : Nat → Nat) (ρ : Nat → ITree → ITree) (P : ITree) : Tm → ITree
  | .par => P
  | .gnd => gndT
  | .sort l => leaf (.sort (Level.value v l))
  | .arr A B => arrT (interp v ρ P A) (interp v ρ P B)
  | .app W t => ρ W (interp v ρ P t)

/-- An assignment of tree functions solves an equation when both sides agree at every parameter. -/
def TreeSolves (v : Nat → Nat) (ρ : Nat → ITree → ITree) (e : Tm × Tm) : Prop :=
  ∀ P : ITree, interp v ρ P e.1 = interp v ρ P e.2

/-- **Rational trees solve the occurs store**: `X` as the constant family at `loopTree`. -/
theorem rational_solution (v : Nat → Nat) :
    TreeSolves v (fun _ _ => loopTree) (SolverControls.X.1, SolverControls.loop.1) := by
  intro P
  show loopTree = arrT loopTree gndT
  exact loopTree_solves

/-- **The store's tree solution is unique**: every assignment of tree functions that solves the
occurs store sends `X`, at every parameter, to `loopTree`. -/
theorem rational_solution_unique (v : Nat → Nat) (ρ : Nat → ITree → ITree)
    (solves : TreeSolves v ρ (SolverControls.X.1, SolverControls.loop.1)) (P : ITree) :
    ρ 0 P = loopTree :=
  loopTree_unique (ρ 0 P) (solves P)

/-- **Well-founded codes refute it**, with the reason "no well-founded solution". -/
theorem well_founded_refutation (v : Nat → Nat) :
    Refutes v [(SolverControls.X, SolverControls.loop)] .noWellFoundedSolution ∧
      ¬ (frames v).Solvable [(SolverControls.X, SolverControls.loop)] :=
  SolverControls.occurs_refuted v

/-- The solver's head (`Tm.head?`) that a root label shows: the parameter read at the empty tree
shows no node. -/
def rootHead : Label → Nat
  | .none => 0
  | .par => 0
  | .gnd => 1
  | .sort _ => 2
  | .arr => 3

/-- At the empty tree as the parameter, the root of a code with a head shows that head. -/
theorem rootHead_interp (v : Nat → Nat) (ρ : Nat → ITree → ITree) :
    ∀ (s : Tm) {k : Nat}, Tm.head? s = some k → rootHead (interp v ρ emptyT s []) = k
  | .par, _, h => by cases h; rfl
  | .gnd, _, h => by cases h; rfl
  | .sort _, _, h => by cases h; rfl
  | .arr _ _, _, h => by cases h; rfl
  | .app _ _, _, h => by cases h

/-- **A clash has no solution in trees either**: every equation the solver refutes as a clash
(`Refutes.clash`: two different heads) has no tree solution, so its reason is not the occurs
check's. -/
theorem clash_in_trees (v : Nat → Nat) (ρ : Nat → ITree → ITree) {s t : Tm} {h h' : Nat}
    (hs : Tm.head? s = some h) (ht : Tm.head? t = some h') (ne : h ≠ h') :
    ¬ TreeSolves v ρ (s, t) := by
  intro solves
  apply ne
  rw [← rootHead_interp v ρ s hs, ← rootHead_interp v ρ t ht]
  exact congrArg rootHead (congrFun (solves emptyT) [])

/-- Negative control: the clash `gnd ≐ arr gnd gnd` has no tree solution. -/
theorem ground_arrow_in_trees (v : Nat → Nat) (ρ : Nat → ITree → ITree) :
    ¬ TreeSolves v ρ (SolverControls.ground.1, SolverControls.arrow.1) :=
  clash_in_trees v ρ (s := .gnd) (t := .arr .gnd .gnd) rfl rfl (by decide)

/-- Negative control: `par ≐ gnd` is a clash with no tree solution, although at the single
parameter `gndT` its two sides are the same tree: a tree solution holds at every parameter. -/
theorem parameter_ground_in_trees (v : Nat → Nat) (ρ : Nat → ITree → ITree) :
    ¬ TreeSolves v ρ (.par, .gnd) ∧ interp v ρ gndT .par = interp v ρ gndT .gnd :=
  ⟨clash_in_trees v ρ (s := .par) (t := .gnd) rfl rfl (by decide), rfl⟩

end OccursNull

#print axioms OccursNull.FTree.no_loop
#print axioms OccursNull.loopTree_unique
#print axioms OccursNull.loopTree_rational
#print axioms OccursNull.loopTree_not_finite
#print axioms OccursNull.rational_solution
#print axioms OccursNull.rational_solution_unique
#print axioms OccursNull.well_founded_refutation
#print axioms OccursNull.clash_in_trees
#print axioms OccursNull.ground_arrow_in_trees
#print axioms OccursNull.parameter_ground_in_trees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels
