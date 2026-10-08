import Mettapedia.CategoryTheory.FiniteActionTreeCoiteration
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Pi.Basic

/-!
# The constructed cofree adjunction and finite-action-tree comonad

Coloured unordered trees are genuinely cofree for labelwise finitely
branching coalgebras. The hom equivalence extends a supplied colour map by
the constructed coiteration, and its inverse reads the actual root colour.
The adjunction derives an actual comonad whose comultiplication labels each
node by its whole subtree. Base and sort indices have independent sizes;
actions are arbitrary and no total finite-support restriction is present.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTreeCofree

open _root_.CategoryTheory
open FiniteActionTree

universe b i u

variable (Base : Type b) (Index : Base → Type i)
    (Actions : ∀ base, Index base → Type u)

abbrev Families := (base : Base) → Index base → Type u

def behavior : Families Base Index ⥤ Families Base Index where
  obj family base index := Actions base index → Finset (family base index)
  map mapping base index := ↾(fun reading action =>
    FinitePowerset.map (mapping base index) (reading action))
  map_id family := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro reading
    funext action
    exact FinitePowerset.map_identity (reading action)
  map_comp earlier later := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro reading
    funext action
    exact (FinitePowerset.map_compose (earlier base index) (later base index)
      (reading action)).symm

def trees : Families Base Index ⥤ Families Base Index where
  obj family base index := Tree (Actions base index) (family base index)
  map mapping base index := ↾(Tree.map (mapping base index))
  map_id family := by
    funext base index
    apply ConcreteCategory.hom_ext
    exact Tree.map_id
  map_comp earlier later := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro tree
    exact (Tree.map_comp (earlier base index) (later base index) tree).symm

def cofreeObject (family : Families Base Index) :
    Endofunctor.Coalgebra (behavior Base Index Actions) where
  V := (trees Base Index Actions).obj family
  str _ _ := ↾Tree.step

def cofreeMap {first second : Families Base Index} (mapping : first ⟶ second) :
    cofreeObject Base Index Actions first ⟶ cofreeObject Base Index Actions second where
  f := (trees Base Index Actions).map mapping
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro tree
    funext action
    exact (Tree.step_map (mapping base index) tree action).symm

def cofree : Families Base Index ⥤ Endofunctor.Coalgebra (behavior Base Index Actions) where
  obj := cofreeObject Base Index Actions
  map := cofreeMap Base Index Actions
  map_id family := by
    apply Endofunctor.Coalgebra.ext
    exact (trees Base Index Actions).map_id family
  map_comp earlier later := by
    apply Endofunctor.Coalgebra.ext
    exact (trees Base Index Actions).map_comp earlier later

def extend (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) (colour : object.V ⟶ family) :
    object ⟶ cofreeObject Base Index Actions family where
  f base index := ↾(Tree.coiterate (object.str base index) (colour base index))
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro state
    funext action
    exact (Tree.step_coiterate (object.str base index) (colour base index) state action).symm

theorem extend_unique (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) (colour : object.V ⟶ family)
    (mapping : object ⟶ cofreeObject Base Index Actions family)
    (roots : ∀ base index state, Tree.root (mapping.f base index state) =
      colour base index state) :
    mapping = extend Base Index Actions object family colour := by
  apply Endofunctor.Coalgebra.ext
  funext base index
  apply ConcreteCategory.hom_ext
  apply Tree.coiterate_unique (object.str base index) (colour base index)
    (mapping.f base index) (roots base index)
  intro state action
  exact (congrArg (fun arrow => arrow base index state action) mapping.h).symm

def homEquiv (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) :
    (object.V ⟶ family) ≃ (object ⟶ cofreeObject Base Index Actions family) where
  toFun := extend Base Index Actions object family
  invFun mapping base index := ↾(fun state => Tree.root (mapping.f base index state))
  left_inv colour := by
    funext base index
    apply ConcreteCategory.hom_ext
    exact Tree.root_coiterate (object.str base index) (colour base index)
  right_inv mapping :=
    (extend_unique Base Index Actions object family _ mapping (fun _ _ _ => rfl)).symm

def adjunction : Endofunctor.Coalgebra.forget (behavior Base Index Actions) ⊣
    cofree Base Index Actions :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv Base Index Actions
      homEquiv_naturality_left_symm := by
        intros
        rfl
      homEquiv_naturality_right := by
        intro object first second colour mapping
        apply Eq.symm
        apply extend_unique Base Index Actions object second (colour ≫ mapping)
        intro base index state
        change Tree.root (Tree.map (mapping base index)
          (Tree.coiterate (object.str base index) (colour base index) state)) = _
        rw [Tree.root_map]
        exact congrArg (fun value => mapping base index value)
          (Tree.root_coiterate (object.str base index) (colour base index) state) }

theorem transpose_readout (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) (colour : object.V ⟶ family)
    (base : Base) (index : Index base) (state : object.V base index) :
    (((adjunction Base Index Actions).homEquiv object family) colour).f base index state =
      Tree.coiterate (object.str base index) (colour base index) state := by
  unfold adjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- An actual comonad, derived from the proved cofree universal property. -/
def comonad : Comonad (Families Base Index) := (adjunction Base Index Actions).toComonad

theorem counit_readout (family : Families Base Index) (base : Base) (index : Index base)
    (tree : Tree (Actions base index) (family base index)) :
    ((comonad Base Index Actions).ε.app family) base index tree = Tree.root tree := rfl

theorem comultiplication_readout (family : Families Base Index)
    (base : Base) (index : Index base)
    (tree : Tree (Actions base index) (family base index)) :
    ((comonad Base Index Actions).δ.app family) base index tree = Tree.duplicate tree := rfl

theorem comultiplication_root (family : Families Base Index)
    (base : Base) (index : Index base)
    (tree : Tree (Actions base index) (family base index)) :
    Tree.root (((comonad Base Index Actions).δ.app family) base index tree) = tree :=
  Tree.root_duplicate tree

theorem comultiplication_successors (family : Families Base Index)
    (base : Base) (index : Index base)
    (tree : Tree (Actions base index) (family base index)) (action : Actions base index) :
    Tree.step (((comonad Base Index Actions).δ.app family) base index tree) action =
      FinitePowerset.map Tree.duplicate (Tree.step tree action) :=
  Tree.step_duplicate tree action

end Mettapedia.CategoryTheory.FiniteActionTreeCofree
