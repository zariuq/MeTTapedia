import Mettapedia.CategoryTheory.PartialActionTree
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Monad.Adjunction
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Types.Basic

/-!
# Cofree deterministic coalgebras on coloured action trees

The indexed family of coloured partial trees is right adjoint to the
forgetful functor of labelwise deterministic coalgebras. Its counit reads
the root colour; its comultiplication labels each enabled path by the
actual subtree at that path. All action carriers are arbitrary.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory.PartialActionTreeCofree

open _root_.CategoryTheory

universe b i u

variable (Base : Type b) (Index : Base → Type i)
    (Actions : ∀ base, Index base → Type u)

/-- Families carry independent base and sort indices. -/
abbrev Families := (base : Base) → Index base → Type u

/-- Labelwise deterministic behavior, including disabled actions. -/
def behavior : Families Base Index ⥤ Families Base Index where
  obj family base index := Actions base index → Option (family base index)
  map mapping base index := ↾(fun reading action => (reading action).map (mapping base index))
  map_id family := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro reading
    funext action
    change (reading action).map id = reading action
    simp
  map_comp earlier later := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro reading
    funext action
    change (reading action).map (later base index ∘ earlier base index) =
      ((reading action).map (earlier base index)).map (later base index)
    exact (Option.map_map ..).symm

/-- Colours vary over families; enabled paths remain unchanged under maps. -/
def trees : Families Base Index ⥤ Families Base Index where
  obj family base index := PartialActionTree (Actions base index) (family base index)
  map mapping base index := ↾(PartialActionTree.map (mapping base index))
  map_id family := by
    funext base index
    apply ConcreteCategory.hom_ext
    exact PartialActionTree.map_id
  map_comp earlier later := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro tree
    exact (PartialActionTree.map_comp (earlier base index) (later base index) tree).symm

/-- The actual one-step coalgebra on complete trees. -/
def cofreeObject (family : Families Base Index) :
    Endofunctor.Coalgebra (behavior Base Index Actions) where
  V := (trees Base Index Actions).obj family
  str _ _ := ↾PartialActionTree.step

/-- Root-colour relabeling is a genuine tree coalgebra map. -/
def cofreeMap {first second : Families Base Index} (mapping : first ⟶ second) :
    cofreeObject Base Index Actions first ⟶ cofreeObject Base Index Actions second where
  f := (trees Base Index Actions).map mapping
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro tree
    funext action
    exact (PartialActionTree.step_map (mapping base index) tree action).symm

/-- The actual cofree functor, retaining all complete subtrees. -/
def cofree : Families Base Index ⥤ Endofunctor.Coalgebra (behavior Base Index Actions) where
  obj := cofreeObject Base Index Actions
  map := cofreeMap Base Index Actions
  map_id family := by
    apply Endofunctor.Coalgebra.ext
    exact (trees Base Index Actions).map_id family
  map_comp earlier later := by
    apply Endofunctor.Coalgebra.ext
    exact (trees Base Index Actions).map_comp earlier later

/-- Every supplied colour map extends by actual finite-path coiteration. -/
def extend (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) (colour : object.V ⟶ family) :
    object ⟶ cofreeObject Base Index Actions family where
  f base index := ↾(PartialActionTree.coiterate (object.str base index) (colour base index))
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro state
    funext action
    exact (PartialActionTree.coiterate_step (object.str base index) (colour base index)
      state action).symm

/-- A colour-preserving coalgebra map is determined by its complete path readings. -/
theorem extend_unique (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) (colour : object.V ⟶ family)
    (mapping : object ⟶ cofreeObject Base Index Actions family)
    (roots : ∀ base index state, (mapping.f base index state).root = colour base index state) :
    mapping = extend Base Index Actions object family colour := by
  apply Endofunctor.Coalgebra.ext
  funext base index
  apply ConcreteCategory.hom_ext
  have steps : ∀ state action,
      (mapping.f base index state).step action =
        (object.str base index state action).map (mapping.f base index) := by
    intro state action
    exact (congrArg (fun arrow => arrow base index state action) mapping.h).symm
  exact congrFun (PartialActionTree.coiterate_unique (object.str base index) (colour base index)
    (mapping.f base index) (roots base index) steps)

/-- The actual cofree universal equivalence; its inverse reads the supplied root. -/
def homEquiv (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) :
    (object.V ⟶ family) ≃ (object ⟶ cofreeObject Base Index Actions family) where
  toFun := extend Base Index Actions object family
  invFun mapping base index := ↾(fun state => (mapping.f base index state).root)
  left_inv colour := by
    rfl
  right_inv mapping := by
    exact (extend_unique Base Index Actions object family _ mapping (fun _ _ _ => rfl)).symm

/-- Deterministic coalgebras have the explicitly constructed cofree right adjoint. -/
def adjunction : Endofunctor.Coalgebra.forget (behavior Base Index Actions) ⊣
    cofree Base Index Actions :=
  Adjunction.mkOfHomEquiv
    { homEquiv := homEquiv Base Index Actions
      homEquiv_naturality_left_symm := by
        intros
        rfl
      homEquiv_naturality_right := by
        intro object first second colour mapping
        exact (extend_unique Base Index Actions object second (colour ≫ mapping) _
          (fun _ _ _ => rfl)).symm }

/-- Adjunction transposition reads the actual coiteration construction. -/
theorem transpose_readout (object : Endofunctor.Coalgebra (behavior Base Index Actions))
    (family : Families Base Index) (colour : object.V ⟶ family)
    (base : Base) (index : Index base) (state : object.V base index) :
    (((adjunction Base Index Actions).homEquiv object family) colour).f base index state =
      PartialActionTree.coiterate (object.str base index) (colour base index) state := by
  unfold adjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]
  rfl

/-- The derived comonad counit reads the complete supplied root colour. -/
theorem derived_counit_readout (family : Families Base Index) (base : Base) (index : Index base)
    (tree : PartialActionTree (Actions base index) (family base index)) :
    ((adjunction Base Index Actions).toComonad.ε.app family) base index tree = tree.root := rfl

/-- Adjunction-derived duplication is the actual tree of all complete subtrees. -/
theorem derived_comultiplication_readout (family : Families Base Index)
    (base : Base) (index : Index base)
    (tree : PartialActionTree (Actions base index) (family base index)) :
    ((adjunction Base Index Actions).toComonad.δ.app family) base index tree =
      PartialActionTree.duplicate tree := by
  change PartialActionTree.coiterate PartialActionTree.step id tree = _
  exact (congrFun (PartialActionTree.coiterate_unique PartialActionTree.step id
    PartialActionTree.duplicate (fun _ => rfl) PartialActionTree.duplicate_step) tree).symm

/-- The explicit cofree comonad: counit reads a colour and duplication exposes subtrees. -/
def comonad : Comonad (Families Base Index) where
  toFunctor := trees Base Index Actions
  ε :=
    { app family base index := ↾PartialActionTree.root
      naturality := by intros; rfl }
  δ :=
    { app family base index := ↾PartialActionTree.duplicate
      naturality := by
        intro first second mapping
        funext base index
        apply ConcreteCategory.hom_ext
        exact PartialActionTree.duplicate_map (mapping base index) }
  coassoc family := by
    funext base index
    apply ConcreteCategory.hom_ext
    exact PartialActionTree.duplicate_coassoc
  left_counit family := by rfl
  right_counit family := by
    funext base index
    apply ConcreteCategory.hom_ext
    exact PartialActionTree.duplicate_counit

end Mettapedia.CategoryTheory.PartialActionTreeCofree
