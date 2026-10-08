import Mettapedia.CategoryTheory.FiniteActionTreeCofree
import Mettapedia.CategoryTheory.FinitePowersetRelation
import Mettapedia.CategoryTheory.FinitePowersetWeakPullback

/-!
# Final observations for indexed labelwise finite coalgebras

Uncoloured unordered action trees are final for the actual indexed finite
behaviour functor. Independently specified two-sided relations construct
coalgebras on their complete related-pair carriers. Both projections are
coalgebra morphisms, so finality identifies exactly the pairs admitted by
some such relation. Base and index universes remain independent, and the
action alphabet need not be finite.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.FiniteActionTreeFinalSemantics

open _root_.CategoryTheory
open FiniteActionTreeCofree

universe b i u

variable (Base : Type b) (Index : Base → Type i)
    (Actions : ∀ base, Index base → Type u)

def finalObject : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions) where
  V := fun base index => FiniteActionTree.Tree (Actions base index) PUnit.{u + 1}
  str _ _ := ↾FiniteActionTree.Tree.step

def observe (object : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions)) :
    object ⟶ finalObject Base Index Actions where
  f base index := ↾(FiniteActionTree.Tree.coiterate (object.str base index)
    (fun _ => PUnit.unit))
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro state
    funext action
    exact (FiniteActionTree.Tree.step_coiterate (object.str base index)
      (fun _ => PUnit.unit) state action).symm

theorem observe_unique (object : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (mapping : object ⟶ finalObject Base Index Actions) :
    mapping = observe Base Index Actions object := by
  apply Endofunctor.Coalgebra.ext
  funext base index
  apply ConcreteCategory.hom_ext
  apply FiniteActionTree.Tree.coiterate_unique (object.str base index)
    (fun _ => PUnit.unit) (mapping.f base index) (fun _ => Subsingleton.elim _ _)
  intro state action
  exact (congrArg (fun arrow => arrow base index state action) mapping.h).symm

def isFinal : Limits.IsTerminal (finalObject Base Index Actions) :=
  Limits.IsTerminal.ofUniqueHom (observe Base Index Actions)
    (observe_unique Base Index Actions)

theorem observe_natural
    {first second : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions)}
    (mapping : first ⟶ second) :
    mapping ≫ observe Base Index Actions second = observe Base Index Actions first :=
  observe_unique Base Index Actions first _

theorem observe_readout (object : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (base : Base) (index : Index base) (state : object.V base index) :
    (observe Base Index Actions object).f base index state =
      FiniteActionTree.Tree.coiterate (object.str base index) (fun _ => PUnit.unit) state := rfl

theorem observe_step (object : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (base : Base) (index : Index base) (state : object.V base index)
    (action : Actions base index) :
    FiniteActionTree.Tree.step ((observe Base Index Actions object).f base index state) action =
      FinitePowerset.map ((observe Base Index Actions object).f base index)
        (object.str base index state action) :=
  (congrArg (fun arrow => arrow base index state action)
    (observe Base Index Actions object).h).symm

abbrev Relation (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions)) :=
  ∀ base index, left.V base index → right.V base index → Prop

def Admitted (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right) : Prop :=
  ∀ base index state other, relation base index state other → ∀ action,
    FinitePowerset.Related (relation base index)
      (left.str base index state action) (right.str base index other action)

abbrev Pairs (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right) : Families.{b, i, u} Base Index :=
  fun base index => FinitePowersetRelation.Pair (relation base index)

def relationCoalgebra (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right) :
    Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions) where
  V := Pairs Base Index Actions left right relation
  str base index := ↾(fun pair action =>
    FinitePowersetRelation.matching (relation base index)
      (left.str base index pair.val.1 action) (right.str base index pair.val.2 action))

def firstMorphism (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right)
    (admitted : Admitted Base Index Actions left right relation) :
    relationCoalgebra Base Index Actions left right relation ⟶ left where
  f base index := ↾(FinitePowersetRelation.first (relation base index))
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    exact FinitePowersetRelation.matching_first (relation base index) _ _
      (admitted base index pair.val.1 pair.val.2 pair.property action)

def secondMorphism (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right)
    (admitted : Admitted Base Index Actions left right relation) :
    relationCoalgebra Base Index Actions left right relation ⟶ right where
  f base index := ↾(FinitePowersetRelation.second (relation base index))
  h := by
    funext base index
    apply ConcreteCategory.hom_ext
    intro pair
    funext action
    exact FinitePowersetRelation.matching_second (relation base index) _ _
      (admitted base index pair.val.1 pair.val.2 pair.property action)

@[simp] theorem first_readout
    (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right)
    (admitted : Admitted Base Index Actions left right relation)
    (base : Base) (index : Index base)
    (pair : Pairs Base Index Actions left right relation base index) :
    (firstMorphism Base Index Actions left right relation admitted).f base index pair =
      pair.val.1 := rfl

@[simp] theorem second_readout
    (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (relation : Relation Base Index Actions left right)
    (admitted : Admitted Base Index Actions left right relation)
    (base : Base) (index : Index base)
    (pair : Pairs Base Index Actions left right relation base index) :
    (secondMorphism Base Index Actions left right relation admitted).f base index pair =
      pair.val.2 := rfl

def Bisimilar (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (base : Base) (index : Index base) (state : left.V base index)
    (other : right.V base index) : Prop :=
  ∃ relation : Relation Base Index Actions left right,
    Admitted Base Index Actions left right relation ∧ relation base index state other

def Kernel (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions)) :
    Relation Base Index Actions left right := fun base index state other =>
  (observe Base Index Actions left).f base index state =
    (observe Base Index Actions right).f base index other

/-- Whole successor-image equality earns all original matches in both directions. -/
theorem kernel_admitted
    (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions)) :
    Admitted Base Index Actions left right (Kernel Base Index Actions left right) := by
  intro base index state other same action
  apply (FinitePowersetWeakPullback.related_iff_matching
    ((observe Base Index Actions left).f base index)
    ((observe Base Index Actions right).f base index)
    (left.str base index state action) (right.str base index other action)).2
  have observations := congrArg (fun tree => FiniteActionTree.Tree.step tree action) same
  rw [observe_step, observe_step] at observations
  exact observations

theorem observe_of_admitted
    {left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions)}
    (relation : Relation Base Index Actions left right)
    (admitted : Admitted Base Index Actions left right relation)
    (base : Base) (index : Index base)
    {state : left.V base index} {other : right.V base index}
    (held : relation base index state other) :
    (observe Base Index Actions left).f base index state =
      (observe Base Index Actions right).f base index other := by
  let pair : Pairs Base Index Actions left right relation base index := ⟨(state, other), held⟩
  have first := congrArg (fun arrow => arrow.f base index pair)
    (observe_natural Base Index Actions
      (firstMorphism Base Index Actions left right relation admitted))
  have second := congrArg (fun arrow => arrow.f base index pair)
    (observe_natural Base Index Actions
      (secondMorphism Base Index Actions left right relation admitted))
  exact first.trans second.symm

/-- Bisimilarity is specified independently, before the final observation kernel. -/
theorem kernel_iff_bisimilar
    (left right : Endofunctor.Coalgebra (behavior.{b, i, u, u} Base Index Actions))
    (base : Base) (index : Index base) (state : left.V base index)
    (other : right.V base index) :
    (observe Base Index Actions left).f base index state =
        (observe Base Index Actions right).f base index other ↔
      Bisimilar Base Index Actions left right base index state other := by
  constructor
  · intro same
    exact ⟨Kernel Base Index Actions left right,
      kernel_admitted Base Index Actions left right, same⟩
  · rintro ⟨relation, admitted, held⟩
    exact observe_of_admitted Base Index Actions relation admitted base index held

end Mettapedia.CategoryTheory.FiniteActionTreeFinalSemantics
