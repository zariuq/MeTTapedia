import Mettapedia.Machines.TIsa.Continuation

/-!
# Data projection and reconstruction of controlled resource firings

A continuation edge attaches a linear control cell to an existing recipe.
Its data firing projects to that same recipe, and any guarded data firing
can be lifted back with the declared successor. This reuses the existing
resource system for memory effects as well as scalar operations.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.TIsa.Control
open Cells CellEffects
universe u
variable {Key : Type u} [DecidableEq Key]

def scopedKeys (activation : Nat) (keys : Finset Key) : Finset (Location Key) :=
  insert (.inl activation) (keys.image Sum.inr)
def dataValues (values : Location Key → Word) : Key → Word := fun key => values (.inr key)
def extendValues (edge : Edge Key) (before : Location Key → Word) (data : Key → Word) : Location Key → Word
  | .inl activation => if activation = edge.activation then edge.next else before (.inl activation)
  | .inr key => data key

theorem Edge.support_eq (edge : Edge Key) :
    edge.recipe.support = scopedKeys edge.activation edge.effect.support := by
  ext location
  cases location <;> simp [Recipe.support,Recipe.writes,Edge.recipe,scopedKeys,List.mem_toFinset,List.mem_map]

theorem Edge.data_support (edge : Edge Key) (keys : Finset Key)
    (included : edge.recipe.support ⊆ scopedKeys edge.activation keys) : edge.effect.support ⊆ keys := by
  intro key member
  have lifted : Sum.inr key ∈ edge.recipe.support := by rw [edge.support_eq];simp [scopedKeys,member]
  simpa [scopedKeys] using included lifted

theorem Edge.project_firing (edge : Edge Key) (keys : Finset Key) (before : Location Key → Word)
    (following : Multiset (Cell (Location Key)))
    (step : (profile [edge.recipe]).theory.rewrites (encode (scopedKeys edge.activation keys) before) following) :
    ∃ after : Location Key → Word,
      before (.inl edge.activation) = edge.point ∧ after (.inl edge.activation) = edge.next ∧
      following = encode (scopedKeys edge.activation keys) after ∧
      (profile [edge.effect]).theory.rewrites (encode keys (dataValues before)) (encode keys (dataValues after)) := by
  obtain ⟨recipe,member,written,included,guarded,endpoint⟩ := (profile_rewrite_iff _ _ _ _).mp step
  have same : recipe = edge.recipe := by simpa using member
  subst recipe
  obtain ⟨point,next,guarded⟩ := (edge.guard_iff before written).mp guarded
  refine ⟨edge.finish before written,point,?_,?_,?_⟩
  · simp [Edge.finish]
  · simpa only [edge.overwrite_eq before written next] using endpoint
  · apply (profile_rewrite_iff _ _ _ _).mpr
    exact ⟨edge.effect,by simp,dataValues written,edge.data_support keys included,guarded,rfl⟩

theorem Edge.lift_firing (edge : Edge Key) (keys : Finset Key) (before : Location Key → Word)
    (following : Multiset (Cell Key)) (point : before (.inl edge.activation) = edge.point)
    (step : (profile [edge.effect]).theory.rewrites (encode keys (dataValues before)) following) :
    ∃ after : Location Key → Word,
      after (.inl edge.activation) = edge.next ∧ following = encode keys (dataValues after) ∧
      (profile [edge.recipe]).theory.rewrites (encode (scopedKeys edge.activation keys) before)
        (encode (scopedKeys edge.activation keys) after) := by
  obtain ⟨recipe,member,written,included,guarded,endpoint⟩ := (profile_rewrite_iff _ _ _ _).mp step
  have same : recipe = edge.effect := by simpa using member
  subst recipe
  let raw := extendValues edge before written
  have next : raw (.inl edge.activation) = edge.next := by simp [raw,extendValues]
  have sourceGuard : edge.recipe.guard (edge.recipe.inputs.map before) (edge.recipe.outputs.map raw) = true :=
    (edge.guard_iff before raw).mpr ⟨point,next,guarded⟩
  have support : edge.recipe.support ⊆ scopedKeys edge.activation keys := by
    rw [edge.support_eq]
    intro location member
    rcases Finset.mem_insert.mp member with same | data
    · exact Finset.mem_insert.mpr (Or.inl same)
    · obtain ⟨key,present,rfl⟩ := Finset.mem_image.mp data
      exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨key,included present,rfl⟩)
  refine ⟨edge.finish before raw,by simp [Edge.finish],?_,?_⟩
  · exact endpoint
  · apply (profile_rewrite_iff _ _ _ _).mpr
    exact ⟨edge.recipe,by simp,raw,support,sourceGuard,congrArg (encode _) (edge.overwrite_eq before raw next).symm⟩

#print axioms Edge.project_firing
#print axioms Edge.lift_firing
end Mettapedia.Machines.TIsa.Control
