import Mettapedia.TypeTheory.Unfolding.AccessibleRecursion.Syntax

/-!
# A semantic recursor for accessible points, without choice

The one-ground calculus is interpreted over `Prop`: the ground type denotes
`Prop`, and every simple type denotes a type of predicates
`Val S₁ → ⋯ → Val Sₙ → Prop`.  For such types a unique value can be described
without choice (`describe`, `describe_eq`): at `Prop` the described value is
`∃ v, G v ∧ v`, and at function types it is described pointwise.

For a relation `R`, a step `F`, and a point `a` accessible for `R`, the graph
of well-founded recursion (`Graph R F`) has exactly one value at `a` when `F`
respects `R` (`RespectsSem`): `Graph.unique` and `Graph.exists_value`.  The
semantic recursor `recSem R F a` describes that value, and it satisfies the
unfolding equation at every accessible point of a respecting step
(`recSem_unfold`).
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Unfolding.AccessibleRecursion

open Mettapedia.TypeTheory.Calculi.SingleBaseSTLC.IntrinsicSTT

/-- Semantic values: types interpreted over `Prop`. -/
abbrev Val (T : Ty) : Type := T.denote Prop

/-- The value described by a predicate: exact whenever the predicate has a
unique solution. -/
def describe : (T : Ty) → (Val T → Prop) → Val T
  | .atom, G => ∃ value : Prop, G value ∧ value
  | .arr _ codomain, G => fun argument =>
      describe codomain (fun result => ∃ function, G function ∧ function argument = result)

/-- **Description without choice.**  A predicate with a unique solution
describes that solution. -/
theorem describe_eq : ∀ (T : Ty) (G : Val T → Prop) (value : Val T), G value →
    (∀ other, G other → other = value) → describe T G = value
  | .atom, G, value, holds, unique => by
      apply propext
      constructor
      · rintro ⟨other, otherHolds, otherTrue⟩
        rw [← unique other otherHolds]
        exact otherTrue
      · intro valueTrue
        exact ⟨value, holds, valueTrue⟩
  | .arr _ codomain, G, value, holds, unique => by
      funext argument
      apply describe_eq codomain
      · exact ⟨value, holds, rfl⟩
      · rintro result ⟨function, functionHolds, rfl⟩
        rw [unique function functionHolds]

/-- A step respects a relation when its value at `x` reads the recursive
argument only below `x`. -/
def RespectsSem {A P : Ty} (R : Val A → Val A → Prop) (F : Val A → (Val A → Val P) → Val P) :
    Prop :=
  ∀ x g g', (∀ y, R y x → g y = g' y) → F x g = F x g'

/-- The graph of well-founded recursion for a relation and a step. -/
inductive Graph {A P : Ty} (R : Val A → Val A → Prop) (F : Val A → (Val A → Val P) → Val P) :
    Val A → Val P → Prop
  | intro (x : Val A) (g : Val A → Val P) :
      (∀ y, R y x → Graph R F y (g y)) → Graph R F x (F x g)

variable {A P : Ty} {R : Val A → Val A → Prop} {F : Val A → (Val A → Val P) → Val P}

/-- At an accessible point of a respecting step, the graph has at most one
value. -/
theorem Graph.unique (respects : RespectsSem R F) {x : Val A} (accessible : Acc R x) :
    ∀ {value other : Val P}, Graph R F x value → Graph R F x other → value = other := by
  induction accessible with
  | intro x _ ih =>
      intro value other valueGraph otherGraph
      cases valueGraph with
      | intro _ g below =>
          cases otherGraph with
          | intro _ g' below' =>
              exact respects x g g' fun y related => ih y related (below y related) (below' y related)

/-- At an accessible point of a respecting step, the graph has a value. -/
theorem Graph.exists_value (respects : RespectsSem R F) {x : Val A} (accessible : Acc R x) :
    ∃ value, Graph R F x value := by
  induction accessible with
  | intro x below ih =>
      refine ⟨F x fun y => describe P (Graph R F y), Graph.intro x _ ?_⟩
      intro y related
      obtain ⟨value, valueGraph⟩ := ih y related
      rw [describe_eq P (Graph R F y) value valueGraph fun other otherGraph =>
        Graph.unique respects (below y related) otherGraph valueGraph]
      exact valueGraph

/-- The semantic recursor: the described value of the graph. -/
def recSem {A P : Ty} (R : Val A → Val A → Prop) (F : Val A → (Val A → Val P) → Val P)
    (x : Val A) : Val P :=
  describe P (Graph R F x)

/-- At an accessible point of a respecting step, the semantic recursor is the
graph's value. -/
theorem recSem_graph (respects : RespectsSem R F) {x : Val A} (accessible : Acc R x) :
    Graph R F x (recSem R F x) := by
  obtain ⟨value, valueGraph⟩ := Graph.exists_value respects accessible
  unfold recSem
  rw [describe_eq P (Graph R F x) value valueGraph fun other otherGraph =>
    Graph.unique respects accessible otherGraph valueGraph]
  exact valueGraph

/-- **The unfolding equation holds semantically** at every accessible point
of a respecting step. -/
theorem recSem_unfold (respects : RespectsSem R F) {x : Val A} (accessible : Acc R x) :
    recSem R F x = F x (recSem R F) := by
  apply Graph.unique respects accessible (recSem_graph respects accessible)
  refine Graph.intro x _ ?_
  intro y related
  exact recSem_graph respects (accessible.inv related)

end Mettapedia.TypeTheory.Unfolding.AccessibleRecursion
