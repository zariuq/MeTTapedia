import Mathlib.Data.List.Basic

/-!
# Branch-local goals for connection replay and search

Each open literal carries its own ancestor path. Expanding one goal creates
child goals with an extended path; goals already in the agenda keep their
original paths. A substitution maps every open literal and every stored
ancestor together.
-/

namespace Mettapedia.Logic.LP

structure ConnectionGoal (Literal : Type u) where
  literal : Literal
  path : List Literal
  deriving DecidableEq, Repr

abbrev ConnectionAgenda (Literal : Type u) := List (ConnectionGoal Literal)

def connectionGoals (goals path : List Literal) : ConnectionAgenda Literal :=
  goals.map fun literal => ⟨literal, path⟩

def ConnectionGoal.map (f : Literal → Other) (goal : ConnectionGoal Literal) : ConnectionGoal Other :=
  ⟨f goal.literal, goal.path.map f⟩

def ConnectionAgenda.map (f : Literal → Other) (agenda : ConnectionAgenda Literal) : ConnectionAgenda Other :=
  List.map (ConnectionGoal.map f) agenda

@[simp] theorem connectionGoals_nil (path : List Literal) : connectionGoals [] path = [] := rfl

@[simp] theorem connectionGoals_cons (literal : Literal) (goals path : List Literal) :
    connectionGoals (literal :: goals) path = ⟨literal, path⟩ :: connectionGoals goals path := rfl

@[simp] theorem connectionGoals_append (first second path : List Literal) :
    connectionGoals (first ++ second) path = connectionGoals first path ++ connectionGoals second path :=
  List.map_append

@[simp] theorem connectionGoals_eq_nil (goals path : List Literal) : connectionGoals goals path = [] ↔ goals = [] := by
  simp [connectionGoals]

end Mettapedia.Logic.LP
