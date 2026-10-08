import Mathlib.Data.List.Basic
import Mathlib.Data.Option.Basic

/-!
# Coloured partial action trees

A tree records a colour at every enabled finite action path. Its root is
present and its enabled domain is prefix closed. The action type is arbitrary;
neither finite branching nor a finite alphabet is imposed.

Coiteration follows the supplied deterministic transition function along a
finite path. Its universal property concerns the complete tree, including
absence of transitions, rather than only its root colour.
-/

set_option autoImplicit false

namespace Mettapedia.CategoryTheory

universe a v w s

/-- A rooted, coloured, prefix-closed partial action tree. -/
structure PartialActionTree (Action : Type a) (Value : Type v) where
  root : Value
  read : List Action → Option Value
  root_read : read [] = some root
  prefix_closed : ∀ initialPath suffix, (read (initialPath ++ suffix)).isSome = true →
    (read initialPath).isSome = true

namespace PartialActionTree

variable {Action : Type a} {Value : Type v} {Other : Type w}

@[ext] theorem ext {first second : PartialActionTree Action Value}
    (readings : ∀ path, first.read path = second.read path) : first = second := by
  have roots : first.root = second.root := by
    apply Option.some.inj
    exact first.root_read.symm.trans ((readings []).trans second.root_read)
  cases first
  cases second
  cases roots
  cases funext readings
  rfl

/-- Change colours without changing the enabled domain. -/
def map (mapping : Value → Other) (tree : PartialActionTree Action Value) :
    PartialActionTree Action Other where
  root := mapping tree.root
  read path := (tree.read path).map mapping
  root_read := by simp [tree.root_read]
  prefix_closed initialPath suffix present := by
    simpa only [Option.isSome_map] using
      tree.prefix_closed initialPath suffix (by simpa only [Option.isSome_map] using present)

@[simp] theorem map_root (mapping : Value → Other) (tree : PartialActionTree Action Value) :
    (map mapping tree).root = mapping tree.root := rfl

@[simp] theorem map_read (mapping : Value → Other) (tree : PartialActionTree Action Value)
    (path : List Action) : (map mapping tree).read path = (tree.read path).map mapping := rfl

@[simp] theorem map_id (tree : PartialActionTree Action Value) : map id tree = tree := by
  apply ext
  intro path
  simp

theorem map_comp {Third : Type s} (earlier : Value → Other) (later : Other → Third)
    (tree : PartialActionTree Action Value) :
    map later (map earlier tree) = map (later ∘ earlier) tree := by
  apply ext
  intro path
  simp [Option.map_map]

/-- The actual subtree at an enabled path, retaining all further colours. -/
def subtree (tree : PartialActionTree Action Value) (initialPath : List Action)
    (present : (tree.read initialPath).isSome = true) : PartialActionTree Action Value where
  root := (tree.read initialPath).get present
  read suffix := tree.read (initialPath ++ suffix)
  root_read := by simp
  prefix_closed first second available := by
    apply tree.prefix_closed (initialPath ++ first) second
    simpa only [List.append_assoc] using available

@[simp] theorem subtree_read (tree : PartialActionTree Action Value) (initialPath suffix : List Action)
    (present : (tree.read initialPath).isSome = true) :
    (subtree tree initialPath present).read suffix = tree.read (initialPath ++ suffix) := rfl

@[simp] theorem subtree_nil (tree : PartialActionTree Action Value)
    (present : (tree.read []).isSome = true) : subtree tree [] present = tree := by
  apply ext
  intro path
  rfl

theorem subtree_subtree (tree : PartialActionTree Action Value) (first second : List Action)
    (firstPresent : (tree.read first).isSome = true)
    (secondPresent : ((subtree tree first firstPresent).read second).isSome = true) :
    subtree (subtree tree first firstPresent) second secondPresent =
      subtree tree (first ++ second) secondPresent := by
  apply ext
  intro path
  exact congrArg tree.read (List.append_assoc first second path).symm

theorem map_subtree (mapping : Value → Other) (tree : PartialActionTree Action Value)
    (initialPath : List Action) (present : (tree.read initialPath).isSome = true) :
    map mapping (subtree tree initialPath present) =
      subtree (map mapping tree) initialPath (by simpa using present) := by
  apply ext
  intro path
  rfl

theorem read_none_of_prefix_none (tree : PartialActionTree Action Value)
    (initialPath suffix : List Action) (absent : tree.read initialPath = none) :
    tree.read (initialPath ++ suffix) = none := by
  cases reading : tree.read (initialPath ++ suffix) with
  | none => rfl
  | some value =>
    have present := tree.prefix_closed initialPath suffix (by simp [reading])
    simp [absent] at present

/-- One deterministic action exposes its complete subtree when enabled. -/
def step (tree : PartialActionTree Action Value) (action : Action) :
    Option (PartialActionTree Action Value) :=
  if present : (tree.read [action]).isSome = true then
    some (subtree tree [action] present)
  else none

theorem read_cons (tree : PartialActionTree Action Value) (action : Action) (path : List Action) :
    tree.read (action :: path) = (tree.step action).bind (fun child => child.read path) := by
  unfold step
  split
  · rfl
  · rename_i absent
    have missing : tree.read [action] = none := by
      cases reading : tree.read [action] <;> simp_all
    exact tree.read_none_of_prefix_none [action] path missing

theorem step_eq_some_iff (tree : PartialActionTree Action Value) (action : Action)
    (child : PartialActionTree Action Value) :
    tree.step action = some child ↔
      ∃ present : (tree.read [action]).isSome = true, subtree tree [action] present = child := by
  unfold step
  split <;> simp_all

theorem step_map (mapping : Value → Other) (tree : PartialActionTree Action Value)
    (action : Action) : (map mapping tree).step action = (tree.step action).map (map mapping) := by
  unfold step
  simp only [map_read, Option.isSome_map]
  split
  · simp only [Option.map_some]
    exact congrArg some (map_subtree mapping tree [action] _).symm
  · rfl

/-- Finite path execution in a supplied deterministic transition system. -/
def run {State : Type s} (transition : State → Action → Option State)
    (state : State) : List Action → Option State
  | [] => some state
  | action :: path => (transition state action).bind (fun next => run transition next path)

@[simp] theorem run_nil {State : Type s} (transition : State → Action → Option State)
    (state : State) : run transition state [] = some state := rfl

@[simp] theorem run_cons {State : Type s} (transition : State → Action → Option State)
    (state : State) (action : Action) (path : List Action) :
    run transition state (action :: path) =
      (transition state action).bind (fun next => run transition next path) := rfl

theorem run_append {State : Type s} (transition : State → Action → Option State)
    (initialPath suffix : List Action) (state : State) :
    run transition state (initialPath ++ suffix) =
      (run transition state initialPath).bind (fun next => run transition next suffix) := by
  induction initialPath generalizing state with
  | nil => rfl
  | cons action initialPath ih =>
    simp only [List.cons_append, run_cons, ih, Option.bind_assoc]

/-- The complete coloured behavior of a state, constructed by finite path traversal. -/
def coiterate {State : Type s} (transition : State → Action → Option State)
    (colour : State → Value) (state : State) : PartialActionTree Action Value where
  root := colour state
  read path := (run transition state path).map colour
  root_read := rfl
  prefix_closed initialPath suffix present := by
    simp only [Option.isSome_map, run_append] at present
    cases reading : run transition state initialPath with
    | none => simp [reading] at present
    | some next => rfl

@[simp] theorem coiterate_root {State : Type s} (transition : State → Action → Option State)
    (colour : State → Value) (state : State) :
    (coiterate transition colour state).root = colour state := rfl

@[simp] theorem coiterate_read {State : Type s} (transition : State → Action → Option State)
    (colour : State → Value) (state : State) (path : List Action) :
    (coiterate transition colour state).read path = (run transition state path).map colour := rfl

theorem coiterate_step {State : Type s} (transition : State → Action → Option State)
    (colour : State → Value) (state : State) (action : Action) :
    (coiterate transition colour state).step action =
      (transition state action).map (coiterate transition colour) := by
  cases reading : transition state action with
  | none => simp [step, reading]
  | some next =>
    simp only [step, coiterate_read, run_cons, reading, Option.bind_some, run_nil,
      Option.map_some, Option.isSome_some, ↓reduceDIte]
    apply congrArg some
    apply ext
    intro path
    simp [run_cons, reading]

/-- Any colour-preserving coalgebra map agrees on every finite path. -/
theorem coiterate_unique {State : Type s} (transition : State → Action → Option State)
    (colour : State → Value) (mapping : State → PartialActionTree Action Value)
    (roots : ∀ state, (mapping state).root = colour state)
    (steps : ∀ state action,
      (mapping state).step action = (transition state action).map mapping) :
    mapping = coiterate transition colour := by
  funext state
  apply ext
  intro path
  induction path generalizing state with
  | nil => simp [roots, (mapping state).root_read]
  | cons action path ih =>
    rw [read_cons, steps]
    simp only [Option.bind_map, Function.comp_def, ih, coiterate_read, run_cons]
    cases transition state action <;> rfl

/-- Subtrees provide the duplicated tree of complete future observations. -/
def duplicate (tree : PartialActionTree Action Value) :
    PartialActionTree Action (PartialActionTree Action Value) where
  root := tree
  read path :=
    if present : (tree.read path).isSome = true then some (subtree tree path present) else none
  root_read := by simp [tree.root_read]
  prefix_closed initialPath suffix present := by
    split at present
    · rename_i enabled
      have earlier := tree.prefix_closed initialPath suffix enabled
      simp [earlier]
    · simp at present

@[simp] theorem duplicate_read (tree : PartialActionTree Action Value) (path : List Action) :
    (duplicate tree).read path =
      if present : (tree.read path).isSome = true then some (subtree tree path present) else none := rfl

theorem duplicate_subtree (tree : PartialActionTree Action Value) (path : List Action)
    (present : (tree.read path).isSome = true) :
    duplicate (subtree tree path present) =
      subtree (duplicate tree) path (by simp [present]) := by
  apply ext
  intro suffix
  simp only [duplicate_read, subtree_read]
  by_cases available : (tree.read (path ++ suffix)).isSome = true
  · simp [available]
    exact subtree_subtree tree path suffix present available
  · simp [available]

theorem duplicate_step (tree : PartialActionTree Action Value) (action : Action) :
    (duplicate tree).step action = (tree.step action).map duplicate := by
  unfold step
  by_cases enabled : (tree.read [action]).isSome = true
  · simp only [duplicate_read, enabled, ↓reduceDIte, Option.isSome_some, Option.map_some]
    exact congrArg some (duplicate_subtree tree [action] enabled).symm
  · simp only [duplicate_read, enabled, ↓reduceDIte, Option.isSome_none, Bool.false_eq_true,
      ↓reduceDIte, Option.map_none]

theorem duplicate_map (mapping : Value → Other) (tree : PartialActionTree Action Value) :
    duplicate (map mapping tree) = map (map mapping) (duplicate tree) := by
  apply ext
  intro path
  simp only [duplicate, map_read, Option.isSome_map]
  split
  · simp only [Option.map_some]
    exact congrArg some (map_subtree mapping tree path _).symm
  · rfl

theorem duplicate_counit (tree : PartialActionTree Action Value) :
    map root (duplicate tree) = tree := by
  apply ext
  intro path
  simp only [map_read, duplicate]
  split
  · rename_i present
    exact Option.some_get present
  · rename_i absent
    cases reading : tree.read path <;> simp_all

theorem duplicate_coassoc (tree : PartialActionTree Action Value) :
    map duplicate (duplicate tree) = duplicate (duplicate tree) := by
  apply ext
  intro path
  by_cases present : (tree.read path).isSome = true
  · simp only [map_read, duplicate_read, present, ↓reduceDIte, Option.isSome_some,
      Option.map_some]
    exact congrArg some (duplicate_subtree tree path present)
  · simp only [map_read, duplicate_read, present, ↓reduceDIte, Option.isSome_none,
      Bool.false_eq_true, ↓reduceDIte, Option.map_none]

end PartialActionTree
end Mettapedia.CategoryTheory
