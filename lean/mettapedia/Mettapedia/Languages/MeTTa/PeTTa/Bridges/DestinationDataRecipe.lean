import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedClosedEquationSource

/-!
# Data recipes and the existing destination preparation rules

Constructor preparation owes one equation for each child and one for the
assembled node. These obligations describe pending data, not completed
evaluation. Their expansion is read from the existing source preparer.
No native plan classifier or child result service is assumed here.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataRecipe

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open EagerDFS.Destination

/-- Pure source syntax, including open variable fields. Native admission
must separately derive this evidence for its accepted pattern recipes. -/
inductive Recipe (program : SpaceSemantics.Program) : Atom → Prop where
  | variableValue (name : String) : Recipe program (.var name)
  | symbol (name : String) : Recipe program (.symbol name)
  | grounded (value : GroundedValue) : Recipe program (.grounded value)
  | named (head : String) (arguments : List Atom)
      (ordinary : Source.lexicalForm (.expression (.symbol head :: arguments)) = false)
      (localForm : Source.scopedForm (.expression (.symbol head :: arguments)) = false)
      (inert : callable program head = false)
      (surface : head ≠ "let*" ∧ head ≠ "case")
      (children : ∀ argument ∈ arguments, Recipe program argument) :
      Recipe program (.expression (.symbol head :: arguments))
  | tuple (children : List Atom)
      (noHead : ∀ head arguments, children ≠ .symbol head :: arguments)
      (parts : ∀ child ∈ children, Recipe program child) : Recipe program (.expression children)

inductive PureGoal (program : SpaceSemantics.Program) : Goal → Prop where
  | evaluate {expression destination : Atom} (data : Recipe program expression) :
      PureGoal program (.evaluate expression destination)
  | equate (expression destination : Atom) : PureGoal program (.equate expression destination)

/-- The equation owed by a pending pure goal. This is a constraint
interpretation, not a definition of evaluator execution. -/
def Says (environment : Environment) : Goal → Prop
  | .evaluate expression destination | .equate expression destination =>
      read environment expression = read environment destination
  | _ => False

def AllSay (environment : Environment) (goals : List Goal) : Prop :=
  ∀ goal ∈ goals, Says environment goal

def AllPure (program : SpaceSemantics.Program) (goals : List Goal) : Prop :=
  ∀ goal ∈ goals, PureGoal program goal

/-- Actual source preparation, projected only to its generated goals. -/
def expansion (program : SpaceSemantics.Program) (control : Control) (expression destination : Atom) : List Goal :=
  (prepare .eagerValue program control expression destination []).goals

theorem zip_reads {environment : Environment} {expressions slots : List Atom}
    (length : expressions.length = slots.length)
    (equal : ∀ {expression slot}, (expression, slot) ∈ expressions.zip slots →
      read environment expression = read environment slot) :
    expressions.map (read environment) = slots.map (read environment) := by
  have related : List.Forall₂ (fun expression slot => read environment expression = read environment slot)
      expressions slots := List.forall₂_iff_zip.mpr ⟨length, equal⟩
  clear length equal
  induction related with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head, ih]

theorem children_equal {environment : Environment} {expressions slots : List Atom}
    (length : expressions.length = slots.length)
    (pending : AllSay environment ((expressions.zip slots).map fun pair => Goal.evaluate pair.1 pair.2)) :
    expressions.map (read environment) = slots.map (read environment) := by
  apply zip_reads length
  intro expression slot member
  exact pending (.evaluate expression slot) (List.mem_map.mpr ⟨(expression, slot), member, rfl⟩)

theorem children_pure {program : SpaceSemantics.Program} {expressions slots : List Atom}
    (data : ∀ expression ∈ expressions, Recipe program expression) :
    AllPure program ((expressions.zip slots).map fun pair => Goal.evaluate pair.1 pair.2) := by
  intro goal member
  obtain ⟨⟨expression, slot⟩, paired, rfl⟩ := List.mem_map.mp member
  exact .evaluate (data expression (List.of_mem_zip paired).1)

theorem named_constraints {environment : Environment} (head : String) (expressions slots : List Atom)
    (destination : Atom) (length : expressions.length = slots.length)
    (pending : AllSay environment
      ((expressions.zip slots).map (fun pair => Goal.evaluate pair.1 pair.2) ++
        [.equate (.expression (.symbol head :: slots)) destination])) :
    read environment (.expression (.symbol head :: expressions)) = read environment destination := by
  have children := children_equal length (fun goal member => pending goal (List.mem_append_left _ member))
  have assembled := pending (.equate (.expression (.symbol head :: slots)) destination)
    (List.mem_append_right _ List.mem_cons_self)
  change read environment (.expression (.symbol head :: slots)) = read environment destination at assembled
  rw [ScopedClosedEquationSource.read_expression, List.map_cons] at assembled ⊢
  simpa only [children] using assembled

theorem tuple_constraints {environment : Environment} (expressions slots : List Atom)
    (destination : Atom) (length : expressions.length = slots.length)
    (pending : AllSay environment (dataGoals .eagerValue expressions slots destination)) :
    read environment (.expression expressions) = read environment destination := by
  have children := children_equal length (fun goal member => pending goal (List.mem_append_left _ member))
  have assembled := pending (.equate (.expression slots) destination) (List.mem_append_right _ List.mem_cons_self)
  change read environment (.expression slots) = read environment destination at assembled
  rw [ScopedClosedEquationSource.read_expression] at assembled ⊢
  simpa only [children] using assembled

theorem expansion_pure {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) (control : Control) (destination : Atom) :
    AllPure program (expansion program control expression destination) := by
  cases data with
  | variableValue name =>
      intro goal member
      have prepared := (Source.Prepared.variableValue (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) name).execution
      rw [expansion, prepared] at member
      cases List.mem_singleton.mp member
      exact .equate _ _
  | symbol name =>
      intro goal member
      have prepared := (Source.Prepared.symbol (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) name).execution
      rw [expansion, prepared] at member
      cases List.mem_singleton.mp member
      exact .equate _ _
  | grounded value =>
      intro goal member
      have prepared := (Source.Prepared.grounded (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) value).execution
      rw [expansion, prepared] at member
      cases List.mem_singleton.mp member
      exact .equate _ _
  | named head arguments ordinary localForm inert surface children =>
      have prepared := (Source.Prepared.construction (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) head arguments ordinary inert).execution
      intro goal member
      rw [expansion, prepared] at member
      simp only [replace, List.append_nil] at member
      rcases List.mem_append.mp member with child | assembled
      · exact children_pure children goal child
      · cases List.mem_singleton.mp assembled
        exact .equate _ _
  | tuple children noHead parts =>
      have prepared := (Source.Prepared.tuple (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) children noHead).execution
      intro goal member
      rw [expansion, prepared] at member
      simp only [replace, dataGoals, List.append_nil] at member
      rcases List.mem_append.mp member with child | assembled
      · exact children_pure parts goal child
      · cases List.mem_singleton.mp assembled
        exact .equate _ _

theorem expansion_entails {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) (control : Control) (destination : Atom) (environment : Environment)
    (pending : AllSay environment (expansion program control expression destination)) :
    read environment expression = read environment destination := by
  cases data with
  | variableValue name =>
      simpa only [AllSay, expansion, prepare, replace, List.singleton_append, List.mem_singleton, forall_eq, Says] using pending
  | symbol name =>
      simpa only [AllSay, expansion, prepare, replace, List.singleton_append, List.mem_singleton, forall_eq, Says] using pending
  | grounded value =>
      simpa only [AllSay, expansion, prepare, replace, List.singleton_append, List.mem_singleton, forall_eq, Says] using pending
  | named head arguments ordinary localForm inert surface children =>
      have prepared := (Source.Prepared.construction (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) head arguments ordinary inert).execution
      rw [expansion, prepared] at pending
      simp only [replace, List.append_nil] at pending
      exact named_constraints head arguments (freshSlots control arguments.length) destination (by simp) pending
  | tuple children noHead parts =>
      have prepared := (Source.Prepared.tuple (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) children noHead).execution
      rw [expansion, prepared] at pending
      simp only [replace, List.append_nil] at pending
      exact tuple_constraints children (freshSlots control children.length) destination (by simp) pending

theorem Recipe.prepared {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) (control : Control) (destination : Atom) (older : List Goal) :
    Source.Prepared .eagerValue program control destination older expression
      (prepare .eagerValue program control expression destination older) := by
  cases data with
  | variableValue name => exact .variableValue name
  | symbol name => exact .symbol name
  | grounded value => exact .grounded value
  | named head arguments ordinary localForm inert surface children =>
      have source := Source.Prepared.construction (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := older) head arguments ordinary inert
      exact source.execution.symm ▸ source
  | tuple children noHead parts =>
      have source := Source.Prepared.tuple (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := older) children noHead
      exact source.execution.symm ▸ source

theorem Recipe.not_scoped {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) : Source.scopedForm expression = false := by
  cases data with
  | variableValue | symbol | grounded => rfl
  | named head arguments ordinary localForm inert surface children => exact localForm
  | tuple children noHead parts =>
      cases children with
      | nil => rfl
      | cons first rest =>
          cases first with
          | symbol head => exact (noHead head rest rfl).elim
          | var | grounded | expression => rfl

theorem expansion_suffix {program : SpaceSemantics.Program} {expression : Atom}
    (data : Recipe program expression) (control : Control) (destination : Atom) (older : List Goal) :
    (prepare .eagerValue program control expression destination older).goals =
      expansion program control expression destination ++ older := by
  cases data with
  | variableValue | symbol | grounded => rfl
  | named head arguments ordinary localForm inert surface children =>
      have first := (Source.Prepared.construction (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) head arguments ordinary inert).execution
      have continued := (Source.Prepared.construction (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := older) head arguments ordinary inert).execution
      rw [continued, expansion, first]
      simp only [replace, List.append_nil]
  | tuple children noHead parts =>
      have first := (Source.Prepared.tuple (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := []) children noHead).execution
      have continued := (Source.Prepared.tuple (policy := .eagerValue) (program := program)
        (control := control) (destination := destination) (older := older) children noHead).execution
      rw [continued, expansion, first]
      simp only [replace, List.append_nil]

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.DestinationDataRecipe
