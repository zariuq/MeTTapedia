import Mettapedia.Logic.TierZero.Adequacy.MM0LocatedInference

/-!
# Inspectable interfaces inferred from symbolic source schedules

Logical hypotheses are selected by actual initial protected proof origins.
Parameter metadata also retains variables from source arguments and their
context-declared dependencies. A closed conclusion is not evidence that a
witness, premise or admission input was unused.

The complete symbolic formal context remains retained. This metadata makes no
unsafe context-strengthening claim and does not replace binder-sensitive
free-variable analysis or the source declaration's own admission check.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInterface

open Mettapedia.Languages.MM0.Kernel
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open MM0Rewriting

def variablePositions : Preterm → Finset Nat
  | .var index => {index}
  | .term _ => ∅
  | .app function argument => variablePositions function ∪ variablePositions argument

theorem variablePositions_iff (expression : Preterm) (index : Nat) :
    index ∈ variablePositions expression ↔ Preterm.Occurs index expression := by
  induction expression with
  | var source =>
      constructor
      · intro member
        have same : index = source := by simpa [variablePositions] using member
        subst index
        exact .var
      · intro occurs
        cases occurs
        simp [variablePositions]
  | term symbol =>
      constructor
      · simp [variablePositions]
      · intro occurs; cases occurs
  | app function argument head tail =>
      constructor
      · intro member
        rcases Finset.mem_union.mp member with left | right
        · exact .function (head.mp left)
        · exact .argument (tail.mp right)
      · intro occurs
        cases occurs with
        | function present => exact Finset.mem_union_left _ (head.mpr present)
        | argument present => exact Finset.mem_union_right _ (tail.mpr present)

def variableSet (expressions : List Preterm) : Finset Nat := expressions.foldr (fun expression rest => variablePositions expression ∪ rest) ∅

theorem expression_variables_retained {expressions : List Preterm} {expression : Preterm}
    (present : expression ∈ expressions) : variablePositions expression ⊆ variableSet expressions := by
  induction expressions with
  | nil => cases present
  | cons first rest earlier =>
      rcases List.mem_cons.mp present with rfl | present
      · exact Finset.subset_union_left
      · exact (earlier present).trans Finset.subset_union_right

def dependencies (formal : Context) (index : Nat) : Finset Nat :=
  match formal[index]? with
  | some (.regular _ needed) => needed
  | _ => ∅

def withDependencies (formal : Context) (used : Finset Nat) : Finset Nat :=
  used ∪ used.biUnion (dependencies formal)

theorem used_parameters_retained (formal : Context) (used : Finset Nat) : used ⊆ withDependencies formal used :=
  Finset.subset_union_left

theorem declared_dependency_retained (formal : Context) (used : Finset Nat) (index : Nat)
    (present : index ∈ used) : dependencies formal index ⊆ withDependencies formal used := by
  intro needed member
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨index, present, member⟩)

def usedHypotheses {O : Type*} [DecidableEq O] (rows : List (O × Preterm)) (used : Finset O) : List Preterm :=
  (rows.filter fun row => decide (row.1 ∈ used)).map Prod.snd

theorem used_hypothesis_retained {O : Type*} [DecidableEq O] {rows : List (O × Preterm)} {used : Finset O}
    {row : O × Preterm} (present : row ∈ rows) (needed : row.1 ∈ used) :
    row.2 ∈ usedHypotheses rows used := by
  apply List.mem_map.mpr
  exact ⟨row, List.mem_filter.mpr ⟨present, by simpa using needed⟩, rfl⟩

def sourceArguments {C X O : Type*}
    (sources : List (SchemaSchedules.SourceFiring (MM0LocatedKernel.SourceSchema C) (MM0LocatedKernel.Inputs X) O)) : List Preterm :=
  sources.flatMap fun source => match source.inputs with
    | .inl arguments => arguments
    | .inr _ => []

def parameterFootprint {C X O : Type*} (formal : Context)
    (sources : List (SchemaSchedules.SourceFiring (MM0LocatedKernel.SourceSchema C) (MM0LocatedKernel.Inputs X) O))
    (hypotheses : List Preterm) (conclusion : Preterm) : Finset Nat :=
  withDependencies formal (variableSet (sourceArguments sources ++ hypotheses ++ [conclusion]))

theorem source_argument_parameters_retained {C X O : Type*} (formal : Context)
    (sources : List (SchemaSchedules.SourceFiring (MM0LocatedKernel.SourceSchema C) (MM0LocatedKernel.Inputs X) O))
    (hypotheses : List Preterm) (conclusion expression : Preterm)
    (used : expression ∈ sourceArguments sources) :
    variablePositions expression ⊆ parameterFootprint formal sources hypotheses conclusion := by
  exact (expression_variables_retained (by simp [used])).trans (used_parameters_retained formal _)

end Mettapedia.Logic.TierZero.Adequacy.MM0SchemaInterface
