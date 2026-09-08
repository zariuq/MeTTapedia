import Mettapedia.GSLT.LanguageDef.FlatTermViewCompilation

/-!
# Counting flat rows after existentially erasing dead bindings

A count observer does not retain the bindings produced by a successful row.
For an admitted flat row, matching can therefore be compiled to two finite
checks: rigid coordinates agree, and every repeated stored root variable is
required to denote the same rigid query value.  An unobserved query coordinate
contributes no requirement.

The semantic side below quantifies over a binding environment.  The physical
side is the finite requirement map implemented by a row matcher.  Their
equivalence is independent of syntax, evaluator, search policy, and storage
representation.  A BN evaluator, a CBPV evaluator, or another frontend need
only present immediate coordinates through the existing flat-term-view
interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FlatTermDeadBindingCountCompilation

open Mettapedia.GSLT.Dynamics.Collapse

universe uVariable uValue uRow uTerm uEnvironment

/-- The stored-coordinate fragment admitted by the direct row counter. -/
inductive StoredCoordinate (Variable : Type uVariable) (Value : Type uValue)
  | rigid (value : Value)
  | storedVar (name : Variable)
deriving DecidableEq, Repr

/-- A fixed-arity stored relation row. -/
structure FlatStoredRow (Variable : Type uVariable) (Value : Type uValue)
    (arity : Nat) where
  coordinate : Fin arity → StoredCoordinate Variable Value

/-- `none` is a distinct open query root whose produced binding is dead;
`some value` is a rigid coordinate after root projection. -/
abbrev DeadBindingQuery (Value : Type uValue) (arity : Nat) :=
  Fin arity → Option Value

/-- Reference meaning of one coordinate under a candidate assignment. -/
def coordinateMatches
    {Variable : Type uVariable} {Value : Type uValue}
    (assignment : Variable → Option Value) :
    StoredCoordinate Variable Value → Option Value → Prop
  | _, none => True
  | .rigid stored, some query => stored = query
  | .storedVar name, some query => assignment name = some query

/-- Materializing reference semantics: some assignment makes every observed
coordinate match.  Dead coordinates are existentially hidden. -/
def SemanticMatches
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity) : Prop :=
  ∃ assignment, ∀ index,
    coordinateMatches assignment (row.coordinate index) (query index)

/-- A rigid query coordinate requires one value from a stored root variable. -/
def Requires
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity)
    (name : Variable) (value : Value) : Prop :=
  ∃ index,
    query index = some value ∧
      row.coordinate index = .storedVar name

/-- Direct rigid-coordinate comparison. -/
def RigidCoordinatesAgree
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity) : Prop :=
  ∀ index,
    match row.coordinate index, query index with
    | .rigid stored, some value => stored = value
    | _, _ => True

/-- The small physical requirement map is consistent exactly when repeated
stored variables never receive two different rigid values. -/
def RequirementsConsistent
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity) : Prop :=
  ∀ leftIndex rightIndex,
    match row.coordinate leftIndex, query leftIndex,
        row.coordinate rightIndex, query rightIndex with
    | .storedVar leftName, some left,
        .storedVar rightName, some right =>
          leftName = rightName → left = right
    | _, _, _, _ => True

/-- The representation-independent physical admission law. -/
def PhysicalMatches
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity) : Prop :=
  RigidCoordinatesAgree row query ∧ RequirementsConsistent row query

theorem requirements_unique
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity)
    (consistent : RequirementsConsistent row query)
    {name : Variable} {left right : Value}
    (leftRequired : Requires row query name left)
    (rightRequired : Requires row query name right) : left = right := by
  obtain ⟨leftIndex, leftQuery, leftStored⟩ := leftRequired
  obtain ⟨rightIndex, rightQuery, rightStored⟩ := rightRequired
  have same := consistent leftIndex rightIndex
  simp [leftStored, leftQuery, rightStored, rightQuery] at same
  exact same

/-- Choose the unique value required for a stored variable, if any. -/
noncomputable def selectedAssignment
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity) : Variable → Option Value := by
  classical
  exact fun name =>
    if present : ∃ value, Requires row query name value then
      some (Classical.choose present)
    else
      none

theorem selectedAssignment_eq_some_of_requires
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity)
    (consistent : RequirementsConsistent row query)
    {name : Variable} {value : Value}
    (required : Requires row query name value) :
    selectedAssignment row query name = some value := by
  classical
  unfold selectedAssignment
  rw [dif_pos ⟨value, required⟩]
  apply congrArg some
  exact requirements_unique row query consistent
    (Classical.choose_spec (show ∃ candidate,
      Requires row query name candidate from ⟨value, required⟩))
    required

/-- Keystone refinement: finite rigid comparison plus a repeated-variable
requirement map is exactly existential matching after dead-binding erasure. -/
theorem semanticMatches_iff_physicalMatches
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (row : FlatStoredRow Variable Value arity)
    (query : DeadBindingQuery Value arity) :
    SemanticMatches row query ↔ PhysicalMatches row query := by
  constructor
  · rintro ⟨assignment, matchesAt⟩
    constructor
    · intro index
      have matched := matchesAt index
      cases storedAt : row.coordinate index <;>
        cases queryAt : query index <;>
        simp [coordinateMatches, storedAt, queryAt] at matched ⊢
      exact matched
    · intro leftIndex rightIndex
      have leftMatched := matchesAt leftIndex
      have rightMatched := matchesAt rightIndex
      cases leftStored : row.coordinate leftIndex <;>
        cases leftQuery : query leftIndex <;>
        cases rightStored : row.coordinate rightIndex <;>
        cases rightQuery : query rightIndex <;>
        simp_all [coordinateMatches]
      intro sameName
      cases sameName
      exact Option.some.inj (leftMatched.symm.trans rightMatched)
  · rintro ⟨rigidAgreement, consistency⟩
    refine ⟨selectedAssignment row query, ?_⟩
    intro index
    cases queryAt : query index with
    | none => simp [coordinateMatches]
    | some value =>
        cases storedAt : row.coordinate index with
        | rigid stored =>
            have equal := rigidAgreement index
            simp [storedAt, queryAt] at equal
            simp [coordinateMatches, equal]
        | storedVar name =>
            have required : Requires row query name value :=
              ⟨index, queryAt, storedAt⟩
            simpa [coordinateMatches, storedAt, queryAt] using
              selectedAssignment_eq_some_of_requires
                row query consistency required

/-! ## Count-algebra lift -/

/-- Rows retained by the materializing existential semantics. -/
noncomputable def semanticRows
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (rows : List (FlatStoredRow Variable Value arity))
    (query : DeadBindingQuery Value arity) :
    List (FlatStoredRow Variable Value arity) := by
  classical
  exact rows.filter fun row => decide (SemanticMatches row query)

/-- Rows retained by the finite direct algorithm. -/
noncomputable def directRows
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (rows : List (FlatStoredRow Variable Value arity))
    (query : DeadBindingQuery Value arity) :
    List (FlatStoredRow Variable Value arity) := by
  classical
  exact rows.filter fun row => decide (PhysicalMatches row query)

theorem semanticRows_eq_directRows
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (rows : List (FlatStoredRow Variable Value arity))
    (query : DeadBindingQuery Value arity) :
    semanticRows rows query = directRows rows query := by
  classical
  unfold semanticRows directRows
  apply List.filter_congr
  intro row _member
  exact decide_eq_decide.mpr
    (semanticMatches_iff_physicalMatches row query)

/-- One positive unit-multiplicity observation per matching occurrence. -/
def unitCountObservations {Row : Type uRow} (rows : List Row) :
    List (Obs Unit Unit) :=
  rows.map fun _ => ⟨(), 1, ()⟩

theorem collapseCount_unitCountObservations {Row : Type uRow}
    (rows : List Row) :
    collapseWith (CountAlg Unit Unit) (unitCountObservations rows) =
      rows.length := by
  induction rows with
  | nil => rfl
  | cons row rest inductionHypothesis =>
      have folded :
          foldStream (CountAlg Unit Unit) (unitCountObservations rest) =
            rest.length := by
        simpa [collapseWith, CountAlg] using inductionHypothesis
      change 1 +
          foldStream (CountAlg Unit Unit) (unitCountObservations rest) =
        rest.length + 1
      rw [folded, Nat.add_comm]

/-- Direct count, preserving duplicate row occurrences. -/
noncomputable def directCount
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (rows : List (FlatStoredRow Variable Value arity))
    (query : DeadBindingQuery Value arity) : Nat :=
  (directRows rows query).length

/-- Direct dead-binding row count implements the shared `CountAlg` observer
over the existential reference matches, without constructing bindings. -/
theorem directCount_exact
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (rows : List (FlatStoredRow Variable Value arity))
    (query : DeadBindingQuery Value arity) :
    directCount rows query =
      collapseWith (CountAlg Unit Unit)
        (unitCountObservations (semanticRows rows query)) := by
  rw [collapseCount_unitCountObservations]
  exact congrArg List.length (semanticRows_eq_directRows rows query).symm

/-! ## Composition with evaluator term views -/

/-- Count through any evaluator representation which supplies the shared root
projection algebra.  `decode` is the language-independent adapter from the
projected term representation to fixed-arity query coordinates. -/
noncomputable def viewDirectCount
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (algebra : FlatTermViewCompilation.RootProjection.Algebra
      Term Environment)
    (decode : Term → DeadBindingQuery Value arity)
    (rows : List (FlatStoredRow Variable Value arity))
    (view : FlatTermViewCompilation.RootProjection.View algebra) : Nat :=
  directCount rows (decode (FlatTermViewCompilation.RootProjection.project
    algebra view))

/-- The storage refinement and the evaluator's borrowed root projection
compose.  Changing an evaluator from BN to CBPV, or changing the physical
row index, affects only its respective adapter and leaves this square intact. -/
theorem viewDirectCount_exact
    {Term : Type uTerm} {Environment : Type uEnvironment}
    {Variable : Type uVariable} {Value : Type uValue} {arity : Nat}
    (algebra : FlatTermViewCompilation.RootProjection.Algebra
      Term Environment)
    (decode : Term → DeadBindingQuery Value arity)
    (rows : List (FlatStoredRow Variable Value arity))
    (view : FlatTermViewCompilation.RootProjection.View algebra)
    (admitted :
      FlatTermViewCompilation.RootProjection.Admitted algebra view) :
    viewDirectCount algebra decode rows view =
      collapseWith (CountAlg Unit Unit)
        (unitCountObservations
          (semanticRows rows
            (decode (algebra.force view.environment view.source)))) := by
  calc
    viewDirectCount algebra decode rows view =
        directCount rows
          (decode (algebra.force view.environment view.source)) := by
      simp [viewDirectCount,
        FlatTermViewCompilation.RootProjection.projection_exact
          algebra view admitted]
    _ = collapseWith (CountAlg Unit Unit)
          (unitCountObservations
            (semanticRows rows
              (decode (algebra.force view.environment view.source)))) :=
      directCount_exact rows _

/-! ## Admission and executable canaries -/

/-- A richer storage coordinate before flat-row admission. -/
inductive EncodedCoordinate (Variable : Type uVariable) (Value : Type uValue)
  | rigid (value : Value)
  | rootVariable (name : Variable)
  | nestedVariableStructure
deriving DecidableEq, Repr

/-- Nested variable structure is deliberately outside this bounded compiler. -/
def admitCoordinate
    {Variable : Type uVariable} {Value : Type uValue} :
    EncodedCoordinate Variable Value →
      Option (StoredCoordinate Variable Value)
  | .rigid value => some (.rigid value)
  | .rootVariable name => some (.storedVar name)
  | .nestedVariableStructure => none

namespace Canary

def repeatedRow : FlatStoredRow String String 2 where
  coordinate := fun _ => .storedVar "same"

def independentRow : FlatStoredRow String String 2 where
  coordinate := fun index =>
    if index = 0 then .storedVar "left" else .storedVar "right"

def queryAA : DeadBindingQuery String 2 := fun _ => some "a"

def queryAB : DeadBindingQuery String 2 := fun index =>
  if index = 0 then some "a" else some "b"

def deadQuery : DeadBindingQuery String 2 := fun _ => none

/-- Positive: one repeated stored variable may receive one rigid value twice. -/
example : PhysicalMatches repeatedRow queryAA := by
  apply (semanticMatches_iff_physicalMatches repeatedRow queryAA).mp
  refine ⟨fun _ => some "a", ?_⟩
  intro index
  simp [coordinateMatches, repeatedRow, queryAA]

/-- Negative: the same stored variable cannot receive two rigid values. -/
example : ¬ PhysicalMatches repeatedRow queryAB := by
  intro physical
  have requiresA : Requires repeatedRow queryAB "same" "a" := by
    refine ⟨0, ?_, ?_⟩ <;> rfl
  have requiresB : Requires repeatedRow queryAB "same" "b" := by
    refine ⟨1, ?_, ?_⟩ <;> rfl
  have impossible := requirements_unique
    repeatedRow queryAB physical.2 requiresA requiresB
  simp at impossible

/-- Dead query roots erase every stored-variable constraint. -/
example : PhysicalMatches repeatedRow deadQuery := by
  apply (semanticMatches_iff_physicalMatches repeatedRow deadQuery).mp
  exact ⟨fun _ => none, by intro index; simp [coordinateMatches, deadQuery]⟩

/-- Independent stored variables remain independently satisfiable. -/
example : PhysicalMatches independentRow queryAB := by
  apply (semanticMatches_iff_physicalMatches independentRow queryAB).mp
  refine ⟨fun name => if name = "left" then some "a" else some "b", ?_⟩
  intro index
  fin_cases index <;>
    simp [coordinateMatches, independentRow, queryAB]

/-- Duplicate stored occurrences contribute duplicate count. -/
example :
    collapseWith (CountAlg Unit Unit)
      (unitCountObservations [repeatedRow, repeatedRow]) = 2 := by
  rfl

/-- Nested stored variables decline this compiler rather than approximating. -/
example :
    admitCoordinate
      (EncodedCoordinate.nestedVariableStructure :
        EncodedCoordinate String String) = none := by
  rfl

/-- The physical positive canary also has an existential reference witness. -/
example : SemanticMatches repeatedRow queryAA :=
  ⟨fun _ => some "a", by
    intro index
    simp [coordinateMatches, repeatedRow, queryAA]⟩

end Canary

#print axioms selectedAssignment_eq_some_of_requires
#print axioms semanticMatches_iff_physicalMatches
#print axioms semanticRows_eq_directRows
#print axioms collapseCount_unitCountObservations
#print axioms directCount_exact
#print axioms viewDirectCount_exact

end Mettapedia.GSLT.LanguageDef.FlatTermDeadBindingCountCompilation
