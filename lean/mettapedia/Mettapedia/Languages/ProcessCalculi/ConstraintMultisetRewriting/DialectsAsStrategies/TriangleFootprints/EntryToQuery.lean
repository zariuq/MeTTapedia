import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.ServiceFootprints
import Mettapedia.Languages.MeTTa.HE.EquationFreshening

/-!
# From HE's entry to the equation query

`ExpressionTriangle` tied HE's run to its entry configuration of an expression
(`RecursiveMachine.Contextual.load`) but did not show that the run reaches the equation query: the
run first passes the type-directed entry, whose cast lookup is a parameter of the machine. Here the
run is built, for **flat ground calls**: `(f a₁ … aₙ)` where `f` and every `aᵢ` are data atoms (a
symbol other than `Empty` and `Error`, or a grounded value), `f` has no declaration in the
program, `f` is no host operation and no minimal instruction.

The services are HE's own: the machine's argument admission is HE's historical service (fixed by
`LocalStep`), and the cast lookup is any lookup meeting `AnswersUndefined` (every query under
`%Undefined%` demand answers at least one type), which HE's historical list-storage lookup
`Completed.rawLookup` meets (`raw_answers`), and so does HE's scoped lookup `Completed.scopedLookup`
(`scoped_answers`, `entry_reaches_equation_query_scoped`). A lookup that answers nothing fails it
(`silent_fails`).

## Results

* `entry_traced`: the run from `load` to the call of `(f a₁ … aₙ)` (`callConfig`), with the declared
  region of every move (`Traced`, under a declared lookup of `ServiceFootprints`), and its word:
  the interpretation's region, then the tuple traversal (`tupleWord`: a cast of each `aᵢ` reads the
  lookup's region of `aᵢ`, every other move reads nothing), then two moves reading nothing.
* `query_fires`: from the call, HE's equation query fires (`callAbsent` on an empty frontier,
  `callEquations` otherwise), and its declared region is H2's equation region
  `eqRegion [%Undefined%] (f a₁ … aₙ) ∅` (`query_region`). Every query has a frontier
  (`frontier_total`).
* `entry_reaches_equation_query`: the two together, the headline of this module.
* `entry_rows_empty`: under HE's raw lookup, on a program with no declaration of `f` or of the
  `aᵢ`, no move of the run before the query reads a row.

## Controls

* `silent_fails` (negative): the contract is not vacuous.
* `Controls.declared_head_blocks_tuple` (negative): with a declaration `(: f T)` in the program, the
  entry's tuple move of `entry_traced` is not available: the run's first move depends on the
  absence of declarations of `f`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace EntryToQuery

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isEmptyOrError isEmptyAtom isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeOccurrencesRel StorageTypesRel TypeCastBatchRel
  TypeMatchRel annotationType? annotationOccurrences withUndefined)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationRowResultsRel
  EquationWork AlphaVariantRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (MatchRel equalityGroundedSemantic)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (LogicalMergeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame
  TypeMatchingPolicy)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation Task)
open HEOnTheStep (HEConfig)
open ServiceFootprints

/-! ## The fragment and the lookup contract -/

/-- **Data atoms**: a symbol other than `Empty` (HE's empty atom) and `Error` (an error head), or a
grounded value. Under `%Undefined%` demand they are cast, and the cast returns them unchanged. -/
inductive DataAtom : Atom → Prop
  | symbol {name : String} : name ≠ "Empty" → name ≠ "Error" → DataAtom (.symbol name)
  | grounded (value : GroundedValue) : DataAtom (.grounded value)

/-- **The cast-lookup contract**: every query under `%Undefined%` demand answers at least one type. -/
def AnswersUndefined (lookup : CastLookup) : Prop :=
  ∀ (scope : List String) (space : Space) (bindings : Bindings) (subject : Atom),
    ∃ (type : Atom) (rest : List Atom),
      lookup scope space bindings subject Atom.undefinedType (type :: rest)

/-- **HE's historical list-storage lookup meets the contract.** -/
theorem raw_answers : AnswersUndefined Completed.rawLookup := by
  intro scope space bindings subject
  obtain ⟨types, queried⟩ := StorageTypesRel.total space subject
  cases types with
  | nil => exact absurd rfl queried.nonempty
  | cons type rest => exact ⟨type, rest, queried⟩

/-- **HE's scoped lookup (fresh variants of the stored declarations) meets the contract.** -/
theorem scoped_answers : AnswersUndefined Completed.scopedLookup := by
  intro scope space bindings subject
  obtain ⟨types, queried⟩ := StorageTypesRel.total space subject
  cases types with
  | nil => exact absurd rfl queried.nonempty
  | cons type rest =>
      obtain ⟨targets, variants⟩ :=
        Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Exact.ArgumentAlphaVariantsRel.exists
          (invocationTypeScope scope [] subject Atom.undefinedType bindings) (type :: rest)
      cases variants with
      | cons first later => exact ⟨_, _, Exists.intro (type :: rest) ⟨queried, .cons first later⟩⟩

/-- **Negative control: a lookup that answers nothing fails the contract.** -/
theorem silent_fails : ¬ AnswersUndefined (fun _ _ _ _ _ _ => False) := by
  intro answers
  obtain ⟨_, _, impossible⟩ := answers [] Space.empty Bindings.empty (.symbol "f")
  exact impossible

namespace DataAtom

theorem not_stopped {atom : Atom} (data : DataAtom atom) : ¬ IsEmptyOrErrorRel atom := by
  cases data with
  | symbol notEmpty _ =>
      rintro (same | ⟨tail, same⟩)
      · exact notEmpty (by simpa [Atom.empty] using same)
      · cases same
  | grounded value =>
      rintro (same | ⟨tail, same⟩)
      · simp [Atom.empty] at same
      · cases same

theorem emptyOrError {atom : Atom} (data : DataAtom atom) : isEmptyOrError atom = false := by
  cases data with
  | symbol notEmpty _ => simp [isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty, notEmpty]
  | grounded value => simp [isEmptyOrError, isEmptyAtom, isErrorAtom, Atom.empty]

theorem status {atom : Atom} (data : DataAtom atom) : (Entry.Value.ofAtom atom).status = .active := by
  cases data <;> simp [Entry.Value.ofAtom, Entry.Value.status]

/-- A data atom under `%Undefined%` demand is cast. -/
theorem entry (reentry : Entry.ReentryPolicy) {atom : Atom} (data : DataAtom atom) :
    Entry.Rel reentry .active atom Atom.undefinedType .cast := by
  cases data with
  | symbol notEmpty notError =>
      exact .cast (DataAtom.symbol notEmpty notError).not_stopped (.symbol _) (by decide +kernel)
        (Or.inl ⟨_, rfl⟩) (fun _ => Or.inr rfl)
  | grounded value =>
      exact .cast (DataAtom.grounded value).not_stopped (.grounded value) (by decide +kernel)
        (Or.inr (Or.inl ⟨value, rfl⟩)) (fun _ => Or.inr rfl)

end DataAtom

/-! ## One cast -/

/-- `%Undefined%` demand matches every actual type and keeps the bindings. -/
theorem undefined_matches (m : TypeMatchingPolicy) (actual : Atom) (frame : Frame) :
    m.Rel Atom.undefinedType actual frame.bindings frame.bindings := by
  cases m with
  | raw => exact TypeMatchRel.undefinedLeft actual frame.bindings
  | finite => exact ⟨TypeMatchRel.undefinedLeft actual frame.bindings, frame.certified.satisfiable⟩

/-- HE's machine step. -/
abbrev HEStep (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) :
    HEConfig → HEConfig → Prop :=
  Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual.Step dispatch lookup policy

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- **A data atom's cast**: under `%Undefined%` demand the cast returns the atom with the empty
activation, the lookup's first type being accepted. -/
theorem cast_step {lookup : CastLookup} (answers : AnswersUndefined lookup) (space : Space)
    {atom : Atom} (data : DataAtom atom) (live : List Atom) (scope : List String)
    (stack : List Continuation) (emitted : List Result) :
    HEStep dispatch lookup policy
      ⟨space, .work (.atom live scope (Entry.Value.ofAtom atom) Atom.undefinedType Frame.empty), stack,
        emitted⟩
      ⟨space, .returning [(Entry.Value.ofAtom atom, Frame.empty)], stack, emitted⟩ := by
  obtain ⟨type, rest, queried⟩ := answers
    (invocationTypeScope scope live atom Atom.undefinedType Frame.empty.bindings) space
    Frame.empty.bindings atom
  refine .internal (LocalStepWith.cast (raw := [(atom, Frame.empty.bindings)]) ?_ ?_ ?_)
  · simp only [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  · simp only [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
    exact TypeCastBatchRel.success (earlierTypes := []) queried rfl
      (fun _ member => by simp at member) (undefined_matches policy.matching type Frame.empty)
  · simp only [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
    exact .cons ⟨by simp [Completed.rawResult], .same _, by simp⟩ .nil

/-! ## Runs with their declared regions -/

/-- The region of a move that reads no row. -/
def nothing : Atom → Bool := fun _ => false

/-- **A run of HE's machine with the declared region of each move**, in order. -/
inductive Traced (D : DeclaredLookup) (dispatch : GroundedDispatch) (policy : Policy) :
    HEConfig → HEConfig → List (Atom → Bool) → Prop
  | refl (x : HEConfig) : Traced D dispatch policy x x []
  | step {x y z : HEConfig} {word : List (Atom → Bool)} :
      HEStep dispatch D.lookup policy x y → Traced D dispatch policy y z word →
      Traced D dispatch policy x z (heRegionD D policy x.control y.control :: word)

namespace Traced

variable {D : DeclaredLookup}

theorem steps {x z : HEConfig} {word : List (Atom → Bool)}
    (traced : Traced D dispatch policy x z word) :
    Relation.ReflTransGen (HEStep dispatch D.lookup policy) x z := by
  induction traced with
  | refl => exact .refl
  | step first _ ih => exact .head first ih

theorem trans {x y z : HEConfig} {word word' : List (Atom → Bool)}
    (first : Traced D dispatch policy x y word) (second : Traced D dispatch policy y z word') :
    Traced D dispatch policy x z (word ++ word') := by
  revert second
  induction first with
  | refl => exact id
  | step here _ ih => exact fun second => .step here (ih second)

theorem cons {x y z : HEConfig} {word : List (Atom → Bool)} {ρ : Atom → Bool}
    (here : HEStep dispatch D.lookup policy x y)
    (region : heRegionD D policy x.control y.control = ρ) (rest : Traced D dispatch policy y z word) :
    Traced D dispatch policy x z (ρ :: word) := by
  subst region
  exact .step here rest

end Traced

/-- A data atom's cast reads the lookup's region of the atom. -/
theorem cast_region (D : DeclaredLookup) {atom : Atom} (data : DataAtom atom) (live : List Atom)
    (scope : List String) (after : Control) :
    heRegionD D policy (.work (.atom live scope (Entry.Value.ofAtom atom) Atom.undefinedType
      Frame.empty)) after = D.region atom := by
  have entry : Entry.Rel policy.reentry (Frame.empty.read policy (Entry.Value.ofAtom atom)).status
      (Frame.empty.read policy (Entry.Value.ofAtom atom)).erase Atom.undefinedType .cast := by
    simp only [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, data.status]
    exact data.entry policy.reentry
  rw [heRegionD_cast entry, Completed.Frame.read_empty, Entry.Value.erase_ofAtom]

/-! ## The tuple traversal -/

theorem map_erase_ofAtom (atoms : List Atom) :
    (atoms.map Entry.Value.ofAtom).map Entry.Value.erase = atoms := by
  simp [List.map_map, Function.comp_def]

theorem tupleSingleton_data {atom : Atom} (data : DataAtom atom) (frame : Frame) :
    Completed.tupleSingleton (Entry.Value.ofAtom atom, frame) =
      (.expression .active [Entry.Value.ofAtom atom], frame) := by
  unfold Completed.tupleSingleton
  have erased : ((Entry.Value.ofAtom atom, frame) : Result).1.erase = atom :=
    Entry.Value.erase_ofAtom atom
  rw [erased, data.emptyOrError]
  rfl

theorem expression_emptyOrError {atom : Atom} (data : DataAtom atom) (rest : List Atom) :
    isEmptyOrError (.expression (atom :: rest)) = false := by
  have notEmpty : isEmptyAtom (.expression (atom :: rest)) = false := by
    simp [isEmptyAtom, Atom.empty]
  have notError : isErrorAtom (.expression (atom :: rest)) = false := by
    cases data with
    | symbol _ notError => simp [isErrorAtom, notError]
    | grounded value => rfl
  simp [isEmptyOrError, notEmpty, notError]

theorem tuplePrepend_data {atom : Atom} (data : DataAtom atom) (rest : List Atom)
    (head : Entry.Value) (frame : Frame) :
    Completed.tuplePrepend head (.expression .active ((atom :: rest).map Entry.Value.ofAtom), frame) =
      (.expression .active (head :: (atom :: rest).map Entry.Value.ofAtom), frame) := by
  unfold Completed.tuplePrepend
  have erased : ((Entry.Value.expression .active ((atom :: rest).map Entry.Value.ofAtom), frame) :
      Result).1.erase = .expression (atom :: rest) := by
    show (Entry.Value.expression .active ((atom :: rest).map Entry.Value.ofAtom)).erase = _
    simp only [Entry.Value.erase, map_erase_ofAtom]
  rw [erased, expression_emptyOrError data rest]
  rfl

/-- **The declared regions of the tuple traversal of data atoms**: the cast of each atom reads the
lookup's region of it; every other move reads nothing. -/
def tupleWord (D : DeclaredLookup) : List Atom → List (Atom → Bool)
  | [] => []
  | [atom] => [nothing, D.region atom, nothing]
  | atom :: next :: rest =>
      [nothing, D.region atom, nothing, nothing] ++ tupleWord D (next :: rest) ++
        [nothing, nothing, nothing, nothing]

/-- **The tuple traversal of data atoms**: from pending work on the tuple, HE's machine returns the
expression of the atoms with the empty activation, its moves reading `tupleWord`. -/
theorem tuple_traced (D : DeclaredLookup) (answers : AnswersUndefined D.lookup) (space : Space) :
    ∀ (values : List Atom), values ≠ [] → (∀ v ∈ values, DataAtom v) →
      ∀ (live : List Atom) (scope : List String) (stack : List Continuation)
        (emitted : List Result),
        Traced D dispatch policy
          ⟨space, .work (.tuple live scope (values.map Entry.Value.ofAtom) Frame.empty), stack,
            emitted⟩
          ⟨space, .returning [(.expression .active (values.map Entry.Value.ofAtom), Frame.empty)],
            stack, emitted⟩
          (tupleWord D values)
  | [], nonempty, _ => absurd rfl nonempty
  | [atom], _, data => by
      intro live scope stack emitted
      have here := data atom List.mem_cons_self
      refine .cons (.internal .tupleSingleton) rfl ?_
      refine .cons (cast_step answers space here _ _ _ _) (cast_region D here _ _ _) ?_
      refine .cons (.internal .singleton) rfl ?_
      rw [List.map_singleton (f := Completed.tupleSingleton), tupleSingleton_data here]
      exact .refl _
  | atom :: next :: rest, _, data => by
      intro live scope stack emitted
      have here := data atom List.mem_cons_self
      have later : ∀ v ∈ next :: rest, DataAtom v := fun v member =>
        data v (List.mem_cons_of_mem _ member)
      have nextData := later next List.mem_cons_self
      refine .cons (.internal .tupleCons) rfl ?_
      refine .cons (cast_step answers space here _ _ _ _) (cast_region D here _ _ _) ?_
      refine .cons (.internal .branches) rfl ?_
      refine .cons (.internal (.branchesContinue ?_)) rfl ?_
      · simpa using here.not_stopped
      refine .trans (tuple_traced D answers space (next :: rest) (List.cons_ne_nil _ _) later
        _ _ _ _) ?_
      refine .cons (.internal .tupleTail) rfl ?_
      rw [List.map_singleton (f := Completed.tuplePrepend _), tuplePrepend_data nextData rest]
      refine .cons (.internal .append) rfl ?_
      refine .cons (.internal .branchesNil) rfl ?_
      refine .cons (.internal .prepend) rfl ?_
      exact .refl _

/-! ## The entry -/

/-- The call `(f a₁ … aₙ)` as the value HE's tuple traversal returns. -/
def callValue (f : String) (args : List Atom) : Entry.Value :=
  .expression .active ((Atom.symbol f :: args).map Entry.Value.ofAtom)

theorem callValue_erase (f : String) (args : List Atom) :
    (callValue f args).erase = .expression (.symbol f :: args) := by
  simp only [callValue, Entry.Value.erase, map_erase_ofAtom]

/-- **The call configuration**: pending work on the call `(f a₁ … aₙ)` under `%Undefined%`, with
the empty activation, over the program's space. -/
def callConfig (atoms : List Atom) (f : String) (args : List Atom) : HEConfig :=
  ⟨Space.ofList atoms, .work (.call [] [] (callValue f args) Atom.undefinedType Frame.empty),
    [.append (.calls [] [] Atom.undefinedType []), .publish (.expression (.symbol f :: args))], []⟩

/-- The entry of a call is an interpretation. -/
theorem call_entry (policy : Policy) {f : String} (headData : DataAtom (.symbol f))
    (args : List Atom) :
    Entry.Rel policy.reentry
      (Frame.empty.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).status
      (Frame.empty.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
      Atom.undefinedType .interpret := by
  rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  have status : (Entry.Value.ofAtom (.expression (.symbol f :: args))).status = .active := by
    simp [Entry.Value.ofAtom, Entry.Value.status]
  rw [status]
  refine .expression ?_ (by decide +kernel) (Or.inr rfl)
  rintro (same | ⟨tail, same⟩)
  · simp [Atom.empty] at same
  · cases headData with
    | symbol _ notError =>
        simp at same
        exact notError same.1

/-- With no declaration of `f`, the type collection of `f` is `%Undefined%` alone. -/
theorem untyped_occurrences {atoms : List Atom} {f : String}
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []) :
    TypeOccurrencesRel ((Space.ofList atoms).atoms : Multiset Atom) (.symbol f)
      {Atom.undefinedType} := by
  have filtered : (Space.ofList atoms).atoms.filter
      (fun row => (annotationType? (.symbol f) row).isSome) = [] := untyped
  have none : annotationOccurrences ((Space.ofList atoms).atoms : Multiset Atom) (.symbol f) = 0 := by
    unfold annotationOccurrences
    rw [Multiset.filterMap_coe, ← filterMap_filter_isSome, filtered]
    rfl
  have collected := TypeOccurrencesRel.symbol (atoms := ((Space.ofList atoms).atoms : Multiset Atom)) f
  rw [none] at collected
  simpa [withUndefined] using collected

/-- **The type-directed entry**: the call is interpreted, and with no declaration of `f` HE's machine
evaluates it as a tuple, under the calls and publication continuations. -/
theorem entry_step {lookup : CastLookup} {atoms : List Atom} {f : String} {args : List Atom}
    (headData : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []) :
    HEStep dispatch lookup policy
      (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
      ⟨Space.ofList atoms, .work (.tuple [Atom.undefinedType] []
          ((Atom.symbol f :: args).map Entry.Value.ofAtom) Frame.empty),
        [.calls [] [] Atom.undefinedType, .publish (.expression (.symbol f :: args))], []⟩ := by
  have shape : Frame.empty.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args))) =
      .expression .active (Entry.Value.ofAtom (.symbol f) :: args.map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have occurrences : TypeOccurrencesRel ((Space.ofList atoms).atoms : Multiset Atom)
      (Entry.Value.ofAtom (.symbol f)).erase {Atom.undefinedType} := by
    rw [Entry.Value.erase_ofAtom]
    exact untyped_occurrences untyped
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := dispatch) (lookup := lookup) (live := []) (scope := []) (stack := [])
    (call_entry policy headData args) shape occurrences
  have published : (Frame.empty.read policy
      (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase = .expression (.symbol f :: args) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  exact .internal step

/-- The entry reads the interpretation's region of the call. -/
theorem entry_region (D : DeclaredLookup) {f : String} (headData : DataAtom (.symbol f))
    (args : List Atom) (after : Control) :
    heRegionD D policy (.work (.atom [] [] (Entry.Value.ofAtom (.expression (.symbol f :: args)))
      Atom.undefinedType Frame.empty)) after = interpretRegion D (.expression (.symbol f :: args)) := by
  rw [heRegionD_interpret (call_entry policy headData args), Completed.Frame.read_empty,
    Entry.Value.erase_ofAtom]

/-- **The declared word of the run from the entry to the call.** -/
def entryWord (D : DeclaredLookup) (f : String) (args : List Atom) : List (Atom → Bool) :=
  interpretRegion D (.expression (.symbol f :: args)) :: (tupleWord D (.symbol f :: args) ++
    [nothing, nothing])

/-- **From the entry to the call, with the declared region of every move.** -/
theorem entry_traced (D : DeclaredLookup) (answers : AnswersUndefined D.lookup)
    {atoms : List Atom} {f : String} {args : List Atom}
    (data : ∀ a ∈ Atom.symbol f :: args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = []) :
    Traced D dispatch policy
      (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
      (callConfig atoms f args) (entryWord D f args) := by
  have headData := data _ List.mem_cons_self
  refine .cons (entry_step headData untyped) (entry_region D headData args _) ?_
  refine .trans (tuple_traced D answers _ (Atom.symbol f :: args) (List.cons_ne_nil _ _) data
    _ _ _ _) ?_
  refine .cons (.internal .calls) rfl ?_
  refine .cons (.internal .callsCons) rfl ?_
  exact .refl _

/-! ## The equation query -/

/-- Every row has a block of works for an equation query. -/
theorem rowResults_total (live : List Atom) (query : Atom) (incoming : Bindings) (position : ℕ)
    (row : Atom) : ∃ block, EquationRowResultsRel live query incoming position row block := by
  classical
  by_cases isEquation : ∃ left right, row = .expression [.symbol "=", left, right]
  · obtain ⟨left, right, rfl⟩ := isEquation
    by_cases hit : ∃ pattern body, AlphaVariantRel live query incoming left right pattern body ∧
        ∃ matched output, MatchRel equalityGroundedSemantic query pattern matched ∧
          LogicalMergeRel matched incoming output
    · obtain ⟨pattern, body, alpha, matched, output, matching, merged⟩ := hit
      exact ⟨_, .hit position left right pattern body matched output alpha matching merged⟩
    · exact ⟨[], .miss position left right _ _
        (Mettapedia.Languages.MeTTa.HE.EquationFreshening.freshRule_alphaVariant live query left
          right incoming position)
        (fun pattern body alpha matched output viable =>
          hit ⟨pattern, body, alpha, matched, output, viable.1, viable.2⟩)⟩
  · exact ⟨[], .irrelevant position row fun left right same => isEquation ⟨left, right, same⟩⟩

/-- **Every equation query has a frontier.** -/
theorem frontier_total (space : Space) (live : List Atom) (query : Atom) (incoming : Bindings) :
    ∃ works, EquationFrontierRel space live query incoming works := by
  have blocks : ∀ rows : List (Atom × ℕ), ∃ blocks : List (List EquationWork),
      List.Forall₂ (fun row block => EquationRowResultsRel live query incoming row.2 row.1 block)
        rows blocks := by
    intro rows
    induction rows with
    | nil => exact ⟨[], .nil⟩
    | cons row rows ih =>
        obtain ⟨block, here⟩ := rowResults_total live query incoming row.2 row.1
        obtain ⟨blocks, rest⟩ := ih
        exact ⟨block :: blocks, .cons here rest⟩
  obtain ⟨blocks, covered⟩ := blocks space.atoms.zipIdx
  exact ⟨_, .completed covered⟩

/-- Where the query leads: the call's value returned on an empty frontier, the frontier's works
otherwise. -/
def queryTarget (atoms : List Atom) (f : String) (args : List Atom) :
    List EquationWork → HEConfig
  | [] => ⟨Space.ofList atoms, .returning [(callValue f args, Frame.empty)],
      [.append (.calls [] [] Atom.undefinedType []), .publish (.expression (.symbol f :: args))], []⟩
  | work :: works => ⟨Space.ofList atoms,
      .work (.equations [] [] (callValue f args) Atom.undefinedType Frame.empty (work :: works)),
      [.append (.calls [] [] Atom.undefinedType []), .publish (.expression (.symbol f :: args))], []⟩

theorem call_not_error {f : String} (headData : DataAtom (.symbol f)) (args : List Atom) :
    ¬ IsErrorRel (callValue f args).erase := by
  rw [callValue_erase]
  rintro ⟨tail, same⟩
  cases headData with
  | symbol _ notError =>
      simp at same
      exact notError same.1

/-- **HE's equation query fires from the call.** -/
theorem query_fires {lookup : CastLookup} {atoms : List Atom} {f : String} {args : List Atom}
    (headData : DataAtom (.symbol f)) (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: args)) = false)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) [Atom.undefinedType]
      (.expression (.symbol f :: args)) Bindings.empty works) :
    HEStep dispatch lookup policy (callConfig atoms f args) (queryTarget atoms f args works) := by
  have notError := call_not_error headData args
  have nonGrounded : NonGroundedCallRel dispatch (callValue f args).erase := by
    rw [callValue_erase]
    refine And.intro ?_ notInstruction
    intro host
    obtain ⟨operator, arguments, same, executable⟩ := host
    simp at same
    rw [← same.1] at executable
    exact notHost executable
  have frontier' : EquationFrontierRel (Space.ofList atoms) [Atom.undefinedType]
      (callValue f args).erase Frame.empty.bindings works := by
    rw [callValue_erase]
    exact frontier
  cases works with
  | nil => exact .internal (.callAbsent notError nonGrounded frontier')
  | cons work works =>
      exact .internal (.callEquations notError nonGrounded frontier' (List.cons_ne_nil _ _))

/-- **The query reads the equation region of the call.** -/
theorem query_region (D : DeclaredLookup) {atoms : List Atom} {f : String} {args : List Atom}
    (headData : DataAtom (.symbol f)) (works : List EquationWork) :
    heRegionD D policy (callConfig atoms f args).control (queryTarget atoms f args works).control =
      eqRegion [Atom.undefinedType] (.expression (.symbol f :: args)) Bindings.empty := by
  have notAtom : ¬ ∃ live scope value expected activation,
      (callConfig atoms f args).control = .work (.atom live scope value expected activation) := by
    rintro ⟨_, _, _, _, _, same⟩
    cases same
  rw [heRegionD_of_not_atom notAtom]
  cases works with
  | nil =>
      show heRegion policy (.work (.call [] [] (callValue f args) Atom.undefinedType Frame.empty))
        (.returning [(callValue f args, Frame.empty)]) = _
      rw [heRegion_call_returning, if_neg (call_not_error headData args), callValue_erase]
      rfl
  | cons work works =>
      show heRegion policy (.work (.call [] [] (callValue f args) Atom.undefinedType Frame.empty))
        (.work (.equations [] [] (callValue f args) Atom.undefinedType Frame.empty (work :: works))) = _
      rw [heRegion_call_equations, if_neg (call_not_error headData args), callValue_erase]
      rfl

/-- **HE's run from the entry reaches the equation query** (obligation 1). For a flat ground call
`(f a₁ … aₙ)` of data atoms, with no declaration of `f`, `f` no host operation and no instruction,
and a cast lookup meeting `AnswersUndefined`: HE's machine runs from `load` to the call, with the
declared word `entryWord`; the equation query has a frontier, fires, and reads H2's equation
region. -/
theorem entry_reaches_equation_query (D : DeclaredLookup) (answers : AnswersUndefined D.lookup)
    {atoms : List Atom} {f : String} {args : List Atom}
    (data : ∀ a ∈ Atom.symbol f :: args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: args)) = false) :
    Relation.ReflTransGen (HEStep dispatch D.lookup policy)
        (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
        (callConfig atoms f args) ∧
      Traced D dispatch policy
        (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
        (callConfig atoms f args) (entryWord D f args) ∧
      ∃ works, EquationFrontierRel (Space.ofList atoms) [Atom.undefinedType]
          (.expression (.symbol f :: args)) Bindings.empty works ∧
        HEStep dispatch D.lookup policy (callConfig atoms f args) (queryTarget atoms f args works) ∧
        heRegionD D policy (callConfig atoms f args).control (queryTarget atoms f args works).control =
          eqRegion [Atom.undefinedType] (.expression (.symbol f :: args)) Bindings.empty := by
  have headData := data _ List.mem_cons_self
  have traced := entry_traced (dispatch := dispatch) (policy := policy) D answers data untyped
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) [Atom.undefinedType]
    (.expression (.symbol f :: args)) Bindings.empty
  exact ⟨traced.steps, traced, works, frontier, query_fires headData notHost notInstruction frontier,
    query_region D headData works⟩

/-- **The same with HE's scoped lookup**, the other cast lookup HE's spec provides. -/
theorem entry_reaches_equation_query_scoped {atoms : List Atom} {f : String} {args : List Atom}
    (data : ∀ a ∈ Atom.symbol f :: args, DataAtom a)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: args)) = false) :
    Traced scopedDeclared dispatch policy
        (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
        (callConfig atoms f args) (entryWord scopedDeclared f args) ∧
      ∃ works, EquationFrontierRel (Space.ofList atoms) [Atom.undefinedType]
          (.expression (.symbol f :: args)) Bindings.empty works ∧
        HEStep dispatch scopedDeclared.lookup policy (callConfig atoms f args)
          (queryTarget atoms f args works) :=
  let headline := entry_reaches_equation_query (dispatch := dispatch) (policy := policy)
    scopedDeclared scoped_answers data untyped notHost notInstruction
  ⟨headline.2.1, headline.2.2.elim fun works facts => ⟨works, facts.1, facts.2.1⟩⟩

/-! ## What the run reads before the query -/

theorem tupleWord_mem {D : DeclaredLookup} :
    ∀ (values : List Atom) (ρ : Atom → Bool), ρ ∈ tupleWord D values →
      ρ = nothing ∨ ∃ a ∈ values, ρ = D.region a
  | [], _, member => by simp [tupleWord] at member
  | [atom], ρ, member => by
      simp only [tupleWord, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr ⟨atom, List.mem_cons_self, rfl⟩
      · exact Or.inl rfl
  | atom :: next :: rest, ρ, member => by
      simp only [tupleWord, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with ((rfl | rfl | rfl | rfl) | inner) | (rfl | rfl | rfl | rfl)
      · exact Or.inl rfl
      · exact Or.inr ⟨atom, List.mem_cons_self, rfl⟩
      · exact Or.inl rfl
      · exact Or.inl rfl
      · rcases tupleWord_mem _ _ inner with same | ⟨a, inValues, same⟩
        · exact Or.inl same
        · exact Or.inr ⟨a, List.mem_cons_of_mem _ inValues, same⟩
      all_goals exact Or.inl rfl

theorem regionRows_eq_nil {ρ : Atom → Bool} {rows : List Atom}
    (outside : ∀ row ∈ rows, ρ row = false) : regionRows ρ rows = [] := by
  apply List.eq_nil_of_map_eq_nil (f := Prod.fst)
  rw [map_fst_regionRows]
  exact List.filter_eq_nil_iff.mpr fun row member => by simp [outside row member]

theorem any_false {p : Atom → Bool} : ∀ {l : List Atom}, (∀ a ∈ l, p a = false) → l.any p = false
  | [], _ => rfl
  | a :: l, outside => by
      rw [List.any_cons, outside a List.mem_cons_self, Bool.false_or]
      exact any_false fun b member => outside b (List.mem_cons_of_mem _ member)

/-- **Before the query, the run reads no row of a program that declares none of the call's
atoms**: under HE's raw lookup, every region of `entryWord` holds no row of the program. -/
theorem entry_rows_empty {atoms : List Atom} {f : String} {args : List Atom}
    (undeclared : ∀ a ∈ Atom.symbol f :: args, ∀ row ∈ atoms, typeRegion a row = false) :
    ∀ ρ ∈ entryWord rawDeclared f args, regionRows ρ atoms = [] := by
  intro ρ member
  apply regionRows_eq_nil
  intro row inAtoms
  simp only [entryWord, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
  rcases member with rfl | inTuple | rfl | rfl
  · have headOut := undeclared _ List.mem_cons_self row inAtoms
    have argsOut : (args.any fun argument => typeRegion argument row) = false :=
      any_false fun a member => undeclared a (List.mem_cons_of_mem _ member) row inAtoms
    show (typeRegion (.symbol f) row || (typeRegion (.symbol f) row ||
      args.any fun argument => typeRegion argument row)) = false
    simp [headOut, argsOut]
  · rcases tupleWord_mem _ _ inTuple with rfl | ⟨a, inValues, rfl⟩
    · rfl
    · exact undeclared a inValues row inAtoms
  · rfl
  · rfl

/-! ## Controls -/

namespace Controls

/-- `(: f Number)`. -/
def declareF : Atom := .expression [.symbol ":", .symbol "f", .symbol "Number"]

/-- **Negative control: a declaration of the head blocks the tuple entry.** With `(: f Number)` in
the program, the type collection of `f` is not `%Undefined%` alone, so the entry move of
`entry_traced` is not available: HE's run depends on the absence of declarations of `f`. -/
theorem declared_head_blocks_tuple :
    ¬ TypeOccurrencesRel ((Space.ofList [declareF]).atoms : Multiset Atom) (.symbol "f")
        {Atom.undefinedType} ∧
      (Space.ofList [declareF]).atoms.filter (typeRegion (.symbol "f")) = [declareF] := by
  constructor
  · intro collected
    have actual := TypeOccurrencesRel.symbol (atoms := ((Space.ofList [declareF]).atoms : Multiset Atom))
      "f"
    have same := collected.unique actual
    have found : [declareF].filterMap (annotationType? (.symbol "f")) = [.symbol "Number"] := by
      decide +kernel
    have occurrences : annotationOccurrences ((Space.ofList [declareF]).atoms : Multiset Atom)
        (.symbol "f") = {.symbol "Number"} := by
      unfold annotationOccurrences
      rw [show (Space.ofList [declareF]).atoms = [declareF] from rfl, Multiset.filterMap_coe, found]
      exact Multiset.coe_singleton _
    rw [occurrences] at same
    simp [withUndefined, Atom.undefinedType] at same
  · decide +kernel

end Controls

#print axioms raw_answers
#print axioms scoped_answers
#print axioms silent_fails
#print axioms cast_step
#print axioms tuple_traced
#print axioms entry_step
#print axioms entry_traced
#print axioms frontier_total
#print axioms query_fires
#print axioms query_region
#print axioms entry_reaches_equation_query
#print axioms entry_reaches_equation_query_scoped
#print axioms entry_rows_empty
#print axioms Controls.declared_head_blocks_tuple

end EntryToQuery

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
