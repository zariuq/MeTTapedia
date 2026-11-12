import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfConditions

/-!
# HE and PeTTa agree on `if` inside bodies, on every run, on the scoped lookup

`ScopedIf` gives HE's `if` at every frame on the scoped lookup: every derivation publishes the branch
taken (`if_source_scoped`) and every run finishes (`fine_if_scoped`). Here `if` becomes a node kind of
a settling class, so it may stand inside equation bodies, as an argument of a constructor, and twice
in one body.

* `Nested`: the argument-product lemmas of `NestedEveryRun` (tuple rows, calls, constructor queries,
  nested determinism) for **any** lookup meeting the contract. `NestedEveryRun` states them for the
  historical lookup only; the proofs carry over with the lookup as a parameter.
* `SettlesIf`: a term settles when it is a data atom; an `if` node `(if c y n)` whose condition is a
  condition of `IfConditions` (a Boolean literal, or a Boolean call such as `(isTrue)`) and whose
  branches are data (the taken one undeclared); a constructor applied to settling terms; or an
  ordinary call of data whose region's bodies (closed, so instance and body coincide) all settle. A
  call whose body is the special form is the `call` node whose body is an `if` node.
* `settlesIf_determined`: every derivation of HE's completed relation for a settling term, at every
  frame, publishes its answers (scoped lookup).
* `settlesIf_fine`: every marked presentation of a settling term runs finely to its answers.
* `settlesIf_petta`: PeTTa's streaming machine evaluates it to the same answers; for an `if` node
  that is PeTTa's special form (`IfComputed.petta_if_computed`).
* `if_bodies_every_run`: **a complete HE run exists, every complete run publishes PeTTa's answers,
  no run is infinite and every reachable configuration steps or is final with those answers**, on
  the scoped lookup.

## Controls

* `Controls.both_every_run` (positive, the polymorphic `if` twice in one body):
  `(= (both) (pair (if True yes no) (if False yes no)))`; every run of `(both)` finishes and
  publishes `(pair yes no)`, as PeTTa does.
* `Controls.pick_every_run` (positive, a call whose body is the special form):
  `(= (pick) (if True yes no))`; every run of `(pick)` finishes with `yes`.
* `Controls.byCall_every_run` (positive, a computed condition inside a body):
  `(= (isTrue) True)`, `(= (byCall) (if (isTrue) yes no))`; every run of `(byCall)` finishes with
  `yes`, as PeTTa does.
* `Controls.declared_branch_not_in_class` (negative, the class's boundary): `(if True 1 2)` is not an
  `if` node of the class, since its taken branch `1` has the declared type `Number`
  (`DeclaredBranchGap` shows why).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfInBodies

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches EveryRunFinishes IfFinishes
  IfComputed ScopedTransfer ScopedIf IfConditions
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## The argument product under any lookup -/

section Nested

variable {lookup : CastLookup}

/-- `t` has answerable answers `L`, determined under `lookup`. -/
def SettledU (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  (∀ a ∈ L, Answerable a) ∧ DeterminedUnder dispatch lookup policy atoms t L

/-- HE's query of `(f vals)` under `lookup` is determined to `A`, on every call value. -/
def QueryDeterminedU (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (value : Entry.Value) (frame : Frame)
    (children : List Result), value.erase = .expression (.symbol f :: vals) →
    Completed.CallRel (Space.ofList atoms) dispatch lookup live scope value
      Atom.undefinedType frame children (policy := policy) →
    children.map (fun r => r.1.erase) = A

theorem data_settled_u (contract : LookupContract lookup) {atoms : List Atom} {d : Atom}
    (data : DataAtom d) : SettledU dispatch lookup policy atoms d [d] :=
  ⟨fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data,
    fun _ _ _ _ derived => by
      obtain ⟨after, rfl⟩ := data_source contract data derived
      simp⟩

theorem branches_rows_u {atoms : List Atom} {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ls : List (List Atom)}
    (tupleRows : ∀ (live : List Atom) (frame : Frame) (results : List Result),
      Completed.TupleRel (Space.ofList atoms) dispatch lookup live scope tail frame
        results (policy := policy) → List.Forall₂ CleanRow results (combos Ls)) :
    ∀ (heads results : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      Completed.TupleBranchesRel (Space.ofList atoms) dispatch lookup live scope tail
        heads results (policy := policy) →
      List.Forall₂ CleanRow results (heads.flatMap fun h => (combos Ls).map (h.1.erase :: ·))
  | [], _, _, derived => by
      cases derived
      exact .nil
  | h :: hs, _, clean, derived => by
      cases derived with
      | stopped stopped _ => exact absurd stopped (clean h List.mem_cons_self).notStopped
      | continuing _ children rest =>
          rw [List.flatMap_cons]
          refine forall₂_append ?_ (branches_rows_u tupleRows hs _
            (fun r member => clean r (List.mem_cons_of_mem _ member)) rest)
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact (tupleRows _ _ _ children).imp fun _ _ row =>
            prepend_row h.1 (clean h List.mem_cons_self) row

theorem tuple_rows_u {atoms : List Atom} {scope : List String} :
    ∀ (ts : List Atom) (Ls : List (List Atom)),
      List.Forall₂ (SettledU dispatch lookup policy atoms) ts Ls →
      ts ≠ [] → ∀ (live : List Atom) (frame : Frame) (results : List Result),
        Completed.TupleRel (Space.ofList atoms) dispatch lookup live scope
          (ts.map Entry.Value.ofAtom) frame results (policy := policy) →
        List.Forall₂ CleanRow results (combos Ls)
  | [], _, _, nonempty, _, _, _, _ => absurd rfl nonempty
  | [t], _, related, _, live, frame, results, derived => by
      obtain ⟨L, Ls', ⟨clean, determined⟩, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      obtain rfl := List.forall₂_nil_left_iff.mp rest
      simp only [List.map_cons, List.map_nil] at derived
      cases derived with
      | singleton headDerived =>
          have erased := determined _ _ _ _ headDerived
          have rows := singleton_rows (HENested.clean_of_erase erased clean)
          subst erased
          rw [combos_singleton, List.map_map]
          exact rows
  | t :: t2 :: rest, _, related, _, live, frame, results, derived => by
      obtain ⟨L, Ls', ⟨clean, determined⟩, restRel, rfl⟩ := List.forall₂_cons_left_iff.mp related
      simp only [List.map_cons] at derived
      cases derived with
      | cons headDerived branches =>
          have erased := determined _ _ _ _ headDerived
          have rows := branches_rows_u
            (fun live' frame' results' tupled =>
              tuple_rows_u (t2 :: rest) Ls' restRel (List.cons_ne_nil _ _) live' frame' results'
                tupled)
            _ _ (HENested.clean_of_erase erased clean) branches
          rwa [flatMap_heads erased] at rows

theorem calls_rows_u {atoms : List Atom} {live : List Atom} {scope : List String} {f : String}
    {Q : List Atom → List Atom} :
    ∀ (rows : List Result) (cs : List (List Atom)) (raw : List Result),
      List.Forall₂ (fun r vals => r.1.erase = .expression (.symbol f :: vals)) rows cs →
      (∀ vals ∈ cs, QueryDeterminedU dispatch lookup policy atoms f vals (Q vals)) →
      Completed.CallsRel (Space.ofList atoms) dispatch lookup live scope
        Atom.undefinedType rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = cs.flatMap Q
  | [], _, _, related, _, derived => by
      cases related
      cases derived
      rfl
  | _ :: rs, _, _, related, queries, derived => by
      obtain ⟨vals, cs', erased, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons called later =>
          rw [List.map_append, queries vals List.mem_cons_self _ _ _ _ _ erased called,
            calls_rows_u rs cs' _ rest (fun v member => queries v (List.mem_cons_of_mem _ member))
              later, List.flatMap_cons]

/-- **A query of a constructor (empty region) returns the call**, under any lookup. -/
theorem query_absent_u {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (valsClean : ∀ v ∈ vals, Answerable v) (empty : regionBodies atoms f vals = []) :
    QueryDeterminedU dispatch lookup policy atoms f vals [.expression (.symbol f :: vals)] := by
  intro live scope value frame children erased called
  have ground : ∀ v ∈ vals,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  have fixed : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    rw [empty]
    intro b member
    cases member
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, notInstruction] at instruction
      cases instruction
  | absent _ _ _ => simp [erased]
  | equations _ _ frontier nonempty _ =>
      rw [erased] at frontier
      have bodies := HERuns.frontier_bodies ground frame.certified.satisfiable program fixed frontier
      rw [empty] at bodies
      exact absurd (List.map_eq_nil_iff.mp bodies) nonempty

/-- **Nested calls are determined, compositionally, under any lookup meeting the contract**
(`NestedEveryRun.nested_determined` with the lookup as a parameter). -/
theorem nested_determined_u (contract : LookupContract lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name)
    (args : List.Forall₂ (SettledU dispatch lookup policy atoms) ts Ls) (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      QueryDeterminedU dispatch lookup policy atoms f vals (Q vals)) :
    SettledU dispatch lookup policy atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap Q) := by
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).1 a inner
  refine ⟨answerableAll, fun live scope frame results derived => ?_⟩
  have readCall := HERuns.read_closed policy frame closed
  have entry : Entry.Rel policy.reentry
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: ts)))).status
      (frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: ts)))).erase
      Atom.undefinedType .interpret := by
    have base := call_entry policy head ts
    rw [Completed.Frame.read_empty] at base
    rw [readCall]
    exact base
  have shape : frame.read policy (Entry.Value.ofAtom (.expression (.symbol f :: ts))) =
      .expression .active (Entry.Value.ofAtom (.symbol f) :: ts.map Entry.Value.ofAtom) := by
    rw [readCall]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have storage : StorageTypesRel (Space.ofList atoms) (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences untyped)
  have exact : ∀ {live : List Atom} {scope : List String} {expression : Atom} {frame : Frame}
      {outcome : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) lookup policy live scope expression
        (.symbol f) Atom.undefinedType frame outcome → outcome = .exhausted [] true :=
    fun chosen => chosen.undefined_exact_of_query fun _ queried =>
      contract.undeclared _ _ _ _ _ storage queried
  have batch : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.ofAtom (.symbol f) = operator → ts.map Entry.Value.ofAtom = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch lookup
        (Atom.undefinedType :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch lookup live scope
        Atom.undefinedType rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro operator arguments rows raw sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    have rowsShape := tuple_rows_u (Atom.symbol f :: ts) ([Atom.symbol f] :: Ls)
      (.cons (data_settled_u contract head) args) (List.cons_ne_nil _ _) _ _ _ tuples
    rw [combos_head, List.forall₂_map_right_iff] at rowsShape
    exact calls_rows_u _ _ _ (rowsShape.imp fun _ _ row => row.2.1)
      (fun vals member => (apps vals member).2) calls
  have publish : ∀ {raw selected : List Result},
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      selected.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro raw selected erased chosen
    have cleanRaw := HENested.clean_of_erase erased answerableAll
    have unchanged : raw.map (Completed.readResult policy) = raw :=
      map_fixed fun r member => HERuns.readResult_closed policy r (cleanRaw r member).closed
    rw [unchanged] at chosen
    have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
      chosen (HERuns.success_all raw fun r member => (cleanRaw r member).notError)
    rw [same, erased]
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped _ tuples calls chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      rw [publish_erase]
      exact publish (batch sameOperator sameArguments tuples calls) chosen
  | function _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      cases exact chosen
  | fallback _ shaped chosen tuples calls selected =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      have operatorErase := congrArg Entry.Value.erase sameOperator
      rw [Entry.Value.erase_ofAtom] at operatorErase
      rw [← operatorErase] at chosen
      have exhausted := exact chosen
      simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
      subst exhausted
      have chosenRaw := selected
      simp only [Completed.diagnosticResults, List.map_nil, List.append_nil] at chosenRaw
      rw [publish_erase]
      exact publish (batch sameOperator sameArguments tuples calls) chosenRaw
  | selectionFailed _ shaped chosen =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at chosen
      have exhausted := exact chosen
      simp at exhausted

end Nested

/-! ## The settling class with `if` nodes -/

/-- **An `if` node of the class**: `(if c y n)` whose condition `c` evaluates under `Bool` to the
Boolean `b` (`IfConditions.ScopedCondition`, under every policy: a literal, or a call of a defined
function, `IfConditions.call_condition`), with data branches with closed stored types, the taken one
undeclared and not `NotReducible`, on a program whose region of `if` on `(if b y n)` is the taken
branch. -/
structure IfNode (dispatch : GroundedDispatch) (atoms : List Atom) (c : Atom) (b : Bool) (y n : Atom) :
    Prop where
  condition : ∀ policy : Policy, ScopedCondition dispatch policy atoms c b
  branches : ScopedBranches atoms b y n
  dataYes : DataAtom y
  dataNo : DataAtom n

/-- **The settling class with `if` nodes.** A data atom; an `if` node; a constructor applied to
settling terms; an ordinary call of data whose region is nonempty, whose bodies are closed (instance
and body coincide), and all of whose bodies settle. Like `Settles`, it is a condition on the program's
call graph, never on an answer or a run. -/
inductive SettlesIf (dispatch : GroundedDispatch) (atoms : List Atom) : Atom → List Atom → Prop
  | data {d : Atom} : DataAtom d → d ≠ Atom.notReducible → SettlesIf dispatch atoms d [d]
  | ifNode {c : Atom} {b : Bool} {y n : Atom} : IfNode dispatch atoms c b y n →
      SettlesIf dispatch atoms (callC c y n) [pick b y n]
  | build {f : String} {ts : List Atom} {Ls : List (List Atom)} : NodeHead dispatch atoms f →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesIf dispatch atoms p.1 p.2) →
      SettlesIf dispatch atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)])
  | call {f : String} {args : List Atom} {Ls : List (List Atom)} : Ordinary dispatch atoms f args →
      NodeHead dispatch atoms f →
      regionInstances atoms f args ≠ [] → regionInstances atoms f args = regionBodies atoms f args →
      (regionInstances atoms f args).length = Ls.length →
      (∀ p ∈ (regionInstances atoms f args).zip Ls, SettlesIf dispatch atoms p.1 p.2) →
      SettlesIf dispatch atoms (.expression (.symbol f :: args)) Ls.flatten

theorem closed_typeVars {t : Atom} (closed : ∀ name, ¬ AtomOccurs t name) :
    TypeSubst.typeVars t = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro name inside
  exact closed name ((Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars t
    name).mpr inside)

theorem app_closed {f : String} {ts : List Atom} (closed : ∀ t ∈ ts, ∀ name, ¬ AtomOccurs t name) :
    ∀ name, ¬ AtomOccurs (.expression (.symbol f :: ts)) name := by
  intro name occurs
  cases occurs with
  | expression member inner =>
      rcases List.mem_cons.mp member with rfl | later
      · cases inner
      · exact closed _ later name inner

theorem app_ground {f : String} :
    ∀ {ts : List Atom}, (∀ t ∈ ts, isGroundAtom t = true) →
      isGroundAtom (.expression (.symbol f :: ts)) = true
  | [], _ => rfl
  | t :: rest, ground => by
      have here := ground t List.mem_cons_self
      have later := app_ground (f := f) (ts := rest) fun u member =>
        ground u (List.mem_cons_of_mem _ member)
      simp only [isGroundAtom, isGroundAtom.isGroundList, Bool.and_eq_true] at later ⊢
      exact ⟨later.1, here, later.2⟩

/-- **The facts of a body for a symbol-headed application of closed, ground terms.** -/
theorem app_facts {f : String} {ts : List Atom} (head : DataAtom (.symbol f))
    (notFunction : f ≠ "function") (closed : ∀ t ∈ ts, ∀ name, ¬ AtomOccurs t name)
    (ground : ∀ t ∈ ts, isGroundAtom t = true) : BodyFacts (.expression (.symbol f :: ts)) := by
  refine ⟨app_closed closed, fun policy pending => ?_, (fun same => by cases same), ?_,
    fun rename => rename_closed rename _ (closed_typeVars (app_closed closed)), app_ground ground⟩
  · obtain ⟨⟨body, same⟩, _⟩ := pending
    rw [Entry.Value.erase_ofAtom] at same
    simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
    exact notFunction same.1
  · rintro (same | ⟨tail, same⟩)
    · simp [Atom.empty] at same
    · simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      cases head with
      | symbol _ notError => exact notError same.1

theorem data_facts {d : Atom} (data : DataAtom d) (notRefused : d ≠ Atom.notReducible) :
    BodyFacts d :=
  settles_facts (Settles.data (dispatch := WholeRunWords.Double.noHost) (atoms := []) data notRefused)

/-- **The shape of a settling term**: answerable answers, and the facts of a body. -/
theorem settlesIf_shape {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesIf dispatch atoms t L) : (∀ a ∈ L, Answerable a) ∧ BodyFacts t := by
  induction settles with
  | @data d data notRefused =>
      refine ⟨fun a member => ?_, data_facts data notRefused⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data
  | @ifNode c b y n node =>
      have cond := node.condition Policy.unmarked
      refine ⟨fun a member => ?_, ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data node.branches.branches.takenData
      · refine app_facts if_data (by decide) (fun t member => ?_) (fun t member => ?_)
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact cond.closed
          · exact (answerable_of_data node.dataYes).closed
          · exact (answerable_of_data node.dataNo).closed
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl
          · exact cond.ground
          · exact (answerable_of_data node.dataYes).ground
          · exact (answerable_of_data node.dataNo).ground
  | @build f ts Ls head noEquation length settled ih =>
      have argsT : List.Forall₂ (fun t L => (∀ a ∈ L, Answerable a) ∧ BodyFacts t) ts Ls :=
        forall₂_of_zip length fun p member => ih p member
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact both.1 a inside
      refine ⟨fun a member => ?_, app_facts head.head head.notFunction (fun t member => ?_)
        (fun t member => ?_)⟩
      · obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
        rw [List.mem_singleton] at inner
        subst inner
        exact app_answerable head.head (combos_answerable allClean vals valsMem)
      · obtain ⟨L, both⟩ := forall₂_left_exists argsT t member
        exact both.2.closed
      · obtain ⟨L, both⟩ := forall₂_left_exists argsT t member
        exact both.2.ground
  | @call f args Ls ordinary _ _ _ length settled ih =>
      have bodiesT : List.Forall₂ (fun t L => (∀ a ∈ L, Answerable a) ∧ BodyFacts t)
          (regionInstances atoms f args) Ls :=
        forall₂_of_zip length fun p member => ih p member
      refine ⟨fun a member => ?_, call_facts ordinary⟩
      obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
      obtain ⟨b, both⟩ := forall₂_right_exists bodiesT L inLs
      exact both.1 a inner

/-! ## HE's source semantics determines the answers, at every frame -/

/-- **Every derivation of HE's completed relation for a settling term, at every frame, publishes its
answers**, on the scoped lookup. -/
theorem settlesIf_determined {atoms : List Atom} (program : IfProgram atoms) {t : Atom}
    {L : List Atom} (settles : SettlesIf dispatch atoms t L) :
    DeterminedUnder dispatch Completed.scopedLookup policy atoms t L := by
  induction settles with
  | @data d data _ =>
      intro live scope frame results derived
      obtain ⟨after, rfl⟩ := data_source scoped_contract data derived
      simp
  | @ifNode c b y n node =>
      intro live scope frame results derived
      exact if_source_c program (node.condition policy) node.branches derived
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesIf.build head noEquation length settled
      have args : List.Forall₂ (SettledU dispatch Completed.scopedLookup policy atoms) ts Ls :=
        forall₂_of_zip length fun p member => ⟨(settlesIf_shape (settled p member)).1, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists args L member
        exact both.1 a inside
      exact (nested_determined_u scoped_contract head.head head.untyped
        (settlesIf_shape whole).2.closed args (fun vals => [.expression (.symbol f :: vals)])
        (fun vals member => ⟨fun a inside => by
            rw [List.mem_singleton] at inside
            subst inside
            exact app_answerable head.head (combos_answerable allClean vals member),
          query_absent_u (scoped_consFree program.rows) head.head (head.instruction vals)
            (combos_answerable allClean vals member)
            (regionBodies_nil_of_no_equation vals noEquation)⟩)).2
  | @call f args Ls ordinary _ nonempty _ length settled ih =>
      have related : List.Forall₂ (fun i L => SettlesIf dispatch atoms i L ∧
          DeterminedUnder dispatch Completed.scopedLookup policy atoms i L)
          (regionInstances atoms f args) Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have cleanAll : ∀ a ∈ Ls.flatten, Answerable a := by
        intro a member
        obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
        obtain ⟨b, both⟩ := forall₂_right_exists related L inLs
        exact (settlesIf_shape both.1).1 a inner
      intro live scope frame results derived
      obtain ⟨after, children, selected, called, chosen, erased⟩ :=
        call_source scoped_contract ordinary derived
      rcases callRel_source_open program.rows ordinary called with
        ⟨_, empty⟩ | ⟨works, _, frontier, equations⟩
      · apply absurd _ nonempty
        rw [regionInstances_sides, empty]
        rfl
      · have instances := works_instances (policy := policy) ordinary.arguments program.rows
          after.certified.satisfiable frontier
        have onWorks : List.Forall₂ (fun w L => ∃ i, (∀ output : Frame,
              output.bindings = w.bindings →
                output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom i) ∧
            DeterminedUnder dispatch Completed.scopedLookup policy atoms i L ∧ BodyFacts i)
            works Ls :=
          (forall₂_comp instances related).imp fun _ _ both => by
            obtain ⟨i, ⟨_, reads⟩, settlesI, determined⟩ := both
            exact ⟨i, reads, determined, (settlesIf_shape settlesI).2⟩
        have erasedChildren := bodies_source_open works Ls onWorks equations
        have clean : ∀ r ∈ children, Answerable r.1.erase := by
          intro r member
          apply cleanAll
          rw [← erasedChildren]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        have unchanged : children.map (Completed.readResult policy) = children :=
          map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
        rw [unchanged] at chosen
        have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
          chosen (HERuns.success_all children fun r member => (clean r member).notError)
        rw [erased, same, erasedChildren]

/-! ## Every run finishes -/

theorem defined_arity_of_region {atoms : List Atom} {f : String} {args : List Atom}
    (nonempty : regionInstances atoms f args ≠ []) :
    ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
      e.arguments.length = args.length := by
  obtain ⟨x, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
  rw [regionInstances_eq] at inRegion
  obtain ⟨e, chosen, _⟩ := List.mem_filterMap.mp inRegion
  obtain ⟨live, selected⟩ := List.mem_filter.mp chosen
  simp only [Bool.and_eq_true, beq_iff_eq] at selected
  exact ⟨e, live, selected.1, selected.2⟩

theorem defined_of_region {atoms : List Atom} {f : String} {args : List Atom}
    (nonempty : regionInstances atoms f args ≠ []) :
    ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f := by
  obtain ⟨e, live, head, _⟩ := defined_arity_of_region nonempty
  exact ⟨e, live, head⟩

theorem if_defined {atoms : List Atom} {c : Atom} {b : Bool} {y n : Atom}
    (node : IfNode dispatch atoms c b y n) :
    ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = "if" :=
  defined_of_region (f := "if") (args := [.grounded (.bool b), y, n]) (by
    rw [node.branches.branches.region]
    exact List.cons_ne_nil _ _)

/-- A settling value is its own answer. -/
theorem settlesIf_value_self {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesIf dispatch atoms t L) : NestedValues.Value dispatch atoms t → L = [t] := by
  induction settles with
  | data _ _ => intro _; rfl
  | ifNode node =>
      intro value
      exact (value_not_defined (if_defined node) value).elim
  | @build f ts Ls head noEquation length _ ih =>
      intro value
      have each : ∀ t ∈ ts, NestedValues.Value dispatch atoms t := fun t member =>
        value_children value t (List.mem_cons_of_mem _ member)
      have singles : Ls = ts.map fun t => [t] := zip_singletons length fun p member =>
        ih p member (each p.1 (List.of_mem_zip member).1)
      subst singles
      rw [combos_singletons]
      simp
  | call _ _ nonempty _ _ _ _ =>
      intro value
      exact (value_not_defined (defined_of_region nonempty) value).elim

/-- **The marked presentations of an `if` node**: only the plain one, since its condition has one,
its branches are data, and `if`, having equations, is no value that could be held. -/
theorem if_presentation {atoms : List Atom} {c : Atom} {b : Bool} {y n : Atom}
    (node : IfNode dispatch atoms c b y n) {v : Entry.Value} (erased : v.erase = callC c y n)
    (marked : Marked dispatch atoms v) : v = Entry.Value.ofAtom (callC c y n) := by
  obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
  obtain ⟨vc, rest, rfl, eraseC, restErase⟩ := List.map_eq_cons_iff.mp vsErase
  obtain ⟨vy, rest', rfl, eraseY, restErase'⟩ := List.map_eq_cons_iff.mp restErase
  obtain ⟨vn, rest'', rfl, eraseN, restErase''⟩ := List.map_eq_cons_iff.mp restErase'
  obtain rfl := List.map_eq_nil_iff.mp restErase''
  have children := marked.children
  rw [(node.condition Policy.unmarked).plain vc eraseC
      (children vc (List.mem_cons_of_mem _ List.mem_cons_self)),
    value_of_data node.dataYes eraseY, value_of_data node.dataNo eraseN]
  cases readiness with
  | active => simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  | held =>
      have value := marked.held_value
      simp only [List.map_cons, List.map_nil, Entry.Value.erase] at value
      exact (value_not_defined (if_defined node) value).elim

/-- **Every marked presentation of a settling term runs finely to its answers**, on the scoped
lookup, under every continuation fine on them: no run is stuck and none is infinite. -/
theorem settlesIf_fine (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {t : Atom} {L : List Atom} (settles : SettlesIf dispatch atoms t L) :
    FineEval dispatch Completed.scopedLookup policy atoms t L := by
  induction settles with
  | @data d data _ => exact fine_data scoped_answers scoped_contract atoms data
  | @ifNode c b y n node =>
      intro v erased marked
      rw [if_presentation node erased marked]
      intro live scope activation stack emitted cont
      exact fine_if_c notHost policy program (node.condition policy) node.branches stack emitted cont
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesIf.build head noEquation length settled
      have argsT : List.Forall₂ (fun t L => SettlesIf dispatch atoms t L ∧
          FineEval dispatch Completed.scopedLookup policy atoms t L) ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesIf_shape both.1).1 a inside
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      subst vsErase
      have closed := (settlesIf_shape whole).2.closed
      have args : List.Forall₂ (fun v L => FineRuns dispatch Completed.scopedLookup policy atoms v L ∧
          ∀ a ∈ L, Answerable a) vs Ls :=
        forall₂_imp_mem (List.forall₂_map_left_iff.mp argsT) fun w member L both =>
          ⟨both.2 w rfl (marked.children w (List.mem_cons_of_mem _ member)),
            (settlesIf_shape both.1).1⟩
      have headFine : FineRuns dispatch Completed.scopedLookup policy atoms (.symbol f) [.symbol f] :=
        fine_data scoped_answers scoped_contract atoms head.head (.symbol f)
          (by simp only [Entry.Value.erase]) (.symbol f)
      have eraseList : (Entry.Value.symbol f :: vs).map Entry.Value.erase =
          .symbol f :: vs.map Entry.Value.erase := by
        simp only [List.map_cons, Entry.Value.erase]
      by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
      · obtain ⟨reuses, rfl⟩ := reusedHeld
        have value := marked.held_value
        rw [eraseList] at value
        rw [settlesIf_value_self whole value]
        have runs := fine_held (dispatch := dispatch) (lookup := Completed.scopedLookup) atoms reuses
          (children := .symbol f :: vs) (by rw [eraseList]; exact closed)
          (by rw [eraseList]; exact call_not_stopped head.head)
        rwa [eraseList] at runs
      · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
          cases reentry : policy.reentry <;> cases readiness <;> simp_all
        exact fine_node scoped_contract head.head head.untyped closed headFine interpreted rfl args
          (fun vals => [.expression (.symbol f :: vals)])
          (fun vals member => ⟨fine_query_absent (scoped_consFree program.rows) head
              (combos_answerable allClean vals member)
              (regionBodies_nil_of_no_equation vals noEquation),
            fun a inside => by
              rw [List.mem_singleton] at inside
              subst inside
              exact app_answerable head.head (combos_answerable allClean vals member)⟩)
  | @call f args Ls ordinary node nonempty _ length settled ih =>
      have whole := SettlesIf.call ordinary node nonempty ‹_› length settled
      have closed := (settlesIf_shape whole).2.closed
      intro v erased marked
      obtain ⟨readiness, vs, rfl, vsErase⟩ := call_value_shape erased
      have plainArgs : vs = args.map Entry.Value.ofAtom := by
        rw [← vsErase, List.map_map]
        conv_lhs => rw [← List.map_id vs]
        apply List.map_congr_left
        intro w member
        exact value_of_data (ordinary.arguments _ (vsErase ▸ List.mem_map_of_mem member)) rfl
      subst plainArgs
      cases readiness with
      | held =>
          have value := marked.held_value
          simp only [List.map_cons, Entry.Value.erase] at value
          rw [List.map_map] at value
          simp only [Function.comp_def, Entry.Value.erase_ofAtom, List.map_id'] at value
          exact (value_not_defined (defined_of_region nonempty) value).elim
      | active =>
          have bodies : List.Forall₂ (fun b L => FineEval dispatch Completed.scopedLookup policy atoms
              b L ∧ BodyFacts b) (regionInstances atoms f args) Ls :=
            forall₂_of_zip length fun p member => ⟨ih p member, (settlesIf_shape (settled p member)).2⟩
          have query := fine_query_equations (policy := policy) program.rows node
            (fun v member => NestedValues.Value.data (ordinary.arguments v member)) nonempty bodies
          have argsF : List.Forall₂ (fun v L => FineRuns dispatch Completed.scopedLookup policy atoms
              v L ∧ ∀ a ∈ L, Answerable a) (args.map Entry.Value.ofAtom) (args.map fun a => [a]) := by
            rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
            apply List.forall₂_same.mpr
            intro a member
            refine ⟨fine_data scoped_answers scoped_contract atoms (ordinary.arguments a member) _
              (Entry.Value.erase_ofAtom a) (marked_ofAtom a), fun x inside => ?_⟩
            rw [List.mem_singleton] at inside
            subst inside
            exact answerable_of_data (ordinary.arguments x member)
          have headFine : FineRuns dispatch Completed.scopedLookup policy atoms (.symbol f)
              [.symbol f] :=
            fine_data scoped_answers scoped_contract atoms node.head (.symbol f)
              (by simp only [Entry.Value.erase]) (.symbol f)
          have cleanBodies : ∀ a ∈ Ls.flatten, Answerable a := by
            intro a member
            obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
            have regions := forall₂_of_zip length fun p member => settled p member
            obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inLs
            exact (settlesIf_shape settlesB).1 a inner
          have runs := fine_node scoped_contract node.head node.untyped closed headFine (Or.inr rfl)
            (by simp [List.map_map, Function.comp_def, Entry.Value.erase_ofAtom]) argsF
            (fun _ => Ls.flatten)
            (fun vals member => by
              rw [combos_singletons, List.mem_singleton] at member
              subst member
              exact ⟨query, cleanBodies⟩)
          rw [combos_singletons] at runs
          simpa using runs

/-! ## PeTTa evaluates the class -/

/-- **PeTTa's streaming machine evaluates a settling term to its answers**; an `if` node is PeTTa's
special form, whose branch frame takes the branch of the Boolean literal. -/
theorem settlesIf_petta {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesIf dispatch atoms t L) : PeTTaEvaluates atoms t L := by
  induction settles with
  | @data d data _ => exact PeTTaRuns.petta_data atoms data
  | @ifNode c b y n node =>
      exact IfComputed.petta_if_computed (node.condition Policy.unmarked).petta
        (PeTTaRuns.petta_data atoms node.branches.branches.takenData)
  | @build f ts Ls head noEquation length settled ih =>
      exact PeTTaNested.petta_nested_constructor head.head head.notCollapse head.notOnce
        (sourceControlForm_of_head head.notControl ts) head.notIO head.notNative noEquation
        (forall₂_of_zip length fun p member => ⟨ih p member, (settlesIf_shape (settled p member)).1⟩)
  | @call f args Ls ordinary _ nonempty sameBodies length settled ih =>
      have bodies : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
          (regionBodies atoms f args) Ls := by
        rw [← sameBodies]
        exact forall₂_of_zip length fun p member =>
          ⟨ih p member, (settlesIf_shape (settled p member)).2.ground⟩
      exact PeTTaRuns.petta_call ordinary (defined_arity_of_region nonempty) bodies

/-! ## Every run -/

/-- **HE and PeTTa agree on `if` inside bodies, on every run, on the scoped lookup.** On a program
carrying HE's `if`, for any dispatch that does not execute `if` and any policy: for a settling term
(with `if` nodes inside bodies, as constructor arguments, or at the entry), a complete HE run exists
and every complete run publishes `L`; no run is infinite and every reachable configuration steps or
is final with `L`; and PeTTa's streaming run yields `L` from some fuel on. -/
theorem if_bodies_every_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfProgram atoms) {c : Atom} {L : List Atom} (settles : SettlesIf dispatch atoms c L) :
    Publishes dispatch Completed.scopedLookup policy (Space.ofList atoms) c L ∧
      Finishes dispatch Completed.scopedLookup policy (Space.ofList atoms) c L ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } c)) = L := by
  have fine : Fine dispatch Completed.scopedLookup policy
      (load (Space.ofList atoms) c Atom.undefinedType) :=
    settlesIf_fine (policy := policy) notHost program settles (Entry.Value.ofAtom c)
      (Entry.Value.erase_ofAtom c) (marked_ofAtom c) [] [] Completed.Frame.empty [] []
      (fun R _ => fine_top R [])
  have determined := settlesIf_determined (policy := policy) program settles
  have every : ∀ emitted : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.scopedLookup policy)
        (load (Space.ofList atoms) c Atom.undefinedType) (final (Space.ofList atoms) emitted) →
      emitted.map (fun r => r.1.erase) = L :=
    fun emitted run => determined _ _ _ _ (complete_source run)
  have shape := settlesIf_shape settles
  refine ⟨⟨?_, every⟩, ⟨fine.acc, fun y path => ?_⟩,
    petta_complete shape.2.ground shape.1 (settlesIf_petta settles)⟩
  · obtain ⟨space, emitted, path⟩ := IfAtFrames.Fine.exists_final fine
    have same : space = Space.ofList atoms := space_fixed path
    subst same
    exact ⟨emitted, path⟩
  · rcases (fine.reaches path).progress with moves | ⟨space, emitted, rfl⟩
    · exact Or.inl moves
    · have same : space = Space.ofList atoms := space_fixed path
      subst same
      exact Or.inr ⟨emitted, rfl, every emitted path⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)

/-- A symbol without a declaration in a program. -/
theorem undeclared_of {atoms : List Atom} {name : String}
    (none : atoms.filterMap (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.symbol name)) = []) :
    StorageTypesRel (Space.ofList atoms) (.symbol name) [Atom.undefinedType] :=
  .symbolUndefined (none ▸ Mettapedia.Languages.MeTTa.HE.Spec.Type.AnnotationTypesRel.complete
    (.symbol name) atoms)

/-- `if`'s stored arrow in a program that extends HE's `if` program by equations. -/
theorem if_types_of {rows : List Atom}
    (none : rows.filterMap (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.symbol "if")) = []) :
    StorageTypesRel (Space.ofList (ifProgram ++ rows)) (.symbol "if") [ifArrow] := by
  have extracted := Mettapedia.Languages.MeTTa.HE.Spec.Type.AnnotationTypesRel.complete (.symbol "if")
    (ifProgram ++ rows)
  have computed : (ifProgram ++ rows).filterMap
      (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.symbol "if")) = [ifArrow] := by
    rw [List.filterMap_append, none, List.append_nil]
    decide
  rw [computed] at extracted
  exact .symbolKnown extracted (by simp)

/-- `(= (both) (pair (if True yes no) (if False yes no)))`, with HE's `if`. -/
abbrev bothRows : List Atom :=
  ifProgram ++ [rule (app "both" [])
    (app "pair" [callOf true (sym "yes") (sym "no"), callOf false (sym "yes") (sym "no")])]

theorem both_types_if : StorageTypesRel (Space.ofList bothRows) (.symbol "if") [ifArrow] :=
  if_types_of (by decide)

theorem both_program : IfProgram bothRows := by
  refine ⟨both_types_if, ?_⟩
  intro row member
  rcases List.mem_append.mp member with inIf | inBoth
  · exact if_program row inIf
  · simp only [List.mem_singleton] at inBoth
    subst inBoth
    refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
    cases same
    decide

theorem both_node (b : Bool) :
    IfNode noHost bothRows (.grounded (.bool b)) b (sym "yes") (sym "no") where
  condition := fun _ => literal_condition bothRows b
  branches :=
    { branches :=
        { takenData := by cases b <;> exact .symbol (by decide) (by decide)
          takenNotRefused := by cases b <;> simp [pick, Atom.notReducible]
          takenUndeclared := by cases b <;> exact undeclared_of (by decide)
          closedYes := data_closed (.symbol (by decide) (by decide))
          closedNo := data_closed (.symbol (by decide) (by decide))
          groundYes := rfl
          groundNo := rfl
          typedYes := ⟨_, undeclared_of (by decide)⟩
          typedNo := ⟨_, undeclared_of (by decide)⟩
          region := by cases b <;> decide +kernel }
      typedYes := ⟨_, undeclared_of (by decide), rfl⟩
      typedNo := ⟨_, undeclared_of (by decide), rfl⟩ }
  dataYes := .symbol (by decide) (by decide)
  dataNo := .symbol (by decide) (by decide)

theorem both_head (f : String) (untyped : (Space.ofList bothRows).atoms.filter
      (typeRegion (.symbol f)) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false) (notControl : controlHead f = false)
    (notEmpty : f ≠ "Empty") (notError : f ≠ "Error") : NodeHead noHost bothRows f :=
  ⟨.symbol notEmpty notError, untyped, fun impossible => impossible, notInstruction, notIO,
    notNative, notControl⟩

/-- **The polymorphic `if` twice in one body settles**: `(both)` gives `(pair yes no)`. -/
theorem both_settles :
    SettlesIf noHost bothRows (app "both" []) [app "pair" [sym "yes", sym "no"]] := by
  have pairHead := both_head "pair" (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have body : SettlesIf noHost bothRows
      (app "pair" [callOf true (sym "yes") (sym "no"), callOf false (sym "yes") (sym "no")])
      [app "pair" [sym "yes", sym "no"]] := by
    have built := SettlesIf.build (dispatch := noHost) (atoms := bothRows) pairHead (by decide +kernel)
      (ts := [callOf true (sym "yes") (sym "no"), callOf false (sym "yes") (sym "no")])
      (Ls := [[sym "yes"], [sym "no"]]) rfl (fun p member => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · exact .ifNode (both_node true)
        · exact .ifNode (both_node false))
    simpa [combos] using built
  have called := SettlesIf.call (dispatch := noHost) (atoms := bothRows) (f := "both") (args := [])
    (Ls := [[app "pair" [sym "yes", sym "no"]]])
    ⟨.symbol (by decide) (by decide), (fun _ member => by cases member), (by decide +kernel),
      (fun impossible => impossible), (by decide), (by decide), (by decide), (by decide),
      (by decide), (by decide)⟩
    (both_head "both" (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun p member => by
      have instances : regionInstances bothRows "both" [] =
          [app "pair" [callOf true (sym "yes") (sym "no"), callOf false (sym "yes") (sym "no")]] := by
        decide +kernel
      rw [instances] at member
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
      subst member
      exact body)
  simpa using called

/-- **Positive control, the polymorphic `if` twice in one body**: on the scoped lookup, a complete
run of `(both)` exists, every complete run publishes `(pair yes no)`, every run finishes, and PeTTa
yields `(pair yes no)`. -/
theorem both_every_run (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList bothRows) (app "both" [])
        [app "pair" [sym "yes", sym "no"]] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList bothRows) (app "both" [])
        [app "pair" [sym "yes", sym "no"]] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate bothRows) n
        (Streaming.enter { state := store bothRows } (app "both" []))) =
          [app "pair" [sym "yes", sym "no"]] :=
  if_bodies_every_run noHost (fun impossible => impossible) policy both_program both_settles

/-- `(= (pick) (if True yes no))`, with HE's `if`: a call whose body is the special form. -/
abbrev pickRows : List Atom :=
  ifProgram ++ [rule (app "pick" []) (callOf true (sym "yes") (sym "no"))]

theorem pick_program : IfProgram pickRows := by
  refine ⟨if_types_of (by decide), ?_⟩
  intro row member
  rcases List.mem_append.mp member with inIf | inPick
  · exact if_program row inIf
  · simp only [List.mem_singleton] at inPick
    subst inPick
    refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
    cases same
    decide

theorem pick_node : IfNode noHost pickRows (.grounded (.bool true)) true (sym "yes") (sym "no") where
  condition := fun _ => literal_condition pickRows true
  branches :=
    { branches :=
        { takenData := .symbol (by decide) (by decide)
          takenNotRefused := by simp [pick, Atom.notReducible]
          takenUndeclared := undeclared_of (by decide)
          closedYes := data_closed (.symbol (by decide) (by decide))
          closedNo := data_closed (.symbol (by decide) (by decide))
          groundYes := rfl
          groundNo := rfl
          typedYes := ⟨_, undeclared_of (by decide)⟩
          typedNo := ⟨_, undeclared_of (by decide)⟩
          region := by decide +kernel }
      typedYes := ⟨_, undeclared_of (by decide), rfl⟩
      typedNo := ⟨_, undeclared_of (by decide), rfl⟩ }
  dataYes := .symbol (by decide) (by decide)
  dataNo := .symbol (by decide) (by decide)

/-- **Positive control, a call whose body is the special form**: every run of `(pick)` finishes with
`yes`, as PeTTa's. -/
theorem pick_every_run (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList pickRows) (app "pick" [])
        [sym "yes"] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList pickRows) (app "pick" [])
        [sym "yes"] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate pickRows) n
        (Streaming.enter { state := store pickRows } (app "pick" []))) = [sym "yes"] := by
  have called := SettlesIf.call (dispatch := noHost) (atoms := pickRows) (f := "pick") (args := [])
    (Ls := [[sym "yes"]])
    ⟨.symbol (by decide) (by decide), (fun _ member => by cases member), (by decide +kernel),
      (fun impossible => impossible), (by decide), (by decide), (by decide), (by decide),
      (by decide), (by decide)⟩
    ⟨.symbol (by decide) (by decide), (by decide +kernel), (fun impossible => impossible),
      (by decide), (by decide), (by decide), (by decide)⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun p member => by
      have instances : regionInstances pickRows "pick" [] = [callOf true (sym "yes") (sym "no")] := by
        decide +kernel
      rw [instances] at member
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
      subst member
      exact .ifNode pick_node)
  have settles : SettlesIf noHost pickRows (app "pick" []) [sym "yes"] := by simpa using called
  exact if_bodies_every_run noHost (fun impossible => impossible) policy pick_program settles

/-- **Negative control, the class's boundary**: `(if True 1 2)` is no `if` node of the class, since
its taken branch `1` has the stored type `Number`; the polymorphic `if` with declared branches is
outside `SettlesIf` (see the module docstring of `ScopedIf` and the report for the open case). -/
theorem declared_branch_not_in_class (atoms : List Atom) (c : Atom) :
    ¬ IfNode noHost atoms c true (.grounded (.int 1)) (.grounded (.int 2)) := by
  intro node
  have undeclared := node.branches.branches.takenUndeclared
  have number : StorageTypesRel (Space.ofList atoms) (.grounded (.int 1)) [sym "Number"] :=
    .groundedKnown (.int 1) (by simp [Atom.undefinedType])
  have same := StorageTypesRel.unique undeclared number
  simp [Atom.undefinedType] at same

/-- An expression without a declaration in a program. -/
theorem expression_undeclared_of {atoms : List Atom} {head : Atom} {tail : List Atom}
    (none : atoms.filterMap
      (Mettapedia.Languages.MeTTa.HE.Spec.Type.annotationType? (.expression (head :: tail))) = []) :
    StorageTypesRel (Space.ofList atoms) (.expression (head :: tail)) [Atom.undefinedType] :=
  .expressionUndefined (none ▸ Mettapedia.Languages.MeTTa.HE.Spec.Type.AnnotationTypesRel.complete
    (.expression (head :: tail)) atoms)

/-- `(= (isTrue) True)` and `(= (byCall) (if (isTrue) yes no))`, with HE's `if`: a computed
condition inside a body. -/
abbrev byCallRows : List Atom :=
  ifProgram ++ [rule (app "isTrue" []) (.grounded (.bool true)),
    rule (app "byCall" []) (callC (app "isTrue" []) (sym "yes") (sym "no"))]

theorem byCall_program : IfProgram byCallRows := by
  refine ⟨if_types_of (by decide), ?_⟩
  intro row member
  rcases List.mem_append.mp member with inIf | inRows
  · exact if_program row inIf
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at inRows
    rcases inRows with rfl | rfl
    · refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
      cases same
      decide
    · refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
      cases same
      decide

/-- **`(isTrue)` is a Boolean call**: its one row's body is `True`. -/
theorem isTrue_call : BoolCall noHost byCallRows "isTrue" [] true where
  ordinary := ⟨.symbol (by decide) (by decide), (fun _ member => by cases member),
    (by decide +kernel), (fun impossible => impossible), (by decide), (by decide), (by decide),
    (by decide), (by decide), (by decide)⟩
  head := ⟨.symbol (by decide) (by decide), (by decide +kernel), (fun impossible => impossible),
    (by decide), (by decide), (by decide), (by decide)⟩
  region := by decide +kernel
  bodies := by decide +kernel
  undeclared := expression_undeclared_of (by decide)

theorem byCall_node :
    IfNode noHost byCallRows (app "isTrue" []) true (sym "yes") (sym "no") where
  condition := fun _ => call_condition byCall_program.rows isTrue_call
  branches :=
    { branches :=
        { takenData := .symbol (by decide) (by decide)
          takenNotRefused := by simp [pick, Atom.notReducible]
          takenUndeclared := undeclared_of (by decide)
          closedYes := data_closed (.symbol (by decide) (by decide))
          closedNo := data_closed (.symbol (by decide) (by decide))
          groundYes := rfl
          groundNo := rfl
          typedYes := ⟨_, undeclared_of (by decide)⟩
          typedNo := ⟨_, undeclared_of (by decide)⟩
          region := by decide +kernel }
      typedYes := ⟨_, undeclared_of (by decide), rfl⟩
      typedNo := ⟨_, undeclared_of (by decide), rfl⟩ }
  dataYes := .symbol (by decide) (by decide)
  dataNo := .symbol (by decide) (by decide)

/-- **Positive control, a computed condition inside a body**: every run of `(byCall)` finishes with
`yes`, the condition `(isTrue)` being evaluated by HE under `Bool` (and by PeTTa as a call), as HE's
own interpreter answers `[yes]`. -/
theorem byCall_every_run (policy : Policy) :
    Publishes noHost Completed.scopedLookup policy (Space.ofList byCallRows) (app "byCall" [])
        [sym "yes"] ∧
      Finishes noHost Completed.scopedLookup policy (Space.ofList byCallRows) (app "byCall" [])
        [sym "yes"] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate byCallRows) n
        (Streaming.enter { state := store byCallRows } (app "byCall" []))) = [sym "yes"] := by
  have called := SettlesIf.call (dispatch := noHost) (atoms := byCallRows) (f := "byCall")
    (args := []) (Ls := [[sym "yes"]])
    ⟨.symbol (by decide) (by decide), (fun _ member => by cases member), (by decide +kernel),
      (fun impossible => impossible), (by decide), (by decide), (by decide), (by decide),
      (by decide), (by decide)⟩
    ⟨.symbol (by decide) (by decide), (by decide +kernel), (fun impossible => impossible),
      (by decide), (by decide), (by decide), (by decide)⟩
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun p member => by
      have instances : regionInstances byCallRows "byCall" [] =
          [callC (app "isTrue" []) (sym "yes") (sym "no")] := by
        decide +kernel
      rw [instances] at member
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
      subst member
      exact .ifNode byCall_node)
  have settles : SettlesIf noHost byCallRows (app "byCall" []) [sym "yes"] := by simpa using called
  exact if_bodies_every_run noHost (fun impossible => impossible) policy byCall_program settles

end Controls

#print axioms settlesIf_shape
#print axioms settlesIf_determined
#print axioms settlesIf_fine
#print axioms settlesIf_petta
#print axioms if_bodies_every_run
#print axioms Controls.both_settles
#print axioms Controls.both_every_run
#print axioms Controls.pick_every_run
#print axioms Controls.declared_branch_not_in_class
#print axioms tuple_rows_u
#print axioms query_absent_u
#print axioms nested_determined_u

end IfInBodies

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
