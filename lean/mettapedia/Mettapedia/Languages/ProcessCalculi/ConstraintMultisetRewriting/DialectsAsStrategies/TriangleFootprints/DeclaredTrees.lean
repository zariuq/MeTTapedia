import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.DeclaredBranchVariant

/-!
# Trees with declared `if`: the variant machine and PeTTa agree on every run

`DeclaredBranchVariant` proves that on the variant machine every run of `(if b y n)` with a declared
taken branch, or an undeclared one, goes on with that branch, at every frame. This module closes
that node under the two ways a program composes terms, and compares the result with PeTTa.

* `SettlesDeclared`: **the class**: a data atom; `(if b y n)` with a Boolean literal and a taken
  branch that is declared (a symbolic type) or undeclared; a constructor applied to terms of the
  class; a call on data of a defined function whose rows' bodies are closed terms of the class. Like
  `IfInBodies.SettlesIf`, it is a condition on the program's call graph, never on an answer or a
  run.
* `settlesDeclared_shape`: its answers are answerable and its terms meet the facts of a body.
* `settlesDeclared_good`: every run of the variant machine on a term of the class goes on with its
  answers, at every frame and under every continuation.
* `settlesDeclared_petta`: PeTTa's streaming machine evaluates a term of the class to the same
  answers; an `if` node is PeTTa's special form, and PeTTa has no declared types to meet.
* `declared_trees_every_run`: **on a program carrying HE's `if`, for a term of the class: a complete
  run of the variant machine exists, every complete run publishes `L`, no run is infinite, every
  configuration reached from the entry steps or is final with `L`; and PeTTa's streaming run yields
  `L` from some fuel on.**

## Controls

* `Controls.pair_if_agree` (positive): `(pair (if True 1 2) (if True True False))` gives `[(pair 1 True)]`
  on every run of the variant machine and on PeTTa. HE's `metta-repl` answers `[(pair 1 True)]`.
* `Controls.twice_agree` (positive): with `(= (twice) (pair (if True 1 2) (if True True False)))`,
  `(twice)` gives `[(pair 1 True)]` on every run and on PeTTa: declared branches inside a body. HE's
  `metta-repl` answers `[(pair 1 True)]`.
* `Controls.mixed_agree` (positive): `(pair (if True 1 2) (if False yes no))`, a declared and an
  undeclared taken branch in one term, gives `[(pair 1 no)]` on every run and on PeTTa.
* `Controls.computed_condition_not_in_class` (negative, the class's boundary): `(if (isTrue) 1 2)`
  is not in the class: its condition is no Boolean literal.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace DeclaredTrees

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
  ScopedTransfer ScopedIf SyntacticMerge VariantRuns DeclaredBranchVariant
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy} {target : List Atom}

/-! ## The class -/

/-- **Trees with declared `if`.** A data atom; `(if b y n)` with a Boolean literal and a declared
taken branch; the same with an undeclared taken branch; a constructor applied to terms of the
class; an ordinary call of data whose region is nonempty, whose bodies are closed (instance and body
coincide), and all of whose bodies are in the class. -/
inductive SettlesDeclared (dispatch : GroundedDispatch) (atoms : List Atom) :
    Atom → List Atom → Prop
  | data {d : Atom} : DataAtom d → d ≠ Atom.notReducible → SettlesDeclared dispatch atoms d [d]
  | declaredIf {b : Bool} {y n : Atom} {s : String} : DeclaredBranches atoms b y n s →
      SettlesDeclared dispatch atoms (callOf b y n) [pick b y n]
  | plainIf {b : Bool} {y n : Atom} : UndeclaredBranches atoms b y n →
      SettlesDeclared dispatch atoms (callOf b y n) [pick b y n]
  | build {f : String} {ts : List Atom} {Ls : List (List Atom)} : NodeHead dispatch atoms f →
      (atoms.filterMap LiveEquations.equationOfRow).all (fun equation => equation.head != f) = true →
      ts.length = Ls.length → (∀ p ∈ ts.zip Ls, SettlesDeclared dispatch atoms p.1 p.2) →
      SettlesDeclared dispatch atoms (.expression (.symbol f :: ts))
        ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)])
  | call {f : String} {args : List Atom} {Ls : List (List Atom)} : Ordinary dispatch atoms f args →
      NodeHead dispatch atoms f →
      regionInstances atoms f args ≠ [] → regionInstances atoms f args = regionBodies atoms f args →
      (regionInstances atoms f args).length = Ls.length →
      (∀ p ∈ (regionInstances atoms f args).zip Ls, SettlesDeclared dispatch atoms p.1 p.2) →
      SettlesDeclared dispatch atoms (.expression (.symbol f :: args)) Ls.flatten

theorem undeclared_taken {atoms : List Atom} {b : Bool} {y n : Atom}
    (branches : UndeclaredBranches atoms b y n) : DataAtom (pick b y n) := by
  cases b
  · exact branches.dataNo
  · exact branches.dataYes

/-- The answers and the body facts of `(if b y n)` with data branches. -/
theorem if_shape {b : Bool} {y n : Atom} (dataYes : DataAtom y) (dataNo : DataAtom n)
    (takenData : DataAtom (pick b y n)) :
    (∀ a ∈ [pick b y n], Answerable a) ∧ BodyFacts (callOf b y n) := by
  refine ⟨fun a member => ?_, ?_⟩
  · rw [List.mem_singleton] at member
    subst member
    exact answerable_of_data takenData
  · refine IfInBodies.app_facts if_data (by decide) (fun t member => ?_) (fun t member => ?_)
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact (answerable_of_data (DataAtom.grounded (.bool b))).closed
      · exact (answerable_of_data dataYes).closed
      · exact (answerable_of_data dataNo).closed
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact (answerable_of_data (DataAtom.grounded (.bool b))).ground
      · exact (answerable_of_data dataYes).ground
      · exact (answerable_of_data dataNo).ground

/-- **The shape of a term of the class**: answerable answers, and the facts of a body. -/
theorem settlesDeclared_shape {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesDeclared dispatch atoms t L) : (∀ a ∈ L, Answerable a) ∧ BodyFacts t := by
  induction settles with
  | @data d data notRefused =>
      refine ⟨fun a member => ?_, IfInBodies.data_facts data notRefused⟩
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data
  | @declaredIf b y n s branches =>
      exact if_shape branches.dataYes branches.dataNo branches.takenData
  | @plainIf b y n branches =>
      exact if_shape branches.dataYes branches.dataNo (undeclared_taken branches)
  | @build f ts Ls head noEquation length settled ih =>
      have argsT : List.Forall₂ (fun t L => (∀ a ∈ L, Answerable a) ∧ BodyFacts t) ts Ls :=
        forall₂_of_zip length fun p member => ih p member
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact both.1 a inside
      refine ⟨fun a member => ?_, IfInBodies.app_facts head.head head.notFunction
        (fun t member => ?_) (fun t member => ?_)⟩
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

/-! ## The variant machine on the class -/

theorem call_value (f : String) (ts : List Atom) :
    Entry.Value.ofAtom (.expression (.symbol f :: ts)) =
      .expression .active (.symbol f :: ts.map Entry.Value.ofAtom) := by
  simp only [Entry.Value.ofAtom, List.map_cons]

theorem head_good (atoms : List Atom) {f : String} (head : DataAtom (.symbol f)) :
    GoodRuns dispatch Completed.scopedLookup policy target atoms (.symbol f) [.symbol f] := by
  have runs := goodv_data (dispatch := dispatch) (policy := policy) (target := target)
    scoped_answers scoped_contract atoms head
  simpa only [Entry.Value.ofAtom] using runs

/-- **Every run of the variant machine on a term of the class goes on with its answers**, at every
frame and under every continuation, on the scoped lookup. -/
theorem settlesDeclared_good (notHost : ¬ dispatch.executable (.symbol "if")) {atoms : List Atom}
    (program : IfProgram atoms) {t : Atom} {L : List Atom}
    (settles : SettlesDeclared dispatch atoms t L) :
    GoodRuns dispatch Completed.scopedLookup policy target atoms (Entry.Value.ofAtom t) L := by
  induction settles with
  | @data d data _ => exact goodv_data scoped_answers scoped_contract atoms data
  | @declaredIf b y n s branches => exact goodv_if_declared notHost program branches
  | @plainIf b y n branches => exact goodv_if_undeclared notHost program branches
  | @build f ts Ls head noEquation length settled ih =>
      have whole := SettlesDeclared.build head noEquation length settled
      have argsT : List.Forall₂ (fun t L => SettlesDeclared dispatch atoms t L ∧
          GoodRuns dispatch Completed.scopedLookup policy target atoms (Entry.Value.ofAtom t) L)
          ts Ls :=
        forall₂_of_zip length fun p member => ⟨settled p member, ih p member⟩
      have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
        intro L member a inside
        obtain ⟨t, both⟩ := forall₂_right_exists argsT L member
        exact (settlesDeclared_shape both.1).1 a inside
      have closed := (settlesDeclared_shape whole).2.closed
      have args : List.Forall₂ (fun v L => GoodRuns dispatch Completed.scopedLookup policy target
          atoms v L ∧ ∀ a ∈ L, Answerable a) (ts.map Entry.Value.ofAtom) Ls :=
        List.forall₂_map_left_iff.mpr
          (argsT.imp fun _ _ both => ⟨both.2, (settlesDeclared_shape both.1).1⟩)
      rw [call_value]
      exact goodv_node scoped_contract head.head head.untyped closed (head_good atoms head.head)
        (Or.inr rfl) (by simp [List.map_map, Function.comp_def, Entry.Value.erase_ofAtom]) args
        (fun vals => [.expression (.symbol f :: vals)])
        (fun vals member => ⟨goodv_query_absent (scoped_consFree program.rows) head
            (combos_answerable allClean vals member)
            (regionBodies_nil_of_no_equation vals noEquation),
          fun a inside => by
            rw [List.mem_singleton] at inside
            subst inside
            exact app_answerable head.head (combos_answerable allClean vals member)⟩)
  | @call f args Ls ordinary node nonempty sameBodies length settled ih =>
      have whole := SettlesDeclared.call ordinary node nonempty sameBodies length settled
      have closed := (settlesDeclared_shape whole).2.closed
      have bodies : List.Forall₂ (fun b L => GoodRuns dispatch Completed.scopedLookup policy target
          atoms (Entry.Value.ofAtom b) L ∧ BodyFacts b) (regionBodies atoms f args) Ls := by
        rw [← sameBodies]
        exact forall₂_of_zip length fun p member =>
          ⟨ih p member, (settlesDeclared_shape (settled p member)).2⟩
      have nonemptyBodies : regionBodies atoms f args ≠ [] := by
        rw [← sameBodies]
        exact nonempty
      have query := goodv_query_bodies (dispatch := dispatch) (lookup := Completed.scopedLookup)
        (policy := policy) (target := target) (scoped_consFree program.rows) node
        (fun v member => answerable_of_data (ordinary.arguments v member)) nonemptyBodies bodies
      have argsG : List.Forall₂ (fun v L => GoodRuns dispatch Completed.scopedLookup policy target
          atoms v L ∧ ∀ a ∈ L, Answerable a) (args.map Entry.Value.ofAtom)
          (args.map fun a => [a]) := by
        rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
        apply List.forall₂_same.mpr
        intro a member
        refine ⟨goodv_data scoped_answers scoped_contract atoms (ordinary.arguments a member),
          fun x inside => ?_⟩
        rw [List.mem_singleton] at inside
        subst inside
        exact answerable_of_data (ordinary.arguments x member)
      have cleanBodies : ∀ a ∈ Ls.flatten, Answerable a := by
        intro a member
        obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
        have regions := forall₂_of_zip length fun p member => settled p member
        obtain ⟨b, settlesB⟩ := forall₂_right_exists regions L inLs
        exact (settlesDeclared_shape settlesB).1 a inner
      rw [call_value]
      have runs := goodv_node scoped_contract node.head node.untyped closed
        (head_good atoms node.head) (Or.inr rfl)
        (by simp [List.map_map, Function.comp_def, Entry.Value.erase_ofAtom]) argsG
        (fun _ => Ls.flatten)
        (fun vals member => by
          rw [combos_singletons, List.mem_singleton] at member
          subst member
          exact ⟨query, cleanBodies⟩)
      rw [combos_singletons] at runs
      simpa using runs

/-! ## PeTTa on the class -/

/-- **PeTTa's streaming machine evaluates a term of the class to its answers**: an `if` node is
PeTTa's special form, whose branch frame takes the branch of the Boolean literal; PeTTa has no
declared type to meet. -/
theorem settlesDeclared_petta {atoms : List Atom} {t : Atom} {L : List Atom}
    (settles : SettlesDeclared dispatch atoms t L) : PeTTaEvaluates atoms t L := by
  induction settles with
  | @data d data _ => exact PeTTaRuns.petta_data atoms data
  | @declaredIf b y n s branches =>
      exact IfComputed.petta_if_computed
        (PeTTaRuns.petta_data atoms (DataAtom.grounded (.bool b)))
        (PeTTaRuns.petta_data atoms branches.takenData)
  | @plainIf b y n branches =>
      exact IfComputed.petta_if_computed
        (PeTTaRuns.petta_data atoms (DataAtom.grounded (.bool b)))
        (PeTTaRuns.petta_data atoms (undeclared_taken branches))
  | @build f ts Ls head noEquation length settled ih =>
      exact PeTTaNested.petta_nested_constructor head.head head.notCollapse head.notOnce
        (sourceControlForm_of_head head.notControl ts) head.notIO head.notNative noEquation
        (forall₂_of_zip length fun p member =>
          ⟨ih p member, (settlesDeclared_shape (settled p member)).1⟩)
  | @call f args Ls ordinary _ nonempty sameBodies length settled ih =>
      have bodies : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
          (regionBodies atoms f args) Ls := by
        rw [← sameBodies]
        exact forall₂_of_zip length fun p member =>
          ⟨ih p member, (settlesDeclared_shape (settled p member)).2.ground⟩
      exact PeTTaRuns.petta_call ordinary (IfInBodies.defined_arity_of_region nonempty) bodies

/-! ## Every run, both dialects -/

/-- **The variant machine and PeTTa agree on trees with declared `if`, on every run.** On a program
carrying HE's `if`, for any dispatch that does not execute `if` and any policy: for a term of the
class, a complete run of the variant machine exists and every complete run publishes `L`; no run is
infinite and every configuration reached from the entry steps or is final with `L`; and PeTTa's
streaming run yields `L` from some fuel on. -/
theorem declared_trees_every_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfProgram atoms) {c : Atom} {L : List Atom}
    (settles : SettlesDeclared dispatch atoms c L) :
    EveryRunV dispatch Completed.scopedLookup policy (Space.ofList atoms) c L ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } c)) = L := by
  have shape := settlesDeclared_shape settles
  exact ⟨(goodv_entry (settlesDeclared_good notHost program settles)).every_run,
    petta_complete shape.2.ground shape.1 (settlesDeclared_petta settles)⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open DeclaredBranchVariant.Controls (one two tru fls pairIfCall pairIfAnswer if_program_full
  number_branches bool_branches yes_branches)

/-- `(pair (if True 1 2) (if True True False))` is a tree with declared `if`. -/
theorem pair_if_settles : SettlesDeclared noHost ifProgram pairIfCall [pairIfAnswer] := by
  have built := SettlesDeclared.build (dispatch := noHost) (atoms := ifProgram)
    VariantRuns.Controls.pair_head (by decide +kernel)
    (ts := [callOf true one two, callOf true tru fls]) (Ls := [[one], [tru]]) rfl
    (fun p member => by
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact .declaredIf (number_branches true)
      · exact .declaredIf bool_branches)
  simpa [combos] using built

/-- **Positive control, both dialects**: `(pair (if True 1 2) (if True True False))`: every run of
the variant machine finishes with `[(pair 1 True)]`, and PeTTa yields `[(pair 1 True)]` from some
fuel on. -/
theorem pair_if_agree (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram) pairIfCall [pairIfAnswer] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate ifProgram) n
        (Streaming.enter { state := store ifProgram } pairIfCall)) = [pairIfAnswer] :=
  declared_trees_every_run noHost (fun impossible => impossible) policy if_program_full pair_if_settles

/-- `(= (twice) (pair (if True 1 2) (if True True False)))`, with HE's `if`. -/
abbrev twiceRows : List Atom := ifProgram ++ [rule (app "twice" []) pairIfCall]

theorem twice_program : IfProgram twiceRows := by
  refine ⟨IfInBodies.Controls.if_types_of (by decide), ?_⟩
  intro row member
  rcases List.mem_append.mp member with inIf | inTwice
  · exact if_program row inIf
  · simp only [List.mem_singleton] at inTwice
    subst inTwice
    refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
    cases same
    decide

theorem twice_number_types (k : Int) :
    StorageTypesRel (Space.ofList twiceRows) (.grounded (.int k)) [sym "Number"] :=
  .groundedKnown (.int k) (by simp [Atom.undefinedType])

theorem twice_number_branches : DeclaredBranches twiceRows true one two "Number" where
  dataYes := .grounded _
  dataNo := .grounded _
  takenNotRefused := by simp [pick, Atom.notReducible]
  takenType := twice_number_types 1
  notUndefined := by decide
  notAtom := by decide
  typedYes := ⟨_, twice_number_types 1, rfl⟩
  typedNo := ⟨_, twice_number_types 2, rfl⟩
  region := by decide +kernel
  sides := by decide +kernel

theorem twice_bool_branches : DeclaredBranches twiceRows true tru fls "Bool" where
  dataYes := .grounded _
  dataNo := .grounded _
  takenNotRefused := by simp [pick, Atom.notReducible]
  takenType := bool_types_in _ true
  notUndefined := by decide
  notAtom := by decide
  typedYes := ⟨_, bool_types_in _ true, rfl⟩
  typedNo := ⟨_, bool_types_in _ false, rfl⟩
  region := by decide +kernel
  sides := by decide +kernel

theorem twice_head (f : String) (untyped : (Space.ofList twiceRows).atoms.filter
      (typeRegion (.symbol f)) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false) (notControl : controlHead f = false)
    (notEmpty : f ≠ "Empty") (notError : f ≠ "Error") : NodeHead noHost twiceRows f :=
  ⟨.symbol notEmpty notError, untyped, fun impossible => impossible, notInstruction, notIO,
    notNative, notControl⟩

/-- **Declared branches inside a body**: `(twice)` is a tree with declared `if`. -/
theorem twice_settles : SettlesDeclared noHost twiceRows (app "twice" []) [pairIfAnswer] := by
  have pairHead := twice_head "pair" (by decide +kernel) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)
  have body : SettlesDeclared noHost twiceRows pairIfCall [pairIfAnswer] := by
    have built := SettlesDeclared.build (dispatch := noHost) (atoms := twiceRows) pairHead
      (by decide +kernel) (ts := [callOf true one two, callOf true tru fls])
      (Ls := [[one], [tru]]) rfl (fun p member => by
        simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
          or_false] at member
        rcases member with rfl | rfl
        · exact .declaredIf twice_number_branches
        · exact .declaredIf twice_bool_branches)
    simpa [combos] using built
  have called := SettlesDeclared.call (dispatch := noHost) (atoms := twiceRows) (f := "twice")
    (args := []) (Ls := [[pairIfAnswer]])
    ⟨.symbol (by decide) (by decide), (fun _ member => by cases member), (by decide +kernel),
      (fun impossible => impossible), (by decide), (by decide), (by decide), (by decide),
      (by decide), (by decide)⟩
    (twice_head "twice" (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide))
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (fun p member => by
      have instances : regionInstances twiceRows "twice" [] = [pairIfCall] := by
        decide +kernel
      rw [instances] at member
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_singleton] at member
      subst member
      exact body)
  simpa using called

/-- **Positive control, both dialects, declared branches inside a body**: `(twice)`: every run of
the variant machine finishes with `[(pair 1 True)]`, and PeTTa yields `[(pair 1 True)]`. -/
theorem twice_agree (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList twiceRows) (app "twice" [])
        [pairIfAnswer] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate twiceRows) n
        (Streaming.enter { state := store twiceRows } (app "twice" []))) = [pairIfAnswer] :=
  declared_trees_every_run noHost (fun impossible => impossible) policy twice_program twice_settles

/-- `(pair (if True 1 2) (if False yes no))`: a declared and an undeclared taken branch. -/
abbrev mixedCall : Atom := app "pair" [callOf true one two, callOf false (sym "yes") (sym "no")]

theorem mixed_settles : SettlesDeclared noHost ifProgram mixedCall [app "pair" [one, sym "no"]] := by
  have built := SettlesDeclared.build (dispatch := noHost) (atoms := ifProgram)
    VariantRuns.Controls.pair_head (by decide +kernel)
    (ts := [callOf true one two, callOf false (sym "yes") (sym "no")])
    (Ls := [[one], [sym "no"]]) rfl
    (fun p member => by
      simp only [List.zip_cons_cons, List.zip_nil_right, List.mem_cons, List.not_mem_nil,
        or_false] at member
      rcases member with rfl | rfl
      · exact .declaredIf (number_branches true)
      · exact .plainIf (yes_branches false))
  simpa [combos] using built

/-- **Positive control, both dialects, both kinds of taken branch in one term**:
`(pair (if True 1 2) (if False yes no))` gives `[(pair 1 no)]` on every run of the variant machine
and on PeTTa. -/
theorem mixed_agree (policy : Policy) :
    EveryRunV noHost Completed.scopedLookup policy (Space.ofList ifProgram) mixedCall
        [app "pair" [one, sym "no"]] ∧
      ∃ N : Nat, ∀ n, N ≤ n → Streaming.values (Streaming.advance (translate ifProgram) n
        (Streaming.enter { state := store ifProgram } mixedCall)) = [app "pair" [one, sym "no"]] :=
  declared_trees_every_run noHost (fun impossible => impossible) policy if_program_full
    mixed_settles

/-- **Negative control, the class's boundary**: `(if (isTrue) 1 2)` is not in the class: its
condition is no Boolean literal, `if` has a declared type (so it is no constructor head), and `if`
is no ordinary head. Computed conditions are covered on the model for undeclared branches
(`IfConditions`, `IfInBodies`), not here. -/
theorem computed_condition_not_in_class (L : List Atom) :
    ¬ SettlesDeclared noHost ifProgram (app "if" [app "isTrue" [], one, two]) L := by
  intro settles
  generalize same : app "if" [app "isTrue" [], one, two] = t at settles
  cases settles with
  | data data _ =>
      subst same
      cases data
  | @declaredIf b y n s branches =>
      simp [callOf, app] at same
  | @plainIf b y n branches =>
      simp [callOf, app] at same
  | build head _ _ _ =>
      simp only [app, Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨rfl, _⟩ := same
      have typed := head.untyped
      revert typed
      decide +kernel
  | call ordinary _ _ _ _ _ =>
      simp only [app, Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
      obtain ⟨rfl, _⟩ := same
      have typed := ordinary.untyped
      revert typed
      decide +kernel

end Controls

#print axioms settlesDeclared_shape
#print axioms settlesDeclared_good
#print axioms settlesDeclared_petta
#print axioms declared_trees_every_run
#print axioms Controls.pair_if_settles
#print axioms Controls.pair_if_agree
#print axioms Controls.twice_program
#print axioms Controls.twice_settles
#print axioms Controls.twice_agree
#print axioms Controls.mixed_settles
#print axioms Controls.mixed_agree
#print axioms Controls.computed_condition_not_in_class

end DeclaredTrees

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
