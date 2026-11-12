import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedCalls

/-!
# Evaluation marks on values: HE reads compound bindings without changing the answers

HE's contextual values carry an evaluation mark on every expression node (`Entry.Value`, status
`active` or `held`). Publication marks results (under `Policy.ready` every successful expression
result is held), substitution keeps the marks of the values it inserts, and under the reuse policy a
held expression is delivered as it is, never evaluated again (`Entry.Rel.held`). So when a variable
of an equation is bound to a compound argument such as `(S Z)`, HE's read of the body is not the
plain value of PeTTa's instance: it carries the argument's marks.

The marks never change an answer on values. A **marked value** (`Marked`) is a contextual value in
which every node marked held is a value of the program (a constructor tree over data atoms,
`NestedValues.Value`). Delivering such a node gives what evaluating it gives, itself.

* `marked_of_value`: every marking of a value is admissible, so no mark needs to be tracked:
  argument results and unifier environments whose atoms are values are marked values.
* `substitute_marked`, `work_read_K`: HE's read of an equation body under its unifier's frame, for a
  call whose arguments are values, is a marked value whose atom is PeTTa's instance.
* `HEEvaluatesM`: HE's machine evaluates every marked presentation of a term to the same answers.
  `tuple_product_M`, `he_nested_M`, `he_held`, `he_query_K` build the runs.
* `DeterminedM`: every derivation of HE's completed relation from every marked presentation returns
  the same atoms. `tuple_rows_M`, `nested_determined_M`, `bodies_source_M`, `query_determined_K`
  prove it compositionally.

## Controls

* `Controls.ready_marks_held`: under `Policy.ready` the publication of `(S Z)` is held, so it is not
  the plain value `ofAtom (S Z)`, and a body variable bound to it reads as the held value
  (`Controls.held_read_not_plain`). The plain read of `BoundVariables.work_read` does not extend to
  compound bindings.
* `Controls.held_call_not_marked` (negative): a held call of a defined head is not a marked value;
  `Controls.held_value_marked` (positive): a held `(S Z)` is.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace MarkedValues

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (applyTypeValuation renameTypeVars
  TypeBindingSatisfied)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom applySubst)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls

variable {dispatch : GroundedDispatch}

/-! ## Values and their parts -/

/-- The items of a compound value are values. -/
theorem value_children {atoms : List Atom} {items : List Atom}
    (value : NestedValues.Value dispatch atoms (.expression items)) :
    ∀ i ∈ items, NestedValues.Value dispatch atoms i := by
  cases value with
  | data data => cases data
  | node head each =>
      intro i member
      rcases List.mem_cons.mp member with rfl | inRest
      · exact .data head.head
      · exact each i inRest

/-- A value is never a variable. -/
theorem value_not_var {atoms : List Atom} {x : String} :
    ¬ NestedValues.Value dispatch atoms (.var x) := by
  intro value
  cases value with
  | data data => cases data

/-- **A valuation that instantiates a term to a value maps each of its variables to a value.** -/
theorem var_of_value {atoms : List Atom} {v : String → Atom} : ∀ (t : Atom) {d : Atom},
    applyTypeValuation v t = d → NestedValues.Value dispatch atoms d →
      ∀ x ∈ TypeSubst.typeVars t, NestedValues.Value dispatch atoms (v x)
  | .var name, d, instantiated, value, x, member => by
      simp only [TypeSubst.typeVars, List.mem_singleton] at member
      subst member
      simp only [applyTypeValuation] at instantiated
      rw [instantiated]
      exact value
  | .symbol _, _, _, _, x, member => by simp [TypeSubst.typeVars] at member
  | .grounded _, _, _, _, x, member => by simp [TypeSubst.typeVars] at member
  | .expression items, d, instantiated, value, x, member => by
      simp only [applyTypeValuation] at instantiated
      subst instantiated
      simp only [TypeSubst.typeVars] at member
      exact list items (value_children value) x member
where
  list : ∀ (items : List Atom),
      (∀ i ∈ items.map (applyTypeValuation v), NestedValues.Value dispatch atoms i) →
      ∀ x ∈ TypeSubst.typeVarsList items, NestedValues.Value dispatch atoms (v x)
    | [], _, x, member => by simp [TypeSubst.typeVarsList] at member
    | i :: is, each, x, member => by
        simp only [TypeSubst.typeVarsList, List.mem_append] at member
        rcases member with inI | inIs
        · exact var_of_value i rfl (each _ (by simp)) x inI
        · exact list is (fun j m => each j (by simp only [List.map_cons]; exact List.mem_cons_of_mem _ m))
            x inIs

/-- The variables of patterns that instantiate to values are bound to values. -/
theorem vars_of_values {atoms : List Atom} {v : String → Atom} {ps args : List Atom}
    (instantiated : ps.map (applyTypeValuation v) = args)
    (values : ∀ a ∈ args, NestedValues.Value dispatch atoms a) :
    ∀ x ∈ TypeSubst.typeVarsList ps, NestedValues.Value dispatch atoms (v x) :=
  var_of_value.list ps (by rw [instantiated]; exact values)

/-! ## Marked values -/

/-- **A marked value**: a contextual value in which every expression node marked held is a value of
the program. -/
inductive Marked (dispatch : GroundedDispatch) (atoms : List Atom) : Entry.Value → Prop
  | symbol (name : String) : Marked dispatch atoms (.symbol name)
  | var (name : String) : Marked dispatch atoms (.var name)
  | grounded (value : GroundedValue) : Marked dispatch atoms (.grounded value)
  | active {children : List Entry.Value} : (∀ c ∈ children, Marked dispatch atoms c) →
      Marked dispatch atoms (.expression .active children)
  | held {children : List Entry.Value} :
      NestedValues.Value dispatch atoms (.expression (children.map Entry.Value.erase)) →
      (∀ c ∈ children, Marked dispatch atoms c) →
      Marked dispatch atoms (.expression .held children)

/-- **Every marking of a value is admissible.** -/
theorem marked_of_value {atoms : List Atom} : ∀ (v : Entry.Value),
    NestedValues.Value dispatch atoms v.erase → Marked dispatch atoms v
  | .symbol name, _ => .symbol name
  | .var name, value => by
      simp only [Entry.Value.erase] at value
      exact (value_not_var value).elim
  | .grounded g, _ => .grounded g
  | .expression readiness children, value => by
      have shaped : NestedValues.Value dispatch atoms (.expression (children.map Entry.Value.erase)) := by
        simpa only [Entry.Value.erase] using value
      have each := list children (fun c member =>
        value_children shaped c.erase (List.mem_map.mpr ⟨c, member, rfl⟩))
      cases readiness with
      | active => exact .active each
      | held => exact .held shaped each
where
  list : ∀ (children : List Entry.Value),
      (∀ c ∈ children, NestedValues.Value dispatch atoms c.erase) →
      ∀ c ∈ children, Marked dispatch atoms c
    | [], _ => fun c member => by cases member
    | c :: cs, each => by
        have here := marked_of_value c (each c List.mem_cons_self)
        have rest := list cs (fun e m => each e (List.mem_cons_of_mem _ m))
        intro d member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact here
        · exact rest d inRest

/-- The plain value of an atom is marked: all its nodes are active. -/
theorem marked_ofAtom {atoms : List Atom} : ∀ (t : Atom),
    Marked dispatch atoms (Entry.Value.ofAtom t)
  | .symbol name => by
      simp only [Entry.Value.ofAtom]
      exact .symbol name
  | .var name => by
      simp only [Entry.Value.ofAtom]
      exact .var name
  | .grounded g => by
      simp only [Entry.Value.ofAtom]
      exact .grounded g
  | .expression items => by
      simp only [Entry.Value.ofAtom]
      exact .active (list items)
where
  list : ∀ (items : List Atom), ∀ c ∈ items.map Entry.Value.ofAtom, Marked dispatch atoms c
    | [] => fun c member => by cases member
    | i :: is => by
        have here := marked_ofAtom (atoms := atoms) i
        have rest := list is
        intro c member
        rcases List.mem_cons.mp member with rfl | inRest
        · exact here
        · exact rest c inRest

/-- **Substituting marked values into a body keeps it marked**: the body's own nodes stay active
under both rebuilding policies, and the inserted values keep their marks. -/
theorem substitute_marked {atoms : List Atom} (rebuilding : Entry.RebuildPolicy)
    (env : String → Entry.Value) : ∀ (t : Atom),
      (∀ x ∈ TypeSubst.typeVars t, Marked dispatch atoms (env x)) →
      Marked dispatch atoms (Entry.Value.substitute rebuilding env (Entry.Value.ofAtom t))
  | .var name, each => by
      simpa [Entry.Value.ofAtom, Entry.Value.substitute] using
        each name (by simp [TypeSubst.typeVars])
  | .symbol name, _ => by
      simpa [Entry.Value.ofAtom, Entry.Value.substitute] using Marked.symbol (dispatch := dispatch)
        (atoms := atoms) name
  | .grounded g, _ => by
      simpa [Entry.Value.ofAtom, Entry.Value.substitute] using Marked.grounded (dispatch := dispatch)
        (atoms := atoms) g
  | .expression items, each => by
      have status : ∀ before after : Atom,
          Entry.Value.rebuildStatus rebuilding .active before after = .active := by
        intro before after
        cases rebuilding <;> simp [Entry.Value.rebuildStatus]
      simp only [Entry.Value.ofAtom, Entry.Value.substitute]
      rw [status]
      exact .active (list items (by simpa [TypeSubst.typeVars] using each))
where
  list : ∀ (items : List Atom), (∀ x ∈ TypeSubst.typeVarsList items, Marked dispatch atoms (env x)) →
      ∀ c ∈ (items.map Entry.Value.ofAtom).map (Entry.Value.substitute rebuilding env),
        Marked dispatch atoms c
    | [], _ => fun c member => by cases member
    | i :: is, each => by
        have here := substitute_marked rebuilding env i fun x member =>
          each x (by simp [TypeSubst.typeVarsList, member])
        have rest := list is fun x member => each x (by simp [TypeSubst.typeVarsList, member])
        intro c member
        simp only [List.map_cons, List.mem_cons] at member
        rcases member with rfl | inRest
        · exact here
        · exact rest c inRest

/-- A closed contextual value reads as itself under every activation. -/
theorem read_closed_value (policy : Policy) (frame : Frame) {v : Entry.Value}
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs v.erase name) :
    frame.read policy v = v := by
  unfold Completed.Frame.read
  exact Entry.Value.substitute_variable_free _ _ _ closed

/-- The contextual value of a call atom headed by a symbol: the head is the symbol itself. -/
theorem call_value_shape {v : Entry.Value} {f : String} {ts : List Atom}
    (erased : v.erase = .expression (.symbol f :: ts)) :
    ∃ readiness vs, v = .expression readiness (.symbol f :: vs) ∧ vs.map Entry.Value.erase = ts := by
  cases v with
  | symbol _ => simp [Entry.Value.erase] at erased
  | var _ => simp [Entry.Value.erase] at erased
  | grounded _ => simp [Entry.Value.erase] at erased
  | expression readiness children =>
      simp only [Entry.Value.erase, Atom.expression.injEq] at erased
      cases children with
      | nil => simp at erased
      | cons c cs =>
          simp only [List.map_cons, List.cons.injEq] at erased
          obtain ⟨headErase, restErase⟩ := erased
          cases c with
          | symbol name =>
              simp only [Entry.Value.erase, Atom.symbol.injEq] at headErase
              subst headErase
              exact ⟨readiness, cs, rfl, restErase⟩
          | var _ => simp [Entry.Value.erase] at headErase
          | grounded _ => simp [Entry.Value.erase] at headErase
          | expression _ _ => simp [Entry.Value.erase] at headErase

/-- The children of a marked expression are marked. -/
theorem Marked.children {atoms : List Atom} {readiness : Entry.Status} {children : List Entry.Value}
    (marked : Marked dispatch atoms (.expression readiness children)) :
    ∀ c ∈ children, Marked dispatch atoms c := by
  cases marked with
  | active each => exact each
  | held _ each => exact each

/-- A held node of a marked value is a value. -/
theorem Marked.held_value {atoms : List Atom} {children : List Entry.Value}
    (marked : Marked dispatch atoms (.expression .held children)) :
    NestedValues.Value dispatch atoms (.expression (children.map Entry.Value.erase)) := by
  cases marked with
  | held value _ => exact value

/-! ## HE's machine on marked values -/

/-- **HE's machine runs the contextual value `v` to the answers `L`**: from pending work on `v` under
`%Undefined%`, with any live list, scope, activation, continuation stack and publication prefix, HE's
machine returns a batch whose atoms are `L`, under the same stack. -/
def HERunsTo (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result),
    ∃ results : List Result, results.map (fun result => result.1.erase) = L ∧
      Relation.ReflTransGen (HEStep dispatch lookup policy)
        ⟨Space.ofList atoms, .work (.atom live scope v Atom.undefinedType activation), stack,
          emitted⟩
        ⟨Space.ofList atoms, .returning results, stack, emitted⟩

/-- **HE's machine evaluates every marked presentation of `t` to `L`.** -/
def HEEvaluatesM (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked dispatch atoms v → HERunsTo dispatch lookup policy atoms v L

section HEMachine

variable {lookup : CastLookup} {policy : Policy}

/-- On the plain presentation, `HEEvaluatesM` is `AnswerBags.HEEvaluates`. -/
theorem HEEvaluatesM.plain {atoms : List Atom} {t : Atom} {L : List Atom}
    (evaluates : HEEvaluatesM dispatch lookup policy atoms t L) :
    HEEvaluates dispatch lookup policy atoms t L :=
  evaluates (Entry.Value.ofAtom t) (Entry.Value.erase_ofAtom t) (marked_ofAtom t)

/-- **A data atom**: its only marked presentation is itself. -/
theorem he_data_M (answers : AnswersUndefined lookup) (atoms : List Atom) {d : Atom}
    (data : DataAtom d) : HEEvaluatesM dispatch lookup policy atoms d [d] := by
  intro v erased _
  rw [value_of_data data erased]
  exact HERuns.he_data answers atoms data

/-- **HE's tuple traversal of marked values**: every element runs to its answers, and the tuple
returns every combination in one batch, the first element varying slowest. -/
theorem tuple_product_M (atoms : List Atom) :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)), vs ≠ [] →
      List.Forall₂ (fun v L => HERunsTo dispatch lookup policy atoms v L ∧
        ∀ a ∈ L, Answerable a) vs Ls →
      ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
        (emitted : List Result), ∃ R : List Result,
          R.map (fun r => r.1.erase) = (combos Ls).map Atom.expression ∧
          (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
          Relation.ReflTransGen (HEStep dispatch lookup policy)
            ⟨Space.ofList atoms, .work (.tuple live scope vs activation), stack, emitted⟩
            ⟨Space.ofList atoms, .returning R, stack, emitted⟩
  | [], _, nonempty, _ => absurd rfl nonempty
  | [v], Ls, _, related => by
      intro live scope activation stack emitted
      cases related with
      | cons here rest =>
          rename_i L Ls'
          cases rest
          obtain ⟨R, eraseR, path⟩ := here.1 live scope activation (.singleton :: stack) emitted
          have clean := HENested.clean_of_erase eraseR here.2
          have singled : ∀ r ∈ R, Completed.tupleSingleton r = (.expression .active [r.1], r.2) := by
            intro r member
            unfold Completed.tupleSingleton
            rw [HENested.emptyOrError_false (clean r member)]
            rfl
          refine ⟨R.map Completed.tupleSingleton, ?_, ?_, ?_⟩
          · rw [List.map_map]
            have mapped : R.map ((fun r : Result => r.1.erase) ∘ Completed.tupleSingleton) =
                (R.map fun r => r.1.erase).map fun a => Atom.expression [a] := by
              rw [List.map_map]
              apply List.map_congr_left
              intro r member
              simp only [Function.comp_apply, singled r member, Entry.Value.erase, List.map_cons,
                List.map_nil]
            rw [mapped, eraseR, combos_singleton, List.map_map]
            rfl
          · intro r member
            obtain ⟨r', member', rfl⟩ := List.mem_map.mp member
            exact ⟨_, by rw [singled r' member']⟩
          · refine .head (.internal .tupleSingleton) ?_
            refine .trans path ?_
            exact .single (.internal .singleton)
  | v :: v2 :: rest, Ls, _, related => by
      intro live scope activation stack emitted
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨R, eraseR, path⟩ := here.1 _ scope activation
            (.branches live scope (v2 :: rest) :: stack) emitted
          have clean := HENested.clean_of_erase eraseR here.2
          have tailRuns := tuple_product_M atoms (v2 :: rest) Ls' (List.cons_ne_nil _ _) later
          have tailClean : ∀ c ∈ combos Ls', ∃ c0 cs, c = c0 :: cs ∧ Answerable c0 := by
            intro c member
            have lengths := combos_length member
            have positive : Ls'.length = (v2 :: rest).length := (List.Forall₂.length_eq later).symm
            obtain ⟨c0, cs, rfl⟩ : ∃ c0 cs, c = c0 :: cs := by
              cases c with
              | nil =>
                  simp only [List.length_nil] at lengths
                  simp only [List.length_cons] at positive
                  omega
              | cons c0 cs => exact ⟨c0, cs, rfl⟩
            refine ⟨c0, cs, rfl, ?_⟩
            have allClean : ∀ L' ∈ Ls', ∀ a ∈ L', Answerable a := by
              intro L' member' a inside
              obtain ⟨t', both⟩ := forall₂_right_exists later L' member'
              exact both.2 a inside
            exact combos_answerable allClean _ member c0 List.mem_cons_self
          obtain ⟨R', eraseR', shapeR', loop⟩ := HENested.branches_loop atoms (live := live)
            (fun live' activation' stack' emitted' => tailRuns live' scope activation' stack' emitted')
            tailClean R clean stack emitted
          refine ⟨R', ?_, shapeR', ?_⟩
          · rw [eraseR']
            have flat : R.flatMap (fun h => (combos Ls').map fun c => Atom.expression (h.1.erase :: c)) =
                (R.map fun h => h.1.erase).flatMap
                  (fun a => (combos Ls').map fun c => Atom.expression (a :: c)) := by
              rw [List.flatMap_map]
            rw [flat, eraseR]
            simp only [combos, List.map_flatMap, List.map_map]
            rfl
          · refine .head (.internal .tupleCons) ?_
            refine .trans path ?_
            refine .head (.internal .branches) ?_
            exact loop

theorem call_not_stopped {f : String} {ts : List Atom} (head : DataAtom (.symbol f)) :
    ¬ IsEmptyOrErrorRel (.expression (.symbol f :: ts)) := by
  rintro (same | ⟨tail, same⟩)
  · simp [Atom.empty] at same
  · cases head with
    | symbol _ notError =>
        simp at same
        exact notError same.1

theorem undefined_not_raw :
    ¬(Atom.undefinedType = Atom.atomType ∨ Atom.undefinedType = Atom.expressionType ∨
      Atom.expressionType = Atom.variableType) := by
  decide +kernel

/-- **HE evaluates a marked call whose root it interprets**: the type-directed entry, the whole
argument product over the marked arguments, the query of `f` on each combination in turn, and the
publication. -/
theorem he_nested_M (answers : AnswersUndefined lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    {readiness : Entry.Status} {vs : List Entry.Value}
    (interpreted : policy.reentry = .reinterpret ∨ readiness = .active)
    (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => HERunsTo dispatch lookup policy atoms v L ∧
      ∀ a ∈ L, Answerable a) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, HEQuery dispatch lookup policy atoms f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    HERunsTo dispatch lookup policy atoms (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  intro live scope activation stack emitted
  have eraseV : (Entry.Value.expression readiness (.symbol f :: vs)).erase =
      .expression (.symbol f :: ts) := by
    simp only [Entry.Value.erase, List.map_cons, erased]
  have readV : activation.read policy (.expression readiness (.symbol f :: vs)) =
      .expression readiness (.symbol f :: vs) :=
    read_closed_value policy activation (by rw [eraseV]; exact closed)
  have entry : Entry.Rel policy.reentry
      (activation.read policy (.expression readiness (.symbol f :: vs))).status
      (activation.read policy (.expression readiness (.symbol f :: vs))).erase
      Atom.undefinedType .interpret := by
    rw [readV, eraseV]
    exact .expression (call_not_stopped head) undefined_not_raw interpreted
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.symbol f).erase
      {Atom.undefinedType} := by
    simp only [Entry.Value.erase]
    exact untyped_occurrences untyped
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := dispatch) (lookup := lookup) (live := live) (scope := scope) (stack := stack)
    entry readV occurrences
  have published : (activation.read policy (.expression readiness (.symbol f :: vs))).erase =
      .expression (.symbol f :: ts) := by
    rw [readV, eraseV]
  rw [published] at step
  have headRuns : HERunsTo dispatch lookup policy atoms (.symbol f) [.symbol f] :=
    he_data_M answers atoms head (.symbol f) (by simp only [Entry.Value.erase]) (.symbol f)
  obtain ⟨T, eraseT, _, pathT⟩ := tuple_product_M (dispatch := dispatch) (lookup := lookup)
    (policy := policy) atoms (.symbol f :: vs) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
    (.cons ⟨headRuns, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩ args) (Atom.undefinedType :: live) scope activation
    (.calls live scope Atom.undefinedType :: .publish (.expression (.symbol f :: ts)) :: stack)
    emitted
  rw [combos_head] at eraseT
  have rows : ∀ r ∈ T, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
      HEQuery dispatch lookup policy atoms f vals (Q vals) := by
    intro r member
    have inRows : r.1.erase ∈ ((combos Ls).map (Atom.symbol f :: ·)).map Atom.expression := by
      rw [← eraseT]
      exact List.mem_map.mpr ⟨r, member, rfl⟩
    rw [List.map_map] at inRows
    obtain ⟨vals, valsMem, valsEq⟩ := List.mem_map.mp inRows
    exact ⟨vals, valsEq.symm, (apps vals valsMem).1⟩
  obtain ⟨R, eraseR, pathR⟩ := HENested.calls_loop (dispatch := dispatch) (lookup := lookup)
    (policy := policy) atoms (live := live) (scope := scope) Q T rows
    (.publish (.expression (.symbol f :: ts)) :: stack) emitted
  have totals : T.flatMap (fun r => Q (HENested.argsOf r.1.erase)) = (combos Ls).flatMap Q := by
    have viaAtoms : T.flatMap (fun r => Q (HENested.argsOf r.1.erase)) =
        (T.map fun r => r.1.erase).flatMap (fun a => Q (HENested.argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseT, List.map_map, List.flatMap_map]
    rfl
  rw [totals] at eraseR
  have clean : ∀ r ∈ R, Answerable r.1.erase := by
    apply HENested.clean_of_erase eraseR
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).2 a inner
  obtain ⟨final, eraseFinal, pathFinal⟩ := HENested.publish_step (dispatch := dispatch)
    (lookup := lookup) (policy := policy) (atoms := atoms) (.expression (.symbol f :: ts)) R clean
    stack emitted
  refine ⟨final, by rw [eraseFinal, eraseR], ?_⟩
  refine .head (.internal step) ?_
  refine .trans pathT ?_
  refine .head (.internal .calls) ?_
  exact pathR.trans pathFinal

/-- **A held expression under the reuse policy is delivered as it is.** -/
theorem he_held (atoms : List Atom) {children : List Entry.Value}
    (reuses : policy.reentry = .reuse)
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (children.map Entry.Value.erase)) name)
    (notStopped : ¬ IsEmptyOrErrorRel (.expression (children.map Entry.Value.erase))) :
    HERunsTo dispatch lookup policy atoms (.expression .held children)
      [.expression (children.map Entry.Value.erase)] := by
  intro live scope activation stack emitted
  have eraseV : (Entry.Value.expression .held children).erase =
      .expression (children.map Entry.Value.erase) := by
    simp only [Entry.Value.erase]
  have readV := read_closed_value policy activation (v := .expression .held children)
    (by rw [eraseV]; exact closed)
  have entry : Entry.Rel policy.reentry
      (activation.read policy (.expression .held children)).status
      (activation.read policy (.expression .held children)).erase Atom.undefinedType .deliver := by
    rw [readV, eraseV]
    exact .held notStopped undefined_not_raw reuses rfl
  refine ⟨[(activation.read policy (.expression .held children), activation)], ?_,
    .single (.internal (.delivered entry))⟩
  rw [readV]
  simp only [List.map_cons, List.map_nil, eraseV]

/-- `BodyFacts` excludes a `function` body under every marking of its atom. -/
theorem not_pending {policy : Policy} {i : Atom} (facts : BodyFacts i) {r : Entry.Value}
    (erased : r.erase = i) : ¬ Completed.FunctionPending policy r := by
  rintro ⟨⟨body, same⟩, _⟩
  rw [erased] at same
  subst same
  exact facts.notFunction policy ⟨⟨body, by rw [Entry.Value.erase_ofAtom]⟩,
    Or.inr (by simp [Entry.Value.ofAtom, Entry.Value.status])⟩

/-- **The equation loop on marked reads**: each work's body is read under its unifier's frame as a
marked value of its instance, evaluated, and the batches are concatenated in work order. -/
theorem equations_steps_K {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        HEEvaluatesM dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          HERuns.HESteps dispatch lookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType activation
              works), stack, emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩
  | [], Ls, _, related, stack, emitted => by
      cases related
      exact ⟨[], rfl, .single (.internal .equationsNil)⟩
  | work :: works, Ls, unifiers, related, stack, emitted => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
          obtain ⟨i, readsAs, evaluates, facts⟩ := here
          obtain ⟨readErase, readMarked⟩ := readsAs output sameBindings
          obtain ⟨R, eraseR, pathR⟩ := evaluates _ readErase readMarked live scope output
            (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType) []) ::
              .append (.equations live scope original Atom.undefinedType activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps_K works Ls'
            (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
            (.prepend (R ++ []) :: stack) emitted
          refine ⟨(R ++ []) ++ R', ?_, ?_⟩
          · rw [List.append_nil, List.map_append, eraseR, eraseR', List.flatten_cons]
          · refine .head (.internal (.equationsCons sameBindings unified)) ?_
            refine .head (.internal (.boundaryProducerRaw (not_pending facts readErase))) ?_
            refine .head (.internal .boundaryBatch) ?_
            refine .head (.internal .boundaryBatchCons) ?_
            refine .head (.internal .boundaryReturned) ?_
            refine .head (.internal (.returnEvaluate ?_ ?_)) ?_
            · rw [readErase]
              exact facts.notRefused
            · rw [readErase]
              exact facts.notStopped
            refine .trans pathR ?_
            refine .head (.internal .append) ?_
            refine .head (.internal .boundaryBatchNil) ?_
            refine .head (.internal .prepend) ?_
            refine .head (.internal .append) ?_
            refine .trans pathR' ?_
            exact .single (.internal .prepend)

end HEMachine

/-! ## HE reads each body as a marked value of its instance -/

/-- **HE reads a work's body as a marked value of PeTTa's instance.** For a work of the frontier of
a call whose arguments are values, on a program whose bodies use only their left side's variables:
the row's sides give an instance, and under every frame whose bindings are the work's, HE's read of
the fresh body is a marked value whose atom is that instance. -/
theorem work_read_K (policy : Policy) {atoms live : List Atom} {f : String} {args : List Atom}
    {incoming : Bindings} (argsValues : ∀ a ∈ args, NestedValues.Value dispatch atoms a)
    (program : ScopedProgram atoms) {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works)
    {w : EquationWork} (member : w ∈ works) :
    ∃ i, sidesInstance args (w.left, w.right) = some i ∧
      ∀ output : Frame, output.bindings = w.bindings →
        (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
        Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body)) := by
  obtain ⟨matched, occurrence⟩ := frontier.occurrence member
  have stored : Atom.expression [.symbol "=", w.left, w.right] ∈ atoms :=
    List.mem_of_getElem? occurrence.stored
  obtain ⟨consFree, boundRow⟩ := program _ stored
  obtain ⟨h, ps, leftShape, psFree⟩ := consFree w.left w.right rfl
  have varsBound := boundRow w.left w.right rfl
  obtain ⟨rename, _, renamedLeft, renamedRight, _⟩ := occurrence.selected.1
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedRight
  have groundQuery : TypeSubst.typeVars (.expression (.symbol f :: args)) = [] := by
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
    exact (Mettapedia.Languages.MeTTa.HE.TypeGrounding.typeVarsList_eq_nil_iff args).mpr
      fun a m => HERuns.ground_typeVars (value_answerable (argsValues a m))
  -- every model of the work's bindings instantiates the left side to the call
  have instantiates : ∀ v, TypeBindingSatisfied v w.bindings →
      applyTypeValuation (v ∘ rename) w.left = .expression (.symbol f :: args) := by
    intro v model
    have equal := ((occurrence.solutions v).mp model).1
    rw [patternEq,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      Mettapedia.Languages.MeTTa.HE.HOLContract.applyTypeValuation_of_ground v groundQuery] at equal
    exact equal.symm
  obtain ⟨model, satisfiedWork⟩ := occurrence.result.1.2
  have first := instantiates model satisfiedWork
  rw [leftShape] at first
  simp only [applyTypeValuation, List.map_cons, Atom.expression.injEq, List.cons.injEq,
    Atom.symbol.injEq] at first
  obtain ⟨sameHead, sameArgs⟩ := first
  -- PeTTa's matching of the patterns against the call's values
  obtain ⟨bound, matchedBound, _⟩ := RegionsWithVariables.completesConsistent_list (model ∘ rename) ps
    (fun p m => RegionsWithVariables.completesConsistent _ (psFree p m)) []
    (RegionsWithVariables.consistent_nil _)
  rw [sameArgs] at matchedBound
  obtain ⟨_, _, instanceArgs⟩ := RegionsWithVariables.sound_list ps
    (fun p m => RegionsWithVariables.sound (psFree p m)) [] bound args matchedBound
  have boundInstance := instanceArgs bound (RegionsWithVariables.Extends.refl bound)
  -- every model agrees with PeTTa's matching on the left side's variables
  have agree : ∀ v, TypeBindingSatisfied v w.bindings → ∀ x ∈ TypeSubst.typeVars w.left,
      (v ∘ rename) x = RegionsWithVariables.asValuation bound x := by
    intro v model x member
    apply agree_of_same (v ∘ rename) (RegionsWithVariables.asValuation bound) w.left
      _ x member
    rw [instantiates v model, leftShape]
    simp only [applyTypeValuation, List.map_cons, boundInstance, sameHead]
  have bodyForced : ∀ v, TypeBindingSatisfied v w.bindings →
      applyTypeValuation v w.body = applySubst bound w.right := by
    intro v model
    rw [bodyEq,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ApplicationEquivariance.applyTypeValuation_renameTypeVars,
      applySubst_eq_valuation]
    exact Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.applyTypeValuation_congr_of_typeVars
      w.right fun x member => agree v model x (varsBound x member)
  have equation : LiveEquations.equationOfRow (.expression [.symbol "=", w.left, w.right]) =
      some ⟨f, ps, w.right⟩ := by
    rw [leftShape, sameHead]
    rfl
  refine ⟨applySubst bound w.right, ?_, fun output sameBindings => ?_⟩
  · simp only [sidesInstance, equation, Option.bind_some, instanceOf, matchedBound, Option.map_some]
  · have certified : Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.BindingTheory.ReadoutCertificate
        w.bindings (Entry.Value.eraseEnvironment output.environment) := by
      have := output.certified
      rwa [sameBindings] at this
    -- each variable of the fresh body reads as a value, under whatever marks
    have marked : ∀ x ∈ TypeSubst.typeVars w.body,
        Marked dispatch atoms (Entry.Value.resolve output.environment x) := by
      intro x member
      rw [bodyEq,
        Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.ScopeObservation.typeVars_renameTypeVars]
        at member
      obtain ⟨y, inRight, rfl⟩ := List.mem_map.mp member
      have inLeft := varsBound y inRight
      rw [leftShape] at inLeft
      simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append] at inLeft
      have value : NestedValues.Value dispatch atoms (RegionsWithVariables.asValuation bound y) :=
        vars_of_values boundInstance argsValues y inLeft
      have inLeftAtom : y ∈ TypeSubst.typeVars w.left := by
        rw [leftShape]
        simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append]
        exact inLeft
      have forced := certified.forced_read (.var (rename y)) (RegionsWithVariables.asValuation bound y)
        fun v model => by
          have := agree v model y inLeftAtom
          simpa [applyTypeValuation] using this
      have erased : (Entry.Value.resolve output.environment (rename y)).erase =
          RegionsWithVariables.asValuation bound y := by
        rw [Entry.Value.erase_resolve]
        simpa [TypeSubst.apply] using forced
      apply marked_of_value
      rw [erased]
      exact value
    have readErase : (output.read policy (Entry.Value.ofAtom w.body)).erase =
        applySubst bound w.right := by
      unfold Completed.Frame.read
      rw [Entry.Value.erase_substitute_environment, Entry.Value.erase_ofAtom]
      exact certified.forced_read w.body _ bodyForced
    refine ⟨readErase, ?_⟩
    unfold Completed.Frame.read
    exact substitute_marked policy.rebuilding (Entry.Value.resolve output.environment) w.body marked

theorem works_instances_K (policy : Policy) {atoms live : List Atom} {f : String}
    {args : List Atom} {incoming : Bindings}
    (argsValues : ∀ a ∈ args, NestedValues.Value dispatch atoms a) (program : ScopedProgram atoms)
    (satisfiable : ∃ model : String → Atom, TypeBindingSatisfied model incoming)
    {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (.expression (.symbol f :: args))
      incoming works) :
    List.Forall₂ (fun w i => sidesInstance args (w.left, w.right) = some i ∧
        ∀ output : Frame, output.bindings = w.bindings →
          (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body)))
      works (regionInstances atoms f args) := by
  have ground : ∀ value ∈ args, TypeSubst.typeVars value = [] :=
    fun a m => HERuns.ground_typeVars (value_answerable (argsValues a m))
  have sidesEq := frontier_sides ground satisfiable (scoped_consFree program) frontier
  have listed := forall₂_filterMap (fun w : EquationWork => sidesInstance args (w.left, w.right))
    (fun w i => ∀ output : Frame, output.bindings = w.bindings →
      (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
      Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body)))
    works fun w member => work_read_K policy argsValues program frontier member
  have instancesEq : works.filterMap (fun w => sidesInstance args (w.left, w.right)) =
      regionInstances atoms f args := by
    rw [regionInstances_sides, ← sidesEq, List.filterMap_map]
    rfl
  rw [instancesEq] at listed
  exact listed

section HEQueries

variable {lookup : CastLookup} {policy : Policy}

/-- **HE's equation query on a call of values with a nonempty region of instances**: the query
fires, each work's body is read as a marked value of its instance and evaluated, and the batches
come back in row order. -/
theorem he_query_K {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {args : List Atom} (head : NodeHead dispatch atoms f)
    (argsValues : ∀ a ∈ args, NestedValues.Value dispatch atoms a)
    (nonempty : regionInstances atoms f args ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => HEEvaluatesM dispatch lookup policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f args) Ls) :
    HEQuery dispatch lookup policy atoms f args Ls.flatten := by
  intro live scope activation value erased stack emitted
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) (Atom.undefinedType :: live)
    (.expression (.symbol f :: args)) activation.bindings
  have instances := works_instances_K policy argsValues program
    activation.certified.satisfiable frontier
  have worksNonempty : works ≠ [] := by
    intro none
    subst none
    apply nonempty
    apply List.eq_nil_of_length_eq_zero
    simpa using instances.length_eq.symm
  have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
      value.erase activation.bindings works := by
    rw [erased]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment value
        (Entry.Value.ofAtom w.pattern) output.environment := by
    intro w member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
    exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
  have related : List.Forall₂ (fun work L => ∃ i, (∀ output : Frame,
        output.bindings = work.bindings →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
      HEEvaluatesM dispatch lookup policy atoms i L ∧ BodyFacts i) works Ls :=
    (forall₂_comp instances bodies).imp fun _ _ both => by
      obtain ⟨i, ⟨_, reads⟩, evaluates, facts⟩ := both
      exact ⟨i, reads, evaluates, facts⟩
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_K works Ls unifiers related stack emitted
  exact ⟨R, eraseR, .head (.internal (.callEquations (HERuns.value_not_error head.head erased)
    (HERuns.value_nonGrounded head.notHost (head.instruction args) erased) frontier'
    worksNonempty)) pathR⟩

end HEQueries

/-! ## HE's source semantics on marked values -/

/-- **HE's source semantics determines the atoms the value `v` publishes**: every derivation of
HE's completed relation for `v` under `%Undefined%` (historical lookup), at any live list, scope and
activation, returns a batch whose atoms are `L`. -/
def RunsDetermined (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom)
    (v : Entry.Value) (L : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (frame : Frame) (results : List Result),
    Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup live scope v
      Atom.undefinedType frame results (policy := policy) →
    results.map (fun r => r.1.erase) = L

/-- **Every marked presentation of `t` is determined to `L`.** -/
def DeterminedM (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (t : Atom)
    (L : List Atom) : Prop :=
  ∀ v : Entry.Value, v.erase = t → Marked dispatch atoms v → RunsDetermined dispatch policy atoms v L

section HESource

variable {policy : Policy}

/-- On the plain presentation, `DeterminedM` is `EveryRun.Determined`. -/
theorem DeterminedM.plain {atoms : List Atom} {t : Atom} {L : List Atom}
    (determined : DeterminedM dispatch policy atoms t L) : Determined dispatch policy atoms t L :=
  determined (Entry.Value.ofAtom t) (Entry.Value.erase_ofAtom t) (marked_ofAtom t)

theorem data_determined_M {atoms : List Atom} {d : Atom} (data : DataAtom d) :
    DeterminedM dispatch policy atoms d [d] := by
  intro v erased _ live scope frame results derived
  rw [value_of_data data erased] at derived
  obtain ⟨after, rfl⟩ := data_source raw_contract data derived
  simp

/-- **HE's tuple of marked arguments returns one row per combination of their answers**, in
lexicographic order, whatever frames its casts and queries reach. -/
theorem tuple_rows_M {atoms : List Atom} {scope : List String} :
    ∀ (vs : List Entry.Value) (Ls : List (List Atom)),
      List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧ RunsDetermined dispatch policy atoms v L)
        vs Ls →
      vs ≠ [] → ∀ (live : List Atom) (frame : Frame) (results : List Result),
        Completed.TupleRel (Space.ofList atoms) dispatch Completed.rawLookup live scope vs frame
          results (policy := policy) →
        List.Forall₂ CleanRow results (combos Ls)
  | [], _, _, nonempty, _, _, _, _ => absurd rfl nonempty
  | [v], _, related, _, live, frame, results, derived => by
      obtain ⟨L, Ls', ⟨clean, determined⟩, rest, rfl⟩ := List.forall₂_cons_left_iff.mp related
      obtain rfl := List.forall₂_nil_left_iff.mp rest
      cases derived with
      | singleton headDerived =>
          have erased := determined _ _ _ _ headDerived
          have rows := singleton_rows (HENested.clean_of_erase erased clean)
          subst erased
          rw [combos_singleton, List.map_map]
          exact rows
  | v :: v2 :: rest, _, related, _, live, frame, results, derived => by
      obtain ⟨L, Ls', ⟨clean, determined⟩, restRel, rfl⟩ := List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons headDerived branches =>
          have erased := determined _ _ _ _ headDerived
          have rows := branches_rows
            (fun live' frame' results' tupled =>
              tuple_rows_M (v2 :: rest) Ls' restRel (List.cons_ne_nil _ _) live' frame' results'
                tupled)
            _ _ (HENested.clean_of_erase erased clean) branches
          rwa [flatMap_heads erased] at rows

/-- **Marked nested calls are determined, compositionally.** For a marked call value of
`(f t₁ … tₙ)`: if each marked argument is determined with answerable answers `Lᵢ`, and the query of
`f` on every combination is determined with answers `Q vals`, then every derivation returns the
concatenation of `Q` over the combinations; when the call is held and reused, it is delivered, and
its answers are itself. -/
theorem nested_determined_M {atoms : List Atom} {f : String} {ts : List Atom}
    {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (.symbol f :: ts)) name)
    {readiness : Entry.Status} {vs : List Entry.Value} (erased : vs.map Entry.Value.erase = ts)
    (args : List.Forall₂ (fun v L => (∀ a ∈ L, Answerable a) ∧
      RunsDetermined dispatch policy atoms v L) vs Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      QueryDetermined dispatch policy atoms f vals (Q vals))
    (held : readiness = .held → policy.reentry = .reuse →
      (combos Ls).flatMap Q = [.expression (.symbol f :: ts)]) :
    RunsDetermined dispatch policy atoms (.expression readiness (.symbol f :: vs))
      ((combos Ls).flatMap Q) := by
  have answerableAll : ∀ a ∈ (combos Ls).flatMap Q, Answerable a := by
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).1 a inner
  intro live scope frame results derived
  have eraseV : (Entry.Value.expression readiness (.symbol f :: vs)).erase =
      .expression (.symbol f :: ts) := by
    simp only [Entry.Value.erase, List.map_cons, erased]
  have readV : frame.read policy (.expression readiness (.symbol f :: vs)) =
      .expression readiness (.symbol f :: vs) :=
    read_closed_value policy frame (by rw [eraseV]; exact closed)
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList atoms)
      (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences untyped)
  have operatorErase : (Entry.Value.symbol f).erase = Atom.symbol f := by
    simp only [Entry.Value.erase]
  have batch : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.symbol f = operator → vs = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch Completed.rawLookup
        (Atom.undefinedType :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
        Atom.undefinedType rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro operator arguments rows raw sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    have headDetermined : RunsDetermined dispatch policy atoms (.symbol f) [.symbol f] :=
      fun live' scope' frame' results' derived' =>
        data_determined_M (policy := policy) head (.symbol f) (by simp only [Entry.Value.erase])
          (.symbol f) live' scope' frame' results' derived'
    have rowsShape := tuple_rows_M (Entry.Value.symbol f :: vs) ([Atom.symbol f] :: Ls)
      (.cons ⟨fun a member => by
          rw [List.mem_singleton] at member
          subst member
          exact answerable_of_data head, headDetermined⟩ args)
      (List.cons_ne_nil _ _) _ _ _ tuples
    rw [combos_head, List.forall₂_map_right_iff] at rowsShape
    exact calls_rows _ _ _ (rowsShape.imp fun _ _ row => row.2.1)
      (fun vals member => (apps vals member).2) calls
  have publish : ∀ {raw selected : List Result},
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q →
      Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
        (fun result : Result => isErrorAtom result.1.erase)
        (raw.map (Completed.readResult policy)) selected →
      selected.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro raw selected erasedRaw chosen
    have cleanRaw := HENested.clean_of_erase erasedRaw answerableAll
    have unchanged : raw.map (Completed.readResult policy) = raw :=
      map_fixed fun r member => HERuns.readResult_closed policy r (cleanRaw r member).closed
    rw [unchanged] at chosen
    have same := Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel.functional
      chosen (HERuns.success_all raw fun r member => (cleanRaw r member).notError)
    rw [same, erasedRaw]
  by_cases reusedHeld : policy.reentry = .reuse ∧ readiness = .held
  · -- a held call under reuse is delivered
    have entry : Entry.Rel policy.reentry
        (frame.read policy (.expression readiness (.symbol f :: vs))).status
        (frame.read policy (.expression readiness (.symbol f :: vs))).erase
        Atom.undefinedType .deliver := by
      rw [readV, eraseV]
      exact .held (call_not_stopped head) undefined_not_raw reusedHeld.1 reusedHeld.2
    cases derived with
    | delivered _ =>
        rw [held reusedHeld.2 reusedHeld.1, readV]
        simp only [List.map_cons, List.map_nil, eraseV]
    | cast entered => cases Entry.functional entered entry
    | tuple entered => cases Entry.functional entered entry
    | function entered => cases Entry.functional entered entry
    | fallback entered => cases Entry.functional entered entry
    | selectionFailed entered => cases Entry.functional entered entry
  · have interpreted : policy.reentry = .reinterpret ∨ readiness = .active := by
      cases reentry : policy.reentry <;> cases readiness <;> simp_all
    have entry : Entry.Rel policy.reentry
        (frame.read policy (.expression readiness (.symbol f :: vs))).status
        (frame.read policy (.expression readiness (.symbol f :: vs))).erase
        Atom.undefinedType .interpret := by
      rw [readV, eraseV]
      exact .expression (call_not_stopped head) undefined_not_raw interpreted
    cases derived with
    | delivered entered => cases Entry.functional entered entry
    | cast entered => cases Entry.functional entered entry
    | tuple _ shaped _ tuples calls chosen =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, sameOperator, sameArguments⟩ := shaped
        rw [publish_erase]
        exact publish (batch sameOperator sameArguments tuples calls) chosen
    | function _ shaped chosen =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, rfl, _⟩ := shaped
        rw [operatorErase] at chosen
        cases chosen.undefined_exact storage
    | fallback _ shaped chosen tuples calls selected =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, sameOperator, sameArguments⟩ := shaped
        rw [← sameOperator, operatorErase] at chosen
        have exhausted := chosen.undefined_exact storage
        simp only [Completed.InvocationSelection.exhausted.injEq, and_true] at exhausted
        subst exhausted
        have chosenRaw := selected
        simp only [Completed.diagnosticResults, List.map_nil, List.append_nil] at chosenRaw
        rw [publish_erase]
        exact publish (batch sameOperator sameArguments tuples calls) chosenRaw
    | selectionFailed _ shaped chosen =>
        rw [readV] at shaped
        simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
        obtain ⟨_, rfl, _⟩ := shaped
        rw [operatorErase] at chosen
        have exhausted := chosen.undefined_exact storage
        simp at exhausted

/-- **The equation bodies, read as marked values**: each body's results are the atoms its instance
determines. -/
theorem bodies_source_M {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {frame : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
          (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
        DeterminedM dispatch policy atoms i L ∧ BodyFacts i) works Ls →
      ∀ {results : List Result},
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
          original Atom.undefinedType frame works results (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, derived => by
      obtain ⟨L, Ls', ⟨i, readsAs, determined, facts⟩, rest, rfl⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons sameBindings _ boundary batch later =>
          obtain ⟨readErase, readMarked⟩ := readsAs _ sameBindings
          cases boundary with
          | producerFunction pending _ => exact absurd pending (not_pending facts readErase)
          | producerRaw _ =>
              cases batch with
              | cons returned tail =>
                  cases tail
                  cases returned with
                  | returned answered =>
                      cases answered with
                      | notReducible same =>
                          rw [readErase] at same
                          exact absurd same facts.notRefused
                      | stopped stopped =>
                          rw [readErase] at stopped
                          exact absurd stopped facts.notStopped
                      | evaluate _ _ evaluated =>
                          rw [List.append_nil, List.map_append,
                            determined _ readErase readMarked _ _ _ _ evaluated,
                            bodies_source_M ws Ls' rest later, List.flatten_cons]

/-- **HE's query of a call of values with open bodies is determined**: every derivation of the call
relation, on every call value of `(f vals)`, returns the instances' answers in row order. -/
theorem query_determined_K {atoms : List Atom} (program : ScopedProgram atoms) {f : String}
    {vals : List Atom} (head : NodeHead dispatch atoms f)
    (valsValues : ∀ v ∈ vals, NestedValues.Value dispatch atoms v)
    (nonempty : regionInstances atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => DeterminedM dispatch policy atoms b L ∧ BodyFacts b)
      (regionInstances atoms f vals) Ls) :
    QueryDetermined dispatch policy atoms f vals Ls.flatten := by
  have ground : ∀ v ∈ vals, TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (value_answerable (valsValues v member))
  intro live scope value frame children erased called
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head.head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, head.instruction vals] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      have sidesEq := frontier_sides ground frame.certified.satisfiable (scoped_consFree program)
        frontier
      apply absurd _ nonempty
      rw [regionInstances_sides, ← sidesEq]
      rfl
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      have instances := works_instances_K policy valsValues program frame.certified.satisfiable
        frontier
      have onWorks : List.Forall₂ (fun (w : EquationWork) (L : List Atom) => ∃ i, (∀ output : Frame,
            output.bindings = w.bindings →
              (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
              Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
          DeterminedM dispatch policy atoms i L ∧ BodyFacts i) _ Ls :=
        (forall₂_comp instances bodies).imp fun _ _ both => by
          obtain ⟨i, ⟨_, reads⟩, determined, facts⟩ := both
          exact ⟨i, reads, determined, facts⟩
      exact bodies_source_M _ Ls onWorks equations

end HESource

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)

/-- The value `(S Z)` as HE's tuple returns it, before publication. -/
def sz : Entry.Value := .expression .active [.symbol "S", .symbol "Z"]

/-- **Negative control (the plain read fails on compound values).** Under `Policy.ready` (reuse,
every successful expression result held), the publication of `(S Z)` is held, so it is not the
plain value of its atom, although its atom is `(S Z)`. -/
theorem ready_marks_held (frame : Frame) :
    (Completed.publishResult Policy.ready (app "S" [sym "Z"]) (sz, frame)).1 =
        .expression .held [.symbol "S", .symbol "Z"] ∧
      (Completed.publishResult Policy.ready (app "S" [sym "Z"]) (sz, frame)).1 ≠
        Entry.Value.ofAtom (app "S" [sym "Z"]) ∧
      (Completed.publishResult Policy.ready (app "S" [sym "Z"]) (sz, frame)).1.erase =
        app "S" [sym "Z"] := by
  refine ⟨?_, ?_, ?_⟩
  · simp [Completed.publishResult, Entry.Value.publish, sz, Entry.publish, Policy.ready,
      Entry.Value.withStatus, Entry.Value.erase, isErrorAtom]
  · simp [Completed.publishResult, Entry.Value.publish, sz, Entry.publish, Policy.ready,
      Entry.Value.withStatus, Entry.Value.erase, isErrorAtom, Entry.Value.ofAtom]
  · simp [Completed.publishResult, sz, Entry.Value.erase]

/-- **A variable bound to the held value reads as the held value**, not as the plain value of its
atom: substitution keeps the marks it inserts. -/
theorem held_read_not_plain (rebuilding : Entry.RebuildPolicy) :
    Entry.Value.substitute rebuilding
        (Entry.Value.resolve [("y", .expression .held [.symbol "S", .symbol "Z"])])
        (Entry.Value.ofAtom (.var "y")) =
      .expression .held [.symbol "S", .symbol "Z"] ∧
    Entry.Value.substitute rebuilding
        (Entry.Value.resolve [("y", .expression .held [.symbol "S", .symbol "Z"])])
        (Entry.Value.ofAtom (.var "y")) ≠ Entry.Value.ofAtom (app "S" [sym "Z"]) := by
  constructor
  · simp [Entry.Value.substitute, Entry.Value.ofAtom, Entry.Value.resolve]
  · simp [Entry.Value.substitute, Entry.Value.ofAtom, Entry.Value.resolve]

/-- The one-row Peano fragment used by the controls. -/
def addRows : List Atom :=
  [AnswerBags.Controls.rule (app "add" [sym "Z", .var "y"]) (.var "y")]

/-- **Negative control (the invariant has content).** A held call of a defined head is not a marked
value: `add` has an equation, so `(add Z Z)` is no value. -/
theorem held_call_not_marked :
    ¬ Marked noHost addRows (.expression .held [.symbol "add", .symbol "Z", .symbol "Z"]) := by
  intro marked
  have value := marked.held_value
  simp only [Entry.Value.erase, List.map_cons, List.map_nil] at value
  cases value with
  | data data => cases data
  | node head _ =>
      have noEquation := head.noEquation
      simp [addRows, AnswerBags.Controls.rule, LiveEquations.equationOfRow] at noEquation

/-- **Positive control.** The held `(S Z)` is a marked value of a program in which `S` has no
equation. -/
theorem held_value_marked :
    Marked noHost addRows (.expression .held [.symbol "S", .symbol "Z"]) := by
  have sHead : ConstructorHead noHost addRows "S" :=
    ⟨.symbol (by decide) (by decide), by decide +kernel, fun impossible => impossible, by decide,
      by decide, by decide, by decide, by decide +kernel⟩
  apply marked_of_value
  simp only [Entry.Value.erase, List.map_cons, List.map_nil]
  refine .node sHead fun v member => ?_
  simp only [List.mem_singleton] at member
  subst member
  exact .data (BoundVariables.Controls.sym_data "Z" (by decide) (by decide))

end Controls

#print axioms marked_of_value
#print axioms substitute_marked
#print axioms tuple_product_M
#print axioms he_nested_M
#print axioms he_held
#print axioms equations_steps_K
#print axioms work_read_K
#print axioms he_query_K
#print axioms tuple_rows_M
#print axioms nested_determined_M
#print axioms bodies_source_M
#print axioms query_determined_K
#print axioms Controls.ready_marks_held
#print axioms Controls.held_read_not_plain
#print axioms Controls.held_call_not_marked
#print axioms Controls.held_value_marked

end MarkedValues

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
