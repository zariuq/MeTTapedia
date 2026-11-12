import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.IfComputed

/-!
# HE's `if` taking a branch that is a call, on every run

`IfComputed` asks the taken branch to be a value: the query of `if` reads it through its unifier's
environment, and only for a value is every marking of the read harmless. A call read as held would
be delivered unevaluated under the reuse policy. Here the read is computed exactly: HE's unifier binds
the fresh pattern variable `$then` (or `$else`) of `if`'s row to the delivered branch itself, so the
read is the plain branch, and the taken branch may be any term that settles, calls and recursion
included.

* `env_unbound`: a name outside the complete support of a frame's bindings has no row in its
  environment (the frame's readout certificate).
* `unify_symbol`, `unify_grounded`, `unify_closed_var`, `if_unify`: HE's contextual unifier on the
  call value of `if` against the fresh pattern `(if b $p $q)` with `$p`, `$q` unbound: the literals
  match identically, and `$p`, `$q` are bound to the delivered branches, unchanged.
* `call_read`: on every frontier of `(if b y n)` over a program whose region of `if` is the row of
  `b`, the one work's body read under any unifier output is the plain taken branch.
* `call_every_run`: a complete HE run of `(if c y n)` exists, every complete run publishes the
  answers of the taken branch, and PeTTa yields the same; the condition settles with one Boolean
  answer, the taken branch is any settling term whose data answers `$t` casts as they are.

## Controls

* `Controls.zero_call` (`(if (isZero 0) (half 4) (loop))` with `(= (half 4) two)`): every complete
  HE run publishes `two`, as PeTTa does; the taken branch is a call of a defined function.
* `Controls.unbound_needed` (negative): an environment whose row binds `$p` makes the read of `$p`
  that row's value, not the delivered branch; the freshness of `$p` is what the proof uses.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace IfCallBranches

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork EquationFrontierRel
  QueryVisibleName)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.Spec.Type (TypeMatchRel StorageTypesRel rawTypeLookupRel
  FunctionTypeRel)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation (TypeSubst)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement (TypeBindingSatisfied
  renameTypeVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation (specBindingVars)
open Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge (AtomOccurs)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun BoundVariables NestedArguments
  NestedEveryRun NestedValues NestedCalls MarkedValues CompoundBindings DeclaredHeads
  DeclaredEveryRun TypedEveryRun AtomDemands IfEveryRun IfBranches DemandSpine IfComputed
open AnswerBags.Controls (sym app rule rule_consFree)

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Environments and fresh names -/

theorem lookup_erase (env : Entry.Value.Environment) (name : String) :
    (Entry.Value.eraseEnvironment env).lookup name = (env.lookup name).map Entry.Value.erase := by
  induction env with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      by_cases same : name = key
      · subst same
        simp [Entry.Value.eraseEnvironment, TypeSubst.lookup, List.lookup]
      · have different : (name == key) = false := by simp [same]
        simpa [Entry.Value.eraseEnvironment, TypeSubst.lookup, List.lookup, same, different] using ih

/-- A name invisible to a query is outside the support of its incoming bindings. -/
theorem outside_of_invisible {live : List Atom} {query : Atom} {incoming : Bindings}
    {name : String} (invisible : ¬ QueryVisibleName live query incoming name) :
    name ∉ specBindingVars incoming := by
  intro member
  apply invisible
  simp only [specBindingVars, List.mem_append, List.mem_flatMap, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with ⟨entry, inAssignments, same | inValue⟩ | ⟨entry, inEqualities, same | same⟩
  · subst same
    exact Or.inr (Or.inr (Or.inl ⟨entry.2, inAssignments⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨entry.1, entry.2, inAssignments,
      (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr
        inValue⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨entry.1, entry.2, inEqualities, Or.inl same⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨entry.1, entry.2, inEqualities, Or.inr same⟩)))

/-- **A name outside the support of a frame's bindings has no row in its environment.** -/
theorem env_unbound (frame : Frame) {name : String}
    (outside : name ∉ specBindingVars frame.bindings) : frame.environment.lookup name = none := by
  have erased := frame.certified.lookup_none_of_outside outside
  rw [lookup_erase] at erased
  cases found : frame.environment.lookup name with
  | none => rfl
  | some _ => simp [found] at erased

theorem lookup_bind_self (rebuilding : Entry.RebuildPolicy) (env : Entry.Value.Environment)
    (name : String) (value : Entry.Value) :
    (Entry.Value.bind rebuilding env name value).lookup name =
      some (Entry.Value.substitute rebuilding (Entry.Value.resolve env) value) := by
  simp [Entry.Value.bind]

theorem lookup_filter_map_none {env : Entry.Value.Environment} {name other : String}
    {transform : Entry.Value → Entry.Value} (absent : env.lookup name = none) :
    ((env.filter fun row => row.1 != other).map fun row => (row.1, transform row.2)).lookup name =
      none := by
  induction env with
  | nil => rfl
  | cons row rest ih =>
      rcases row with ⟨key, value⟩
      by_cases same : name = key
      · subst same
        simp [List.lookup] at absent
      · have different : (name == key) = false := by simp [same]
        have restAbsent : rest.lookup name = none := by
          simpa [List.lookup, different] using absent
        by_cases kept : (key != other) = true
        · simp [List.filter, kept, List.lookup, different, ih restAbsent]
        · simp only [Bool.not_eq_true] at kept
          simp [List.filter, kept, ih restAbsent]

theorem lookup_bind_unbound {rebuilding : Entry.RebuildPolicy} {env : Entry.Value.Environment}
    {name other : String} {value : Entry.Value} (different : name ≠ other)
    (absent : env.lookup name = none) :
    (Entry.Value.bind rebuilding env other value).lookup name = none := by
  have notEq : (name == other) = false := by simp [different]
  simp only [Entry.Value.bind, List.lookup, notEq]
  exact lookup_filter_map_none absent

/-- After binding `p` to a closed value and then another name `q`, `p` still reads that value. -/
theorem lookup_bind_bind {rebuilding : Entry.RebuildPolicy} {env : Entry.Value.Environment}
    {p q : String} {vy vq : Entry.Value} (different : p ≠ q)
    (closedY : ∀ name, ¬ AtomOccurs vy.erase name) :
    (Entry.Value.bind rebuilding (Entry.Value.bind rebuilding env p vy) q vq).lookup p = some vy := by
  have notEq : (p == q) = false := by simp [different]
  have keep : (p != q) = true := by simp [different]
  have resolved : Entry.Value.substitute rebuilding (Entry.Value.resolve env) vy = vy :=
    Entry.Value.substitute_variable_free rebuilding _ vy closedY
  have resolvedAgain : ∀ σ : String → Entry.Value, Entry.Value.substitute rebuilding σ vy = vy :=
    fun σ => Entry.Value.substitute_variable_free rebuilding σ vy closedY
  simp [Entry.Value.bind, List.lookup, notEq, keep, resolved, resolvedAgain]

/-! ## HE's unifier on the call of `if` -/

theorem var_occurs (x : String) : AtomOccurs (Entry.Value.var x).erase x :=
  (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr
    (by simp [Entry.Value.erase, TypeSubst.typeVars])

theorem unify_symbol {rebuilding : Entry.RebuildPolicy} {env out : Entry.Value.Environment}
    {name : String}
    (unified : Entry.Value.UnifyRel rebuilding env (.symbol name) (.symbol name) out) : out = env := by
  cases unified with
  | ordinary applied =>
      simp only [Entry.Value.substitute] at applied
      cases applied with
      | identical _ => rfl

theorem unify_grounded {rebuilding : Entry.RebuildPolicy} {env out : Entry.Value.Environment}
    {value : Mettapedia.Languages.MeTTa.OSLFCore.GroundedValue}
    (unified : Entry.Value.UnifyRel rebuilding env (.grounded value) (.grounded value) out) :
    out = env := by
  cases unified with
  | ordinary applied =>
      simp only [Entry.Value.substitute] at applied
      cases applied with
      | identical _ => rfl

/-- **A closed value against an unbound variable binds it to that value.** -/
theorem unify_closed_var {rebuilding : Entry.RebuildPolicy} {env out : Entry.Value.Environment}
    {v : Entry.Value} {x : String} (closed : ∀ name, ¬ AtomOccurs v.erase name)
    (unbound : env.lookup x = none)
    (unified : Entry.Value.UnifyRel rebuilding env v (.var x) out) :
    out = Entry.Value.bind rebuilding env x v := by
  cases unified with
  | ordinary applied =>
      rw [Entry.Value.substitute_variable_free rebuilding _ v closed] at applied
      have right : Entry.Value.substitute rebuilding (Entry.Value.resolve env) (.var x) = .var x := by
        simp [Entry.Value.substitute, Entry.Value.resolve, unbound]
      rw [right] at applied
      cases applied with
      | identical same =>
          apply absurd _ (closed x)
          rw [same]
          exact (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr
            (by simp [Entry.Value.erase, TypeSubst.typeVars])
      | bindLeft _ => exact absurd (var_occurs _) (closed _)
      | bindRight _ _ => rfl

/-- **The unifier of `if`'s row on its call binds `$p` and `$q` to the delivered branches.** -/
theorem if_unify {rebuilding : Entry.RebuildPolicy} {env out : Entry.Value.Environment}
    {r : Entry.Status} {b : Bool} {y n : Atom} {p q : String}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    (different : p ≠ q) (unboundP : env.lookup p = none) (unboundQ : env.lookup q = none)
    (unified : Entry.Value.UnifyRel rebuilding env
      (.expression r [.symbol "if", .grounded (.bool b), Entry.Value.ofAtom y, Entry.Value.ofAtom n])
      (Entry.Value.ofAtom (app "if" [.grounded (.bool b), .var p, .var q])) out) :
    out.lookup p = some (Entry.Value.ofAtom y) ∧ out.lookup q = some (Entry.Value.ofAtom n) := by
  have closedYv : ∀ name, ¬ AtomOccurs (Entry.Value.ofAtom y).erase name := by
    rw [Entry.Value.erase_ofAtom]
    exact closedY
  have closedNv : ∀ name, ¬ AtomOccurs (Entry.Value.ofAtom n).erase name := by
    rw [Entry.Value.erase_ofAtom]
    exact closedN
  have closedCall : ∀ name, ¬ AtomOccurs (Entry.Value.expression r [.symbol "if",
      .grounded (.bool b), Entry.Value.ofAtom y, Entry.Value.ofAtom n]).erase name := by
    have erased : (Entry.Value.expression r [.symbol "if", .grounded (.bool b),
        Entry.Value.ofAtom y, Entry.Value.ofAtom n]).erase = callOf b y n := by
      simp [Entry.Value.erase, Entry.Value.erase_ofAtom, callOf, app]
    rw [erased]
    intro name occurs
    have inVars := (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mp
      occurs
    simp only [TypeSubst.typeVars, TypeSubst.typeVarsList, List.nil_append,
      List.mem_append, List.not_mem_nil, or_false] at inVars
    rcases inVars with inY | inN
    · exact closedY name
        ((Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr inY)
    · exact closedN name
        ((Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr inN)
  cases unified with
  | ordinary applied =>
      rw [Entry.Value.substitute_variable_free rebuilding _ _ closedCall] at applied
      obtain ⟨s, patternSide⟩ : ∃ s, Entry.Value.substitute rebuilding (Entry.Value.resolve env)
          (Entry.Value.ofAtom (app "if" [.grounded (.bool b), .var p, .var q])) =
          .expression s [.symbol "if", .grounded (.bool b), .var p, .var q] := by
        apply Exists.intro
        simp [app, Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.resolve, unboundP,
          unboundQ]
        rfl
      rw [patternSide] at applied
      cases applied with
      | identical same =>
          simp only [Entry.Value.erase, Entry.Value.erase_ofAtom, List.map_cons, List.map_nil,
            Atom.expression.injEq, List.cons.injEq] at same
          exact absurd (show AtomOccurs y p by
            rw [same.2.2.1]
            exact (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr
              (by simp [TypeSubst.typeVars])) (closedY p)
      | expression lists =>
          cases lists with
          | cons first rest1 =>
              obtain rfl := unify_symbol first
              cases rest1 with
              | cons second rest2 =>
                  obtain rfl := unify_grounded second
                  cases rest2 with
                  | cons third rest3 =>
                      obtain rfl := unify_closed_var closedYv unboundP third
                      cases rest3 with
                      | cons fourth rest4 =>
                          obtain rfl := unify_closed_var closedNv
                            (lookup_bind_unbound (Ne.symm different) unboundQ) fourth
                          cases rest4
                          refine ⟨lookup_bind_bind different closedYv, ?_⟩
                          rw [lookup_bind_self]
                          rw [Entry.Value.substitute_variable_free rebuilding _ _ closedNv]

/-! ## The read of the taken branch -/

/-- The variable of `if`'s row that names the branch `b` takes. -/
def branchName : Bool → String
  | true => "then"
  | false => "else"

/-- **The region of `if` on `(if b y n)` is HE's standard-library row of `b`**, a condition on the
program and the call. -/
def IfRegion (atoms : List Atom) (b : Bool) (y n : Atom) : Prop :=
  regionSides atoms "if" [.grounded (.bool b), y, n] =
    [(app "if" [.grounded (.bool b), .var "then", .var "else"], .var (branchName b))]

/-- **The read of the taken branch is the plain branch.** On every frontier of `(if b y n)` over a
program whose region of `if` is the row of `b`, there is one work, and under every output of HE's
unifier on the call value whose branches were delivered as they are, the work's body reads as the
plain taken branch: the row's fresh variables are unbound in the frame (they avoid its support), so
the unifier binds them to the delivered branches. -/
theorem call_read (policy : Policy) {atoms : List Atom}
    (consFree : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {b : Bool} {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    (region : IfRegion atoms b y n) {live : List Atom} {frame : Frame} {works : List EquationWork}
    (frontier : EquationFrontierRel (Space.ofList atoms) live (callOf b y n) frame.bindings works) :
    ∃ w, works = [w] ∧ ∀ (r : Entry.Status) (output : Frame),
      Entry.Value.UnifyRel policy.rebuilding frame.environment
        (.expression r [.symbol "if", .grounded (.bool b), Entry.Value.ofAtom y,
          Entry.Value.ofAtom n])
        (Entry.Value.ofAtom w.pattern) output.environment →
      output.read policy (Entry.Value.ofAtom w.body) = Entry.Value.ofAtom (pick b y n) := by
  have ground := call_ground (b := b) closedY closedN
  have sidesEq := frontier_sides ground frame.certified.satisfiable consFree frontier
  rw [region] at sidesEq
  obtain ⟨w, rfl⟩ : ∃ w, works = [w] := by
    cases works with
    | nil => simp at sidesEq
    | cons w rest =>
        cases rest with
        | nil => exact ⟨w, rfl⟩
        | cons _ _ => simp at sidesEq
  simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at sidesEq
  obtain ⟨leftEq, rightEq⟩ := sidesEq
  obtain ⟨matched, occurrence⟩ := frontier.occurrence (List.mem_singleton_self w)
  obtain ⟨rename, injective, renamedLeft, renamedRight, fresh⟩ := occurrence.selected.1
  have patternEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedLeft
  have bodyEq := Mettapedia.Languages.MeTTa.HE.EquationFreshening.alphaRename_eq renamedRight
  have occurs : ∀ x ∈ ["then", "else"], AtomOccurs w.left x := by
    intro x member
    rw [leftEq]
    apply (Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps.atomOccurs_iff_mem_typeVars _ _).mpr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;>
      simp [TypeSubst.typeVars, TypeSubst.typeVarsList]
  have unboundThen := env_unbound frame
    (outside_of_invisible (fresh "then" (Or.inl (occurs "then" (by simp)))))
  have unboundElse := env_unbound frame
    (outside_of_invisible (fresh "else" (Or.inl (occurs "else" (by simp)))))
  have different : rename "then" ≠ rename "else" := fun same => by
    have := injective same
    simp at this
  refine ⟨w, rfl, fun r output unified => ?_⟩
  rw [patternEq, leftEq] at unified
  simp only [app, renameTypeVars, List.map_cons, List.map_nil] at unified
  obtain ⟨atThen, atElse⟩ := if_unify closedY closedN different unboundThen unboundElse unified
  rw [bodyEq, rightEq]
  cases b with
  | true =>
      simp [renameTypeVars, branchName, pick, Completed.Frame.read, Entry.Value.ofAtom,
        Entry.Value.substitute, Entry.Value.resolve, atThen]
  | false =>
      simp [renameTypeVars, branchName, pick, Completed.Frame.read, Entry.Value.ofAtom,
        Entry.Value.substitute, Entry.Value.resolve, atElse]

/-! ## Equation loops whose reads use the unifier -/

/-- `DemandSpine.equations_steps_at`, with reads that hold under the unifier's outputs only. -/
theorem equations_steps_unified {atoms : List Atom} {E : Atom} {live : List Atom}
    {scope : List String} {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work L => ∃ i, (∀ output : Frame, output.bindings = work.bindings →
          Entry.Value.UnifyRel policy.rebuilding activation.environment original
            (Entry.Value.ofAtom work.pattern) output.environment →
          (output.read policy (Entry.Value.ofAtom work.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom work.body))) ∧
        HEEvaluatesAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ results : List Result, results.map (fun result => result.1.erase) = Ls.flatten ∧
          HERuns.HESteps dispatch Completed.rawLookup policy
            ⟨Space.ofList atoms, .work (.equations live scope original E activation works), stack,
              emitted⟩
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
          obtain ⟨readErase, readMarked⟩ := readsAs output sameBindings unified
          obtain ⟨R, eraseR, pathR⟩ := evaluates _ readErase readMarked live scope output
            (.append (.boundaryBatch live scope none (.returned original E) []) ::
              .append (.equations live scope original E activation works) :: stack)
            emitted
          obtain ⟨R', eraseR', pathR'⟩ := equations_steps_unified works Ls'
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

/-- `DemandSpine.bodies_source_at`, with reads that hold under the unifier's outputs only. -/
theorem bodies_source_unified {atoms : List Atom} {E : Atom} {live : List Atom}
    {scope : List String} {original : Entry.Value} {frame : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)),
      List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
          Entry.Value.UnifyRel policy.rebuilding frame.environment original
            (Entry.Value.ofAtom w.pattern) output.environment →
          (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
          Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
        DeterminedAt dispatch policy atoms E i L ∧ BodyFacts i) works Ls →
      ∀ {results : List Result},
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
          original E frame works results (policy := policy) →
        results.map (fun r => r.1.erase) = Ls.flatten
  | [], _, related, _, derived => by
      cases related
      cases derived
      rfl
  | w :: ws, _, related, _, derived => by
      obtain ⟨L, Ls', ⟨i, readsAs, determined, facts⟩, rest, rfl⟩ :=
        List.forall₂_cons_left_iff.mp related
      cases derived with
      | cons sameBindings unified boundary batch later =>
          obtain ⟨readErase, readMarked⟩ := readsAs _ sameBindings unified
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
                            bodies_source_unified ws Ls' rest later, List.flatten_cons]

/-! ## The program and the branches -/

/-- **The branches, the taken one any settling term**: it settles with the answers `L` whose data
form `$t` casts as they are; both branches are closed with one stored type each; and the region of
`if` on the call is HE's row of `b`. -/
structure CallBranches (dispatch : GroundedDispatch) (atoms : List Atom) (b : Bool) (y n : Atom)
    (L : List Atom) : Prop where
  takenSettles : SettlesK dispatch atoms (pick b y n) L
  takenCasts : ∀ a ∈ L, DataAtom a → CastsAt atoms (.var "t") a
  closedYes : ∀ name, ¬ AtomOccurs y name
  closedNo : ∀ name, ¬ AtomOccurs n name
  groundYes : isGroundAtom y = true
  groundNo : isGroundAtom n = true
  typedYes : ∃ T, StorageTypesRel (Space.ofList atoms) y [T]
  typedNo : ∃ T, StorageTypesRel (Space.ofList atoms) n [T]
  region : IfRegion atoms b y n

/-- The call value `if`'s application assembles. -/
abbrev callValueOf (b : Bool) (y n : Atom) : Entry.Value :=
  .expression .active [.symbol "if", .grounded (.bool b), Entry.Value.ofAtom y, Entry.Value.ofAtom n]

theorem assembled_eq (b : Bool) (y n : Atom) (frame : Frame) :
    (Completed.functionAssemble (Entry.Value.ofAtom (.symbol "if"))
      (Entry.Value.argumentPacket [Entry.Value.ofAtom (.grounded (.bool b)), Entry.Value.ofAtom y,
        Entry.Value.ofAtom n], frame)).1 = callValueOf b y n := by
  simp [Completed.functionAssemble, Entry.Value.argumentPacket, Entry.Value.unpackArguments,
    Entry.Value.ofAtom]

theorem callValue_erase (b : Bool) (y n : Atom) : (callValueOf b y n).erase = callOf b y n := by
  simp [Entry.Value.erase, Entry.Value.erase_ofAtom, callOf, app]

/-- **Every derivation of the typed query of `(if b y n)` under `$t` returns the taken branch's
answers.** -/
theorem call_query_source {atoms : List Atom} (program : IfCallProgram atoms) {b : Bool}
    {y n : Atom} {L : List Atom} (branches : CallBranches dispatch atoms b y n L) {live : List Atom}
    {scope : List String} {frame : Frame} {children : List Result}
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
      (callValueOf b y n) (.var "t") frame children (policy := policy)) :
    children.map (fun r => r.1.erase) = L := by
  have ground := call_ground (b := b) branches.closedYes branches.closedNo
  have erased := callValue_erase b y n
  have both := settlesK_at (policy := policy) program.rows (var_transparent "t")
    branches.takenSettles branches.takenCasts
  cases called with
  | error failed =>
      rw [erased] at failed
      obtain ⟨tail, same⟩ := failed
      simp at same
  | embedded _ _ instruction _ _ =>
      rw [erased] at instruction
      simp [Minimal.embeddedInstruction] at instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      have sidesEq := frontier_sides ground frame.certified.satisfiable
        (scoped_consFree program.rows.scoped) frontier
      rw [branches.region] at sidesEq
      simp at sidesEq
  | equations _ _ frontier _ equations =>
      rw [erased] at frontier
      obtain ⟨w, rfl, reads⟩ := call_read policy (scoped_consFree program.rows.scoped)
        branches.closedYes branches.closedNo branches.region frontier
      have related : List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
            Entry.Value.UnifyRel policy.rebuilding frame.environment (callValueOf b y n)
              (Entry.Value.ofAtom w.pattern) output.environment →
            (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
            Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
          DeterminedAt dispatch policy atoms (.var "t") i L ∧ BodyFacts i) [w] [L] :=
        .cons ⟨pick b y n, fun output _ unified => by
            rw [reads .active output unified]
            exact ⟨Entry.Value.erase_ofAtom _, marked_ofAtom _⟩,
          both.2, settlesK_facts branches.takenSettles⟩ .nil
      simpa using bodies_source_unified [w] [L] related equations

/-- **The query of `(if b y n)` under `$t` runs to the taken branch's answers**, from any activation. -/
theorem call_query (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfCallProgram atoms) {b : Bool} {y n : Atom}
    {L : List Atom} (branches : CallBranches dispatch atoms b y n L) (activation : Frame)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.call [] [] (callValueOf b y n) (.var "t") activation), stack, []⟩
        ⟨Space.ofList atoms, .returning results, stack, []⟩ ∧
      results.map (fun r => r.1.erase) = L := by
  obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms) [.var "t"] (callOf b y n)
    activation.bindings
  obtain ⟨w, rfl, reads⟩ := call_read policy (scoped_consFree program.rows.scoped)
    branches.closedYes branches.closedNo branches.region frontier
  have both := settlesK_at (policy := policy) program.rows (var_transparent "t")
    branches.takenSettles branches.takenCasts
  have frontier' : EquationFrontierRel (Space.ofList atoms) [.var "t"] (callValueOf b y n).erase
      activation.bindings [w] := by
    rw [callValue_erase]
    exact frontier
  obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
    (policy := policy.rebuilding) activation.certified frontier'
  have unifiers : ∀ w' ∈ [w], ∃ output : Frame, output.bindings = w'.bindings ∧
      Entry.Value.UnifyRel policy.rebuilding activation.environment (callValueOf b y n)
        (Entry.Value.ofAtom w'.pattern) output.environment := by
    intro w' member
    obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w' member
    exact ⟨⟨w'.bindings, after, certificate⟩, rfl, unified⟩
  have related : List.Forall₂ (fun w L => ∃ i, (∀ output : Frame, output.bindings = w.bindings →
        Entry.Value.UnifyRel policy.rebuilding activation.environment (callValueOf b y n)
          (Entry.Value.ofAtom w.pattern) output.environment →
        (output.read policy (Entry.Value.ofAtom w.body)).erase = i ∧
        Marked dispatch atoms (output.read policy (Entry.Value.ofAtom w.body))) ∧
      HEEvaluatesAt dispatch policy atoms (.var "t") i L ∧ BodyFacts i) [w] [L] :=
    .cons ⟨pick b y n, fun output _ unified => by
        rw [reads .active output unified]
        exact ⟨Entry.Value.erase_ofAtom _, marked_ofAtom _⟩,
      both.1, settlesK_facts branches.takenSettles⟩ .nil
  have notError : ¬ IsErrorRel (callValueOf b y n).erase := by
    rw [callValue_erase]
    rintro ⟨tail, same⟩
    simp at same
  have nonGrounded : NonGroundedCallRel dispatch (callValueOf b y n).erase := by
    rw [callValue_erase]
    refine And.intro ?_ (by simp [Minimal.embeddedInstruction])
    rintro ⟨operator, arguments, same, executable⟩
    simp only [callOf, app, Atom.expression.injEq, List.cons.injEq] at same
    rw [← same.1] at executable
    exact notHost executable
  obtain ⟨R, eraseR, pathR⟩ := equations_steps_unified (dispatch := dispatch) (policy := policy)
    (live := []) (scope := []) (original := callValueOf b y n) (activation := activation) [w] [L]
    unifiers related stack []
  exact ⟨R, .head (.internal (.callEquations notError nonGrounded frontier'
    (List.cons_ne_nil _ _))) pathR, by rw [eraseR]; simp⟩

/-! ## Every derivation for `(if c y n)` with a call branch -/

/-- **Every derivation of HE's completed relation for `(if c y n)` publishes the answers of the
taken branch.** -/
theorem call_source {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom} {L : List Atom}
    (branches : CallBranches dispatch atoms b y n L) {results : List Result}
    (derived : Completed.AtomRel (Space.ofList atoms) dispatch Completed.rawLookup [] []
      (Entry.Value.ofAtom (callC c y n)) Atom.undefinedType Completed.Frame.empty results
      (policy := policy)) :
    results.map (fun r => r.1.erase) = L := by
  obtain ⟨Tc, typesC, acceptsC, keepsC⟩ := condition.typed
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have conditionDetermined := (settlesK_at (policy := policy) program.rows bool_transparent
    condition.settles condition.casts).2
  have clean : ∀ a ∈ L, Answerable a := (settlesK_shape branches.takenSettles).1.answers
  have entry := call_entry policy if_data [c, y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have outcome : ∀ {result : Completed.InvocationSelection},
      Completed.InvocationSelectionRel (Space.ofList atoms) Completed.rawLookup policy [] []
        (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase
        (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty result →
      ∃ (signature : SelectedTypePolicy) (after : Frame), signature.functionType = ifArrow ∧
        after.bindings = Bindings.empty ∧ result = .selected signature [after] := by
    intro result chosenRel
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom] at chosenRel
    exact cond_selection program typesC acceptsC keepsC typesY typesN chosenRel
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame branches.closedYes
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame branches.closedNo
  cases derived with
  | delivered entered => cases Entry.functional entered entry
  | cast entered => cases Entry.functional entered entry
  | tuple _ shaped occurs _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      rw [Entry.Value.erase_ofAtom] at occurs
      have same := Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel.unique occurs
        program.types.occurrences
      simp [Atom.undefinedType] at same
  | fallback _ shaped chosenRel _ _ _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | selectionFailed _ shaped chosenRel _ =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, _⟩ := shaped
      obtain ⟨_, _, _, _, impossible⟩ := outcome chosenRel
      cases impossible
  | function _ shaped chosenRel invoked priority =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, rfl, rfl⟩ := shaped
      obtain ⟨signature, after, functionType, afterBindings, selected⟩ := outcome chosenRel
      simp only [Completed.InvocationSelection.selected.injEq] at selected
      obtain ⟨rfl, rfl⟩ := selected
      have projections := if_projections functionType
      have returnTypeOf : ∀ {s : SelectedTypePolicy}, s.returnType = .var "t" →
          Completed.invocationReturnType s = .var "t" := by
        intro s same
        simp [Completed.invocationReturnType, same, Atom.expressionType]
      have returnType := returnTypeOf projections.2
      cases invoked with
      | cons function calls rest =>
          cases rest
          cases function with
          | evaluated _ operatorRel branchesRel =>
              rw [functionType] at operatorRel
              obtain ⟨frF, rfl⟩ := typed_cast_source_at if_data
                (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) program.types
                (ifArrow_accepts afterBindings) operatorRel
              rw [projections.1] at branchesRel
              simp only [List.map_cons, List.map_nil, List.zip_cons_cons, List.zip_nil_right]
                at branchesRel
              cases branchesRel with
              | stopped stopped _ =>
                  rw [Entry.Value.erase_ofAtom] at stopped
                  exact absurd stopped if_data.not_stopped
              | continuing _ arguments restBranches =>
                  cases restBranches
                  cases arguments with
                  | cons conditionRel conditionBranches =>
                      have conditionErase := conditionDetermined (Entry.Value.ofAtom c)
                        (Entry.Value.erase_ofAtom c) (marked_ofAtom c) _ _ _ _ conditionRel
                      obtain ⟨fr1, rfl⟩ := single_data_result (.grounded (.bool b)) conditionErase
                      cases conditionBranches with
                      | stopped stopped _ =>
                          obtain ⟨stoppedCondition, _⟩ := stopped
                          rw [Entry.Value.erase_ofAtom] at stoppedCondition
                          exact absurd stoppedCondition (DataAtom.grounded (.bool b)).not_stopped
                      | continuing _ yesArguments restCondition =>
                          cases restCondition
                          cases yesArguments with
                          | cons yesRel yesBranches =>
                              have yesDelivered := atom_demand_source yesRel
                              subst yesDelivered
                              rw [readY] at yesBranches
                              cases yesBranches with
                              | stopped stopped _ =>
                                  obtain ⟨_, different⟩ := stopped
                                  exact absurd rfl different
                              | continuing _ noArguments restYes =>
                                  cases restYes
                                  cases noArguments with
                                  | cons noRel noBranches =>
                                      have noDelivered := atom_demand_source noRel
                                      subst noDelivered
                                      rw [readN] at noBranches
                                      cases noBranches with
                                      | stopped stopped _ =>
                                          obtain ⟨_, different⟩ := stopped
                                          exact absurd rfl different
                                      | continuing _ packets restNo =>
                                          cases restNo
                                          cases packets
                                          rw [returnType] at calls
                                          simp only [List.map_cons, List.map_nil, List.append_nil,
                                            Completed.argumentPrepend_packet] at calls
                                          cases calls with
                                          | cons callRel restCalls =>
                                              cases restCalls
                                              rw [assembled_eq] at callRel
                                              have answered := call_query_source program branches
                                                callRel
                                              exact publish_answers
                                                (by simp only [List.append_nil]; exact answered)
                                                clean priority

/-! ## A complete run -/

/-- **The function application of `(if c y n)` assembles the call value of the condition's answer
and the delivered branches.** -/
theorem call_function_segment (dispatch : GroundedDispatch) (policy : Policy)
    {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom}
    (closedY : ∀ name, ¬ AtomOccurs y name) (closedN : ∀ name, ¬ AtomOccurs n name)
    (stack : List Continuation) :
    ∃ results : List Result,
      HERuns.HESteps dispatch Completed.rawLookup policy
        ⟨Space.ofList atoms, .work (.function [Completed.invocationReturnType ifPolicy] []
          Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
          [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n]
          Completed.Frame.empty), stack, []⟩
        ⟨Space.ofList atoms, .returning results, stack, []⟩ ∧
      ∃ activation, results = [(callValueOf b y n, activation)] := by
  obtain ⟨frF, renewal⟩ := if_operator_renewal policy
  have readY : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom y) = Entry.Value.ofAtom y :=
    fun frame => HERuns.read_closed policy frame closedY
  have readN : ∀ frame : Frame, frame.read policy (Entry.Value.ofAtom n) = Entry.Value.ofAtom n :=
    fun frame => HERuns.read_closed policy frame closedN
  have ifCast := renewed_cast_step dispatch policy (atom := .symbol "if") (closed_symbol "if")
    (symbol_cast_entry (by decide) (by decide) (by decide +kernel)) program.types
    Completed.Frame.empty frF renewal
  have conditionRuns := (settlesK_at (policy := policy) program.rows bool_transparent
    condition.settles condition.casts).1 (Entry.Value.ofAtom c) (Entry.Value.erase_ofAtom c)
    (marked_ofAtom c)
  obtain ⟨R, eraseR, conditionRun⟩ := conditionRuns
    (Completed.argumentScope (requestsOf c y n).tail ++
      [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy])
    [] frF
    (.arguments [(Entry.Value.ofAtom (.symbol "if")).erase, Completed.invocationReturnType ifPolicy]
        [] (Entry.Value.ofAtom c) (requestsOf c y n).tail ::
      .functionAssemble (Entry.Value.ofAtom (.symbol "if")) ::
      .append (.functionBranches [Completed.invocationReturnType ifPolicy] [] (requestsOf c y n) []) ::
      stack) []
  obtain ⟨fr, rfl⟩ := single_data_result (.grounded (.bool b)) eraseR
  apply Exists.intro
  refine ⟨?_, ?_⟩
  · refine .head (.internal (.functionStart rfl)) ?_
    refine .head (ifCast _ _ _ _) ?_
    refine .head (.internal .functionHeads) ?_
    refine .head (.internal (.functionBranchesContinue ?_)) ?_
    · simpa using if_data.not_stopped
    refine .head (.internal .argumentsCons) ?_
    refine .trans conditionRun ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨stopped, _⟩
      exact (DataAtom.grounded (.bool b)).not_stopped (by simpa using stopped)
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨_, different⟩
      simp only [readY] at different
      exact different rfl
    refine .head (.internal .argumentsCons) ?_
    refine .head (.internal (.delivered (atom_demand_deliver _))) ?_
    refine .head (.internal .arguments) ?_
    refine .head (.internal (.argumentBranchesContinue ?_)) ?_
    · rintro ⟨_, different⟩
      simp only [readN] at different
      exact different rfl
    refine .head (.internal .argumentsNil) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .argumentTail) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .argumentBranchesNil) ?_
    refine .head (.internal .prepend) ?_
    refine .head (.internal .functionAssemble) ?_
    refine .head (.internal .append) ?_
    refine .head (.internal .functionBranchesNil) ?_
    exact .single (.internal .prepend)
  · refine ⟨fr, ?_⟩
    simp [Completed.functionAssemble, Completed.argumentPrepend, Entry.Value.argumentPacket,
      Entry.Value.unpackArguments, Entry.Value.ofAtom, readY, readN]

/-- **A complete run of `(if c y n)` on HE's machine, publishing the taken branch's answers.** -/
theorem call_run (dispatch : GroundedDispatch) (notHost : ¬ dispatch.executable (.symbol "if"))
    (policy : Policy) {atoms : List Atom} (program : IfCallProgram atoms) {c : Atom} {b : Bool}
    (condition : Condition dispatch atoms c b) {y n : Atom} {L : List Atom}
    (branches : CallBranches dispatch atoms b y n L) :
    ∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = L := by
  obtain ⟨Tc, typesC, acceptsC, _⟩ := condition.typed
  obtain ⟨Ty, typesY⟩ := branches.typedYes
  obtain ⟨Tn, typesN⟩ := branches.typedNo
  have entry := call_entry policy if_data [c, y, n]
  have shape : Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n)) =
      .expression .active (Entry.Value.ofAtom (.symbol "if") ::
        [c, y, n].map Entry.Value.ofAtom) := by
    rw [Completed.Frame.read_empty]
    simp only [callC, app, Entry.Value.ofAtom, List.map_cons, List.map_nil]
  have selection : Completed.ArgumentService.historical.selection (Space.ofList atoms)
      Completed.rawLookup policy [] []
      (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase
      (Entry.Value.ofAtom (.symbol "if")).erase Atom.undefinedType Completed.Frame.empty
      (.selected ifPolicy [Completed.Frame.empty]) := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom, Entry.Value.erase_ofAtom]
    exact cond_selection_succeeds policy program typesC acceptsC typesY typesN
  have step := LocalStepWith.atomFunction (admission := .historical)
    (space := Space.ofList atoms) (dispatch := dispatch) (lookup := Completed.rawLookup)
    (live := []) (scope := []) (stack := []) entry shape selection
  have published : (Completed.Frame.empty.read policy (Entry.Value.ofAtom (callC c y n))).erase =
      callC c y n := by
    rw [Completed.Frame.read_empty, Entry.Value.erase_ofAtom]
  rw [published] at step
  have returned : Completed.invocationReturnType ifPolicy = .var "t" := by
    simp [Completed.invocationReturnType, ifPolicy, Atom.expressionType]
  obtain ⟨F, pathF, activation, rfl⟩ := call_function_segment dispatch policy program condition
    branches.closedYes branches.closedNo
    (.calls [] [] (Completed.invocationReturnType ifPolicy) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] []) ::
        [.publish (callC c y n)])
  obtain ⟨Q, pathQ, eraseQ⟩ := call_query dispatch notHost policy program branches activation
    (.append (.calls [] [] (.var "t") []) ::
      .append (.invocations [] [] Atom.undefinedType ifPolicy (Entry.Value.ofAtom (.symbol "if"))
        [Entry.Value.ofAtom c, Entry.Value.ofAtom y, Entry.Value.ofAtom n] []) ::
        [.publish (callC c y n)])
  have cleanL : ∀ a ∈ L, Answerable a := (settlesK_shape branches.takenSettles).1.answers
  have clean : ∀ r ∈ (Q ++ []) ++ [], Answerable r.1.erase := by
    intro r member
    simp only [List.append_nil] at member
    apply cleanL
    rw [← eraseQ]
    exact List.mem_map.mpr ⟨r, member, rfl⟩
  obtain ⟨publishedAnswers, eraseP, pathP⟩ := NestedArguments.HENested.publish_step
    (dispatch := dispatch) (lookup := Completed.rawLookup) (policy := policy) (atoms := atoms)
    (callC c y n) ((Q ++ []) ++ []) clean [] []
  refine ⟨publishedAnswers, ?_, by rw [eraseP]; simpa using eraseQ⟩
  refine .head (.internal step) ?_
  refine .head (.internal .invocationsCons) ?_
  refine .trans pathF ?_
  refine .head (.internal .calls) ?_
  rw [returned]
  refine .head (.internal .callsCons) ?_
  refine .trans pathQ ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .callsNil) ?_
  refine .head (.internal .prepend) ?_
  refine .head (.internal .append) ?_
  refine .head (.internal .invocationsNil) ?_
  refine .head (.internal .prepend) ?_
  exact pathP.trans (HERuns.publish_all _ publishedAnswers [])

/-! ## Every run -/

/-- **HE's `if` with a computed condition and a call branch, on every run.** On a program carrying
HE's standard-library `if` (`IfCallProgram`), historical lookup, any policy and any dispatch that
does not execute `if`: for a condition that settles with one Boolean answer `b` and meets `Bool`, and
branches meeting `CallBranches` (the taken one any settling term with answers `L` whose data form
`$t` casts as they are, the other any closed atom, the region of `if` HE's row of `b`): a complete
HE run of `(if c y n)` exists, every complete run publishes `L`, and PeTTa's special form yields `L`
from some fuel on. -/
theorem call_every_run (dispatch : GroundedDispatch)
    (notHost : ¬ dispatch.executable (.symbol "if")) (policy : Policy) {atoms : List Atom}
    (program : IfCallProgram atoms) {c : Atom} {b : Bool} (condition : Condition dispatch atoms c b)
    {y n : Atom} {L : List Atom} (branches : CallBranches dispatch atoms b y n L) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
          (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) (callC c y n) Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = L) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate atoms) k
        (Streaming.enter { state := store atoms } (callC c y n))) = L := by
  obtain ⟨heAnswers, path, _⟩ := call_run dispatch notHost policy program condition branches
  have cShape := (settlesK_shape condition.settles).1
  have ground : isGroundAtom (callC c y n) = true := by
    simp [isGroundAtom, isGroundAtom.isGroundList, cShape.answerable.ground,
      branches.groundYes, branches.groundNo]
  exact ⟨⟨heAnswers, path⟩,
    fun emitted run => call_source program condition branches (complete_source run),
    petta_complete ground (settlesK_shape branches.takenSettles).1.answers
      (petta_if_computed (petta_settles program.rows condition.settles)
        (petta_settles program.rows branches.takenSettles))⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open CompoundBindings.Controls (call_single)
open IfComputed.Controls (num loop_closed)

/-- HE's `if`, `(= (isZero 0) True)`, `(= (half 4) two)` and `(= (loop) (loop))`. -/
abbrev callRows : List Atom :=
  ifProgram ++ [rule (app "isZero" [num 0]) (.grounded (.bool true)),
    rule (app "half" [num 4]) (sym "two"), rule (app "loop" []) (app "loop" [])]

theorem call_types_if : StorageTypesRel (Space.ofList callRows) (.symbol "if") [ifArrow] :=
  .symbolKnown (.hit (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) .nil)))))) (by simp)

theorem call_rows : CallProgram callRows := by
  intro row member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with ((rfl | rfl | rfl) | rfl | rfl | rfl)
  · exact ⟨fun lhs rhs same => by simp at same, fun lhs rhs same => by simp at same⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      exact ⟨by decide, .item (.var _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl | rfl
      · exact .grounded _
      · exact .var _
      · exact .var _
    · cases same
      exact ⟨by decide, .item (.var _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_singleton] at inside
      subst inside
      exact .grounded _
    · cases same
      exact ⟨by decide, .item (.grounded _)⟩
  · refine ⟨rule_consFree fun a inside => ?_, fun lhs rhs same => ?_⟩
    · simp only [List.mem_singleton] at inside
      subst inside
      exact .grounded _
    · cases same
      exact ⟨by decide, .item (.symbol _)⟩
  · refine ⟨rule_consFree fun a inside => (by cases inside), fun lhs rhs same => ?_⟩
    cases same
    exact ⟨by decide, .node (by decide) fun u member => by cases member⟩

theorem call_program : IfCallProgram callRows := ⟨call_types_if, call_rows⟩

theorem expression_undeclared (items : List Atom) (notIf : ∀ T,
    Atom.expression [.symbol ":", .symbol "if", ifArrow] ≠ .expression [.symbol ":", .expression items, T]) :
    StorageTypesRel (Space.ofList callRows) (.expression items) [Atom.undefinedType] := by
  cases items with
  | nil => exact .unit _
  | cons head tail =>
      exact .expressionUndefined (.skip notIf (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
          (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same) .nil))))))

theorem symbol_undeclared (name : String) (notIf : name ≠ "if") :
    StorageTypesRel (Space.ofList callRows) (sym name) [Atom.undefinedType] :=
  .symbolUndefined (.skip (fun _ same => by cases same; exact notIf rfl)
    (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
      (.skip (fun _ same => by simp at same) (.skip (fun _ same => by simp at same)
        (.skip (fun _ same => by simp at same) .nil))))))

theorem head_of (f : String) (untyped : (Space.ofList callRows).atoms.filter
      (typeRegion (.symbol f)) = [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false) (notControl : controlHead f = false)
    (notEmpty : f ≠ "Empty") (notError : f ≠ "Error") : NodeHead noHost callRows f :=
  ⟨.symbol notEmpty notError, untyped, fun impossible => impossible, notInstruction, notIO,
    notNative, notControl⟩

/-- `(isZero 0)` settles with `True` in `callRows`. -/
theorem isZero_condition : Condition noHost callRows (app "isZero" [num 0]) true :=
  ⟨call_single (head_of "isZero" (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide +kernel)
      (.cons (.data (.grounded _) (fun same => by cases same)) .nil) rfl (by decide +kernel)
      (.data (.grounded _) (fun same => by cases same)),
    Atom.undefinedType, expression_undeclared _ (fun _ same => by simp at same),
    fun _ => .undefinedRight _ _,
    fun _ _ matched => Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeMatchRel.wildcard_output matched
      (Or.inr (Or.inr (Or.inl rfl)))⟩

/-- `(half 4)` settles with `two`. -/
theorem half_settles : SettlesK noHost callRows (app "half" [num 4]) [sym "two"] :=
  call_single (head_of "half" (by decide +kernel) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)) (by decide +kernel)
    (.cons (.data (.grounded _) (fun same => by cases same)) .nil) rfl (by decide +kernel)
    (.data (.symbol (by decide) (by decide)) (by decide))

/-- The branches of `(if (isZero 0) (half 4) (loop))`: the taken one is a call. -/
theorem half_branches :
    CallBranches noHost callRows true (app "half" [num 4]) (app "loop" []) [sym "two"] where
  takenSettles := half_settles
  takenCasts := fun a member data => by
    rw [List.mem_singleton] at member
    subst member
    exact undeclared_casts data (symbol_undeclared "two" (by decide)) "t"
  closedYes := (call_answerable (f := "half") (.symbol (by decide) (by decide)) fun a member => by
    rw [List.mem_singleton] at member
    subst member
    exact .grounded _).closed
  closedNo := loop_closed
  groundYes := rfl
  groundNo := rfl
  typedYes := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  typedNo := ⟨_, expression_undeclared _ (fun _ same => by simp at same)⟩
  region := by
    unfold IfRegion
    decide +kernel

/-- **The test with a call branch**: `(if (isZero 0) (half 4) (loop))` publishes `two` on every
complete HE run, a complete run exists, and PeTTa yields `two`. The taken branch is a call of a
defined function, evaluated under `$t`; the branch left diverges if run. -/
theorem zero_call (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
          (load (Space.ofList callRows)
            (callC (app "isZero" [num 0]) (app "half" [num 4]) (app "loop" [])) Atom.undefinedType)
          ⟨Space.ofList callRows, .returning [], [], heAnswers⟩) ∧
      (∀ emitted : List Result,
        Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
            (load (Space.ofList callRows)
              (callC (app "isZero" [num 0]) (app "half" [num 4]) (app "loop" [])) Atom.undefinedType)
            ⟨Space.ofList callRows, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = [sym "two"]) ∧
      ∃ N : Nat, ∀ k, N ≤ k → Streaming.values (Streaming.advance (translate callRows) k
        (Streaming.enter { state := store callRows }
          (callC (app "isZero" [num 0]) (app "half" [num 4]) (app "loop" [])))) = [sym "two"] :=
  call_every_run noHost (fun impossible => impossible) policy call_program isZero_condition
    half_branches

/-- **Negative control: freshness is what the read uses.** If the environment already binds the
pattern variable `$p` to `z`, HE's unifier cannot bind `$p` to the delivered branch `y`: no
unification of `y` with `$p` exists there. -/
theorem bound_pattern_blocks (rebuilding : Entry.RebuildPolicy) :
    ¬ ∃ out, Entry.Value.UnifyRel rebuilding [("p", Entry.Value.ofAtom (sym "z"))]
      (Entry.Value.ofAtom (sym "y")) (.var "p") out := by
  rintro ⟨out, unified⟩
  cases unified with
  | ordinary applied =>
      have left : Entry.Value.substitute rebuilding
          (Entry.Value.resolve [("p", Entry.Value.ofAtom (sym "z"))])
          (Entry.Value.ofAtom (sym "y")) = .symbol "y" := by
        simp [Entry.Value.ofAtom, Entry.Value.substitute]
      have right : Entry.Value.substitute rebuilding
          (Entry.Value.resolve [("p", Entry.Value.ofAtom (sym "z"))]) (.var "p") = .symbol "z" := by
        simp [Entry.Value.ofAtom, Entry.Value.substitute, Entry.Value.resolve]
      rw [left, right] at applied
      generalize sameL : Entry.Value.symbol "y" = L at applied
      generalize sameR : Entry.Value.symbol "z" = R at applied
      cases applied with
      | identical same =>
          subst sameL sameR
          simp [Entry.Value.erase] at same
      | bindLeft _ => cases sameL
      | bindRight _ _ => cases sameR
      | expression _ => cases sameL

end Controls

#print axioms lookup_erase
#print axioms outside_of_invisible
#print axioms env_unbound
#print axioms unify_closed_var
#print axioms if_unify
#print axioms call_read
#print axioms equations_steps_unified
#print axioms bodies_source_unified
#print axioms call_query_source
#print axioms call_query
#print axioms call_source
#print axioms call_function_segment
#print axioms call_run
#print axioms call_every_run
#print axioms Controls.zero_call
#print axioms Controls.bound_pattern_blocks

end IfCallBranches

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
