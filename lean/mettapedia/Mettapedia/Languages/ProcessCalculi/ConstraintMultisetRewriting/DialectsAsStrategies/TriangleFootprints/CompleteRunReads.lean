import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AnswerBags

/-!
# What HE reads over a complete run: PeTTa's request rows of every call it queries

`CompleteRun.double_complete_run` showed, for `(double 4)`, that HE's complete run reads exactly
the row PeTTa's call request reads. `WholeRunWords.whole_run_rows` showed it for the run from the
entry through the first query. Here HE's complete run of any settling call is traced, with the
declared region of every firing (`EntryToQuery.Traced`, under HE's raw lookup), through every
recursive query and body, to the published answers.

* `settles_reads`: for a settling term on a program with no type declaration, HE's machine returns
  the term's answers along a traced run whose rows are, in order, the rows of PeTTa's complete call
  request (`WholeRunWords.pettaRows`) of each call HE queries, one request per query. Every other
  firing reads no row.
* `complete_run_reads`: from HE's entry configuration of a settling call, a complete traced run
  publishes the answers PeTTa's streaming run yields, the first query is the call itself, and the
  rows read over the whole run are the request rows of the queried calls.

PeTTa's own run word over a whole run (that its streaming run issues one complete call request per
call, in this order) is not stated here.

## Controls

* `Controls.toss_reads` (positive): HE's complete run of `(toss)` on the coin program reads first
  exactly the two rows of PeTTa's request for `(toss)`.
* `Controls.declared_read` (negative): with `(: b Bool)` in the program, HE's cast of `b` reads that
  row and PeTTa's call region of `(f b)` leaves it out, so the hypothesis of no declarations is
  needed (H3's absence guards).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace CompleteRunReads

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationFrontierRel EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags

/-! ## Words and their rows -/

/-- The positioned rows a declared word reads from the program, firing by firing. -/
def wordRows (atoms : List Atom) (word : List (Atom → Bool)) : List (Atom × ℕ) :=
  (word.map fun ρ => regionRows ρ atoms).flatten

@[simp] theorem wordRows_nil (atoms : List Atom) : wordRows atoms [] = [] := rfl

@[simp] theorem wordRows_cons (atoms : List Atom) (ρ : Atom → Bool) (word : List (Atom → Bool)) :
    wordRows atoms (ρ :: word) = regionRows ρ atoms ++ wordRows atoms word := rfl

@[simp] theorem wordRows_append (atoms : List Atom) (first second : List (Atom → Bool)) :
    wordRows atoms (first ++ second) = wordRows atoms first ++ wordRows atoms second := by
  simp [wordRows]

@[simp] theorem regionRows_nothing (atoms : List Atom) : regionRows nothing atoms = [] :=
  regionRows_eq_nil fun _ _ => rfl

theorem wordRows_nothings (atoms : List Atom) {α : Type} :
    ∀ (items : List α), wordRows atoms (items.map fun _ => nothing) = []
  | [] => rfl
  | _ :: rest => by
      rw [List.map_cons, wordRows_cons, regionRows_nothing, wordRows_nothings atoms rest]
      rfl

/-- A program with no type declaration. -/
def NoDeclarations (atoms : List Atom) : Prop :=
  ∀ row ∈ atoms, ∀ subject type, row ≠ .expression [.symbol ":", subject, type]

theorem typeRegion_false {atoms : List Atom} (none : NoDeclarations atoms) (a : Atom) :
    ∀ row ∈ atoms, typeRegion a row = false := by
  intro row member
  cases found : typeRegion a row with
  | false => rfl
  | true =>
      obtain ⟨type, same⟩ := WholeRunWords.typeRegion_declaration found
      exact absurd same (none row member a type)

theorem cast_rows {atoms : List Atom} (none : NoDeclarations atoms) (a : Atom) :
    regionRows (rawDeclared.region a) atoms = [] :=
  regionRows_eq_nil (typeRegion_false none a)

theorem interpret_rows {atoms : List Atom} (none : NoDeclarations atoms) (c : Atom) :
    regionRows (interpretRegion rawDeclared c) atoms = [] := by
  apply regionRows_eq_nil
  intro row member
  unfold interpretRegion
  split
  · rename_i operator rest
    show (typeRegion operator row || admissionRegion typeRegion _ operator row) = false
    simp [admissionRegion, typeRegion_false none _ row member]
  · rfl

theorem tupleWord_rows {atoms : List Atom} (none : NoDeclarations atoms) :
    ∀ values : List Atom, wordRows atoms (tupleWord rawDeclared values) = [] := by
  intro values
  apply List.flatten_eq_nil_iff.mpr
  intro rows member
  obtain ⟨ρ, inWord, rfl⟩ := List.mem_map.mp member
  rcases tupleWord_mem values ρ inWord with rfl | ⟨a, _, rfl⟩
  · exact regionRows_nothing atoms
  · exact cast_rows none a

/-! ## HE's machine, traced -/

variable {dispatch : GroundedDispatch} {policy : Policy}

/-- **HE's machine evaluates `t` to `L`, reading `R`**: from pending work on `t`, under any live list,
scope, activation, stack and publication prefix, along a traced run whose rows are `R`. -/
def HEReads (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (t : Atom)
    (L : List Atom) (R : List (Atom × ℕ)) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
    (emitted : List Result), ∃ (results : List Result) (word : List (Atom → Bool)),
    results.map (fun result => result.1.erase) = L ∧
    Traced rawDeclared dispatch policy
      ⟨Space.ofList atoms, .work (.atom live scope (Entry.Value.ofAtom t) Atom.undefinedType
        activation), stack, emitted⟩
      ⟨Space.ofList atoms, .returning results, stack, emitted⟩ word ∧
    wordRows atoms word = R

theorem data_reads {atoms : List Atom} (none : NoDeclarations atoms) {d : Atom} (data : DataAtom d) :
    HEReads dispatch policy atoms d [d] [] := by
  intro live scope activation stack emitted
  refine ⟨[(Entry.Value.ofAtom d, activation)], [rawDeclared.region d], by simp, ?_, by
    simp [cast_rows none d]⟩
  exact .cons (CompleteRun.cast_step_frame raw_answers _ data activation live scope stack emitted)
    (CompleteRun.cast_region_frame rawDeclared data activation live scope _) (.refl _)

/-- The tuple traversal of data atoms under any activation, traced. -/
theorem tuple_traced_frame (space : Space) :
    ∀ (values : List Atom), values ≠ [] → (∀ v ∈ values, DataAtom v) →
      ∀ (live : List Atom) (scope : List String) (frame : Frame) (stack : List Continuation)
        (emitted : List Result),
        Traced rawDeclared dispatch policy
          ⟨space, .work (.tuple live scope (values.map Entry.Value.ofAtom) frame), stack, emitted⟩
          ⟨space, .returning [(.expression .active (values.map Entry.Value.ofAtom), frame)], stack,
            emitted⟩
          (tupleWord rawDeclared values)
  | [], nonempty, _ => absurd rfl nonempty
  | [atom], _, data => by
      intro live scope frame stack emitted
      have here := data atom List.mem_cons_self
      refine .cons (.internal .tupleSingleton) rfl ?_
      refine .cons (CompleteRun.cast_step_frame raw_answers space here frame _ _ _ _)
        (CompleteRun.cast_region_frame rawDeclared here frame _ _ _) ?_
      refine .cons (.internal .singleton) rfl ?_
      rw [List.map_singleton (f := Completed.tupleSingleton), tupleSingleton_data here]
      exact .refl _
  | atom :: next :: rest, _, data => by
      intro live scope frame stack emitted
      have here := data atom List.mem_cons_self
      have later : ∀ v ∈ next :: rest, DataAtom v := fun v member =>
        data v (List.mem_cons_of_mem _ member)
      have nextData := later next List.mem_cons_self
      refine .cons (.internal .tupleCons) rfl ?_
      refine .cons (CompleteRun.cast_step_frame raw_answers space here frame _ _ _ _)
        (CompleteRun.cast_region_frame rawDeclared here frame _ _ _) ?_
      refine .cons (.internal .branches) rfl ?_
      refine .cons (.internal (.branchesContinue ?_)) rfl ?_
      · simpa using here.not_stopped
      refine .trans (tuple_traced_frame space (next :: rest) (List.cons_ne_nil _ _) later
        _ _ _ _ _) ?_
      refine .cons (.internal .tupleTail) rfl ?_
      rw [List.map_singleton (f := Completed.tuplePrepend _), tuplePrepend_data nextData rest]
      refine .cons (.internal .append) rfl ?_
      refine .cons (.internal .branchesNil) rfl ?_
      refine .cons (.internal .prepend) rfl ?_
      exact .refl _

/-- From pending work on an ordinary call to its equation query, traced. -/
theorem call_entry_traced {atoms : List Atom} {f : String} {args : List Atom}
    (ordinary : Ordinary dispatch atoms f args) (live : List Atom) (scope : List String)
    (activation : Frame) (stack : List Continuation) (emitted : List Result) :
    Traced rawDeclared dispatch policy
      ⟨Space.ofList atoms, .work (.atom live scope
        (Entry.Value.ofAtom (.expression (.symbol f :: args))) Atom.undefinedType activation), stack,
        emitted⟩
      ⟨Space.ofList atoms, .work (.call live scope (callValue f args) Atom.undefinedType activation),
        .append (.calls live scope Atom.undefinedType []) ::
          .publish (.expression (.symbol f :: args)) :: stack, emitted⟩
      (interpretRegion rawDeclared (.expression (.symbol f :: args)) ::
        (tupleWord rawDeclared (.symbol f :: args) ++ [nothing, nothing])) := by
  have data := HERuns.ordinary_data ordinary
  have closed := (call_answerable ordinary.head ordinary.arguments).closed
  have readCall := HERuns.read_closed policy activation closed
  have entry : Entry.Rel policy.reentry
      (activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).status
      (activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase
      Atom.undefinedType .interpret := by
    have base := call_entry policy ordinary.head args
    rw [Completed.Frame.read_empty] at base
    rw [readCall]
    exact base
  have shape : activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: args))) =
      .expression .active (Entry.Value.ofAtom (.symbol f) :: args.map Entry.Value.ofAtom) := by
    rw [readCall]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.ofAtom (.symbol f)).erase
      {Atom.undefinedType} := by
    rw [Entry.Value.erase_ofAtom]
    exact untyped_occurrences ordinary.untyped
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := dispatch) (lookup := rawDeclared.lookup) (live := live) (scope := scope)
    (stack := stack) entry shape occurrences
  have published : (activation.read policy
      (Entry.Value.ofAtom (.expression (.symbol f :: args)))).erase =
      .expression (.symbol f :: args) := by
    rw [readCall, Entry.Value.erase_ofAtom]
  rw [published] at step
  have region : heRegionD rawDeclared policy
      (.work (.atom live scope (Entry.Value.ofAtom (.expression (.symbol f :: args)))
        Atom.undefinedType activation))
      (.work (.tuple (Atom.undefinedType :: live) scope
        (Entry.Value.ofAtom (.symbol f) :: args.map Entry.Value.ofAtom) activation)) =
      interpretRegion rawDeclared (.expression (.symbol f :: args)) := by
    rw [heRegionD_interpret entry, published]
  refine .cons (.internal step) region ?_
  refine .trans (tuple_traced_frame _ (Atom.symbol f :: args) (List.cons_ne_nil _ _) data
    _ _ _ _ _) ?_
  refine .cons (.internal .calls) rfl ?_
  refine .cons (.internal .callsCons) rfl ?_
  exact .refl _

/-- The rows of the query of an ordinary call at any activation are PeTTa's request rows. -/
theorem query_rows {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {args : List Atom} (data : ∀ a ∈ args, DataAtom a) (live : List Atom) (activation : Frame) :
    regionRows (eqRegion live (.expression (.symbol f :: args)) activation.bindings) atoms =
      WholeRunWords.pettaRows atoms f args :=
  RegionsWithVariables.footprints_coincide_consFree atoms live
    (fun v member => WholeRunWords.data_closed (data v member)) activation program

theorem call_region {f : String} {args : List Atom} (head : DataAtom (.symbol f))
    (live : List Atom) (scope : List String) (activation : Frame) (after : Control)
    (notInvocation : ∀ live' scope' caller value activation',
      after ≠ .work (.invocation live' scope' caller value activation')) :
    heRegionD rawDeclared policy (.work (.call live scope (callValue f args) Atom.undefinedType
      activation)) after =
      eqRegion (Atom.undefinedType :: live) (.expression (.symbol f :: args)) activation.bindings := by
  have notAtom : ¬ ∃ l s v e a,
      (Control.work (.call live scope (callValue f args) Atom.undefinedType activation) : Control) =
        .work (.atom l s v e a) := by
    rintro ⟨_, _, _, _, _, same⟩
    cases same
  rw [heRegionD_of_not_atom notAtom]
  show heCallRegion live (callValue f args) Atom.undefinedType activation after = _
  unfold heCallRegion
  split
  · rename_i live' scope' caller value activation'
    exact absurd rfl (notInvocation live' scope' caller value activation')
  · rw [if_neg (call_not_error head args), callValue_erase]

/-- **The equation loop, traced**: each body's run reads its own rows; every other firing reads
nothing. -/
theorem equations_traced {atoms : List Atom} {live : List Atom} {scope : List String}
    {original : Entry.Value} {activation : Frame} :
    ∀ (works : List EquationWork) (Ls : List (List Atom)) (Rs : List (List (Atom × ℕ))),
      (∀ work ∈ works, ∃ output : Frame, output.bindings = work.bindings ∧
        Entry.Value.UnifyRel policy.rebuilding activation.environment original
          (Entry.Value.ofAtom work.pattern) output.environment) →
      List.Forall₂ (fun work (LR : List Atom × List (Atom × ℕ)) =>
        HEReads dispatch policy atoms work.body LR.1 LR.2 ∧ BodyFacts work.body) works
        (Ls.zip Rs) → Ls.length = Rs.length →
      ∀ (stack : List Continuation) (emitted : List Result),
        ∃ (results : List Result) (word : List (Atom → Bool)),
          results.map (fun result => result.1.erase) = Ls.flatten ∧
          Traced rawDeclared dispatch policy
            ⟨Space.ofList atoms, .work (.equations live scope original Atom.undefinedType
              activation works), stack, emitted⟩
            ⟨Space.ofList atoms, .returning results, stack, emitted⟩ word ∧
          wordRows atoms word = Rs.flatten
  | [], Ls, Rs, _, related, lengths, stack, emitted => by
      cases Ls with
      | nil =>
          cases Rs with
          | nil => exact ⟨[], [nothing], rfl, .cons (.internal .equationsNil) rfl (.refl _), by simp⟩
          | cons _ _ => simp at lengths
      | cons L Ls' =>
          cases Rs with
          | nil => simp at lengths
          | cons R Rs' => cases related
  | work :: works, Ls, Rs, unifiers, related, lengths, stack, emitted => by
      cases Ls with
      | nil =>
          cases Rs with
          | nil => cases related
          | cons _ _ => simp at lengths
      | cons L Ls' =>
          cases Rs with
          | nil => simp at lengths
          | cons R Rs' =>
              cases related with
              | cons here later =>
                  obtain ⟨output, sameBindings, unified⟩ := unifiers work List.mem_cons_self
                  obtain ⟨evaluates, facts⟩ := here
                  have readBody := HERuns.read_closed policy output facts.closed
                  obtain ⟨Rb, wordB, eraseB, pathB, rowsB⟩ := evaluates live scope output
                    (.append (.boundaryBatch live scope none (.returned original Atom.undefinedType)
                      []) :: .append (.equations live scope original Atom.undefinedType activation
                        works) :: stack) emitted
                  obtain ⟨Rw, wordW, eraseW, pathW, rowsW⟩ := equations_traced works Ls' Rs'
                    (fun w member => unifiers w (List.mem_cons_of_mem _ member)) later
                    (by simpa using lengths) (.prepend (Rb ++ []) :: stack) emitted
                  refine ⟨(Rb ++ []) ++ Rw,
                    nothing :: nothing :: nothing :: nothing :: nothing :: nothing ::
                      (wordB ++ (nothing :: nothing :: nothing :: nothing :: (wordW ++ [nothing]))),
                    ?_, ?_, ?_⟩
                  · rw [List.append_nil, List.map_append, eraseB, eraseW, List.flatten_cons]
                  · refine .cons (.internal (.equationsCons sameBindings unified)) rfl ?_
                    rw [readBody]
                    refine .cons (.internal (.boundaryProducerRaw (facts.notFunction policy))) rfl
                      ?_
                    refine .cons (.internal .boundaryBatch) rfl ?_
                    refine .cons (.internal .boundaryBatchCons) rfl ?_
                    refine .cons (.internal .boundaryReturned) rfl ?_
                    refine .cons (.internal (.returnEvaluate ?_ ?_)) rfl ?_
                    · rw [Entry.Value.erase_ofAtom]
                      exact facts.notRefused
                    · rw [Entry.Value.erase_ofAtom]
                      exact facts.notStopped
                    refine .trans pathB ?_
                    refine .cons (.internal .append) rfl ?_
                    refine .cons (.internal .boundaryBatchNil) rfl ?_
                    refine .cons (.internal .prepend) rfl ?_
                    refine .cons (.internal .append) rfl ?_
                    refine .trans pathW ?_
                    exact .cons (.internal .prepend) rfl (.refl _)
                  · simp [rowsB, rowsW]

/-- The calls continuation closes and the batch is published, traced. -/
theorem finish_traced {atoms : List Atom} {live : List Atom} {scope : List String} (c : Atom)
    (results : List Result) (clean : ∀ r ∈ results, Answerable r.1.erase)
    (stack : List Continuation) (emitted : List Result) :
    ∃ published : List Result,
      published.map (fun r => r.1.erase) = results.map (fun r => r.1.erase) ∧
      Traced rawDeclared dispatch policy
        ⟨Space.ofList atoms, .returning results,
          .append (.calls live scope Atom.undefinedType []) :: .publish c :: stack, emitted⟩
        ⟨Space.ofList atoms, .returning published, stack, emitted⟩
        [nothing, nothing, nothing, nothing] := by
  have unchanged : (results ++ []).map (Completed.readResult policy) = results := by
    rw [List.append_nil]
    exact map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      ((results ++ []).map (Completed.readResult policy)) results := by
    rw [unchanged]
    exact HERuns.success_all results fun r member => (clean r member).notError
  refine ⟨results.map (Completed.publishResult policy c), by simp [Completed.publishResult], ?_⟩
  refine .cons (.internal .append) rfl ?_
  refine .cons (.internal .callsNil) rfl ?_
  refine .cons (.internal .prepend) rfl ?_
  exact .cons (.internal (.publish selected)) rfl (.refl _)

/-- HE's top-level publication, traced: it reads nothing. -/
theorem publish_traced (space : Space) : ∀ (results emitted : List Result),
    Traced rawDeclared dispatch policy ⟨space, .returning results, [], emitted⟩
      ⟨space, .returning [], [], emitted ++ results⟩ (results.map fun _ => nothing)
  | [], emitted => by
      rw [List.append_nil]
      exact .refl _
  | r :: rs, emitted => by
      refine .cons .publish rfl ?_
      have later := publish_traced space rs (emitted ++ [r])
      rwa [List.append_assoc, List.singleton_append] at later

/-! ## Both machines, with HE's reads -/

/-- **HE reads PeTTa's request rows of every call it queries.** For a settling term on a program of
symbol-headed, `cons`-free equations with no type declaration: an answer list `L` shared by both
machines, and the list of calls HE queries (in order; for a call, the call itself first) whose PeTTa
request rows are exactly the rows HE's traced run reads. -/
theorem settles_reads {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) (none : NoDeclarations atoms)
    {t : Atom} (settles : Settles dispatch atoms t) :
    ∃ (L : List Atom) (calls : List (String × List Atom)),
      (∀ a ∈ L, Answerable a) ∧
      HEReads dispatch policy atoms t L
        (calls.flatMap fun call => WholeRunWords.pettaRows atoms call.1 call.2) ∧
      PeTTaEvaluates atoms t L ∧
      (∀ call ∈ calls, Settles dispatch atoms (.expression (.symbol call.1 :: call.2))) ∧
      (∀ (g : String) (vals : List Atom), t = .expression (.symbol g :: vals) →
        calls.head? = some (g, vals)) := by
  induction settles with
  | @data d data notRefused =>
      refine ⟨[d], [], fun a member => ?_, by simpa using data_reads none data,
        PeTTaRuns.petta_data atoms data, (fun _ member => by cases member), ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact answerable_of_data data
      · intro g vals same
        cases data <;> cases same
  | @constructor f args ordinary noEquation =>
      have empty := regionBodies_nil_of_no_equation args noEquation
      refine ⟨[.expression (.symbol f :: args)], [(f, args)], fun a member => ?_, ?_,
        PeTTaRuns.petta_constructor ordinary noEquation, fun call member => ?_, ?_⟩
      · rw [List.mem_singleton] at member
        subst member
        exact call_answerable ordinary.head ordinary.arguments
      · intro live scope activation stack emitted
        have clean : ∀ r ∈ [(callValue f args, activation)], Answerable r.1.erase := by
          intro r member
          rw [List.mem_singleton] at member
          subst member
          rw [callValue_erase]
          exact call_answerable ordinary.head ordinary.arguments
        obtain ⟨published, erased, finish⟩ := finish_traced (dispatch := dispatch)
          (policy := policy) (atoms := atoms) (live := live) (scope := scope)
          (.expression (.symbol f :: args)) [(callValue f args, activation)] clean stack emitted
        obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms)
          (Atom.undefinedType :: live) (.expression (.symbol f :: args)) activation.bindings
        have bodies := HERuns.frontier_bodies
          (fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member)))
          activation.certified.satisfiable program (by rw [empty]; intro b member; cases member)
          frontier
        rw [empty] at bodies
        have noWorks : works = [] := List.map_eq_nil_iff.mp bodies
        subst noWorks
        have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
            (callValue f args).erase activation.bindings [] := by
          rw [callValue_erase]
          exact frontier
        refine ⟨published,
          (interpretRegion rawDeclared (.expression (.symbol f :: args)) ::
            (tupleWord rawDeclared (.symbol f :: args) ++ [nothing, nothing])) ++
          (eqRegion (Atom.undefinedType :: live) (.expression (.symbol f :: args))
            activation.bindings :: [nothing, nothing, nothing, nothing]),
          by rw [erased]; simp [callValue_erase], ?_, ?_⟩
        · refine .trans (call_entry_traced ordinary live scope activation stack emitted) ?_
          refine .cons (.internal (.callAbsent (call_not_error ordinary.head args)
            (HERuns.nonGrounded_call ordinary) frontier')) (call_region ordinary.head live scope
              activation _ fun _ _ _ _ _ same => by cases same) ?_
          exact finish
        · simp [interpret_rows none, tupleWord_rows none, query_rows program ordinary.arguments]
      · rw [List.mem_singleton] at member
        subst member
        exact .constructor ordinary noEquation
      · intro g vals same
        simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        rfl
  | @call f args ordinary nonempty settled ih =>
      have each : ∀ b ∈ regionBodies atoms f args, ∃ (P : List Atom × List (String × List Atom)),
          Settles dispatch atoms b ∧ (∀ a ∈ P.1, Answerable a) ∧
          HEReads dispatch policy atoms b P.1
            (P.2.flatMap fun call => WholeRunWords.pettaRows atoms call.1 call.2) ∧
          PeTTaEvaluates atoms b P.1 ∧
          (∀ call ∈ P.2, Settles dispatch atoms (.expression (.symbol call.1 :: call.2))) := by
        intro b member
        obtain ⟨L, calls, clean, reads, petta, settledCalls, _⟩ := ih b member
        exact ⟨(L, calls), settled b member, clean, reads, petta, settledCalls⟩
      obtain ⟨Ps, related⟩ := forall₂_of_forall_exists _ each
      set Ls := Ps.map Prod.fst with LsEq
      set Rs := Ps.map fun P => P.2.flatMap fun call => WholeRunWords.pettaRows atoms call.1 call.2
        with RsEq
      have defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f ∧
          e.arguments.length = args.length := by
        obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
        obtain ⟨e, live, head, arity, _⟩ := mem_regionBodies inRegion
        exact ⟨e, live, head, arity⟩
      have pettaBodies : List.Forall₂ (fun b L => PeTTaEvaluates atoms b L ∧ isGroundAtom b = true)
          (regionBodies atoms f args) Ls := by
        rw [LsEq, List.forall₂_map_right_iff]
        exact related.imp fun _ _ both => ⟨both.2.2.2.1, (settles_facts both.1).ground⟩
      have cleanAll : ∀ a ∈ Ls.flatten, Answerable a := by
        intro a member
        obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
        rw [LsEq] at inLs
        obtain ⟨P, inPs, rfl⟩ := List.mem_map.mp inLs
        obtain ⟨b, both⟩ := forall₂_right_exists related P inPs
        exact both.2.1 a inner
      refine ⟨Ls.flatten, (f, args) :: Ps.flatMap Prod.snd, cleanAll, ?_,
        PeTTaRuns.petta_call ordinary defined pettaBodies, ?_, ?_⟩
      · intro live scope activation stack emitted
        obtain ⟨works, frontier⟩ := frontier_total (Space.ofList atoms)
          (Atom.undefinedType :: live) (.expression (.symbol f :: args)) activation.bindings
        have fixed : ∀ b ∈ regionBodies atoms f args, ∀ rename : String → String,
            Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b =
              b := by
          intro b member
          obtain ⟨P, both⟩ := forall₂_left_exists related b member
          exact (settles_facts both.1).fixed
        have bodiesEq := HERuns.frontier_bodies
          (fun v member => HERuns.ground_typeVars (answerable_of_data (ordinary.arguments v member)))
          activation.certified.satisfiable program fixed frontier
        have worksNonempty : works ≠ [] := by
          intro noWorks
          subst noWorks
          exact nonempty bodiesEq.symm
        have frontier' : EquationFrontierRel (Space.ofList atoms) (Atom.undefinedType :: live)
            (callValue f args).erase activation.bindings works := by
          rw [callValue_erase]
          exact frontier
        obtain ⟨environments, paired⟩ := Entry.Value.UnifyRel.equation_frontier
          (policy := policy.rebuilding) activation.certified frontier'
        have unifiers : ∀ w ∈ works, ∃ output : Frame, output.bindings = w.bindings ∧
            Entry.Value.UnifyRel policy.rebuilding activation.environment (callValue f args)
              (Entry.Value.ofAtom w.pattern) output.environment := by
          intro w member
          obtain ⟨after, unified, certificate⟩ := forall₂_left_exists paired w member
          exact ⟨⟨w.bindings, after, certificate⟩, rfl, unified⟩
        have zipped : Ls.zip Rs = Ps.map fun P => (P.1,
            P.2.flatMap fun call => WholeRunWords.pettaRows atoms call.1 call.2) := by
          rw [LsEq, RsEq, List.zip_map']
        have onWorks : List.Forall₂ (fun work (LR : List Atom × List (Atom × ℕ)) =>
            HEReads dispatch policy atoms work.body LR.1 LR.2 ∧ BodyFacts work.body) works
            (Ls.zip Rs) := by
          rw [zipped, List.forall₂_map_right_iff]
          have onBodies := related
          rw [← bodiesEq] at onBodies
          exact (List.forall₂_map_left_iff.mp onBodies).imp fun _ _ both =>
            ⟨both.2.2.1, settles_facts both.1⟩
        obtain ⟨R, wordE, eraseR, pathR, rowsR⟩ := equations_traced works Ls Rs unifiers onWorks
          (by rw [LsEq, RsEq, List.length_map, List.length_map])
          (.append (.calls live scope Atom.undefinedType []) ::
            .publish (.expression (.symbol f :: args)) :: stack) emitted
        have clean : ∀ r ∈ R, Answerable r.1.erase := by
          intro r member
          apply cleanAll
          rw [← eraseR]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        obtain ⟨published, erased, finish⟩ := finish_traced (dispatch := dispatch)
          (policy := policy) (atoms := atoms) (live := live) (scope := scope)
          (.expression (.symbol f :: args)) R clean stack emitted
        refine ⟨published,
          (interpretRegion rawDeclared (.expression (.symbol f :: args)) ::
            (tupleWord rawDeclared (.symbol f :: args) ++ [nothing, nothing])) ++
          (eqRegion (Atom.undefinedType :: live) (.expression (.symbol f :: args))
            activation.bindings :: (wordE ++ [nothing, nothing, nothing, nothing])),
          by rw [erased, eraseR], ?_, ?_⟩
        · refine .trans (call_entry_traced ordinary live scope activation stack emitted) ?_
          refine .cons (.internal (.callEquations (call_not_error ordinary.head args)
            (HERuns.nonGrounded_call ordinary) frontier' worksNonempty)) (call_region ordinary.head
              live scope activation _ fun _ _ _ _ _ same => by cases same) ?_
          exact pathR.trans finish
        · simp only [wordRows_cons, wordRows_append, interpret_rows none, tupleWord_rows none,
            query_rows program ordinary.arguments, rowsR, regionRows_nothing, wordRows_nil,
            List.nil_append, List.append_nil, List.flatMap_cons]
          rw [RsEq, ← List.flatMap_def, List.flatMap_assoc]
      · intro call member
        rcases List.mem_cons.mp member with rfl | inner
        · exact .call ordinary nonempty settled
        · obtain ⟨P, inPs, inCalls⟩ := List.mem_flatMap.mp inner
          obtain ⟨b, both⟩ := forall₂_right_exists related P inPs
          exact both.2.2.2.2 call inCalls
      · intro g vals same
        simp only [Atom.expression.injEq, List.cons.injEq, Atom.symbol.injEq] at same
        obtain ⟨rfl, rfl⟩ := same
        rfl

/-- **HE's complete run of a settling call reads exactly PeTTa's request rows of the calls it
queries, and publishes PeTTa's answers.** From HE's entry configuration of `(f a₁ … aₙ)`, with HE's
raw lookup, on a program of symbol-headed, `cons`-free equations with no type declaration: a traced
complete run whose first query is the call itself, whose rows read are, in order, the rows of
PeTTa's complete call request (`WholeRunWords.pettaRows`) of each queried call, and whose published
answers are the values of PeTTa's streaming run of the translation from some fuel on. -/
theorem complete_run_reads (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) (none : NoDeclarations atoms)
    {f : String} {args : List Atom}
    (settles : Settles dispatch atoms (.expression (.symbol f :: args))) :
    ∃ (heAnswers : List Result) (word : List (Atom → Bool)) (calls : List (String × List Atom))
      (N : Nat),
      Traced rawDeclared dispatch policy
          (load (Space.ofList atoms) (.expression (.symbol f :: args)) Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ word ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        wordRows atoms word =
          calls.flatMap (fun call => WholeRunWords.pettaRows atoms call.1 call.2) ∧
        calls.head? = some (f, args) ∧
        (∀ call ∈ calls, Settles dispatch atoms (.expression (.symbol call.1 :: call.2))) ∧
        ∀ n, N ≤ n →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } (.expression (.symbol f :: args)))) =
            heAnswers.map (fun r => r.1.erase) := by
  obtain ⟨L, calls, clean, reads, petta, settled, head⟩ :=
    settles_reads (policy := policy) program none settles
  obtain ⟨R, word, eraseR, path, rowsR⟩ := reads [] [] Completed.Frame.empty [] []
  obtain ⟨N, stable⟩ := petta_complete (settles_facts settles).ground clean petta
  refine ⟨R, word ++ R.map (fun _ => nothing), calls, N,
    path.trans (publish_traced (Space.ofList atoms) R []), rfl, ?_, head f args rfl, settled,
    fun n bigger => by rw [stable n bigger, eraseR]⟩
  rw [wordRows_append, wordRows_nothings, List.append_nil, rowsR]

/-! ## Controls -/

namespace Controls

open AnswerBags.Controls (sym app rule coinRows coin_program toss_settles)
open WholeRunWords.Double (noHost)

theorem coin_no_declarations : NoDeclarations coinRows := by
  intro row member subject type same
  simp only [coinRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp at same

/-- **Positive control: `(toss)` reads its own request's rows first.** HE's complete traced run of
`(toss)` on the coin program reads, before anything else, exactly the two rows of PeTTa's request
for `(toss)`: `(= (toss) (coin))` at position `2` and `(= (toss) edge)` at position `3`. -/
theorem toss_reads (policy : Policy) :
    ∃ (heAnswers : List Result) (word : List (Atom → Bool)) (rest : List (Atom × ℕ)),
      Traced rawDeclared noHost policy
          (load (Space.ofList coinRows) (app "toss" []) Atom.undefinedType)
          ⟨Space.ofList coinRows, .returning [], [], heAnswers⟩ word ∧
        wordRows coinRows word =
          [(rule (app "toss" []) (app "coin" []), 2), (rule (app "toss" []) (sym "edge"), 3)] ++
            rest := by
  obtain ⟨R, word, calls, N, path, _, rows, head, _, _⟩ :=
    complete_run_reads noHost policy coin_program coin_no_declarations toss_settles
  cases calls with
  | nil => cases head
  | cons first others =>
      simp only [List.head?_cons, Option.some.injEq] at head
      subst head
      refine ⟨R, word, others.flatMap fun call => WholeRunWords.pettaRows coinRows call.1 call.2,
        path, ?_⟩
      rw [rows, List.flatMap_cons]
      congr 1
      decide +kernel

/-- `{(: b Bool), (= (f $x) yes)}`. -/
abbrev guardRows : List Atom :=
  [.expression [.symbol ":", sym "b", sym "Bool"], rule (app "f" [.var "x"]) (sym "yes")]

/-- **Negative control: the hypothesis of no declarations is needed.** With `(: b Bool)` in the
program, HE's cast of `b` reads that row (H3's absence guards), and PeTTa's call region of `(f b)`
leaves it out. -/
theorem declared_read :
    ¬ NoDeclarations guardRows ∧
      regionRows (rawDeclared.region (sym "b")) guardRows =
        [(.expression [.symbol ":", sym "b", sym "Bool"], 0)] ∧
      pettaCallRegion "f" [sym "b"] (.expression [.symbol ":", sym "b", sym "Bool"]) = false :=
  ⟨fun none => none _ List.mem_cons_self _ _ rfl, by decide +kernel, by decide +kernel⟩

end Controls

#print axioms tuple_traced_frame
#print axioms call_entry_traced
#print axioms call_region
#print axioms equations_traced
#print axioms finish_traced
#print axioms settles_reads
#print axioms complete_run_reads
#print axioms Controls.toss_reads
#print axioms Controls.declared_read

end CompleteRunReads

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
