import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.AnswerBags

/-!
# Nested ground arguments: HE builds the argument product first, PeTTa streams, the answers agree

`AnswerBags` compared HE and PeTTa on flat calls `(f a₁ … aₙ)` of data atoms. Here an argument may
itself be a call, `(f t₁ … tₙ)` with `tᵢ` evaluated first. The two dialects order the work
differently:

* **HE** evaluates the whole argument tuple before the call: its tuple traversal evaluates `t₁`,
  then for each answer of `t₁` (in order) evaluates the rest of the tuple, and returns every
  combination in one batch, the first argument varying slowest (`tuple_product`). Only then does
  the calls continuation query `f` on each combination in turn (`calls_loop`).
* **PeTTa** streams: each answer of `t₁` is returned into its argument frame, which continues the
  argument traversal and runs `f`'s selected bodies for that combination before the next answer of
  `t₁` is produced (`args_run`, by delivery through the frames).

The answers are the same list: for each combination in lexicographic order, the answers of `f` on
it (`nested_agree`, `nested_constructor_agree`). The comparison is compositional: it takes the joint
evaluation of each argument and of `f` on each combination of argument answers, and gives the joint
evaluation of the nested call. `nested_complete` reads it on complete runs from both entries.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace NestedArguments

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE (Space Bindings isErrorAtom isEmptyOrError isEmptyAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (LocalStepWith load observe)
open Mettapedia.Languages.MeTTa.HE.RecursiveTasks.Contextual (Control Continuation)
open HEOnTheStep (HEConfig)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (Subst isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags

/-! ## Argument combinations -/

/-- The argument combinations in lexicographic order: the first argument varies slowest. -/
def combos : List (List Atom) → List (List Atom)
  | [] => [[]]
  | L :: Ls => L.flatMap fun r => (combos Ls).map (r :: ·)

theorem mem_combos_cons {r : Atom} {L : List Atom} {Ls : List (List Atom)} {c : List Atom}
    (here : r ∈ L) (later : c ∈ combos Ls) : r :: c ∈ combos (L :: Ls) :=
  List.mem_flatMap.mpr ⟨r, here, List.mem_map.mpr ⟨c, later, rfl⟩⟩

theorem combos_answerable : ∀ {Ls : List (List Atom)}, (∀ L ∈ Ls, ∀ a ∈ L, Answerable a) →
    ∀ c ∈ combos Ls, (∀ a ∈ c, Answerable a)
  | [], _, c, member => by
      simp only [combos, List.mem_singleton] at member
      subst member
      intro a inside
      cases inside
  | L :: Ls, clean, c, member => by
      obtain ⟨r, here, inner⟩ := List.mem_flatMap.mp member
      obtain ⟨c', later, rfl⟩ := List.mem_map.mp inner
      intro a inside
      rcases List.mem_cons.mp inside with rfl | inRest
      · exact clean L List.mem_cons_self a here
      · exact combos_answerable (fun L' member' => clean L' (List.mem_cons_of_mem _ member')) c'
          later a inRest

theorem combos_length : ∀ {Ls : List (List Atom)} {c : List Atom}, c ∈ combos Ls →
    c.length = Ls.length
  | [], c, member => by
      simp only [combos, List.mem_singleton] at member
      subst member
      rfl
  | L :: Ls, c, member => by
      obtain ⟨r, _, inner⟩ := List.mem_flatMap.mp member
      obtain ⟨c', later, rfl⟩ := List.mem_map.mp inner
      simp [combos_length later]

theorem combos_head (f : Atom) (Ls : List (List Atom)) :
    combos ([f] :: Ls) = (combos Ls).map (f :: ·) := by
  simp [combos]

theorem flatMap_combos (L : List Atom) (Ls : List (List Atom)) (A : List Atom → List Atom)
    (K : Atom → List Atom) :
    L.flatMap (fun r => ((combos Ls).flatMap fun c => A (r :: c)).flatMap K) =
      ((combos (L :: Ls)).flatMap A).flatMap K := by
  simp only [combos, List.flatMap_assoc, List.flatMap_map]

theorem combos_singleton : ∀ (L : List Atom), combos [L] = L.map fun r => [r]
  | [] => rfl
  | r :: rest => by
      rw [List.map_cons, ← combos_singleton rest]
      rfl

/-! ## HE: the argument tuple, then the calls -/

/-- HE's equation query on every call value of `(f vals)` returns answers `A`. -/
def HEQuery (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy) (atoms : List Atom)
    (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (activation : Frame) (value : Entry.Value),
    value.erase = .expression (.symbol f :: vals) → ∀ (stack : List Continuation) (emitted : List Result),
      ∃ results : List Result, results.map (fun result => result.1.erase) = A ∧
        Relation.ReflTransGen (HEStep dispatch lookup policy)
          ⟨Space.ofList atoms, .work (.call live scope value Atom.undefinedType activation), stack,
            emitted⟩
          ⟨Space.ofList atoms, .returning results, stack, emitted⟩

namespace HENested

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

theorem emptyOrError_false {a : Atom} (clean : Answerable a) : isEmptyOrError a = false := by
  have notEmpty : a ≠ Atom.empty := fun same => clean.notStopped (Or.inl same)
  simp [isEmptyOrError, isEmptyAtom, notEmpty, clean.notError]

theorem expression_clean {c : Atom} {cs : List Atom} (clean : Answerable c) :
    isEmptyOrError (.expression (c :: cs)) = false := by
  have notEmpty : isEmptyAtom (.expression (c :: cs)) = false := by
    simp [isEmptyAtom, Atom.empty]
  have notError : isErrorAtom (.expression (c :: cs)) = false := by
    cases c with
    | symbol name =>
        have different : name ≠ "Error" := fun same => clean.notErrorSymbol (by rw [same])
        simp [isErrorAtom, different]
    | var _ => rfl
    | grounded _ => rfl
    | expression _ => rfl
  simp [isEmptyOrError, notEmpty, notError]

/-- Results whose atoms are the given answers are answerable. -/
theorem clean_of_erase {R : List Result} {L : List Atom} (erased : R.map (fun r => r.1.erase) = L)
    (clean : ∀ a ∈ L, Answerable a) : ∀ r ∈ R, Answerable r.1.erase := by
  intro r member
  apply clean
  rw [← erased]
  exact List.mem_map.mpr ⟨r, member, rfl⟩

/-- Prepend an atom to an expression's items. -/
def prependAtom (x : Atom) : Atom → Atom
  | .expression items => .expression (x :: items)
  | other => other

theorem tuplePrepend_erase (head : Entry.Value) {r : Result} {children : List Entry.Value}
    (shape : r.1 = .expression .active children) {c0 : Atom} {cs : List Atom}
    (erased : r.1.erase = .expression (c0 :: cs)) (clean : Answerable c0) :
    (Completed.tuplePrepend head r).1 = .expression .active (head :: children) ∧
      (Completed.tuplePrepend head r).1.erase = .expression (head.erase :: c0 :: cs) := by
  obtain ⟨value, frame⟩ := r
  simp only at shape erased ⊢
  subst shape
  have stopped : isEmptyOrError (Entry.Value.expression .active children).erase = false := by
    rw [erased]
    exact expression_clean clean
  have unfolded : Completed.tuplePrepend head (Entry.Value.expression .active children, frame) =
      (.expression .active (head :: children), frame) := by
    unfold Completed.tuplePrepend
    simp [stopped]
  rw [unfolded]
  refine ⟨rfl, ?_⟩
  simp only [Entry.Value.erase, Atom.expression.injEq] at erased ⊢
  rw [List.map_cons, erased]

/-- **The branches of a tuple's head**: for each answer of the head, in order, the rest of the tuple
is evaluated under that answer's activation, and the head is prepended to every combination. -/
theorem branches_loop (atoms : List Atom) {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ts : List (List Atom)}
    (tailRuns : ∀ (live' : List Atom) (activation : Frame) (stack : List Continuation)
      (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) = Ts.map Atom.expression ∧
        (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
        Relation.ReflTransGen (HEStep dispatch lookup policy)
          ⟨Space.ofList atoms, .work (.tuple live' scope tail activation), stack, emitted⟩
          ⟨Space.ofList atoms, .returning R, stack, emitted⟩)
    (tailClean : ∀ c ∈ Ts, ∃ c0 cs, c = c0 :: cs ∧ Answerable c0) :
    ∀ (heads : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      ∀ (stack : List Continuation) (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) =
          heads.flatMap (fun h => Ts.map fun c => Atom.expression (h.1.erase :: c)) ∧
        (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
        Relation.ReflTransGen (HEStep dispatch lookup policy)
          ⟨Space.ofList atoms, .work (.branches live scope tail heads), stack, emitted⟩
          ⟨Space.ofList atoms, .returning R, stack, emitted⟩
  | [], _, stack, emitted => ⟨[], rfl, (fun _ member => by cases member),
      .single (.internal .branchesNil)⟩
  | h :: hs, clean, stack, emitted => by
      have hClean := clean h List.mem_cons_self
      obtain ⟨Rt, eraseRt, shapeRt, pathRt⟩ := tailRuns (h.1.erase :: live) h.2
        (.tupleTail h.1 :: .append (.branches live scope tail hs) :: stack) emitted
      have pointwise : ∀ r ∈ Rt, (∃ children,
            (Completed.tuplePrepend h.1 r).1 = .expression .active children) ∧
          (Completed.tuplePrepend h.1 r).1.erase = prependAtom h.1.erase r.1.erase := by
        intro r member
        obtain ⟨children, shape⟩ := shapeRt r member
        have inTs : r.1.erase ∈ Ts.map Atom.expression := by
          rw [← eraseRt]
          exact List.mem_map.mpr ⟨r, member, rfl⟩
        obtain ⟨c, cMem, cEq⟩ := List.mem_map.mp inTs
        obtain ⟨c0, cs, rfl, clean0⟩ := tailClean c cMem
        have result := tuplePrepend_erase h.1 shape cEq.symm clean0
        refine ⟨⟨_, result.1⟩, ?_⟩
        rw [result.2, ← cEq]
        rfl
      obtain ⟨Rh, eraseRh, shapeRh, pathRh⟩ := branches_loop atoms tailRuns tailClean hs
        (fun x member => clean x (List.mem_cons_of_mem _ member))
        (.prepend (Rt.map (Completed.tuplePrepend h.1)) :: stack) emitted
      refine ⟨Rt.map (Completed.tuplePrepend h.1) ++ Rh, ?_, ?_, ?_⟩
      · rw [List.map_append, eraseRh, List.flatMap_cons, List.map_map]
        congr 1
        have mapped : (Rt.map ((fun r : Result => r.1.erase) ∘ Completed.tuplePrepend h.1)) =
            (Rt.map fun r => r.1.erase).map (prependAtom h.1.erase) := by
          rw [List.map_map]
          apply List.map_congr_left
          intro r member
          exact (pointwise r member).2
        rw [mapped, eraseRt, List.map_map]
        rfl
      · intro r member
        rcases List.mem_append.mp member with inPrepended | inRest
        · obtain ⟨r', member', rfl⟩ := List.mem_map.mp inPrepended
          exact (pointwise r' member').1
        · exact shapeRh r inRest
      · refine .head (.internal (.branchesContinue hClean.notStopped)) ?_
        refine .trans pathRt ?_
        refine .head (.internal .tupleTail) ?_
        refine .head (.internal .append) ?_
        refine .trans pathRh ?_
        exact .single (.internal .prepend)

/-- **HE's tuple traversal of nested arguments**: every element is evaluated to its answers, and
the tuple returns every combination in one batch, the first element varying slowest. -/
theorem tuple_product (atoms : List Atom) :
    ∀ (ts : List Atom) (Ls : List (List Atom)), ts ≠ [] →
      List.Forall₂ (fun t L => HEEvaluates dispatch lookup policy atoms t L ∧
        ∀ a ∈ L, Answerable a) ts Ls →
      ∀ (live : List Atom) (scope : List String) (activation : Frame) (stack : List Continuation)
        (emitted : List Result), ∃ R : List Result,
          R.map (fun r => r.1.erase) = (combos Ls).map Atom.expression ∧
          (∀ r ∈ R, ∃ children, r.1 = .expression .active children) ∧
          Relation.ReflTransGen (HEStep dispatch lookup policy)
            ⟨Space.ofList atoms, .work (.tuple live scope (ts.map Entry.Value.ofAtom) activation),
              stack, emitted⟩
            ⟨Space.ofList atoms, .returning R, stack, emitted⟩
  | [], _, nonempty, _ => absurd rfl nonempty
  | [t], Ls, _, related => by
      intro live scope activation stack emitted
      cases related with
      | cons here rest =>
          rename_i L Ls'
          cases rest
          obtain ⟨R, eraseR, path⟩ := here.1 live scope activation (.singleton :: stack) emitted
          have clean := clean_of_erase eraseR here.2
          have singled : ∀ r ∈ R, Completed.tupleSingleton r = (.expression .active [r.1], r.2) := by
            intro r member
            unfold Completed.tupleSingleton
            rw [emptyOrError_false (clean r member)]
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
  | t :: t2 :: rest, Ls, _, related => by
      intro live scope activation stack emitted
      cases related with
      | cons here later =>
          rename_i L Ls'
          obtain ⟨R, eraseR, path⟩ := here.1 _ scope activation
            (.branches live scope ((t2 :: rest).map Entry.Value.ofAtom) :: stack) emitted
          have clean := clean_of_erase eraseR here.2
          have tailRuns := tuple_product atoms (t2 :: rest) Ls' (List.cons_ne_nil _ _) later
          have tailClean : ∀ c ∈ combos Ls', ∃ c0 cs, c = c0 :: cs ∧ Answerable c0 := by
            intro c member
            have lengths := combos_length member
            have positive : Ls'.length = (t2 :: rest).length := (List.Forall₂.length_eq later).symm
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
          obtain ⟨R', eraseR', shapeR', loop⟩ := branches_loop atoms (live := live)
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

/-- The arguments of a call atom. -/
def argsOf : Atom → List Atom
  | .expression (_ :: vals) => vals
  | _ => []

/-- **The calls continuation over the argument product**: each combination's call value is queried
in turn, and the batches are concatenated in combination order. -/
theorem calls_loop (atoms : List Atom) {live : List Atom} {scope : List String} {f : String}
    (Q : List Atom → List Atom) :
    ∀ (rows : List Result),
      (∀ r ∈ rows, ∃ vals, r.1.erase = .expression (.symbol f :: vals) ∧
        HEQuery dispatch lookup policy atoms f vals (Q vals)) →
      ∀ (stack : List Continuation) (emitted : List Result), ∃ R : List Result,
        R.map (fun r => r.1.erase) = rows.flatMap (fun r => Q (argsOf r.1.erase)) ∧
        Relation.ReflTransGen (HEStep dispatch lookup policy)
          ⟨Space.ofList atoms, .work (.calls live scope Atom.undefinedType rows), stack, emitted⟩
          ⟨Space.ofList atoms, .returning R, stack, emitted⟩
  | [], _, stack, emitted => ⟨[], rfl, .single (.internal .callsNil)⟩
  | r :: rs, queries, stack, emitted => by
      obtain ⟨vals, erased, query⟩ := queries r List.mem_cons_self
      obtain ⟨Qr, eraseQr, pathQr⟩ := query live scope r.2 r.1 erased
        (.append (.calls live scope Atom.undefinedType rs) :: stack) emitted
      obtain ⟨Rs, eraseRs, pathRs⟩ := calls_loop atoms Q rs
        (fun x member => queries x (List.mem_cons_of_mem _ member)) (.prepend Qr :: stack) emitted
      refine ⟨Qr ++ Rs, ?_, ?_⟩
      · rw [List.map_append, eraseQr, eraseRs, List.flatMap_cons, erased]
        rfl
      · refine .head (.internal .callsCons) ?_
        refine .trans pathQr ?_
        refine .head (.internal .append) ?_
        refine .trans pathRs ?_
        exact .single (.internal .prepend)

/-- **The call's batch is published**: none of its answers is an error, so all are kept. -/
theorem publish_step {atoms : List Atom} (c : Atom) (results : List Result)
    (clean : ∀ r ∈ results, Answerable r.1.erase) (stack : List Continuation)
    (emitted : List Result) :
    ∃ published : List Result,
      published.map (fun r => r.1.erase) = results.map (fun r => r.1.erase) ∧
      Relation.ReflTransGen (HEStep dispatch lookup policy)
        ⟨Space.ofList atoms, .returning results, .publish c :: stack, emitted⟩
        ⟨Space.ofList atoms, .returning published, stack, emitted⟩ := by
  have unchanged : results.map (Completed.readResult policy) = results :=
    map_fixed fun r member => HERuns.readResult_closed policy r (clean r member).closed
  have selected : Mettapedia.Machines.OrderedProtocol.Completion.SuccessPriorityRel
      (fun result : Result => isErrorAtom result.1.erase)
      (results.map (Completed.readResult policy)) results := by
    rw [unchanged]
    exact HERuns.success_all results fun r member => (clean r member).notError
  exact ⟨results.map (Completed.publishResult policy c), by simp [Completed.publishResult],
    .single (.internal (.publish selected))⟩

/-- **HE evaluates a nested call**: the type-directed entry, the whole argument product, the query
of `f` on each combination in turn, and the publication. -/
theorem he_nested (answers : AnswersUndefined lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    (args : List.Forall₂ (fun t L => HEEvaluates dispatch lookup policy atoms t L ∧
      ∀ a ∈ L, Answerable a) ts Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, HEQuery dispatch lookup policy atoms f vals (Q vals) ∧
      ∀ a ∈ Q vals, Answerable a) :
    HEEvaluates dispatch lookup policy atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap Q) := by
  intro live scope activation stack emitted
  have readCall := HERuns.read_closed policy activation closed
  have entry : Entry.Rel policy.reentry
      (activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: ts)))).status
      (activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: ts)))).erase
      Atom.undefinedType .interpret := by
    have base := call_entry policy head ts
    rw [Completed.Frame.read_empty] at base
    rw [readCall]
    exact base
  have shape : activation.read policy (Entry.Value.ofAtom (.expression (.symbol f :: ts))) =
      .expression .active (Entry.Value.ofAtom (.symbol f) :: ts.map Entry.Value.ofAtom) := by
    rw [readCall]
    simp only [Entry.Value.ofAtom, List.map_cons]
  have occurrences : Mettapedia.Languages.MeTTa.HE.Spec.Type.TypeOccurrencesRel
      ((Space.ofList atoms).atoms : Multiset Atom) (Entry.Value.ofAtom (.symbol f)).erase
      {Atom.undefinedType} := by
    rw [Entry.Value.erase_ofAtom]
    exact untyped_occurrences untyped
  have step := LocalStepWith.atomTuple (admission := .historical) (space := Space.ofList atoms)
    (dispatch := dispatch) (lookup := lookup) (live := live) (scope := scope) (stack := stack)
    entry shape occurrences
  have published : (activation.read policy
      (Entry.Value.ofAtom (.expression (.symbol f :: ts)))).erase = .expression (.symbol f :: ts) := by
    rw [readCall, Entry.Value.erase_ofAtom]
  rw [published] at step
  have headRuns : HEEvaluates dispatch lookup policy atoms (.symbol f) [.symbol f] :=
    HERuns.he_data answers atoms head
  obtain ⟨T, eraseT, _, pathT⟩ := tuple_product (dispatch := dispatch) (lookup := lookup)
    (policy := policy) atoms (Atom.symbol f :: ts) ([.symbol f] :: Ls) (List.cons_ne_nil _ _)
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
  obtain ⟨R, eraseR, pathR⟩ := calls_loop (dispatch := dispatch) (lookup := lookup)
    (policy := policy) atoms (live := live) (scope := scope) Q T rows
    (.publish (.expression (.symbol f :: ts)) :: stack) emitted
  have totals : T.flatMap (fun r => Q (argsOf r.1.erase)) = (combos Ls).flatMap Q := by
    have viaAtoms : T.flatMap (fun r => Q (argsOf r.1.erase)) =
        (T.map fun r => r.1.erase).flatMap (fun a => Q (argsOf a)) := by
      rw [List.flatMap_map]
    rw [viaAtoms, eraseT, List.map_map, List.flatMap_map]
    rfl
  rw [totals] at eraseR
  have clean : ∀ r ∈ R, Answerable r.1.erase := by
    apply clean_of_erase eraseR
    intro a member
    obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
    exact (apps vals valsMem).2 a inner
  obtain ⟨final, eraseFinal, pathFinal⟩ := publish_step (dispatch := dispatch) (lookup := lookup)
    (policy := policy) (atoms := atoms) (.expression (.symbol f :: ts)) R clean stack emitted
  refine ⟨final, by rw [eraseFinal, eraseR], ?_⟩
  refine .head (.internal step) ?_
  refine .trans pathT ?_
  refine .head (.internal .calls) ?_
  exact pathR.trans pathFinal

end HENested

/-! ## PeTTa: the argument traversal streams -/

/-- **PeTTa applies the target to the held values with answers `A`**, under any frames that deliver
them: from any reached world over the translation's store, with ground, fresh bindings. -/
def PeTTaApplies (atoms : List Atom) (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (held : List Atom) (A : List Atom) : Prop :=
  ∀ (frames : List Streaming.Frame) (K : Atom → List Atom), (∀ v ∈ A, Delivers atoms frames K v) →
  ∀ (world : Streaming.World) (σ : Subst), world.state = store atoms → world.privateCode = [] →
    Unifying.GroundRange σ → (∀ k, Unifying.FreshFor (world.uses + k) σ) →
    ∀ (index : Nat) (older : List Streaming.Job) (answers : List Unifying.Answer) (next : Nat),
      ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
        out.map (fun answer => Unifying.resolve answer.bindings answer.value) = A.flatMap K ∧
        PeTTaRuns.PSteps (translate atoms)
          ⟨world, .execute ⟨.arguments σ target [] held index, frames⟩ :: older, answers, next⟩
          ⟨{world with uses := uses}, older, answers ++ out, next⟩

namespace PeTTaNested

open PeTTaRuns

/-- **PeTTa's argument traversal streams**: each answer of an argument is returned into its
argument frame, which continues with the remaining arguments and the application for that
combination before the argument's next answer is produced. Over the whole traversal the deliveries
come in combination order. -/
theorem args_run (atoms : List Atom) (target : Mettapedia.Languages.MeTTa.PeTTa.Eval.Target)
    (demanded : ∀ i, rawDemand (translate atoms) target i = false) :
    ∀ (ts : List Atom) (Ls : List (List Atom)),
      List.Forall₂ (fun t L => PeTTaEvaluates atoms t L ∧ ∀ a ∈ L, Answerable a) ts Ls →
      ∀ (held : List Atom) (A : List Atom → List Atom),
        (∀ c ∈ combos Ls, PeTTaApplies atoms target (held ++ c) (A c)) →
        ∀ (frames : List Streaming.Frame) (K : Atom → List Atom),
          (∀ c ∈ combos Ls, ∀ v ∈ A c, Delivers atoms frames K v) →
          ∀ (world : Streaming.World) (σ : Subst), world.state = store atoms →
            world.privateCode = [] → Unifying.GroundRange σ →
            (∀ k, Unifying.FreshFor (world.uses + k) σ) →
            ∀ (index : Nat) (older : List Streaming.Job) (answers : List Unifying.Answer)
              (next : Nat),
              ∃ (uses : Nat) (out : List Unifying.Answer), world.uses ≤ uses ∧
                out.map (fun answer => Unifying.resolve answer.bindings answer.value) =
                  ((combos Ls).flatMap A).flatMap K ∧
                PSteps (translate atoms)
                  ⟨world, .execute ⟨.arguments σ target ts held index, frames⟩ :: older, answers,
                    next⟩
                  ⟨{world with uses := uses}, older, answers ++ out, next⟩
  | [], Ls, related, held, A, apps, frames, K, deliver, world, σ, state, privateCode, range,
      fresh, index, older, answers, next => by
      cases related
      have only : ([] : List Atom) ∈ combos [] := by simp [combos]
      have app := apps [] only
      rw [List.append_nil] at app
      obtain ⟨uses, out, grown, valuesOut, path⟩ := app frames K
        (fun v member => deliver [] only v member) world σ state privateCode
        range fresh index older answers next
      exact ⟨uses, out, grown, by rw [valuesOut]; simp [combos], path⟩
  | t :: ts, Ls, related, held, A, apps, frames, K, deliver, world, σ, state, privateCode, range,
      fresh, index, older, answers, next => by
      cases related with
      | cons here later =>
          rename_i L Ls'
          have deliverArg : ∀ r ∈ L, Delivers atoms
              (.source (.argument target ts held index) :: frames)
              (fun r => ((combos Ls').flatMap fun c => A (r :: c)).flatMap K) r := by
            intro r rMem world' σ' state' privateCode' range' fresh' older' answers' next'
            obtain ⟨uses, out, grown, valuesOut, path⟩ := args_run atoms target demanded ts Ls'
              later (held ++ [r]) (fun c => A (r :: c))
              (fun c cMem => by
                have app := apps (r :: c) (mem_combos_cons rMem cMem)
                rwa [List.append_cons] at app)
              frames K (fun c cMem v vMem => deliver (r :: c) (mem_combos_cons rMem cMem) v vMem)
              world' σ' state' privateCode' range' fresh' (index + 1) older' answers' next'
            refine ⟨uses, out, grown, valuesOut, ?_⟩
            refine .head (return_argument world' ⟨r, σ'⟩ target ts held index frames older'
              answers' next') ?_
            refine .head (alternatives world' _ frames older' answers' next') ?_
            exact path
          obtain ⟨uses, out, grown, valuesOut, path⟩ := here.1 _ _ deliverArg world σ state
            privateCode range fresh older answers next
          refine ⟨uses, out, grown, by rw [valuesOut, flatMap_combos], ?_⟩
          exact .head (evaluate_argument world σ target t ts held index (demanded index) frames
            older answers next) path

/-- **PeTTa evaluates a nested call of a defined head**: the call entry, the streaming argument
traversal, and the application on each combination. -/
theorem petta_nested_defined {atoms : List Atom} {f : String} {ts : List Atom}
    {Ls : List (List Atom)} (notCollapse : f ≠ "collapse") (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: ts)) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (fun t L => PeTTaEvaluates atoms t L ∧ ∀ a ∈ L, Answerable a) ts Ls)
    (A : List Atom → List Atom)
    (apps : ∀ c ∈ combos Ls, PeTTaApplies atoms (.function f) c (A c)) :
    PeTTaEvaluates atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap A) := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  have callable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      true := by
    obtain ⟨e, live, head⟩ := defined
    rw [privateCode, notIO, notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    exact List.any_eq_true.mpr ⟨e, live, by simp [head]⟩
  obtain ⟨uses, out, grown, valuesOut, path⟩ := args_run atoms (.function f)
    (fun index => argumentIsRaw_false notNative untyped index) ts Ls args [] A
    (fun c cMem => by
      rw [List.nil_append]
      exact apps c cMem)
    frames K (fun c cMem v vMem => deliver v (List.mem_flatMap.mpr ⟨c, cMem, vMem⟩)) world σ
    state privateCode range fresh 0 older answers next
  exact ⟨uses, out, grown, valuesOut,
    .head (call_enter world σ notCollapse notOnce notControl callable frames older answers next)
      path⟩

/-- **PeTTa evaluates a nested call of a constructor**: the items are evaluated in turn, streaming,
and each combination is built and delivered. -/
theorem petta_nested_constructor {atoms : List Atom} {f : String} {ts : List Atom}
    {Ls : List (List Atom)} (head : DataAtom (.symbol f)) (notCollapse : f ≠ "collapse")
    (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: ts)) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true)
    (args : List.Forall₂ (fun t L => PeTTaEvaluates atoms t L ∧ ∀ a ∈ L, Answerable a) ts Ls) :
    PeTTaEvaluates atoms (.expression (.symbol f :: ts))
      ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)]) := by
  intro frames K deliver world σ state privateCode range fresh older answers next
  have notCallable : (Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f || StdLib.known f ||
      (Unifying.codeRegistry (translate atoms) world.privateCode).equations.any (·.head == f)) =
      false := by
    rw [privateCode, notIO, notNative]
    simp only [Unifying.codeRegistry, List.nil_append, translate_equations, Bool.false_or]
    apply List.any_eq_false.mpr
    intro e member
    have different := List.all_eq_true.mp noEquation e member
    simpa using different
  have headArg : PeTTaEvaluates atoms (.symbol f) [.symbol f] ∧
      ∀ a ∈ [Atom.symbol f], Answerable a :=
    ⟨petta_data atoms head, fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data head⟩
  have related : List.Forall₂ (fun t L => PeTTaEvaluates atoms t L ∧ ∀ a ∈ L, Answerable a)
      (.symbol f :: ts) ([.symbol f] :: Ls) := .cons headArg args
  have allClean : ∀ L ∈ [Atom.symbol f] :: Ls, ∀ a ∈ L, Answerable a := by
    intro L member a inside
    obtain ⟨t, both⟩ := forall₂_right_exists related L member
    exact both.2 a inside
  obtain ⟨uses, out, grown, valuesOut, path⟩ := args_run atoms .data (fun _ => rfl)
    (.symbol f :: ts) ([.symbol f] :: Ls) related [] (fun c => [.expression c])
    (fun c cMem => by
      rw [List.nil_append]
      intro frames' K' deliver' world' σ' state' privateCode' range' fresh' index' older' answers'
        next'
      obtain ⟨u, o, g, v, p⟩ := petta_construct
        (fun v member => (combos_answerable allClean c cMem v member).ground)
        frames' K' (deliver' _ List.mem_cons_self) world' σ' state' privateCode' range' fresh'
        index' older' answers' next'
      exact ⟨u, o, g, by rw [v, List.flatMap_singleton], p⟩)
    frames K (fun c cMem v vMem => by
      rw [combos_head] at cMem
      obtain ⟨vals, valsMem, rfl⟩ := List.mem_map.mp cMem
      rw [List.mem_singleton] at vMem
      subst vMem
      exact deliver _ (List.mem_flatMap.mpr ⟨vals, valsMem, List.mem_singleton_self _⟩))
    world σ state privateCode range fresh 0 older answers next
  refine ⟨uses, out, grown, ?_, ?_⟩
  · rw [valuesOut, combos_head, List.flatMap_map]
  · exact .head (data_enter world σ notCollapse notOnce notControl notCallable frames older answers
      next) path

end PeTTaNested

/-! ## Both machines on nested calls -/

/-- **Both machines evaluate `t` to the answers `L`.** -/
def Joint (dispatch : GroundedDispatch) (lookup : CastLookup) (policy : Policy)
    (atoms : List Atom) (t : Atom) (L : List Atom) : Prop :=
  (∀ a ∈ L, Answerable a) ∧ HEEvaluates dispatch lookup policy atoms t L ∧ PeTTaEvaluates atoms t L

section JointNested

variable {dispatch : GroundedDispatch} {lookup : CastLookup} {policy : Policy}

theorem joint_data (answers : AnswersUndefined lookup) (atoms : List Atom) {d : Atom}
    (data : DataAtom d) : Joint dispatch lookup policy atoms d [d] :=
  ⟨fun a member => by
    rw [List.mem_singleton] at member
    subst member
    exact answerable_of_data data, HERuns.he_data answers atoms data, PeTTaRuns.petta_data atoms data⟩

/-- **The application of a defined head to evaluated values**, from the joint evaluation of the
bodies of its region: HE's query on any call value of `(f vals)`, PeTTa's application to `vals`. -/
theorem joint_query {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f)) (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false) (valsClean : ∀ v ∈ vals, Answerable v)
    (nonempty : regionBodies atoms f vals ≠ []) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => Joint dispatch lookup policy atoms b L ∧ BodyFacts b)
      (regionBodies atoms f vals) Ls) :
    (∀ a ∈ Ls.flatten, Answerable a) ∧ HEQuery dispatch lookup policy atoms f vals Ls.flatten ∧
      PeTTaApplies atoms (.function f) vals Ls.flatten := by
  have ground := fun v member => HERuns.ground_typeVars (valsClean v member)
  refine ⟨?_, fun live scope activation value erased stack emitted =>
    HERuns.he_query_equations program head notHost notInstruction ground nonempty
      (bodies.imp fun _ _ both => ⟨both.1.2.1, both.2, both.1.1⟩) live scope activation value
      erased stack emitted, ?_⟩
  · intro a member
    obtain ⟨L, inLs, inner⟩ := List.mem_flatten.mp member
    obtain ⟨b, both⟩ := forall₂_right_exists bodies L inLs
    exact both.1.1 a inner
  · intro frames K deliver world σ state privateCode range fresh index older answers next
    obtain ⟨b, inRegion⟩ := List.exists_mem_of_ne_nil _ nonempty
    obtain ⟨e, live, eHead, arity, _⟩ := mem_regionBodies inRegion
    exact PeTTaRuns.petta_apply notIO notNative ⟨e, live, eHead, arity⟩
      (fun v member => (valsClean v member).ground)
      (bodies.imp fun _ _ both => ⟨both.1.2.2, both.2.ground⟩) frames K deliver world σ state
      privateCode range fresh index older answers next

/-- **Nested calls agree (defined head).** If every argument `tᵢ` is evaluated jointly to `Lᵢ`, and
`f` applied to every combination of argument answers is evaluated jointly to `Q vals`, then both
machines evaluate `(f t₁ … tₙ)` to the concatenation of `Q` over the combinations, the first
argument varying slowest. HE gets there by building the whole argument product before the first
query; PeTTa by streaming each combination through its argument frames. -/
theorem nested_agree (answers : AnswersUndefined lookup) {atoms : List Atom} {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (notCollapse : f ≠ "collapse") (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: ts)) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (Joint dispatch lookup policy atoms) ts Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      HEQuery dispatch lookup policy atoms f vals (Q vals) ∧
      PeTTaApplies atoms (.function f) vals (Q vals)) :
    Joint dispatch lookup policy atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap Q) := by
  refine ⟨?_, HENested.he_nested answers head untyped closed
    (args.imp fun _ _ both => ⟨both.2.1, both.1⟩) Q fun vals member =>
      ⟨(apps vals member).2.1, (apps vals member).1⟩,
    PeTTaNested.petta_nested_defined notCollapse notOnce notControl notIO notNative untyped defined
      (args.imp fun _ _ both => ⟨both.2.2, both.1⟩) Q fun c member => (apps c member).2.2⟩
  intro a member
  obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
  exact (apps vals valsMem).1 a inner

/-- **Nested calls agree (constructor head).** Both machines build `(f v₁ … vₙ)` for every
combination of argument answers, in combination order. -/
theorem nested_constructor_agree (answers : AnswersUndefined lookup) {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (notHost : ¬ dispatch.executable (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol f]) = false)
    (notCollapse : f ≠ "collapse") (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: ts)) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (closed : ∀ name,
      ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs (.expression (.symbol f :: ts)) name)
    (noEquation : (atoms.filterMap LiveEquations.equationOfRow).all
      (fun equation => equation.head != f) = true)
    (args : List.Forall₂ (Joint dispatch lookup policy atoms) ts Ls) :
    Joint dispatch lookup policy atoms (.expression (.symbol f :: ts))
      ((combos Ls).flatMap fun vals => [.expression (.symbol f :: vals)]) := by
  have allClean : ∀ L ∈ Ls, ∀ a ∈ L, Answerable a := by
    intro L member a inside
    obtain ⟨t, both⟩ := forall₂_right_exists args L member
    exact both.1 a inside
  have query : ∀ vals ∈ combos Ls, HEQuery dispatch lookup policy atoms f vals
      [.expression (.symbol f :: vals)] ∧
      ∀ a ∈ [Atom.expression (.symbol f :: vals)], Answerable a := by
    intro vals member
    have valsClean := combos_answerable allClean vals member
    refine ⟨fun live scope activation value erased stack emitted => ?_, fun a inside => ?_⟩
    · refine ⟨[(value, activation)], by simp [erased], ?_⟩
      have instruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false :=
        notInstruction
      exact HERuns.he_query_absent program head notHost instruction
        (fun v inside => HERuns.ground_typeVars (valsClean v inside))
        (regionBodies_nil_of_no_equation vals noEquation) live scope activation value erased stack
        emitted
    · rw [List.mem_singleton] at inside
      subst inside
      exact app_answerable head valsClean
  refine ⟨?_, HENested.he_nested answers head untyped closed
    (args.imp fun _ _ both => ⟨both.2.1, both.1⟩) _ query,
    PeTTaNested.petta_nested_constructor head notCollapse notOnce notControl notIO notNative
      noEquation (args.imp fun _ _ both => ⟨both.2.2, both.1⟩)⟩
  intro a member
  obtain ⟨vals, valsMem, inner⟩ := List.mem_flatMap.mp member
  exact (query vals valsMem).2 a inner

/-- **Complete runs of a nested call agree**: HE's machine runs from its entry configuration to a
completed phase, and from some fuel on PeTTa's streaming run yields exactly the atoms HE
published. -/
theorem nested_complete {atoms : List Atom} {c : Atom} {L : List Atom}
    (ground : isGroundAtom c = true) (joint : Joint dispatch lookup policy atoms c L) :
    ∃ (heAnswers : List Result) (N : Nat),
      Relation.ReflTransGen (HEStep dispatch lookup policy)
          (load (Space.ofList atoms) c Atom.undefinedType)
          ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ ∧
        observe ⟨Space.ofList atoms, .returning [], [], heAnswers⟩ = some heAnswers ∧
        heAnswers.map (fun r => r.1.erase) = L ∧
        ∀ n, N ≤ n →
          Streaming.values (Streaming.advance (translate atoms) n
            (Streaming.enter { state := store atoms } c)) = L := by
  obtain ⟨R, eraseR, path, observed⟩ := he_complete joint.2.1
  obtain ⟨N, stable⟩ := petta_complete ground joint.1 joint.2.2
  exact ⟨R, N, path, observed, eraseR, stable⟩

/-- **HE publishes only from a completed phase**: a step of HE's machine that changes the published
answers starts from a returned batch with no pending continuation. So HE answers nothing while any
argument, query or body is still pending (it does not stream). -/
theorem emission_needs_empty_stack {x y : HEConfig} (step : HEStep dispatch lookup policy x y)
    (changed : y.emitted ≠ x.emitted) :
    x.stack = [] ∧ ∃ head tail, x.control = .returning (head :: tail) := by
  cases step with
  | internal _ => exact absurd rfl changed
  | publish => exact ⟨rfl, _, _, rfl⟩

/-- Data bodies evaluate jointly to themselves. -/
theorem data_bodies (answers : AnswersUndefined lookup) (atoms : List Atom) :
    ∀ (bodies : List Atom), (∀ b ∈ bodies, DataAtom b ∧ b ≠ Atom.notReducible) →
      List.Forall₂ (fun b L => Joint dispatch lookup policy atoms b L ∧ BodyFacts b) bodies
        (bodies.map fun b => [b])
  | [], _ => .nil
  | b :: rest, each => by
      obtain ⟨data, notRefused⟩ := each b List.mem_cons_self
      exact .cons ⟨joint_data answers atoms data,
        settles_facts (Settles.data (dispatch := dispatch) (atoms := atoms) data notRefused)⟩
        (data_bodies answers atoms rest fun c member => each c (List.mem_cons_of_mem _ member))

theorem flatten_singletons : ∀ (bodies : List Atom), (bodies.map fun b => [b]).flatten = bodies
  | [] => rfl
  | b :: rest => by simp [flatten_singletons rest]

end JointNested

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app rule rule_consFree)

/-- `coin` has two equations; `flip` swaps `heads` and `tails`. -/
def flipRows : List Atom :=
  [rule (app "coin" []) (sym "heads"), rule (app "coin" []) (sym "tails"),
   rule (app "flip" [sym "heads"]) (sym "tails"), rule (app "flip" [sym "tails"]) (sym "heads")]

theorem flip_program : ∀ row ∈ flipRows, RegionsWithVariables.ConsFreeHeads row := by
  intro row member
  simp only [flipRows, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl
  · exact rule_consFree (by simp)
  · exact rule_consFree (by simp)
  · exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .symbol _
  · exact rule_consFree fun a member => by
      simp only [List.mem_singleton] at member
      subst member
      exact .symbol _

theorem symbol_data (name : String) (notEmpty : name ≠ "Empty") (notError : name ≠ "Error")
    (notRefused : name ≠ "NotReducible") : DataAtom (sym name) ∧ sym name ≠ Atom.notReducible :=
  ⟨.symbol notEmpty notError, fun same => notRefused (by cases same; rfl)⟩

/-- `(coin)` evaluates jointly to `heads`, `tails`. -/
theorem coin_joint {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy) :
    Joint noHost lookup policy flipRows (app "coin" []) [sym "heads", sym "tails"] := by
  have ordinary : Ordinary noHost flipRows "coin" [] :=
    ⟨.symbol (by decide) (by decide), by simp, by decide +kernel, fun impossible => impossible,
      by decide +kernel, by decide, by decide, by decide +kernel, by decide, by decide⟩
  have bodies : regionBodies flipRows "coin" [] = [sym "heads", sym "tails"] := by decide +kernel
  have related := data_bodies (dispatch := noHost) (lookup := lookup) (policy := policy) answers
    flipRows [sym "heads", sym "tails"] (by
      intro b member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact symbol_data "heads" (by decide) (by decide) (by decide)
      · exact symbol_data "tails" (by decide) (by decide) (by decide))
  rw [← bodies] at related
  have defined : ∃ e ∈ flipRows.filterMap LiveEquations.equationOfRow, e.head = "coin" ∧
      e.arguments.length = ([] : List Atom).length :=
    ⟨⟨"coin", [], sym "heads"⟩, List.mem_filterMap.mpr ⟨_, List.mem_cons_self, rfl⟩, rfl, rfl⟩
  have joint : Joint noHost lookup policy flipRows (app "coin" [])
      ((regionBodies flipRows "coin" []).map fun b => [b]).flatten :=
    ⟨by
      rw [flatten_singletons, bodies]
      intro a member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact answerable_of_data (symbol_data "heads" (by decide) (by decide) (by decide)).1
      · exact answerable_of_data (symbol_data "tails" (by decide) (by decide) (by decide)).1,
     HERuns.he_call answers flip_program ordinary (by rw [bodies]; simp)
      (related.imp fun _ _ both => ⟨both.1.2.1, both.2, both.1.1⟩),
     PeTTaRuns.petta_call ordinary defined
      (related.imp fun _ _ both => ⟨both.1.2.2, both.2.ground⟩)⟩
  rwa [flatten_singletons, bodies] at joint

theorem flip_app {lookup : CastLookup} (answers : AnswersUndefined lookup) (policy : Policy)
    (side other : String) (bodies : regionBodies flipRows "flip" [sym side] = [sym other])
    (sideData : DataAtom (sym side)) (otherData : DataAtom (sym other) ∧ sym other ≠ Atom.notReducible)
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol "flip", sym side]) = false) :
    (∀ a ∈ [sym other], Answerable a) ∧
      HEQuery noHost lookup policy flipRows "flip" [sym side] [sym other] ∧
      PeTTaApplies flipRows (.function "flip") [sym side] [sym other] := by
  have related := data_bodies (dispatch := noHost) (lookup := lookup) (policy := policy) answers
    flipRows [sym other] (by
      intro b member
      rw [List.mem_singleton] at member
      subst member
      exact otherData)
  rw [← bodies] at related
  have query := joint_query flip_program (.symbol (by decide) (by decide))
    (fun impossible => impossible) notInstruction (by decide) (by decide)
    (fun v member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data sideData)
    (by rw [bodies]; simp) related
  rwa [flatten_singletons, bodies] at query

/-- **Nested positive control: `(flip (coin))`.** Both dialects answer `tails`, `heads`: the coin's
answers in order, each flipped. HE gets there by evaluating `(coin)` to both answers before its
first query of `flip`; PeTTa by flipping `heads` before it evaluates the coin's second body
(after twelve steps it has recorded `tails` with one job, the coin's `tails` body, still pending). -/
theorem flip_coin_agrees {lookup : CastLookup} (answers : AnswersUndefined lookup)
    (policy : Policy) :
    (∃ heAnswers : List Result,
      Relation.ReflTransGen (HEStep noHost lookup policy)
          (load (Space.ofList flipRows) (app "flip" [app "coin" []]) Atom.undefinedType)
          ⟨Space.ofList flipRows, .returning [], [], heAnswers⟩ ∧
        heAnswers.map (fun r => r.1.erase) = [sym "tails", sym "heads"]) ∧
      Streaming.values (Streaming.advance (translate flipRows) 80
        (Streaming.enter { state := store flipRows } (app "flip" [app "coin" []]))) =
        [sym "tails", sym "heads"] ∧
      (Streaming.advance (translate flipRows) 12
        (Streaming.enter { state := store flipRows } (app "flip" [app "coin" []]))).answers.length =
        1 ∧
      (Streaming.advance (translate flipRows) 12
        (Streaming.enter { state := store flipRows } (app "flip" [app "coin" []]))).agenda.length =
        1 := by
  have coin := coin_joint answers policy
  have combosEq : combos [[sym "heads", sym "tails"]] = [[sym "heads"], [sym "tails"]] := rfl
  have heads := flip_app answers policy "heads" "tails" (by decide +kernel)
    (.symbol (by decide) (by decide)) (symbol_data "tails" (by decide) (by decide) (by decide))
    (by decide +kernel)
  have tails := flip_app answers policy "tails" "heads" (by decide +kernel)
    (.symbol (by decide) (by decide)) (symbol_data "heads" (by decide) (by decide) (by decide))
    (by decide +kernel)
  let Q : List Atom → List Atom := fun vals =>
    if vals = [sym "heads"] then [sym "tails"] else [sym "heads"]
  have apps : ∀ vals ∈ combos [[sym "heads", sym "tails"]], (∀ a ∈ Q vals, Answerable a) ∧
      HEQuery noHost lookup policy flipRows "flip" vals (Q vals) ∧
      PeTTaApplies flipRows (.function "flip") vals (Q vals) := by
    intro vals member
    rw [combosEq] at member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · simpa [Q] using heads
    · simpa [Q] using tails
  have closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (app "flip" [app "coin" []]) name := by
    intro name occurs
    cases occurs with
    | expression member inner =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · cases inner
        · cases inner with
          | expression member' inner' =>
              simp only [List.mem_singleton] at member'
              subst member'
              cases inner'
  have nested := nested_agree (dispatch := noHost) answers (atoms := flipRows) (f := "flip")
    (ts := [app "coin" []])
    (.symbol (by decide) (by decide)) (by decide +kernel) (by decide) (by decide) (by decide +kernel)
    (by decide) (by decide) closed
    ⟨⟨"flip", [sym "heads"], sym "tails"⟩,
      List.mem_filterMap.mpr ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        rfl⟩, rfl⟩
    (.cons coin .nil) Q apps
  have answersEq : (combos [[sym "heads", sym "tails"]]).flatMap Q = [sym "tails", sym "heads"] := by
    rw [combosEq]
    simp [Q]
  rw [answersEq] at nested
  obtain ⟨R, N, path, _, erased, stable⟩ := nested_complete (by decide +kernel) nested
  refine ⟨⟨R, path, erased⟩, ?_, by decide +kernel, by decide +kernel⟩
  have finished : (Streaming.advance (translate flipRows) 80
      (Streaming.enter { state := store flipRows }
        (app "flip" [app "coin" []]))).agenda.length = 0 := by
    decide +kernel
  rw [← advance_stable (List.eq_nil_of_length_eq_zero finished) (max N 80) (le_max_right _ _)]
  exact stable (max N 80) (le_max_left _ _)

end Controls

#print axioms combos_answerable
#print axioms flatMap_combos
#print axioms HENested.branches_loop
#print axioms HENested.tuple_product
#print axioms HENested.calls_loop
#print axioms HENested.he_nested
#print axioms PeTTaNested.args_run
#print axioms PeTTaNested.petta_nested_defined
#print axioms PeTTaNested.petta_nested_constructor
#print axioms joint_query
#print axioms nested_agree
#print axioms nested_constructor_agree
#print axioms nested_complete
#print axioms emission_needs_empty_stack
#print axioms Controls.coin_joint
#print axioms Controls.flip_coin_agrees

end NestedArguments

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
