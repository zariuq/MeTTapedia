import Mettapedia.Languages.MeTTa.PeTTa.AddAtomStep
import Mettapedia.Languages.MeTTa.ContextualTransform.PeTTaQueryInterpretation
import Mettapedia.Languages.MeTTa.PeTTa.StreamingPrefixes

/-!
# The store effects of a PeTTa evaluation are one run of the ordered-store step

The streaming PeTTa machine keeps one world for all its pending alternatives. This module
follows that world's spaces along an evaluation and shows that what the evaluation does to
them is one run of the calculus's ordered-store step, with the evaluator as its client.

* `Supply`: occurrences of stored atoms over every space. An occurrence has the atom it
  holds and the space it is in, and a new one can always be had. `Row` is one such supply.
* `Tracks`: the occurrences `ids` are distinct, and every space of the machine's store
  holds, in order, the atoms of the occurrences placed in it.
* `ask`: the request a configuration of the unifying machine makes of the occurrences.
  `add-atom` makes one occurrence; `remove-atom` takes the occurrences whose atoms unify
  with its pattern; `match` (written, or called with values) reads the occurrences whose
  atoms unify with its pattern; `get-atoms` reads every occurrence of its space; a call of
  an authored function (written, or made at run time) reads the equation occurrences of
  the program's own space whose heads unify with its arguments.
  `Asked` states the same as a relation, and `ask_iff` shows they agree.
* `ask_admitted`: every such request is admitted by the ordered-store step.
* `transition_tracks`: after any transition of the unifying machine, the occurrences
  published by its request (or the same occurrences, when it makes none) track the store
  the machine reached. So a transition that changes a space is one of the requests.
* `written_match_continues`, `native_match_answers`, `get_atoms_answers`,
  `call_continues`: the bodies a written `match` goes on to evaluate, the answers of a
  `match` call and of `get-atoms`, and the bodies a call goes on to evaluate, are those of
  the occurrences it reads (for a call, after the bodies of the privately installed
  clauses, which are not rows).
* `streaming_store_run`: for any number of steps of the streaming machine there is one run
  of the ordered-store step from the occurrences at the start whose word is the requests
  of those steps in order (`requests`), whose knowledge is unchanged, and whose last
  occurrences track the store the machine reached.

* `tracks_load`, `evaluation_store_run`: a program's loaded store is tracked by its rows
  numbered in order, so the theorem applies to every evaluation against a loaded program.

Examples (`Controls`): the requests of single configurations and of whole evaluations
computed by the kernel, among them a `match` with two answers each feeding an `add-atom`
(one read, two makes, both rows stored in one run) and a call of a stored equation (one
read of its row). Negative examples: no occurrences do not track a store with rows;
`add-atom` to something that is not a space, a call that touches no space, a call of a
name with no equation and an evaluation with no steps taken ask nothing.

Not in the word: two decisions the machine takes from the equations without selecting any.
Whether a call has a known arity is read from the registry (for a call made at run time,
from the equations then stored), and a head called at run time with no equation stored is
data: an observation that no such row is there. The requests carry no predicate query:
which rows a removal, a `match` or a call selects is fixed by `selectedRows`, `scan` and
`scanCall`, whose tests rename each row for its own use and so are not predicates of the
row's atom alone.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting
open Interface
open Mettapedia.Languages.MeTTa.ContextualTransform
open PeTTaStoreSelection (atomFrames selectedRows Removal)
open PeTTaQueryInterpretation (scan continuations)
open AddAtomStep (addRequest addRequest_admitted)
open Unifying (resolve)
open NamedSpaces (Handle)

/-! ## Occurrences over every space -/

/-- Occurrences of stored atoms over every space: each has the atom it holds and the space
it is in, and there is always a new one for a given space and atom. -/
structure Supply (O : Type) where
  label : O → Atom
  place : O → Handle
  fresh : List O → Handle → Atom → O
  fresh_new : ∀ ids handle atom, fresh ids handle atom ∉ ids
  label_fresh : ∀ ids handle atom, label (fresh ids handle atom) = atom
  place_fresh : ∀ ids handle atom, place (fresh ids handle atom) = handle

variable {O : Type} [DecidableEq O] (S : Supply O)

/-- The occurrences in one space, in store order. -/
def Supply.rowsAt (handle : Handle) (ids : List O) : List O :=
  ids.filter fun occurrence => decide (S.place occurrence = handle)

omit [DecidableEq O] in
theorem Supply.rowsAt_sublist (handle : Handle) (ids : List O) :
    (S.rowsAt handle ids).Sublist ids := List.filter_sublist

omit [DecidableEq O] in
theorem Supply.mem_rowsAt {handle : Handle} {ids : List O} {occurrence : O} :
    occurrence ∈ S.rowsAt handle ids ↔ occurrence ∈ ids ∧ S.place occurrence = handle := by
  simp [Supply.rowsAt]

theorem Supply.rowsAt_survivors (handle : Handle) (ids taken : List O) :
    S.rowsAt handle (OrderedStore.survivors ids taken) =
      OrderedStore.survivors (S.rowsAt handle ids) taken := by
  simp only [Supply.rowsAt, OrderedStore.survivors, List.filter_filter]
  apply List.filter_congr
  intro occurrence _
  exact Bool.and_comm _ _

omit [DecidableEq O] in
theorem Supply.rowsAt_fresh_same (handle : Handle) (ids : List O) (atom : Atom) :
    S.rowsAt handle (ids ++ [S.fresh ids handle atom]) =
      S.rowsAt handle ids ++ [S.fresh ids handle atom] := by
  simp [Supply.rowsAt, List.filter_append, S.place_fresh]

omit [DecidableEq O] in
theorem Supply.rowsAt_fresh_other {handle other : Handle} (different : other ≠ handle)
    (ids : List O) (atom : Atom) :
    S.rowsAt other (ids ++ [S.fresh ids handle atom]) = S.rowsAt other ids := by
  simp [Supply.rowsAt, List.filter_append, S.place_fresh, Ne.symm different]

/-- The occurrences `ids` are the machine's spaces: they are distinct, every space holds in
order the atoms of the occurrences placed in it, and every occurrence is in a space that
exists. -/
structure Tracks (ids : List O) (state : Effects.State) : Prop where
  distinct : ids.Nodup
  rows : ∀ handle rows, state.read handle = some rows →
    rows = (S.rowsAt handle ids).map S.label
  allocated : ∀ occurrence ∈ ids, (state.read (S.place occurrence)).isSome = true

variable {S}

omit [DecidableEq O] in
/-- `add-atom` on the machine's store is the new occurrence at the end. -/
theorem Tracks.insert {ids : List O} {state after : Effects.State} {handle : Handle}
    {atom : Atom} (tracks : Tracks S ids state)
    (inserted : Effects.insert state handle atom = some after) :
    Tracks S (ids ++ [S.fresh ids handle atom]) after := by
  obtain ⟨before, wasOpen, nowOpen⟩ := Effects.insert_reads_back inserted
  have stays : ∀ other, (state.read other).isSome = true → (after.read other).isSome = true := by
    intro other opened
    by_cases same : other = handle
    · rw [same, nowOpen]; rfl
    · rw [Effects.insert_read_other inserted same]; exact opened
  refine ⟨?_, ?_, ?_⟩
  · refine List.nodup_append.mpr ⟨tracks.distinct, List.nodup_singleton _, ?_⟩
    intro occurrence old other new same
    rw [List.mem_singleton] at new
    subst new
    exact S.fresh_new ids handle atom (same ▸ old)
  · intro other rows opened
    by_cases same : other = handle
    · subst same
      rw [nowOpen] at opened
      have : rows = before ++ [atom] := (Option.some.inj opened).symm
      rw [this, S.rowsAt_fresh_same, List.map_append, List.map_singleton, S.label_fresh,
        ← tracks.rows other before wasOpen]
    · rw [Effects.insert_read_other inserted same] at opened
      rw [S.rowsAt_fresh_other same]
      exact tracks.rows other rows opened
  · intro occurrence member
    rcases List.mem_append.mp member with old | new
    · exact stays _ (tracks.allocated occurrence old)
    · rw [List.mem_singleton] at new
      rw [new, S.place_fresh, nowOpen]; rfl

/-- `remove-atom` on the machine's store is the contraction of the occurrences it selects
in its space. -/
theorem Tracks.remove {ids : List O} {state after : Effects.State} {handle : Handle}
    {pattern : Atom} {use : Nat} {kept taken : List O} (tracks : Tracks S ids state)
    (selected : Removal S.label pattern use (S.rowsAt handle ids) kept taken)
    (written : state.write handle (kept.map S.label) = some after) :
    Tracks S (OrderedStore.survivors ids taken) after := by
  have unique : (S.rowsAt handle ids).Nodup :=
    (S.rowsAt_sublist handle ids).nodup tracks.distinct
  have stays : ∀ other, (state.read other).isSome = true → (after.read other).isSome = true := by
    intro other opened
    by_cases same : other = handle
    · rw [same, NamedSpaces.Store.write_reads_back state handle _ after written]; rfl
    · rw [NamedSpaces.Store.write_read_other state handle other _ after written same]
      exact opened
  refine ⟨tracks.distinct.filter _, ?_, ?_⟩
  · intro other rows opened
    rw [S.rowsAt_survivors]
    by_cases same : other = handle
    · subst same
      rw [NamedSpaces.Store.write_reads_back state other _ after written] at opened
      rw [selected.contracts S.label unique]
      exact (Option.some.inj opened).symm
    · rw [NamedSpaces.Store.write_read_other state handle other _ after written same] at opened
      have untouched : OrderedStore.survivors (S.rowsAt other ids) taken = S.rowsAt other ids := by
        apply List.filter_eq_self.mpr
        intro occurrence member
        have elsewhere := (S.mem_rowsAt.mp member).2
        have notTaken : occurrence ∉ taken := by
          intro chosen
          have here := (S.mem_rowsAt.mp ((selected.taken_sublist S.label).subset chosen)).2
          exact same (elsewhere.symm.trans here)
        simpa using notTaken
      rw [untouched]
      exact tracks.rows other rows opened
  · intro occurrence member
    exact stays _ (tracks.allocated occurrence (List.mem_of_mem_filter member))

omit [DecidableEq O] in
/-- `new-space` adds a space with no occurrence in it. -/
theorem Tracks.allocate {ids : List O} {state : Effects.State} (tracks : Tracks S ids state) :
    Tracks S ids (state.allocate []).2 := by
  have elsewhere : ∀ occurrence ∈ ids, S.place occurrence ≠ (state.allocate []).1 := by
    intro occurrence member same
    have opened := tracks.allocated occurrence member
    rw [same] at opened
    simp [NamedSpaces.Store.allocate] at opened
  refine ⟨tracks.distinct, ?_, ?_⟩
  · intro handle rows opened
    by_cases same : handle = (state.allocate []).1
    · subst same
      rw [NamedSpaces.Store.allocation_reads_empty] at opened
      have none : S.rowsAt (state.allocate []).1 ids = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro occurrence member
        simpa using elsewhere occurrence member
      rw [none, ← Option.some.inj opened]; rfl
    · rw [NamedSpaces.Store.allocation_read_existing state [] handle same] at opened
      exact tracks.rows handle rows opened
  · intro occurrence member
    rw [NamedSpaces.Store.allocation_read_existing state [] _ (elsewhere occurrence member)]
    exact tracks.allocated occurrence member

omit [DecidableEq O] in
/-- `change-state!` writes a cell and no space. -/
theorem Tracks.putCell {ids : List O} {state : Effects.State} (tracks : Tracks S ids state)
    (name : String) (value : Atom) : Tracks S ids (state.putCell name value) := by
  have same : ∀ handle, (state.putCell name value).read handle = state.read handle := by
    intro handle; cases handle <;> rfl
  exact ⟨tracks.distinct, fun handle rows opened => tracks.rows handle rows (same handle ▸ opened),
    fun occurrence member => (same _).symm ▸ tracks.allocated occurrence member⟩

/-! ## The request a configuration makes -/

variable (S)

/-- The request that reads the given occurrences and touches nothing. -/
def readRequest (read : List O) : OrderedStore.Publication Atom O := ⟨⟨[], read, []⟩, []⟩

/-- The occurrences a `match` unifies its pattern with: those of the space `location`
names, each renamed for its own use, under the bindings the `match` runs with. -/
def askQuery (ids : List O) (state : Effects.State) (bindings : Subst) (uses : Nat)
    (location pattern : Atom) : Option (OrderedStore.Publication Atom O) :=
  (Effects.readHandle location).bind fun handle =>
    if (state.read handle).isSome then
      (scan S.label bindings pattern uses (S.rowsAt handle ids)).map fun packets =>
        readRequest (packets.map Prod.fst)
    else none

/-- The request of a native call whose arguments are values. -/
def askCall (ids : List O) (state : Effects.State) (bindings : Subst) (uses : Nat)
    (head : String) (values : List Atom) : Option (OrderedStore.Publication Atom O) :=
  if head = "add-atom" then
    match values with
    | [location, atom] =>
        (Effects.readHandle location).bind fun handle =>
          if (state.read handle).isSome then some (addRequest (S.fresh ids handle atom))
          else none
    | _ => none
  else if head = "remove-atom" then
    match values with
    | [location, .expression (first :: rest)] =>
        (Effects.readHandle location).bind fun handle =>
          if (state.read handle).isSome then
            (selectedRows S.label (.expression (first :: rest)) uses (S.rowsAt handle ids)).map
              PeTTaStoreSelection.request
          else none
    | _ => none
  else if head = "match" then
    match values with
    | [location, pattern, _] => askQuery S ids state bindings uses location pattern
    | _ => none
  else if head = "get-atoms" then
    match values with
    | [location] =>
        (Effects.readHandle location).bind fun handle =>
          if (state.read handle).isSome then some (readRequest (S.rowsAt handle ids)) else none
    | _ => none
  else none

variable {S} in
/-- The equation occurrences a call of `head` selects among rows: the occurrences whose
atom is an equation of `head` with as many arguments as the call has values, each renamed
for its own use, whose argument patterns unify with the values; each with the control the
machine goes on with. `none` when a unification ran out of fuel. -/
def scanCall (label : O → Atom) (bindings : Subst) (head : String) (values : List Atom) :
    Nat → List O → Option (List (O × Unifying.Control))
  | _, [] => some []
  | use, occurrence :: rest =>
      match LiveEquations.equationOfRow (label occurrence) with
      | some equation =>
          if equation.head == head && equation.arguments.length == values.length then do
            let later ← scanCall label bindings head values (use + 1) rest
            match Unifying.unifyArguments bindings
                (equation.arguments.map (Unifying.rename use)) values with
            | .ok bound =>
                some ((occurrence, .evaluate bound (Unifying.rename use equation.body)) :: later)
            | .clash => some later
            | .exhausted => none
          else scanCall label bindings head values use rest
      | none => scanCall label bindings head values use rest

/-- The request of a call of an authored function, classified by `registry`: a read of the
equation occurrences of the program's own space that the call selects. The clauses
installed privately are not rows; they take the first uses. -/
def askEquations (registry : SpaceSemantics.Program) (ids : List O)
    (privateCode : List SpaceSemantics.Equation) (bindings : Subst) (uses : Nat)
    (head : String) (values : List Atom) : Option (OrderedStore.Publication Atom O) :=
  if values.length ∈ Eval.arities registry head then
    (scanCall S.label bindings head values
      (uses + (Unifying.candidates privateCode head values.length).length)
      (S.rowsAt .self ids)).map fun packets => readRequest (packets.map Prod.fst)
  else none

/-- **The request a configuration of the unifying machine makes of the occurrences.** A
native call asks when all its arguments are values; a written `match` asks when the value
of its space has returned; a call of an authored function, written or made at run time,
asks for the equations of the program's own space that it selects. -/
def ask (registry : SpaceSemantics.Program) (ids : List O) (source : Unifying.Configuration) :
    Option (OrderedStore.Publication Atom O) :=
  match source.control with
  | .arguments bindings (.function head) [] held _ =>
      if StdLib.known head = false ∧ Eval.ioHead head = false then
        askEquations S (Unifying.codeRegistry registry source.privateCode) ids
          source.privateCode bindings source.uses head (held.map (resolve bindings))
      else askCall S ids source.state bindings source.uses head (held.map (resolve bindings))
  | .dynamic bindings callee supplied =>
      match resolve bindings callee with
      | .symbol head =>
          if (Eval.ioHead head || StdLib.known head) = false ∧
              (Unifying.codeEquations source.state source.privateCode).any
                (fun equation => equation.head == head) = true then
            askEquations S (Unifying.runtimeRegistry registry source.state source.privateCode)
              ids source.privateCode bindings source.uses head
              (supplied.map (resolve bindings))
          else none
      | _ => none
  | .returned [answer] =>
      match source.frames with
      | .query pattern _ :: _ =>
          askQuery S ids source.state answer.bindings source.uses answer.value pattern
      | _ => none
  | _ => none

/-- The occurrences after a configuration's request: published by it, or the same. -/
def published (registry : SpaceSemantics.Program) (ids : List O)
    (source : Unifying.Configuration) : List O :=
  match ask S registry ids source with
  | none => ids
  | some request => OrderedStore.publish ids request.selection

/-- The same requests as a relation: which configuration asks what. -/
inductive Asked (registry : SpaceSemantics.Program) (ids : List O)
    (source : Unifying.Configuration) : OrderedStore.Publication Atom O → Prop where
  | add {bindings : Subst} {index : Nat} {location atom : Atom} {handle : Handle}
      {rows : List Atom}
      (control : source.control =
        .arguments bindings (.function "add-atom") [] [location, atom] index)
      (resolved : Effects.readHandle (resolve bindings location) = some handle)
      (opened : source.state.read handle = some rows) :
      Asked registry ids source (addRequest (S.fresh ids handle (resolve bindings atom)))
  | remove {bindings : Subst} {index : Nat} {location pattern first : Atom}
      {rest : List Atom} {handle : Handle} {rows : List Atom} {taken : List O}
      (control : source.control =
        .arguments bindings (.function "remove-atom") [] [location, pattern] index)
      (resolved : Effects.readHandle (resolve bindings location) = some handle)
      (opened : source.state.read handle = some rows)
      (shape : resolve bindings pattern = .expression (first :: rest))
      (selected : selectedRows S.label (.expression (first :: rest)) source.uses
        (S.rowsAt handle ids) = some taken) :
      Asked registry ids source (PeTTaStoreSelection.request taken)
  | nativeMatch {bindings : Subst} {index : Nat} {location pattern template : Atom}
      {handle : Handle} {rows : List Atom} {packets : List (O × Subst)}
      (control : source.control =
        .arguments bindings (.function "match") [] [location, pattern, template] index)
      (resolved : Effects.readHandle (resolve bindings location) = some handle)
      (opened : source.state.read handle = some rows)
      (scanned : scan S.label bindings (resolve bindings pattern) source.uses
        (S.rowsAt handle ids) = some packets) :
      Asked registry ids source (readRequest (packets.map Prod.fst))
  | getAtoms {bindings : Subst} {index : Nat} {location : Atom} {handle : Handle}
      {rows : List Atom}
      (control : source.control =
        .arguments bindings (.function "get-atoms") [] [location] index)
      (resolved : Effects.readHandle (resolve bindings location) = some handle)
      (opened : source.state.read handle = some rows) :
      Asked registry ids source (readRequest (S.rowsAt handle ids))
  | writtenMatch {answer : Unifying.Answer} {pattern body : Atom}
      {later : List Unifying.Frame} {handle : Handle} {rows : List Atom}
      {packets : List (O × Subst)}
      (control : source.control = .returned [answer])
      (frames : source.frames = .query pattern body :: later)
      (resolved : Effects.readHandle answer.value = some handle)
      (opened : source.state.read handle = some rows)
      (scanned : scan S.label answer.bindings pattern source.uses (S.rowsAt handle ids) =
        some packets) :
      Asked registry ids source (readRequest (packets.map Prod.fst))
  | call {bindings : Subst} {index : Nat} {head : String} {held : List Atom}
      {packets : List (O × Unifying.Control)}
      (control : source.control = .arguments bindings (.function head) [] held index)
      (authored : StdLib.known head = false) (ordinary : Eval.ioHead head = false)
      (arity : (held.map (resolve bindings)).length ∈
        Eval.arities (Unifying.codeRegistry registry source.privateCode) head)
      (scanned : scanCall S.label bindings head (held.map (resolve bindings))
        (source.uses + (Unifying.candidates source.privateCode head
          (held.map (resolve bindings)).length).length)
        (S.rowsAt .self ids) = some packets) :
      Asked registry ids source (readRequest (packets.map Prod.fst))
  | dynamicCall {bindings : Subst} {callee : Atom} {supplied : List Atom} {head : String}
      {packets : List (O × Unifying.Control)}
      (control : source.control = .dynamic bindings callee supplied)
      (resolved : resolve bindings callee = .symbol head)
      (authored : (Eval.ioHead head || StdLib.known head) = false)
      (registered : (Unifying.codeEquations source.state source.privateCode).any
        (fun equation => equation.head == head) = true)
      (arity : (supplied.map (resolve bindings)).length ∈
        Eval.arities (Unifying.runtimeRegistry registry source.state source.privateCode) head)
      (scanned : scanCall S.label bindings head (supplied.map (resolve bindings))
        (source.uses + (Unifying.candidates source.privateCode head
          (supplied.map (resolve bindings)).length).length)
        (S.rowsAt .self ids) = some packets) :
      Asked registry ids source (readRequest (packets.map Prod.fst))

variable {S}

omit [DecidableEq O] in
theorem askQuery_some {ids : List O} {state : Effects.State} {bindings : Subst} {uses : Nat}
    {location pattern : Atom} {request : OrderedStore.Publication Atom O}
    (asked : askQuery S ids state bindings uses location pattern = some request) :
    ∃ handle rows packets, Effects.readHandle location = some handle ∧
      state.read handle = some rows ∧
      scan S.label bindings pattern uses (S.rowsAt handle ids) = some packets ∧
      request = readRequest (packets.map Prod.fst) := by
  unfold askQuery at asked
  cases resolved : Effects.readHandle location with
  | none => simp [resolved] at asked
  | some handle =>
      cases opened : state.read handle with
      | none => simp [resolved, opened] at asked
      | some rows =>
          cases scanned : scan S.label bindings pattern uses (S.rowsAt handle ids) with
          | none => simp [resolved, opened, scanned] at asked
          | some packets =>
              simp [resolved, opened, scanned] at asked
              exact ⟨handle, rows, packets, rfl, opened, scanned, asked.symm⟩

omit [DecidableEq O] in
theorem askQuery_of {ids : List O} {state : Effects.State} {bindings : Subst} {uses : Nat}
    {location pattern : Atom} {handle : Handle} {rows : List Atom}
    {packets : List (O × Subst)}
    (resolved : Effects.readHandle location = some handle)
    (opened : state.read handle = some rows)
    (scanned : scan S.label bindings pattern uses (S.rowsAt handle ids) = some packets) :
    askQuery S ids state bindings uses location pattern =
      some (readRequest (packets.map Prod.fst)) := by
  simp [askQuery, resolved, opened, scanned]

theorem opened_some {α : Type} {state : Effects.State} {location : Atom}
    {produce : Handle → Option α} {result : α}
    (asked : ((Effects.readHandle location).bind fun handle =>
      if (state.read handle).isSome then produce handle else none) = some result) :
    ∃ handle rows, Effects.readHandle location = some handle ∧
      state.read handle = some rows ∧ produce handle = some result := by
  cases resolved : Effects.readHandle location with
  | none => simp [resolved] at asked
  | some handle =>
      cases opened : state.read handle with
      | none => simp [resolved, opened] at asked
      | some rows =>
          simp [resolved, opened] at asked
          exact ⟨handle, rows, rfl, opened, asked⟩

theorem known_add : StdLib.known "add-atom" = true := by decide
theorem known_remove : StdLib.known "remove-atom" = true := by decide
theorem known_match : StdLib.known "match" = true := by decide
theorem known_get_atoms : StdLib.known "get-atoms" = true := by decide
theorem known_new_space : StdLib.known "new-space" = true := by decide
theorem known_change_state : StdLib.known "change-state!" = true := by decide

theorem ne_of_unknown {head name : String} (authored : StdLib.known head = false)
    (known : StdLib.known name = true) : head ≠ name := by
  rintro rfl
  rw [known] at authored
  cases authored

omit [DecidableEq O] in
theorem askEquations_some {registry : SpaceSemantics.Program} {ids : List O}
    {privateCode : List SpaceSemantics.Equation} {bindings : Subst} {uses : Nat}
    {head : String} {values : List Atom} {request : OrderedStore.Publication Atom O}
    (asked : askEquations S registry ids privateCode bindings uses head values =
      some request) :
    values.length ∈ Eval.arities registry head ∧ ∃ packets,
      scanCall S.label bindings head values
        (uses + (Unifying.candidates privateCode head values.length).length)
        (S.rowsAt .self ids) = some packets ∧
      request = readRequest (packets.map Prod.fst) := by
  unfold askEquations at asked
  split_ifs at asked with arity
  obtain ⟨packets, scanned, made⟩ := Option.map_eq_some_iff.mp asked
  exact ⟨arity, packets, scanned, made.symm⟩

omit [DecidableEq O] in
/-- The occurrences a call selects are among the rows it scans, in their order. -/
theorem scanCall_sublist (label : O → Atom) (bindings : Subst) (head : String)
    (values : List Atom) :
    ∀ (use : Nat) (rows : List O) (packets : List (O × Unifying.Control)),
      scanCall label bindings head values use rows = some packets →
      (packets.map Prod.fst).Sublist rows
  | _, [], packets, scanned => by
      simp only [scanCall, Option.some.injEq] at scanned
      subst scanned
      exact .slnil
  | use, occurrence :: rest, packets, scanned => by
      unfold scanCall at scanned
      split at scanned
      · split_ifs at scanned with fits
        · cases later : scanCall label bindings head values (use + 1) rest with
          | none => simp [later] at scanned
          | some remaining =>
              have inherited := scanCall_sublist label bindings head values (use + 1) rest
                remaining later
              simp only [later, bind, Option.bind_some] at scanned
              split at scanned
              · cases scanned
                exact inherited.cons_cons _
              · cases scanned
                exact inherited.cons _
              · cases scanned
        · exact (scanCall_sublist label bindings head values use rest packets scanned).cons _
      · exact (scanCall_sublist label bindings head values use rest packets scanned).cons _

omit [DecidableEq O] in
/-- The function asks only what the relation states. -/
theorem asked_of_ask {registry : SpaceSemantics.Program} {ids : List O}
    {source : Unifying.Configuration}
    {request : OrderedStore.Publication Atom O} (asked : ask S registry ids source = some request) :
    Asked S registry ids source request := by
  rcases source with ⟨state, control, frames, input, output, uses, privateCode⟩
  cases control with
  | arguments bindings target pending held index =>
      cases target with
      | data => simp [ask] at asked
      | function head =>
          cases pending with
          | cons first rest => simp [ask] at asked
          | nil =>
              simp only [ask] at asked
              split_ifs at asked with authored
              · obtain ⟨arity, packets, scanned, rfl⟩ := askEquations_some asked
                exact Asked.call rfl authored.1 authored.2 arity scanned
              unfold askCall at asked
              split_ifs at asked with isAdd isRemove isMatch isGet
              · subst isAdd
                match held, asked with
                | [location, atom], asked =>
                    simp only [List.map_cons, List.map_nil] at asked
                    obtain ⟨handle, rows, resolved, opened, made⟩ := opened_some asked
                    cases made
                    exact Asked.add rfl resolved opened
                | [], asked => simp at asked
                | [_], asked => simp at asked
                | _ :: _ :: _ :: _, asked => simp at asked
              · subst isRemove
                match held, asked with
                | [location, pattern], asked =>
                    simp only [List.map_cons, List.map_nil] at asked
                    cases shape : resolve bindings pattern with
                    | expression items =>
                        cases items with
                        | nil => simp [shape] at asked
                        | cons first rest =>
                            rw [shape] at asked
                            simp only at asked
                            obtain ⟨handle, rows, resolved, opened, made⟩ := opened_some asked
                            obtain ⟨taken, selected, rfl⟩ := Option.map_eq_some_iff.mp made
                            exact Asked.remove rfl resolved opened shape selected
                    | var name => simp [shape] at asked
                    | symbol name => simp [shape] at asked
                    | grounded value => simp [shape] at asked
                | [], asked => simp at asked
                | [_], asked => simp at asked
                | _ :: _ :: _ :: _, asked => simp at asked
              · subst isMatch
                match held, asked with
                | [location, pattern, template], asked =>
                    simp only [List.map_cons, List.map_nil] at asked
                    obtain ⟨handle, rows, packets, resolved, opened, scanned, rfl⟩ :=
                      askQuery_some asked
                    exact Asked.nativeMatch rfl resolved opened scanned
                | [], asked => simp at asked
                | [_], asked => simp at asked
                | [_, _], asked => simp at asked
                | _ :: _ :: _ :: _ :: _, asked => simp at asked
              · subst isGet
                match held, asked with
                | [location], asked =>
                    simp only [List.map_cons, List.map_nil] at asked
                    obtain ⟨handle, rows, resolved, opened, made⟩ := opened_some asked
                    cases made
                    exact Asked.getAtoms rfl resolved opened
                | [], asked => simp at asked
                | _ :: _ :: _, asked => simp at asked
  | returned answers =>
      match answers, asked with
      | [answer], asked =>
          simp only [ask] at asked
          match frames, asked with
          | .query pattern body :: later, asked =>
              simp only at asked
              obtain ⟨handle, rows, packets, resolved, opened, scanned, rfl⟩ :=
                askQuery_some asked
              exact Asked.writtenMatch rfl rfl resolved opened scanned
          | [], asked => simp at asked
          | .bind _ _ :: _, asked => simp at asked
          | .select _ :: _, asked => simp at asked
          | .branch _ _ :: _, asked => simp at asked
          | .collect _ :: _, asked => simp at asked
          | .argument _ _ _ _ :: _, asked => simp at asked
          | .sequence _ _ :: _, asked => simp at asked
          | .dispatch :: _, asked => simp at asked
          | .dynamicCall :: _, asked => simp at asked
      | [], asked => simp [ask] at asked
      | _ :: _ :: _, asked => simp [ask] at asked
  | evaluate bindings expression => simp [ask] at asked
  | dynamic bindings callee supplied =>
      simp only [ask] at asked
      cases shape : resolve bindings callee with
      | symbol head =>
          rw [shape] at asked
          simp only at asked
          split_ifs at asked with authored
          obtain ⟨arity, packets, scanned, rfl⟩ := askEquations_some asked
          exact Asked.dynamicCall rfl shape authored.1 authored.2 arity scanned
      | var name => simp [shape] at asked
      | grounded value => simp [shape] at asked
      | expression items => simp [shape] at asked
  | sequence remaining answers => simp [ask] at asked
  | fault reason => simp [ask] at asked

omit [DecidableEq O] in
/-- The function asks everything the relation states. -/
theorem ask_of_asked {registry : SpaceSemantics.Program} {ids : List O}
    {source : Unifying.Configuration}
    {request : OrderedStore.Publication Atom O} (asked : Asked S registry ids source request) :
    ask S registry ids source = some request := by
  cases asked with
  | add control resolved opened => simp [ask, control, askCall, known_add, resolved, opened]
  | remove control resolved opened shape selected =>
      simp [ask, control, askCall, known_remove, shape, resolved, opened, selected]
  | nativeMatch control resolved opened scanned =>
      simp [ask, control, askCall, known_match, askQuery_of resolved opened scanned]
  | getAtoms control resolved opened =>
      simp [ask, control, askCall, known_get_atoms, resolved, opened]
  | writtenMatch control frames resolved opened scanned =>
      simp [ask, control, frames, askQuery_of resolved opened scanned]
  | call control authored ordinary arity scanned =>
      simp only [ask, control]
      rw [if_pos ⟨authored, ordinary⟩]
      unfold askEquations
      rw [if_pos arity, scanned]
      rfl
  | dynamicCall control resolved authored registered arity scanned =>
      simp only [ask, control, resolved]
      rw [if_pos ⟨authored, registered⟩]
      unfold askEquations
      rw [if_pos arity, scanned]
      rfl

omit [DecidableEq O] in
/-- **The request function is the relation.** -/
theorem ask_iff (registry : SpaceSemantics.Program) (ids : List O)
    (source : Unifying.Configuration) (request : OrderedStore.Publication Atom O) :
    ask S registry ids source = some request ↔ Asked S registry ids source request :=
  ⟨asked_of_ask, ask_of_asked⟩

/-! ## Every request is admitted -/

theorem takes_admitted (label : O → Atom) (knowledge : EquationStore Atom)
    (ids taken : List O) (unique : ids.Nodup) (within : taken.Sublist ids)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, ids))
      (PeTTaStoreSelection.request taken) := by
  refine ⟨⟨unique, within.nodup unique, List.nodup_nil⟩, ?_, consistent⟩
  refine ⟨?_,
    by simp [PeTTaStoreSelection.request, OrderedStore.Publication.commit, Selection.commit],
    by simp [PeTTaStoreSelection.request, OrderedStore.Publication.commit, Selection.commit],
    by simp [PeTTaStoreSelection.request, OrderedStore.Publication.commit, Selection.commit],
    ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr (within.subset (List.mem_toFinset.mp member))
  · intro query member
    simp [PeTTaStoreSelection.request, OrderedStore.Publication.commit] at member

theorem reads_admitted (label : O → Atom) (knowledge : EquationStore Atom)
    (ids read : List O) (unique : ids.Nodup) (within : ∀ occurrence ∈ read, occurrence ∈ ids)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit label).Admits (s := (knowledge, ids))
      (readRequest read) := by
  refine ⟨⟨unique, List.nodup_nil, List.nodup_nil⟩, ?_, consistent⟩
  refine ⟨by simp [readRequest, OrderedStore.Publication.commit, Selection.commit], ?_,
    by simp [readRequest, OrderedStore.Publication.commit, Selection.commit],
    by simp [readRequest, OrderedStore.Publication.commit, Selection.commit], ?_⟩
  · intro occurrence member
    exact List.mem_toFinset.mpr (within occurrence (List.mem_toFinset.mp member))
  · intro query member
    simp [readRequest, OrderedStore.Publication.commit] at member

/-- **Every request of the machine is admitted by the ordered-store step**, at distinct
occurrences and consistent knowledge: a made occurrence is new, the taken occurrences are
distinct occurrences of the store, and the read occurrences are in the store. -/
theorem asked_admitted {registry : SpaceSemantics.Program} {ids : List O}
    {source : Unifying.Configuration}
    {request : OrderedStore.Publication Atom O} (unique : ids.Nodup)
    (asked : Asked S registry ids source request) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit S.label).Admits (s := (knowledge, ids)) request := by
  cases asked with
  | add control resolved opened =>
      exact addRequest_admitted S.label knowledge ids _ unique (S.fresh_new _ _ _) consistent
  | @remove bindings index location pattern first rest handle rows taken control resolved
      opened shape selected =>
      obtain ⟨kept, removal⟩ := PeTTaStoreSelection.prepared_selection S.label selected
      exact takes_admitted S.label knowledge ids taken unique
        ((removal.taken_sublist S.label).trans (S.rowsAt_sublist handle ids)) consistent
  | @nativeMatch bindings index location pattern template handle rows packets control
      resolved opened scanned =>
      exact reads_admitted S.label knowledge ids _ unique (fun occurrence member =>
        (S.rowsAt_sublist handle ids).subset
          ((PeTTaQueryInterpretation.scanned_occurrences_sublist S.label _ _ _ _ _
            scanned).subset member)) consistent
  | @getAtoms bindings index location handle rows control resolved opened =>
      exact reads_admitted S.label knowledge ids _ unique
        (fun occurrence member => (S.rowsAt_sublist handle ids).subset member) consistent
  | @writtenMatch answer pattern body later handle rows packets control frames resolved
      opened scanned =>
      exact reads_admitted S.label knowledge ids _ unique (fun occurrence member =>
        (S.rowsAt_sublist handle ids).subset
          ((PeTTaQueryInterpretation.scanned_occurrences_sublist S.label _ _ _ _ _
            scanned).subset member)) consistent
  | call control authored ordinary arity scanned =>
      exact reads_admitted S.label knowledge ids _ unique (fun occurrence member =>
        (S.rowsAt_sublist .self ids).subset
          ((scanCall_sublist S.label _ _ _ _ _ _ scanned).subset member)) consistent
  | dynamicCall control resolved authored registered arity scanned =>
      exact reads_admitted S.label knowledge ids _ unique (fun occurrence member =>
        (S.rowsAt_sublist .self ids).subset
          ((scanCall_sublist S.label _ _ _ _ _ _ scanned).subset member)) consistent

/-! ## What a transition does to the store -/

/-- The unifying machine is deterministic. -/
theorem transition_unique {registry : SpaceSemantics.Program}
    {source first second : Unifying.Configuration}
    (one : Unifying.Transition registry source first)
    (other : Unifying.Transition registry source second) : first = second := by
  have computed := Unifying.transition_step one
  rw [Unifying.transition_step other] at computed
  exact (Option.some.inj computed).symm

/-- A transition leaves the store as it is, or is a completed `remove-atom`, or is a
native call other than `remove-atom` that returned. -/
theorem transition_state (registry : SpaceSemantics.Program)
    {source target : Unifying.Configuration}
    (step : Unifying.Transition registry source target) :
    target.state = source.state ∨
    (∃ bindings index location pattern answers used,
      source.control =
        .arguments bindings (.function "remove-atom") [] [location, pattern] index ∧
      Unifying.removeRows source.state (resolve bindings location) (resolve bindings pattern)
        source.uses = some (.ok (target.state, answers, used))) ∨
    (∃ bindings head index held answers,
      source.control = .arguments bindings (.function head) [] held index ∧
      head ≠ "remove-atom" ∧
      StdLib.apply source.state head
        (Unifying.primitiveInputs head source.uses (held.map (resolve bindings))) =
          .ok (target.state, answers)) := by
  cases step
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr (Or.inl ⟨_, _, _, _, _, _, ‹_›, ‹_›⟩)
    | exact Or.inr (Or.inr ⟨_, _, _, _, _, ‹_›, ‹_›, ‹_›⟩)

/-- A completed removal leaves the store as it is, or writes the survivors of an
expression pattern to its space. -/
theorem removeRows_ok {state after : Effects.State} {location pattern : Atom} {use : Nat}
    {answers : List Atom} {used : Nat}
    (removed : Unifying.removeRows state location pattern use =
      some (.ok (after, answers, used))) :
    after = state ∨ ∃ handle rows first rest kept,
      Effects.readHandle location = some handle ∧ state.read handle = some rows ∧
      pattern = .expression (first :: rest) ∧
      Unifying.survivors pattern use rows = some kept ∧
      state.write handle kept = some after := by
  unfold Unifying.removeRows at removed
  cases resolved : Effects.readHandle location with
  | none => simp [resolved] at removed
  | some handle =>
      cases opened : state.read handle with
      | none => simp [resolved, opened] at removed
      | some rows =>
          cases pattern with
          | var name =>
              simp [resolved, opened] at removed
              exact Or.inl removed.1.symm
          | symbol name =>
              simp [resolved, opened] at removed
              exact Or.inl removed.1.symm
          | grounded value =>
              simp [resolved, opened] at removed
              exact Or.inl removed.1.symm
          | expression items =>
              cases items with
              | nil =>
                  simp [resolved, opened] at removed
                  exact Or.inl removed.1.symm
              | cons first rest =>
                  simp only [resolved, opened] at removed
                  cases survived : Unifying.survivors (.expression (first :: rest)) use rows with
                  | none => simp [survived] at removed
                  | some kept =>
                      cases written : state.write handle kept with
                      | none => simp [survived, written] at removed
                      | some next =>
                          simp [survived, written] at removed
                          exact Or.inr ⟨handle, rows, first, rest, kept, rfl, opened, rfl, survived,
                            removed.1 ▸ written⟩

theorem apply_add_atom {state after : Effects.State} {arguments answers : List Atom}
    (returned : StdLib.apply state "add-atom" arguments = .ok (after, answers)) :
    ∃ location atom handle, arguments = [location, atom] ∧
      Effects.readHandle location = some handle ∧
      Effects.insert state handle atom = some after := by
  match arguments, returned with
  | [location, atom], returned =>
      rw [StdLib.add_atom_call] at returned
      cases resolved : Effects.readHandle location with
      | none => simp [resolved] at returned
      | some handle =>
          cases inserted : Effects.insert state handle atom with
          | none => simp [resolved, inserted] at returned
          | some next =>
              simp [resolved, inserted] at returned
              exact ⟨location, atom, handle, rfl, resolved, returned.1 ▸ inserted⟩
  | [], returned =>
      cases (returned : (.error (.invalidArguments "add-atom") : Effects.Result) = _)
  | [_], returned =>
      cases (returned : (.error (.invalidArguments "add-atom") : Effects.Result) = _)
  | _ :: _ :: _ :: _, returned =>
      cases (returned : (.error (.invalidArguments "add-atom") : Effects.Result) = _)

theorem apply_new_space {state after : Effects.State} {arguments answers : List Atom}
    (returned : StdLib.apply state "new-space" arguments = .ok (after, answers)) :
    after = (state.allocate []).2 := by
  match arguments, returned with
  | [], returned =>
      rw [StdLib.new_space_call] at returned
      injection returned with same
      exact (congrArg Prod.fst same).symm
  | _ :: _, returned =>
      cases (returned : (.error (.invalidArguments "new-space") : Effects.Result) = _)

theorem apply_change_state {state after : Effects.State} {arguments answers : List Atom}
    (returned : StdLib.apply state "change-state!" arguments = .ok (after, answers)) :
    ∃ name value, after = state.putCell name value := by
  rcases arguments with _ | ⟨first, _ | ⟨value, _ | ⟨third, rest⟩⟩⟩
  · cases (returned : (.error (.invalidArguments "change-state!") : Effects.Result) = _)
  · cases first <;>
      cases (returned : (.error (.invalidArguments "change-state!") : Effects.Result) = _)
  · cases first with
    | symbol name =>
        rw [StdLib.change_state_call] at returned
        injection returned with same
        exact ⟨name, value, (congrArg Prod.fst same).symm⟩
    | var _ =>
        cases (returned : (.error (.invalidArguments "change-state!") : Effects.Result) = _)
    | grounded _ =>
        cases (returned : (.error (.invalidArguments "change-state!") : Effects.Result) = _)
    | expression _ =>
        cases (returned : (.error (.invalidArguments "change-state!") : Effects.Result) = _)
  · cases first <;>
      cases (returned : (.error (.invalidArguments "change-state!") : Effects.Result) = _)

theorem primitiveInputs_of_ne {head : String} (notChange : head ≠ "change-state!")
    (use : Nat) (values : List Atom) : Unifying.primitiveInputs head use values = values := by
  unfold Unifying.primitiveInputs
  split
  · exact absurd rfl notChange
  · rfl

/-- A native call that is not one of the four that write leaves the store as it is. -/
theorem call_keeps_state {registry : SpaceSemantics.Program}
    {source target : Unifying.Configuration} {bindings : Subst} {head : String}
    {held : List Atom} {index : Nat}
    (step : Unifying.Transition registry source target)
    (control : source.control = .arguments bindings (.function head) [] held index)
    (notNew : head ≠ "new-space") (notAdd : head ≠ "add-atom")
    (notRemove : head ≠ "remove-atom") (notChange : head ≠ "change-state!") :
    target.state = source.state := by
  rcases transition_state registry step with same | ⟨_, _, _, _, _, _, removal, _⟩ |
    ⟨_, _, _, _, _, native, _, applied⟩
  · exact same
  · rw [control] at removal
    injection removal with _ target _ _ _
    injection target with name
    exact absurd name notRemove
  · rw [control] at native
    injection native with _ target _ _ _
    injection target with name
    subst name
    exact StdLib.successful_apply_state notNew notAdd notRemove notChange applied

/-- The return of answers to a waiting frame leaves the store as it is. -/
theorem return_keeps_state {registry : SpaceSemantics.Program}
    {source target : Unifying.Configuration} {answers : List Unifying.Answer}
    (step : Unifying.Transition registry source target)
    (control : source.control = .returned answers) : target.state = source.state := by
  rcases transition_state registry step with same | ⟨_, _, _, _, _, _, removal, _⟩ |
    ⟨_, _, _, _, _, native, _, _⟩
  · exact same
  · rw [control] at removal
    cases removal
  · rw [control] at native
    cases native

/-- A call made at run time leaves the store as it is. -/
theorem dynamic_keeps_state {registry : SpaceSemantics.Program}
    {source target : Unifying.Configuration} {bindings : Subst} {callee : Atom}
    {supplied : List Atom}
    (step : Unifying.Transition registry source target)
    (control : source.control = .dynamic bindings callee supplied) :
    target.state = source.state := by
  rcases transition_state registry step with same | ⟨_, _, _, _, _, _, removal, _⟩ |
    ⟨_, _, _, _, _, native, _, _⟩
  · exact same
  · rw [control] at removal
    cases removal
  · rw [control] at native
    cases native

/-- **A transition of the machine and its request.** After any transition, the occurrences
published by the request the source configuration makes (the same occurrences when it makes
none) track the store the machine reached. A transition that changes a space therefore
makes a request, and the request's effect on the occurrences is the machine's effect on the
space. -/
theorem transition_tracks {registry : SpaceSemantics.Program}
    {source target : Unifying.Configuration} {ids : List O}
    (tracks : Tracks S ids source.state)
    (step : Unifying.Transition registry source target) :
    Tracks S (published S registry ids source) target.state := by
  unfold published
  cases asked : ask S registry ids source with
  | some request =>
      simp only
      cases asked_of_ask asked with
      | @add bindings index location atom handle rows control resolved opened =>
          obtain ⟨after, inserted⟩ :=
            Effects.insert_exists_of_read_some opened (resolve bindings atom)
          rw [AddAtomStep.add_atom_transition_unique registry source target bindings index
            location atom handle after control resolved inserted step]
          show Tracks S (OrderedStore.publish ids
            ⟨[], [], [S.fresh ids handle (resolve bindings atom)]⟩) after
          rw [OrderedStore.append_only]
          exact tracks.insert inserted
      | @remove bindings index location pattern first rest handle rows taken control resolved
          opened shape selected =>
          obtain ⟨kept, removal⟩ := PeTTaStoreSelection.prepared_selection S.label selected
          have held := tracks.rows handle rows opened
          obtain ⟨after, written⟩ := NamedSpaces.Store.write_exists_of_read_some source.state
            handle rows (kept.map S.label) opened
          have removed := PeTTaStoreSelection.source_remove_rows S.label source.state after
            (resolve bindings location) first rest handle source.uses (S.rowsAt handle ids)
            kept taken resolved (by rw [← held]; exact opened) removal written
          rw [← shape] at removed
          rw [transition_unique step (Unifying.Transition.remove control removed)]
          show Tracks S (OrderedStore.publish ids ⟨taken, [], []⟩) after
          have contracted : OrderedStore.publish ids ⟨taken, [], []⟩ =
              OrderedStore.survivors ids taken := by simp [OrderedStore.publish]
          rw [contracted]
          exact tracks.remove removal written
      | nativeMatch control resolved opened scanned =>
          rw [call_keeps_state step control (by decide) (by decide) (by decide) (by decide)]
          show Tracks S (OrderedStore.publish ids ⟨[], _, []⟩) source.state
          rw [OrderedStore.reads_only]
          exact tracks
      | getAtoms control resolved opened =>
          rw [call_keeps_state step control (by decide) (by decide) (by decide) (by decide)]
          show Tracks S (OrderedStore.publish ids ⟨[], _, []⟩) source.state
          rw [OrderedStore.reads_only]
          exact tracks
      | writtenMatch control frames resolved opened scanned =>
          rw [return_keeps_state step control]
          show Tracks S (OrderedStore.publish ids ⟨[], _, []⟩) source.state
          rw [OrderedStore.reads_only]
          exact tracks
      | call control authored ordinary arity scanned =>
          rw [call_keeps_state step control (ne_of_unknown authored known_new_space)
            (ne_of_unknown authored known_add) (ne_of_unknown authored known_remove)
            (ne_of_unknown authored known_change_state)]
          show Tracks S (OrderedStore.publish ids ⟨[], _, []⟩) source.state
          rw [OrderedStore.reads_only]
          exact tracks
      | dynamicCall control resolved authored registered arity scanned =>
          rw [dynamic_keeps_state step control]
          show Tracks S (OrderedStore.publish ids ⟨[], _, []⟩) source.state
          rw [OrderedStore.reads_only]
          exact tracks
  | none =>
      simp only
      rcases transition_state registry step with same |
        ⟨bindings, index, location, pattern, answers, used, control, removed⟩ |
        ⟨bindings, head, index, held, answers, control, notRemove, applied⟩
      · rw [same]
        exact tracks
      · rcases removeRows_ok removed with same |
          ⟨handle, rows, first, rest, kept, resolved, opened, shape, survived, written⟩
        · rw [same]
          exact tracks
        · exfalso
          rw [tracks.rows handle rows opened, shape] at survived
          obtain ⟨keptIds, taken, removal, _⟩ :=
            PeTTaStoreSelection.source_selection S.label survived
          have prepared := removal.prepared S.label
          simp [ask, control, askCall, known_remove, shape, resolved, opened, prepared] at asked
      · by_cases isAdd : head = "add-atom"
        · subst isAdd
          exfalso
          rw [primitiveInputs_of_ne (by decide)] at applied
          obtain ⟨location, atom, handle, shape, resolved, inserted⟩ := apply_add_atom applied
          obtain ⟨before, opened, _⟩ := Effects.insert_reads_back inserted
          simp [ask, control, askCall, known_add, shape, resolved, opened] at asked
        · by_cases isNew : head = "new-space"
          · subst isNew
            rw [apply_new_space applied]
            exact tracks.allocate
          · by_cases isChange : head = "change-state!"
            · subst isChange
              obtain ⟨name, value, reached⟩ := apply_change_state applied
              rw [reached]
              exact tracks.putCell name value
            · rw [StdLib.successful_apply_state isNew isAdd notRemove isChange applied]
              exact tracks

/-! ## What a `match` goes on with is what it read -/

omit [DecidableEq O] in
/-- The answers of a `match` called with values are those of the scanned occurrences: the
template under each occurrence's unifier, in store order. -/
theorem scan_answers (label : O → Atom) (bindings : Subst) (pattern template : Atom)
    (use : Nat) (rows : List O) :
    Unifying.matchAnswers bindings pattern template use (rows.map label) =
      (scan label bindings pattern use rows).map fun packets =>
        packets.map fun row => (⟨resolve row.2 template, row.2⟩ : Unifying.Answer) := by
  induction rows generalizing use with
  | nil => rfl
  | cons occurrence rest ih =>
      simp only [List.map_cons, Unifying.matchAnswers, scan, ih]
      cases later : scan label bindings pattern (use + 1) rest with
      | none => simp
      | some packets =>
          cases matched : Unifying.unify bindings pattern
            (Unifying.rename use (label occurrence)) <;> simp

omit [DecidableEq O] in
/-- **A written `match` goes on with exactly the occurrences it reads**: the machine's next
configuration evaluates the body once under the unifier of each read occurrence, in store
order, and nothing else. -/
theorem written_match_continues {registry : SpaceSemantics.Program}
    {source : Unifying.Configuration} {ids : List O} (tracks : Tracks S ids source.state)
    {answer : Unifying.Answer} {pattern body : Atom} {later : List Unifying.Frame}
    {handle : Handle} {rows : List Atom} {packets : List (O × Subst)}
    (control : source.control = .returned [answer])
    (frames : source.frames = .query pattern body :: later)
    (resolved : Effects.readHandle answer.value = some handle)
    (opened : source.state.read handle = some rows)
    (scanned : scan S.label answer.bindings pattern source.uses (S.rowsAt handle ids) =
      some packets) :
    Unifying.Transition registry source
      { source with
        control := .sequence (continuations body packets) []
        frames := later
        uses := source.uses + (S.rowsAt handle ids).length } := by
  apply PeTTaQueryInterpretation.source_query_transition S.label registry source answer
    pattern body later (S.rowsAt handle ids) packets control frames ?_ scanned
  have same := tracks.rows handle rows opened
  simp [resolved, opened, same]

omit [DecidableEq O] in
/-- **A `match` called with values answers from exactly the occurrences it reads.** -/
theorem native_match_answers {registry : SpaceSemantics.Program}
    {source : Unifying.Configuration} {ids : List O} (tracks : Tracks S ids source.state)
    {bindings : Subst} {index : Nat} {location pattern template : Atom}
    {handle : Handle} {rows : List Atom} {packets : List (O × Subst)}
    (control : source.control =
      .arguments bindings (.function "match") [] [location, pattern, template] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (opened : source.state.read handle = some rows)
    (scanned : scan S.label bindings (resolve bindings pattern) source.uses
      (S.rowsAt handle ids) = some packets) :
    Unifying.Transition registry source
      { source with
        control := .returned (packets.map fun row =>
          ⟨resolve row.2 (resolve bindings template), row.2⟩)
        uses := source.uses + (S.rowsAt handle ids).length } := by
  apply Unifying.Transition.native_query control
  have same := tracks.rows handle rows opened
  simp [Unifying.matchCall, resolved, opened, same, scan_answers, scanned]

omit [DecidableEq O] in
/-- **`get-atoms` answers exactly the occurrences it reads**: the atoms of the occurrences
of its space, in store order, each copied for its own use. -/
theorem get_atoms_answers {registry : SpaceSemantics.Program}
    {source : Unifying.Configuration} {ids : List O} (tracks : Tracks S ids source.state)
    {bindings : Subst} {index : Nat} {location : Atom} {handle : Handle} {rows : List Atom}
    (control : source.control =
      .arguments bindings (.function "get-atoms") [] [location] index)
    (resolved : Effects.readHandle (resolve bindings location) = some handle)
    (opened : source.state.read handle = some rows) :
    Unifying.Transition registry source
      { source with
        control := .returned ((Unifying.copyTerms source.uses
          ((S.rowsAt handle ids).map S.label)).map fun value => ⟨value, bindings⟩)
        uses := source.uses + (S.rowsAt handle ids).length } := by
  have same := tracks.rows handle rows opened
  have step := Unifying.Transition.primitive (registry := registry) (source := source)
    (bindings := bindings) (head := "get-atoms") (index := index) (held := [location])
    (answers := (S.rowsAt handle ids).map S.label) (after := source.state) control
    (by decide) (by decide) (by decide) (by decide)
    (by simp [Unifying.primitiveInputs, resolved, opened, same])
  simpa [Unifying.primitiveOutputs, Unifying.primitiveUses, Unifying.primitiveCopies] using step

/-! ## What a call goes on with is what it read -/

/-- Selecting among two lists of equations selects among each, the second with the uses
after the first's. -/
theorem selections_append (bindings : Subst) (values : List Atom) :
    ∀ (use : Nat) (first second : List SpaceSemantics.Equation),
      Unifying.selections bindings values use (first ++ second) =
        (Unifying.selections bindings values (use + first.length) second).bind fun later =>
          (Unifying.selections bindings values use first).map fun earlier => earlier ++ later
  | use, [], second => by
      cases found : Unifying.selections bindings values use second <;>
        simp [Unifying.selections, found]
  | use, equation :: rest, second => by
      have ih := selections_append bindings values (use + 1) rest second
      have shift : use + (rest.length + 1) = use + 1 + rest.length := by omega
      simp only [List.cons_append, Unifying.selections, ih, List.length_cons, shift]
      cases Unifying.selections bindings values (use + 1 + rest.length) second with
      | none => simp
      | some later =>
          cases Unifying.selections bindings values (use + 1) rest with
          | none => simp
          | some others =>
              cases Unifying.unifyArguments bindings
                (equation.arguments.map (Unifying.rename use)) values <;> simp

omit [DecidableEq O] in
/-- Selecting among the equations of `head` held by rows is the scan of the rows: the
controls the machine goes on with are those of the occurrences the scan selects. -/
theorem selections_scan (label : O → Atom) (bindings : Subst) (head : String)
    (values : List Atom) :
    ∀ (use : Nat) (rows : List O),
      Unifying.selections bindings values use
        (Unifying.candidates ((rows.map label).filterMap LiveEquations.equationOfRow)
          head values.length) =
      (scanCall label bindings head values use rows).map fun packets => packets.map Prod.snd
  | _, [] => rfl
  | use, occurrence :: rest => by
      cases row : LiveEquations.equationOfRow (label occurrence) with
      | none =>
          have ih := selections_scan label bindings head values use rest
          simpa only [List.map_cons, List.filterMap_cons, row, scanCall] using ih
      | some equation =>
          by_cases fits : (equation.head == head &&
              equation.arguments.length == values.length) = true
          · have ih := selections_scan label bindings head values (use + 1) rest
            simp only [Unifying.candidates] at ih
            simp only [List.map_cons, List.filterMap_cons, row, scanCall, Unifying.candidates,
              List.filter_cons, fits, if_true, Unifying.selections, ih]
            cases scanCall label bindings head values (use + 1) rest with
            | none => simp
            | some later =>
                cases Unifying.unifyArguments bindings
                  (equation.arguments.map (Unifying.rename use)) values <;> simp
          · have ih := selections_scan label bindings head values use rest
            simp only [Unifying.candidates] at ih
            simp only [List.map_cons, List.filterMap_cons, row, scanCall, Unifying.candidates,
              List.filter_cons, fits, if_false, Bool.false_eq_true, ih]

omit [DecidableEq O] in
/-- **A call of an authored function goes on with exactly the equations it reads**: the
bodies of the privately installed clauses that its values select, then, in store order,
the body of each equation occurrence of the program's own space that the scan selects,
each under its own unifier, and nothing else. -/
theorem call_continues {registry : SpaceSemantics.Program}
    {source : Unifying.Configuration} {ids : List O} (tracks : Tracks S ids source.state)
    {bindings : Subst} {index : Nat} {head : String} {held : List Atom}
    {fromPrivate : List Unifying.Control} {packets : List (O × Unifying.Control)}
    (control : source.control = .arguments bindings (.function head) [] held index)
    (authored : StdLib.known head = false) (ordinary : Eval.ioHead head = false)
    (arity : (held.map (resolve bindings)).length ∈
      Eval.arities (Unifying.codeRegistry registry source.privateCode) head)
    (privately : Unifying.selections bindings (held.map (resolve bindings)) source.uses
      (Unifying.candidates source.privateCode head (held.map (resolve bindings)).length) =
        some fromPrivate)
    (scanned : scanCall S.label bindings head (held.map (resolve bindings))
      (source.uses + (Unifying.candidates source.privateCode head
        (held.map (resolve bindings)).length).length)
      (S.rowsAt .self ids) = some packets) :
    Unifying.Transition registry source
      { source with
        control := .sequence (fromPrivate ++ packets.map Prod.snd) []
        uses := source.uses + (Unifying.candidates
          (Unifying.codeEquations source.state source.privateCode) head
          (held.map (resolve bindings)).length).length } := by
  apply Unifying.Transition.equations control ordinary (ne_of_unknown authored known_remove)
    authored
  have live : LiveEquations.liveEquations source.state =
      ((S.rowsAt .self ids).map S.label).filterMap LiveEquations.equationOfRow := by
    unfold LiveEquations.liveEquations
    rw [show source.state.core = (S.rowsAt .self ids).map S.label from
      tracks.rows .self _ rfl]
  have split : Unifying.candidates (Unifying.codeEquations source.state source.privateCode)
      head (held.map (resolve bindings)).length =
        Unifying.candidates source.privateCode head (held.map (resolve bindings)).length ++
          Unifying.candidates (LiveEquations.liveEquations source.state) head
            (held.map (resolve bindings)).length := by
    simp only [Unifying.candidates, Unifying.codeEquations, List.filter_append]
  have selected : Unifying.selections bindings (held.map (resolve bindings)) source.uses
      (Unifying.candidates (Unifying.codeEquations source.state source.privateCode) head
        (held.map (resolve bindings)).length) = some (fromPrivate ++ packets.map Prod.snd) := by
    rw [split, selections_append, live, selections_scan, scanned, privately]
    rfl
  unfold Unifying.application
  rw [if_pos arity]
  simp only [selected, Option.map_some]

/-! ## Along an evaluation of the streaming machine -/

/-- The configuration of the unifying machine that the streaming machine's next step runs,
when that step is one of the unifying machine's: an ordinary phase of the task in front, or
the return of the front task's first answer to the frame that waits for it. -/
def source? (state : Streaming.State) : Option Unifying.Configuration :=
  match state.agenda with
  | .execute task :: _ =>
      if Streaming.phaseControl task.control then
        some (state.world.configuration task.control)
      else
        match task.control, task.frames with
        | .returned (answer :: _), .source frame :: _ =>
            some (state.world.configuration (.returned [answer]) [frame])
        | _, _ => none
  | _ => none

variable (S)

/-- The request the streaming machine's next step makes of the occurrences. -/
def askStream (registry : SpaceSemantics.Program) (ids : List O) (state : Streaming.State) :
    Option (OrderedStore.Publication Atom O) :=
  (source? state).bind (ask S registry ids)

/-- The occurrences after the streaming machine's next step. -/
def publishedStream (registry : SpaceSemantics.Program) (ids : List O)
    (state : Streaming.State) : List O :=
  match askStream S registry ids state with
  | none => ids
  | some request => OrderedStore.publish ids request.selection

/-- The requests of the first `fuel` steps of the streaming machine, in order. The
occurrences are published as the steps are taken. -/
def requests (registry : SpaceSemantics.Program) :
    Nat → Streaming.State → List O → List (OrderedStore.Publication Atom O)
  | 0, _, _ => []
  | fuel + 1, state, ids =>
      match Streaming.step registry state with
      | none => []
      | some next =>
          match askStream S registry ids state with
          | none => requests registry fuel next ids
          | some request =>
              request :: requests registry fuel next (OrderedStore.publish ids request.selection)

variable {S}

theorem publishedStream_of_source {registry : SpaceSemantics.Program} {ids : List O}
    {state : Streaming.State}
    {source : Unifying.Configuration} (found : source? state = some source) :
    publishedStream S registry ids state = published S registry ids source := by
  simp [publishedStream, askStream, found, published]

theorem publishedStream_of_none {registry : SpaceSemantics.Program} {ids : List O}
    {state : Streaming.State}
    (found : source? state = none) : publishedStream S registry ids state = ids := by
  simp [publishedStream, askStream, found]

/-- A step of the unifying machine inside a step of the streaming machine. -/
theorem stream_source_tracks {registry : SpaceSemantics.Program} {before : Streaming.State}
    {ids : List O} {source reached : Unifying.Configuration}
    (tracks : Tracks S ids before.world.state)
    (transition : Unifying.Transition registry source reached)
    (found : source? before = some source) (same : source.state = before.world.state) :
    Tracks S (publishedStream S registry ids before) reached.state := by
  rw [publishedStream_of_source found]
  exact transition_tracks (same ▸ tracks) transition

/-- **A step of the streaming machine and its request.** After any step, the occurrences
published by the step's request track the world's store. -/
theorem stream_tracks {registry : SpaceSemantics.Program} {before after : Streaming.State}
    {ids : List O} (tracks : Tracks S ids before.world.state)
    (taken : Streaming.Transition registry before after) :
    Tracks S (publishedStream S registry ids before) after.world.state := by
  cases taken with
  | collection_done agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda])]
      exact tracks
  | handler_done agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda])]
      exact tracks
  | first_done agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda])]
      exact tracks
  | empty agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
      exact tracks
  | alternatives agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
      exact tracks
  | collection_enter agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
      exact tracks
  | first_enter agenda =>
      rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
      exact tracks
  | caught agenda handler closed =>
      rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
      exact tracks
  | answer agenda delivered =>
      cases delivered with
      | root =>
          rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
          exact tracks
      | source transition placed =>
          rw [placed.world]
          exact stream_source_tracks tracks transition
            (by simp [source?, agenda, Streaming.phaseControl]) rfl
      | collection changed =>
          rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
          exact tracks
      | handler =>
          rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
          exact tracks
      | first found =>
          rw [publishedStream_of_none (by simp [source?, agenda, Streaming.phaseControl])]
          exact tracks
  | phase agenda ordinary transition placed =>
      rw [placed.world]
      exact stream_source_tracks tracks transition (by simp [source?, agenda, ordinary]) rfl

/-- Every request of the streaming machine is admitted by the ordered-store step. -/
theorem askStream_admitted {registry : SpaceSemantics.Program} {ids : List O}
    {state : Streaming.State}
    {request : OrderedStore.Publication Atom O} (unique : ids.Nodup)
    (asked : askStream S registry ids state = some request) (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    (OrderedStore.step atomFrames PUnit.unit S.label).Admits (s := (knowledge, ids)) request := by
  obtain ⟨source, _, made⟩ := Option.bind_eq_some_iff.mp asked
  exact asked_admitted unique (asked_of_ask made) knowledge consistent

/-- **The store effects of a PeTTa evaluation are one run of the ordered-store step.** For
any number of steps of the streaming machine, from occurrences that track its world's
store, there is one run of the step whose word is exactly the requests of those steps in
order, whose knowledge is the knowledge it started with, and whose last occurrences track
the store the machine reached. -/
theorem streaming_store_run (registry : SpaceSemantics.Program)
    (knowledge : EquationStore Atom)
    (consistent : atomFrames.Solvable (a := PUnit.unit) knowledge) :
    ∀ (fuel : Nat) (state : Streaming.State) (ids : List O),
      Tracks S ids state.world.state →
      ∃ run : (OrderedStore.step atomFrames PUnit.unit S.label).Run (knowledge, ids),
        run.word.map (fun firing => (firing.2 : OrderedStore.Publication Atom O)) =
          requests S registry fuel state ids ∧
        run.last.1 = knowledge ∧
        Tracks S run.last.2 (Streaming.advance registry fuel state).world.state
  | 0, state, ids, tracks => ⟨.nil _, rfl, rfl, tracks⟩
  | fuel + 1, state, ids, tracks => by
      cases stepped : Streaming.step registry state with
      | none =>
          have stays : Streaming.advance registry (fuel + 1) state = state := by
            simp [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run, stepped]
          refine ⟨.nil _, ?_, rfl, ?_⟩
          · simp [requests, stepped, Step.Run.word]
          · rw [stays]
            exact tracks
      | some next =>
          have taken := Streaming.transition_of_computed registry state next stepped
          have tracked := stream_tracks tracks taken
          have advanced : Streaming.advance registry (fuel + 1) state =
              Streaming.advance registry fuel next := by
            simp [Streaming.advance, Mettapedia.Machines.BoundedDeterministicRun.run, stepped]
          cases asked : askStream S registry ids state with
          | none =>
              simp only [publishedStream, asked] at tracked
              obtain ⟨run, word, kept, last⟩ :=
                streaming_store_run registry knowledge consistent fuel next ids tracked
              refine ⟨run, ?_, kept, ?_⟩
              · simp [requests, stepped, asked, word]
              · rw [advanced]
                exact last
          | some request =>
              simp only [publishedStream, asked] at tracked
              have admitted := askStream_admitted tracks.distinct asked knowledge consistent
              obtain ⟨run, word, kept, last⟩ :=
                streaming_store_run registry knowledge consistent fuel next
                  (OrderedStore.publish ids request.selection) tracked
              refine ⟨.cons request admitted run, ?_, kept, ?_⟩
              · simp only [requests, stepped, asked, Step.Run.word, List.map_cons]
                exact congrArg (List.cons request) word
              · rw [advanced]
                exact last

/-! ## A supply of occurrences, and the start of an evaluation -/

/-- An occurrence as its number in order of making, its space and its atom. -/
structure Row where
  serial : Nat
  place : Handle
  atom : Atom
  deriving DecidableEq

/-- A number above every number in use. -/
def Row.next (ids : List Row) : Nat := (ids.map Row.serial).foldr max 0 + 1

theorem Row.serial_lt_next : ∀ (ids : List Row) (row : Row), row ∈ ids →
    row.serial < Row.next ids
  | first :: rest, row, member => by
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
      · exact Nat.lt_of_lt_of_le (Row.serial_lt_next rest row later)
          (Nat.succ_le_succ (Nat.le_max_right _ _))

/-- Numbered occurrences are a supply: the new one takes the next number. -/
def rowSupply : Supply Row where
  label := Row.atom
  place := Row.place
  fresh ids handle atom := ⟨Row.next ids, handle, atom⟩
  fresh_new ids _ _ member := Nat.lt_irrefl _ (Row.serial_lt_next ids _ member)
  label_fresh _ _ _ := rfl
  place_fresh _ _ _ := rfl

/-- The rows of a program's own space as occurrences, numbered from `serial`. -/
def Row.load : Nat → List Atom → List Row
  | _, [] => []
  | serial, atom :: rest => ⟨serial, .self, atom⟩ :: Row.load (serial + 1) rest

theorem Row.load_serial : ∀ (serial : Nat) (atoms : List Atom) (row : Row),
    row ∈ Row.load serial atoms → serial ≤ row.serial ∧ row.place = .self
  | serial, atom :: rest, row, member => by
      rcases List.mem_cons.mp member with same | later
      · subst same
        exact ⟨Nat.le_refl _, rfl⟩
      · have found := Row.load_serial (serial + 1) rest row later
        exact ⟨Nat.le_of_succ_le found.1, found.2⟩

theorem Row.load_nodup : ∀ (serial : Nat) (atoms : List Atom), (Row.load serial atoms).Nodup
  | _, [] => List.nodup_nil
  | serial, atom :: rest => by
      refine List.nodup_cons.mpr ⟨?_, Row.load_nodup (serial + 1) rest⟩
      intro member
      exact Nat.lt_irrefl _ (Row.load_serial (serial + 1) rest _ member).1

theorem Row.load_atoms : ∀ (serial : Nat) (atoms : List Atom),
    (Row.load serial atoms).map Row.atom = atoms
  | _, [] => rfl
  | serial, atom :: rest => congrArg (List.cons atom) (Row.load_atoms (serial + 1) rest)

/-- **A store with only the program's own space is tracked by its rows in order.** -/
theorem tracks_load (core : List Atom) :
    Tracks rowSupply (Row.load 0 core) (NamedSpaces.Store.new core []) := by
  refine ⟨Row.load_nodup 0 core, ?_, ?_⟩
  · intro handle rows opened
    cases handle with
    | self =>
        have all : rowSupply.rowsAt .self (Row.load 0 core) = Row.load 0 core := by
          apply List.filter_eq_self.mpr
          intro row member
          exact decide_eq_true (Row.load_serial 0 core row member).2
        rw [all]
        have : rows = core := (Option.some.inj opened).symm
        rw [this]
        exact (Row.load_atoms 0 core).symm
    | privateSpace index =>
        simp [NamedSpaces.Store.new, NamedSpaces.Store.read] at opened
  · intro row member
    have here : rowSupply.place row = .self := (Row.load_serial 0 core row member).2
    rw [here]
    rfl

/-- No knowledge is consistent knowledge. -/
theorem solvable_nil : atomFrames.Solvable (a := PUnit.unit) ([] : EquationStore Atom) :=
  ⟨PUnit.unit, atomFrames.id PUnit.unit, fun _ member => nomatch member⟩

/-- **The store effects of evaluating an expression against a loaded program are one run
of the ordered-store step**, from the program's rows and no knowledge: its word is the
evaluation's requests, and its last occurrences track the store the evaluation reached. -/
theorem evaluation_store_run (registry program : SpaceSemantics.Program) (expression : Atom)
    (fuel : Nat) :
    ∃ run : (OrderedStore.step atomFrames PUnit.unit rowSupply.label).Run
        (([] : EquationStore Atom), Row.load 0 (SpaceSemantics.loadedAtoms program)),
      run.word.map (fun firing => (firing.2 : OrderedStore.Publication Atom Row)) =
        requests rowSupply registry fuel
          (Streaming.enter { state := Effects.loaded program } expression)
          (Row.load 0 (SpaceSemantics.loadedAtoms program)) ∧
      run.last.1 = [] ∧
      Tracks rowSupply run.last.2
        (Streaming.advance registry fuel
          (Streaming.enter { state := Effects.loaded program } expression)).world.state :=
  streaming_store_run registry [] solvable_nil fuel _ _
    (tracks_load (SpaceSemantics.loadedAtoms program))

/-! ## Examples -/

namespace Controls

def p (value : Atom) : Atom := .expression [.symbol "p", value]
def a : Atom := .symbol "a"
def b : Atom := .symbol "b"
def q : Atom := .symbol "q"

/-- A registry with no function. -/
def registry : SpaceSemantics.Program := { equations := [], declarations := [] }

/-- A store whose own space holds `(p a)`, `q`, `(p b)`. -/
def store : Effects.State := NamedSpaces.Store.new [p a, q, p b] []
def ids : List Row := Row.load 0 [p a, q, p b]

/-- What a request takes, reads and makes. -/
def shape (request : OrderedStore.Publication Atom Row) : List Row × List Row × List Row :=
  (request.selection.taken, request.selection.read, request.selection.made)

/-- The occurrences track the store. -/
theorem ids_track : Tracks rowSupply ids store := tracks_load _

/-- Negative: no occurrences do not track a store that has rows. -/
theorem nothing_does_not_track : ¬ Tracks rowSupply [] store := by
  intro tracks
  have rows := tracks.rows .self [p a, q, p b] rfl
  simp [Supply.rowsAt] at rows

/-- `add-atom` makes one new occurrence in the space, with the next number. -/
theorem adding_makes :
    (ask rowSupply registry ids
      { state := store
        control := .arguments [] (.function "add-atom") [] [.symbol "&self", p q] 0 }).map shape =
      some ([], [], [⟨3, .self, p q⟩]) := by
  decide

/-- `remove-atom` takes the occurrences whose atoms unify with its pattern, and no other. -/
theorem removing_takes :
    (ask rowSupply registry ids
      { state := store
        control := .arguments [] (.function "remove-atom") []
          [.symbol "&self", p (.var "x")] 0 }).map shape =
      some ([⟨0, .self, p a⟩, ⟨2, .self, p b⟩], [], []) := by
  decide

/-- A written `match` reads the occurrences whose atoms unify with its pattern, when the
value of its space has returned. -/
theorem matching_reads :
    (ask rowSupply registry ids
      { state := store
        control := .returned [⟨.symbol "&self", []⟩]
        frames := [.query (p (.var "x")) (.var "x")] }).map shape =
      some ([], [⟨0, .self, p a⟩, ⟨2, .self, p b⟩], []) := by
  decide

/-- Negative: `add-atom` to something that is not a space asks nothing of the store. -/
theorem adding_nowhere_asks_nothing :
    (ask rowSupply registry ids
      { state := store
        control := .arguments [] (.function "add-atom") [] [.symbol "nowhere", p q] 0 }).map shape =
      none := by
  decide

/-- Negative: a call that does not touch a space asks nothing of the store. -/
theorem arithmetic_asks_nothing :
    (ask rowSupply registry ids
      { state := store
        control := .arguments [] (.function "+") []
          [.grounded (.int 1), .grounded (.int 2)] 0 }).map shape = none := by
  decide

/-! ### Whole evaluations -/

def r (value : Atom) : Atom := .expression [.symbol "r", value]

/-- `(add-atom &self (p q))`. -/
def addOne : Atom := .expression [.symbol "add-atom", .symbol "&self", p q]

/-- `(let $x (match &self (p $y) $y) (add-atom &self (r $x)))`. -/
def addEach : Atom :=
  .expression [.symbol "let", .var "x",
    .expression [.symbol "match", .symbol "&self", p (.var "y"), .var "y"],
    .expression [.symbol "add-atom", .symbol "&self", r (.var "x")]]

/-- `(remove-atom &self (p $y))`. -/
def removeEach : Atom := .expression [.symbol "remove-atom", .symbol "&self", p (.var "y")]

/-- `(+ 1 2)`. -/
def sum : Atom := .expression [.symbol "+", .grounded (.int 1), .grounded (.int 2)]

/-- Evaluating one `add-atom` is a word of one make. -/
theorem addOne_requests :
    (requests rowSupply registry 30 (Streaming.enter { state := store } addOne) ids).map shape =
      [([], [], [⟨3, .self, p q⟩])] := by
  decide +kernel

/-- A `match` with two answers, each feeding an `add-atom`: the word is one read of the two
matching occurrences and then one make per answer. Both rows are stored, in one run, though
the two answers bind `$x` differently: the store is shared by the alternatives, their
bindings are not. -/
theorem addEach_requests :
    (requests rowSupply registry 60 (Streaming.enter { state := store } addEach) ids).map shape =
      [([], [⟨0, .self, p a⟩, ⟨2, .self, p b⟩], []),
       ([], [], [⟨3, .self, r a⟩]),
       ([], [], [⟨4, .self, r b⟩])] := by
  decide +kernel

/-- That evaluation completes, and its store is the rows of the run's last occurrences. -/
theorem addEach_store :
    (Streaming.advance registry 60 (Streaming.enter { state := store } addEach)).agenda = [] ∧
    (Streaming.advance registry 60 (Streaming.enter { state := store } addEach)).world.state.core =
      [p a, q, p b, r a, r b] := by
  decide +kernel

/-- Evaluating a `remove-atom` is a word of one take of the matching occurrences. -/
theorem removeEach_requests :
    (requests rowSupply registry 30 (Streaming.enter { state := store } removeEach) ids).map
        shape =
      [([⟨0, .self, p a⟩, ⟨2, .self, p b⟩], [], [])] := by
  decide +kernel

/-- Negative: an evaluation that touches no space has the empty word. -/
theorem sum_requests :
    requests rowSupply registry 30 (Streaming.enter { state := store } sum) ids = [] := by
  decide +kernel

/-- Negative: with no steps taken the word is empty, whatever the expression. The word is
the requests of the steps taken, not of the expression. -/
theorem no_steps_no_requests :
    requests rowSupply registry 0 (Streaming.enter { state := store } addOne) ids = [] := rfl

/-! ### A call reads its equation -/

/-- `(= (double $x) (+ $x $x))` as a stored row. -/
def doubleEquation : Atom :=
  .expression [.symbol "=", .expression [.symbol "double", .var "x"],
    .expression [.symbol "+", .var "x", .var "x"]]

/-- The registry of a program with that one function. -/
def doubling : SpaceSemantics.Program :=
  { equations := [⟨"double", [.var "x"], .expression [.symbol "+", .var "x", .var "x"]⟩],
    declarations := [] }

def codeStore : Effects.State := NamedSpaces.Store.new [p a, doubleEquation] []
def codeIds : List Row := Row.load 0 [p a, doubleEquation]

/-- `(double 4)`. -/
def callDouble : Atom := .expression [.symbol "double", .grounded (.int 4)]

/-- `(triple 4)`. -/
def callTriple : Atom := .expression [.symbol "triple", .grounded (.int 4)]

/-- Evaluating a call of a stored equation is a word of one read of the equation's row,
and the evaluation answers with the equation's body. -/
theorem callDouble_requests :
    (requests rowSupply doubling 30 (Streaming.enter { state := codeStore } callDouble)
        codeIds).map shape = [([], [⟨1, .self, doubleEquation⟩], [])] ∧
    Streaming.values (Streaming.advance doubling 30
      (Streaming.enter { state := codeStore } callDouble)) = [.grounded (.int 8)] := by
  decide +kernel

/-- Negative: a call of a name with no equation asks nothing and is data. -/
theorem callTriple_requests :
    requests rowSupply doubling 30 (Streaming.enter { state := codeStore } callTriple)
        codeIds = [] ∧
    Streaming.values (Streaming.advance doubling 30
      (Streaming.enter { state := codeStore } callTriple)) = [callTriple] := by
  decide +kernel

end Controls

end Mettapedia.Languages.MeTTa.PeTTa.RunsAsFirings
