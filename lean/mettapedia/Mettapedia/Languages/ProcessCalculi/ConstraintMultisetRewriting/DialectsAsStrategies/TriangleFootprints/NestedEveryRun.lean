import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.EveryRun
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints.NestedArguments

/-!
# Nested ground arguments: every complete run of HE publishes PeTTa's answers

`NestedArguments.nested_agree` builds one run of HE's machine for `(f t₁ … tₙ)` and shows it
publishes PeTTa's answers. Here every complete run is covered, by the route of `EveryRun`: a
complete run is a derivation of HE's completed relation (`EveryRun.complete_source`), and that
relation determines the atoms on nested calls.

* `tuple_rows`: HE's tuple of `t₁ … tₙ` returns one row per combination of the arguments' answers,
  in lexicographic order (the first argument varying slowest), whatever frames its casts and
  queries reach;
* `calls_rows`: the calls continuation queries each row in turn;
* `query_absent`, `query_equations`: the query of `(f v₁ … vₙ)` on any call value, under any
  activation, returns the call itself when the region is empty and the bodies' answers otherwise;
* `nested_determined`: compositionally, a nested call's answers are determined by its arguments'
  answers and the queries of its combinations;
* `nested_every_run`: every complete run of HE from the entry configuration of a nested call
  publishes exactly the values of PeTTa's streaming run from some fuel on.

## Controls

* `Controls.coin_settled`, `Controls.flip_query`: `(coin)` and `(flip heads)`, `(flip tails)` are
  determined.
* `Controls.flip_coin_every_run` (positive): every complete run of `(flip (coin))` publishes
  `tails`, `heads`.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints

namespace NestedEveryRun

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE (Space isErrorAtom)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Steps (EquationWork)
open Mettapedia.Languages.MeTTa.HE.Spec.Eval.Completed (Policy Result CastLookup Frame)
open Mettapedia.Languages.MeTTa.HE.RecursiveMachine.Contextual (load observe)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.ProcessCalculi.MORK (isGroundAtom)
open ServiceFootprints EntryToQuery AnswerBags EveryRun NestedArguments

variable {dispatch : GroundedDispatch} {policy : Policy}

/-! ## Determined terms and queries -/

/-- `t` has answerable answers `L`, and HE's source semantics determines them. -/
def Settled (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom) (t : Atom)
    (L : List Atom) : Prop :=
  (∀ a ∈ L, Answerable a) ∧ Determined dispatch policy atoms t L

/-- **HE's query of `(f v₁ … vₙ)` is determined**: on every call value whose atom is the call, under
any live list, scope and activation, every derivation of HE's call relation returns a batch whose
atoms are `A`. -/
def QueryDetermined (dispatch : GroundedDispatch) (policy : Policy) (atoms : List Atom)
    (f : String) (vals : List Atom) (A : List Atom) : Prop :=
  ∀ (live : List Atom) (scope : List String) (value : Entry.Value) (frame : Frame)
    (children : List Result), value.erase = .expression (.symbol f :: vals) →
    Completed.CallRel (Space.ofList atoms) dispatch Completed.rawLookup live scope value
      Atom.undefinedType frame children (policy := policy) →
    children.map (fun r => r.1.erase) = A

theorem data_settled {atoms : List Atom} {d : Atom} (data : DataAtom d) :
    Settled dispatch policy atoms d [d] :=
  ⟨fun a member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data data,
    fun _ _ _ _ derived => by
      obtain ⟨after, rfl⟩ := data_source raw_contract data derived
      simp⟩

theorem data_determined_bodies (atoms : List Atom) :
    ∀ (bodies : List Atom), (∀ b ∈ bodies, DataAtom b ∧ b ≠ Atom.notReducible) →
      List.Forall₂ (fun b L => Determined dispatch policy atoms b L ∧ BodyFacts b) bodies
        (bodies.map fun b => [b])
  | [], _ => .nil
  | b :: rest, each => by
      obtain ⟨data, notRefused⟩ := each b List.mem_cons_self
      exact .cons ⟨(data_settled data).2,
          settles_facts (Settles.data (dispatch := dispatch) (atoms := atoms) data notRefused)⟩
        (data_determined_bodies atoms rest fun b member => each b (List.mem_cons_of_mem _ member))

/-- The query of a call of answerable values: the call itself with an empty region, the bodies'
derivations otherwise. -/
theorem query_cases {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (valsClean : ∀ v ∈ vals, Answerable v)
    (fixed : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b)
    {live : List Atom} {scope : List String} {value : Entry.Value} {frame : Frame}
    {children : List Result} (erased : value.erase = .expression (.symbol f :: vals))
    (called : Completed.CallRel (Space.ofList atoms) dispatch Completed.rawLookup live scope value
      Atom.undefinedType frame children (policy := policy)) :
    (children = [(value, frame)] ∧ regionBodies atoms f vals = []) ∨
      ∃ works : List EquationWork, works ≠ [] ∧
        works.map EquationWork.body = regionBodies atoms f vals ∧
        Completed.EquationBodiesRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
          value Atom.undefinedType frame works children (policy := policy) := by
  have ground : ∀ v ∈ vals,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.TypeSubst.typeVars v = [] :=
    fun v member => HERuns.ground_typeVars (valsClean v member)
  cases called with
  | error failed => exact absurd failed (HERuns.value_not_error head erased)
  | embedded _ _ instruction _ _ =>
      rw [erased, notInstruction] at instruction
      cases instruction
  | absent _ _ frontier =>
      rw [erased] at frontier
      exact Or.inl ⟨rfl,
        (HERuns.frontier_bodies ground frame.certified.satisfiable program fixed frontier).symm⟩
  | equations _ _ frontier nonempty bodies =>
      rw [erased] at frontier
      exact Or.inr ⟨_, nonempty,
        HERuns.frontier_bodies ground frame.certified.satisfiable program fixed frontier, bodies⟩

/-- **A query with an empty region returns the call.** -/
theorem query_absent {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (valsClean : ∀ v ∈ vals, Answerable v) (empty : regionBodies atoms f vals = []) :
    QueryDetermined dispatch policy atoms f vals [.expression (.symbol f :: vals)] := by
  intro live scope value frame children erased called
  rcases query_cases program head notInstruction valsClean
      (by rw [empty]; intro b member; cases member) erased called with
    ⟨rfl, _⟩ | ⟨works, nonemptyWorks, bodies, _⟩
  · simp [erased]
  · rw [empty] at bodies
    exact absurd (List.map_eq_nil_iff.mp bodies) nonemptyWorks

/-- **A query with a nonempty region returns its bodies' answers**, in row order. -/
theorem query_equations {atoms : List Atom}
    (program : ∀ row ∈ atoms, RegionsWithVariables.ConsFreeHeads row) {f : String}
    {vals : List Atom} (head : DataAtom (.symbol f))
    (notInstruction : Minimal.embeddedInstruction (.expression (.symbol f :: vals)) = false)
    (valsClean : ∀ v ∈ vals, Answerable v) {Ls : List (List Atom)}
    (bodies : List.Forall₂ (fun b L => Determined dispatch policy atoms b L ∧ BodyFacts b)
      (regionBodies atoms f vals) Ls)
    (nonempty : regionBodies atoms f vals ≠ []) :
    QueryDetermined dispatch policy atoms f vals Ls.flatten := by
  have fixed : ∀ b ∈ regionBodies atoms f vals, ∀ rename : String → String,
      Mettapedia.Languages.MeTTa.HE.Spec.Type.RuntimeRefinement.renameTypeVars rename b = b := by
    intro b member
    obtain ⟨L, both⟩ := forall₂_left_exists bodies b member
    exact both.2.fixed
  intro live scope value frame children erased called
  rcases query_cases program head notInstruction valsClean fixed erased called with
    ⟨_, empty⟩ | ⟨works, _, workBodies, equations⟩
  · exact absurd empty nonempty
  · have onWorks : List.Forall₂
        (fun w L => Determined dispatch policy atoms w.body L ∧ BodyFacts w.body) works Ls := by
      have onBodies := bodies
      rw [← workBodies] at onBodies
      exact List.forall₂_map_left_iff.mp onBodies
    exact bodies_source works Ls onWorks equations

/-! ## The argument product -/

/-- A row of HE's tuple: an expression value whose atom is `(v₁ … vₙ)`, `n ≥ 1`, all answerable. -/
def CleanRow (r : Result) (vals : List Atom) : Prop :=
  (∃ children : List Entry.Value, r.1 = .expression .active children) ∧
    r.1.erase = .expression vals ∧ vals ≠ [] ∧ ∀ a ∈ vals, Answerable a

theorem forall₂_append {α β : Type} {R : α → β → Prop} :
    ∀ {l₁ l₂ : List α} {r₁ r₂ : List β}, List.Forall₂ R l₁ r₁ → List.Forall₂ R l₂ r₂ →
      List.Forall₂ R (l₁ ++ l₂) (r₁ ++ r₂)
  | _, _, _, _, .nil, second => second
  | _, _, _, _, .cons here rest, second => .cons here (forall₂_append rest second)

theorem singleton_rows : ∀ {heads : List Result},
    (∀ h ∈ heads, Answerable h.1.erase) →
    List.Forall₂ CleanRow (heads.map Completed.tupleSingleton) (heads.map fun h => [h.1.erase])
  | [], _ => .nil
  | h :: hs, clean => by
      have here := clean h List.mem_cons_self
      refine .cons ?_ (singleton_rows fun r member => clean r (List.mem_cons_of_mem _ member))
      have unfolded : Completed.tupleSingleton h = (.expression .active [h.1], h.2) := by
        unfold Completed.tupleSingleton
        simp [HENested.emptyOrError_false here]
      rw [unfolded]
      refine ⟨⟨_, rfl⟩, by simp [Entry.Value.erase], List.cons_ne_nil _ _, ?_⟩
      intro a member
      rw [List.mem_singleton] at member
      subst member
      exact here

theorem prepend_row (head : Entry.Value) (headClean : Answerable head.erase) {r : Result}
    {vals : List Atom} (row : CleanRow r vals) :
    CleanRow (Completed.tuplePrepend head r) (head.erase :: vals) := by
  obtain ⟨⟨children, shape⟩, erased, nonempty, clean⟩ := row
  obtain ⟨c0, cs, rfl⟩ := List.exists_cons_of_ne_nil nonempty
  obtain ⟨value, rerased⟩ :=
    HENested.tuplePrepend_erase head shape erased (clean c0 List.mem_cons_self)
  refine ⟨⟨_, value⟩, rerased, List.cons_ne_nil _ _, ?_⟩
  intro a member
  rcases List.mem_cons.mp member with rfl | inner
  · exact headClean
  · exact clean a inner

/-- **The branches of a tuple's head**: for each answer of the head, in order, the rows of the rest
of the tuple with that answer in front. -/
theorem branches_rows {atoms : List Atom} {live : List Atom} {scope : List String}
    {tail : List Entry.Value} {Ls : List (List Atom)}
    (tupleRows : ∀ (live : List Atom) (frame : Frame) (results : List Result),
      Completed.TupleRel (Space.ofList atoms) dispatch Completed.rawLookup live scope tail frame
        results (policy := policy) → List.Forall₂ CleanRow results (combos Ls)) :
    ∀ (heads results : List Result), (∀ h ∈ heads, Answerable h.1.erase) →
      Completed.TupleBranchesRel (Space.ofList atoms) dispatch Completed.rawLookup live scope tail
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
          refine forall₂_append ?_ (branches_rows tupleRows hs _
            (fun r member => clean r (List.mem_cons_of_mem _ member)) rest)
          rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff]
          exact (tupleRows _ _ _ children).imp fun _ _ row =>
            prepend_row h.1 (clean h List.mem_cons_self) row

theorem flatMap_heads {heads : List Result} {L : List Atom}
    (erased : heads.map (fun r => r.1.erase) = L) (Ls : List (List Atom)) :
    (heads.flatMap fun h => (combos Ls).map (h.1.erase :: ·)) = combos (L :: Ls) := by
  subst erased
  simp only [combos, List.flatMap_map]

/-- **HE's tuple of the arguments returns one row per combination of their answers**, in
lexicographic order, whatever frames the casts and queries reach. -/
theorem tuple_rows {atoms : List Atom} {scope : List String} :
    ∀ (ts : List Atom) (Ls : List (List Atom)), List.Forall₂ (Settled dispatch policy atoms) ts Ls →
      ts ≠ [] → ∀ (live : List Atom) (frame : Frame) (results : List Result),
        Completed.TupleRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
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
          have rows := branches_rows
            (fun live' frame' results' tupled =>
              tuple_rows (t2 :: rest) Ls' restRel (List.cons_ne_nil _ _) live' frame' results' tupled)
            _ _ (HENested.clean_of_erase erased clean) branches
          rwa [flatMap_heads erased] at rows

/-- **The calls continuation over the rows**: each row's call value is queried in turn, and the
batches are concatenated in row order. -/
theorem calls_rows {atoms : List Atom} {live : List Atom} {scope : List String} {f : String}
    {Q : List Atom → List Atom} :
    ∀ (rows : List Result) (cs : List (List Atom)) (raw : List Result),
      List.Forall₂ (fun r vals => r.1.erase = .expression (.symbol f :: vals)) rows cs →
      (∀ vals ∈ cs, QueryDetermined dispatch policy atoms f vals (Q vals)) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
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
            calls_rows rs cs' _ rest (fun v member => queries v (List.mem_cons_of_mem _ member))
              later, List.flatMap_cons]

theorem publish_erase (policy : Policy) (original : Atom) (selected : List Result) :
    (selected.map (Completed.publishResult policy original)).map (fun r => r.1.erase) =
      selected.map (fun r => r.1.erase) := by
  simp [Completed.publishResult]

/-! ## Nested calls -/

/-- **Nested calls are determined, compositionally.** If each argument `tᵢ` is determined with
answerable answers `Lᵢ`, and the query of `f` on every combination `vals` of argument answers is
determined with answerable answers `Q vals`, then every derivation for `(f t₁ … tₙ)` returns the
concatenation of `Q` over the combinations, the first argument varying slowest. -/
theorem nested_determined {atoms : List Atom} {f : String} {ts : List Atom}
    {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (.symbol f :: ts)) name)
    (args : List.Forall₂ (Settled dispatch policy atoms) ts Ls) (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      QueryDetermined dispatch policy atoms f vals (Q vals)) :
    Settled dispatch policy atoms (.expression (.symbol f :: ts)) ((combos Ls).flatMap Q) := by
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
  have storage : Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel (Space.ofList atoms)
      (.symbol f) [Atom.undefinedType] :=
    (Mettapedia.Languages.MeTTa.HE.Spec.Type.StorageTypesRel.undefined_iff_occurrences _ _).mpr
      (untyped_occurrences untyped)
  have batch : ∀ {operator : Entry.Value} {arguments : List Entry.Value} {rows raw : List Result},
      Entry.Value.ofAtom (.symbol f) = operator → ts.map Entry.Value.ofAtom = arguments →
      Completed.TupleRel (Space.ofList atoms) dispatch Completed.rawLookup
        (Atom.undefinedType :: live) scope (operator :: arguments) frame rows (policy := policy) →
      Completed.CallsRel (Space.ofList atoms) dispatch Completed.rawLookup live scope
        Atom.undefinedType rows raw (policy := policy) →
      raw.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
    intro operator arguments rows raw sameOperator sameArguments tuples calls
    subst sameOperator sameArguments
    have rowsShape := tuple_rows (Atom.symbol f :: ts) ([Atom.symbol f] :: Ls)
      (.cons (data_settled head) args) (List.cons_ne_nil _ _) _ _ _ tuples
    rw [combos_head, List.forall₂_map_right_iff] at rowsShape
    exact calls_rows _ _ _ (rowsShape.imp fun _ _ row => row.2.1)
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
      cases chosen.undefined_exact storage
  | fallback _ shaped chosen tuples calls selected =>
      rw [shape] at shaped
      simp only [Entry.Value.expression.injEq, List.cons.injEq] at shaped
      obtain ⟨_, sameOperator, sameArguments⟩ := shaped
      have operatorErase := congrArg Entry.Value.erase sameOperator
      rw [Entry.Value.erase_ofAtom] at operatorErase
      rw [← operatorErase] at chosen
      have exhausted := chosen.undefined_exact storage
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
      have exhausted := chosen.undefined_exact storage
      simp at exhausted

/-- **Every complete run of a nested call publishes PeTTa's answers.** Under the hypotheses of
`NestedArguments.nested_agree` (with HE's historical lookup), and with each argument and each
combination's query determined: there is a fuel from which on PeTTa's streaming run yields
`(combos Ls).flatMap Q`, and every run of HE's machine from the entry configuration of
`(f t₁ … tₙ)` to a completed phase publishes exactly these atoms. -/
theorem nested_every_run (dispatch : GroundedDispatch) (policy : Policy) {atoms : List Atom}
    {f : String} {ts : List Atom} {Ls : List (List Atom)} (head : DataAtom (.symbol f))
    (untyped : (Space.ofList atoms).atoms.filter (typeRegion (.symbol f)) = [])
    (notCollapse : f ≠ "collapse") (notOnce : f ≠ "once")
    (notControl : Unifying.sourceControlForm (.expression (.symbol f :: ts)) = false)
    (notIO : Mettapedia.Languages.MeTTa.PeTTa.Eval.ioHead f = false)
    (notNative : StdLib.known f = false)
    (closed : ∀ name, ¬ Mettapedia.Languages.MeTTa.HE.Spec.Match.Merge.AtomOccurs
      (.expression (.symbol f :: ts)) name)
    (ground : isGroundAtom (.expression (.symbol f :: ts)) = true)
    (defined : ∃ e ∈ atoms.filterMap LiveEquations.equationOfRow, e.head = f)
    (args : List.Forall₂ (fun t L => Joint dispatch Completed.rawLookup policy atoms t L ∧
      Determined dispatch policy atoms t L) ts Ls)
    (Q : List Atom → List Atom)
    (apps : ∀ vals ∈ combos Ls, (∀ a ∈ Q vals, Answerable a) ∧
      HEQuery dispatch Completed.rawLookup policy atoms f vals (Q vals) ∧
      PeTTaApplies atoms (.function f) vals (Q vals) ∧
      QueryDetermined dispatch policy atoms f vals (Q vals)) :
    ∃ N : Nat, ∀ n, N ≤ n →
      Streaming.values (Streaming.advance (translate atoms) n
        (Streaming.enter { state := store atoms } (.expression (.symbol f :: ts)))) =
        (combos Ls).flatMap Q ∧
      ∀ emitted : List Result,
        Relation.ReflTransGen (HEStep dispatch Completed.rawLookup policy)
            (load (Space.ofList atoms) (.expression (.symbol f :: ts)) Atom.undefinedType)
            ⟨Space.ofList atoms, .returning [], [], emitted⟩ →
          emitted.map (fun r => r.1.erase) = (combos Ls).flatMap Q := by
  have joint := nested_agree (dispatch := dispatch) (policy := policy) raw_answers head untyped
    notCollapse notOnce notControl notIO notNative closed defined
    (args.imp fun _ _ both => both.1) Q
    (fun vals member => ⟨(apps vals member).1, (apps vals member).2.1, (apps vals member).2.2.1⟩)
  obtain ⟨_, N, _, _, _, stable⟩ := nested_complete ground joint
  have determined := nested_determined head untyped closed
    (args.imp fun _ _ both => ⟨both.1.1, both.2⟩) Q
    (fun vals member => ⟨(apps vals member).1, (apps vals member).2.2.2⟩)
  exact ⟨N, fun n bigger => ⟨stable n bigger, fun emitted run =>
    determined.2 _ _ _ _ (complete_source run)⟩⟩

/-! ## Controls -/

namespace Controls

open WholeRunWords.Double (noHost)
open AnswerBags.Controls (sym app)
open NestedArguments.Controls (flipRows flip_program symbol_data)

/-- `(coin)` is determined, with answers `heads`, `tails`. -/
theorem coin_settled (policy : Policy) :
    Settled noHost policy flipRows (app "coin" []) [sym "heads", sym "tails"] := by
  have coinData : DataAtom (.symbol "coin") := .symbol (by decide) (by decide)
  have bodies : regionBodies flipRows "coin" [] = [sym "heads", sym "tails"] := by decide +kernel
  have related := data_determined_bodies (dispatch := noHost) (policy := policy) flipRows
    [sym "heads", sym "tails"] (by
      intro b member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact symbol_data "heads" (by decide) (by decide) (by decide)
      · exact symbol_data "tails" (by decide) (by decide) (by decide))
  rw [← bodies] at related
  have query := query_equations (dispatch := noHost) (policy := policy) flip_program coinData
    (by decide +kernel) (fun v member => by cases member) related (by rw [bodies]; simp)
  rw [flatten_singletons, bodies] at query
  have nested := nested_determined (dispatch := noHost) (policy := policy) (atoms := flipRows)
    (ts := []) (Ls := []) coinData (by decide +kernel)
    (call_answerable coinData (fun a member => by cases member)).closed .nil
    (fun _ => [sym "heads", sym "tails"]) (by
      intro vals member
      simp only [combos, List.mem_singleton] at member
      subst member
      refine ⟨fun a inside => ?_, query⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at inside
      rcases inside with rfl | rfl
      · exact answerable_of_data (symbol_data "heads" (by decide) (by decide) (by decide)).1
      · exact answerable_of_data (symbol_data "tails" (by decide) (by decide) (by decide)).1)
  simpa [combos] using nested

/-- The query of `flip` on one side is determined: its answers are the bodies of its region. -/
theorem flip_query (policy : Policy) (side : String) (sideData : DataAtom (sym side))
    (bodiesData : ∀ b ∈ regionBodies flipRows "flip" [sym side],
      DataAtom b ∧ b ≠ Atom.notReducible)
    (nonempty : regionBodies flipRows "flip" [sym side] ≠ [])
    (notInstruction : Minimal.embeddedInstruction (.expression [.symbol "flip", sym side]) = false) :
    QueryDetermined noHost policy flipRows "flip" [sym side]
      (regionBodies flipRows "flip" [sym side]) := by
  have related := data_determined_bodies (dispatch := noHost) (policy := policy) flipRows _
    bodiesData
  have query := query_equations (dispatch := noHost) (policy := policy) flip_program
    (f := "flip") (.symbol (by decide) (by decide)) notInstruction
    (fun v member => by
      rw [List.mem_singleton] at member
      subst member
      exact answerable_of_data sideData) related nonempty
  rwa [flatten_singletons] at query

/-- **Positive control: every complete run of `(flip (coin))` publishes `tails`, `heads`.** -/
theorem flip_coin_every_run (policy : Policy) (emitted : List Result)
    (run : Relation.ReflTransGen (HEStep noHost Completed.rawLookup policy)
      (load (Space.ofList flipRows) (app "flip" [app "coin" []]) Atom.undefinedType)
      ⟨Space.ofList flipRows, .returning [], [], emitted⟩) :
    emitted.map (fun r => r.1.erase) = [sym "tails", sym "heads"] := by
  have headsBodies : regionBodies flipRows "flip" [sym "heads"] = [sym "tails"] := by
    decide +kernel
  have tailsBodies : regionBodies flipRows "flip" [sym "tails"] = [sym "heads"] := by
    decide +kernel
  have combosEq : combos [[sym "heads", sym "tails"]] = [[sym "heads"], [sym "tails"]] := rfl
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
  have side : ∀ (one other : String), regionBodies flipRows "flip" [sym one] = [sym other] →
      DataAtom (sym one) → DataAtom (sym other) ∧ sym other ≠ Atom.notReducible →
      Minimal.embeddedInstruction (.expression [.symbol "flip", sym one]) = false →
      (∀ a ∈ regionBodies flipRows "flip" [sym one], Answerable a) ∧
        QueryDetermined noHost policy flipRows "flip" [sym one]
          (regionBodies flipRows "flip" [sym one]) := by
    intro one other bodies oneData otherData notInstruction
    have each : ∀ b ∈ regionBodies flipRows "flip" [sym one],
        DataAtom b ∧ b ≠ Atom.notReducible := by
      rw [bodies]
      intro b member
      rw [List.mem_singleton] at member
      subst member
      exact otherData
    exact ⟨fun a member => answerable_of_data (each a member).1,
      flip_query policy one oneData each (by rw [bodies]; simp) notInstruction⟩
  have nested := nested_determined (dispatch := noHost) (policy := policy) (atoms := flipRows)
    (f := "flip") (ts := [app "coin" []]) (Ls := [[sym "heads", sym "tails"]])
    (.symbol (by decide) (by decide)) (by decide +kernel) closed (.cons (coin_settled policy) .nil)
    (regionBodies flipRows "flip") (by
      intro vals member
      rw [combosEq] at member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact side "heads" "tails" headsBodies (.symbol (by decide) (by decide))
          (symbol_data "tails" (by decide) (by decide) (by decide)) (by decide +kernel)
      · exact side "tails" "heads" tailsBodies (.symbol (by decide) (by decide))
          (symbol_data "heads" (by decide) (by decide) (by decide)) (by decide +kernel))
  have answersEq : (combos [[sym "heads", sym "tails"]]).flatMap (regionBodies flipRows "flip") =
      [sym "tails", sym "heads"] := by
    rw [combosEq, List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, headsBodies,
      tailsBodies]
    rfl
  rw [nested.2 _ _ _ _ (complete_source run), answersEq]

end Controls

#print axioms query_absent
#print axioms query_equations
#print axioms branches_rows
#print axioms tuple_rows
#print axioms calls_rows
#print axioms nested_determined
#print axioms nested_every_run
#print axioms Controls.coin_settled
#print axioms Controls.flip_query
#print axioms Controls.flip_coin_every_run

end NestedEveryRun

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.DialectsAsStrategies.TriangleFootprints
