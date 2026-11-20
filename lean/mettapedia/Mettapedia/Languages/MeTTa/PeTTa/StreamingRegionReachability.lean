import Mettapedia.Languages.MeTTa.PeTTa.StreamingRegionPreservation
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution

/-!
# Entry and paid prefixes retain the right region owners

Every actual request earns marker ordering and complete continuation links.
The logical-variable allocation counter is not used as a marker identity.
An arbitrary suspended prefix retains the same invariant on resumption.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

theorem enter_wellFormed (world : World) (expression : Atom) : WellFormed (enter world expression) :=
  ⟨True.intro,True.intro,True.intro⟩

theorem every_request_prefix_wellFormed (registry : SpaceSemantics.Program) (fuel : Nat)
    (world : World) (expression : Atom) : WellFormed (advance registry fuel (enter world expression)) :=
  advance_wellFormed registry fuel _ (enter_wellFormed world expression)

theorem every_reachable_request_wellFormed {registry : SpaceSemantics.Program} {world : World}
    {expression : Atom} {state : State}
    (path : Relation.ReflTransGen (Transition registry) (enter world expression) state) : WellFormed state :=
  path_wellFormed path (enter_wellFormed world expression)

theorem paid_resumption_wellFormed (registry : SpaceSemantics.Program) (first second : Nat)
    (world : World) (expression : Atom) :
    WellFormed (advance registry second (advance registry first (enter world expression))) :=
  advance_wellFormed registry second _ (every_request_prefix_wellFormed registry first world expression)

theorem marker_keys_unique (state : State) (good : WellFormed state) :
    ((markers state.agenda).map Boundary.key).Nodup := ordered_keys_nodup good.1

theorem marker_key_allocated (state : State) (good : WellFormed state) :
    ∀ scope ∈ markers state.agenda, scope.key < state.nextBoundary := ordered_key_lt good.1

theorem next_marker_fresh (state : State) (good : WellFormed state) :
    ∀ scope ∈ markers state.agenda, scope.key ≠ state.nextBoundary := by
  intro scope present
  exact Nat.ne_of_lt (marker_key_allocated state good scope present)

theorem job_links_at {state : State} {before older : List Job} {job : Job}
    (good : WellFormed state) (agenda : state.agenda = before ++ job :: older) :
    jobFits (markers older) job := by
  have all := good.2
  rw [agenda] at all
  exact (linked_suffix before (job :: older) all).1

theorem task_links_at {state : State} {before older : List Job} {task : Task}
    (good : WellFormed state) (agenda : state.agenda = before ++ .execute task :: older) :
    framesFit (markers older) task.frames := job_links_at good agenda

/-! ## The actual request's rigid marker ledger -/

namespace Custody

open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LocatedSubstitution.Authority
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting (Selection)

/-- A request identity is supplied by the caller's occurrence interface,
not by unification or by PeTTa's variable freshening counter. The none
address is the request itself; a local counter names a delimiter. -/
abbrev Address (Request : Type*) := Request × Option Nat

def site {Request : Type*} (request : Request) (key : Nat) : Address Request := (request, some key)

def entry {Request : Type*} (request : Request) (scope : Boundary) :
    Address Request × Mark (Address Request) Boundary :=
  let address := site request scope.key
  (address, .control ⟨address, (request, none), none⟩ scope)

variable {Request : Type*} [DecidableEq Request]

def live (request : Request) (state : State) : Finset (Address Request) :=
  ((markers state.agenda).map (site request ∘ Boundary.key)).toFinset

def issued (request : Request) (limit : Nat) : Finset (Address Request) :=
  insert (request, none) ((Finset.range limit).image (site request))

def ledger (request : Request) (state : State) : Ledger (Address Request) Boundary :=
  ⟨fun address => ((markers state.agenda).map (entry request)).lookup address, issued request state.nextBoundary⟩

theorem mem_live {request : Request} {state : State} {address : Address Request} :
    address ∈ live request state ↔ ∃ b ∈ markers state.agenda, site request b.key = address := by
  simp only [live, List.mem_toFinset, List.mem_map, Function.comp_apply]

theorem ledger_covers (request : Request) (state : State) (good : WellFormed state) :
    (ledger request state).Covers (live request state) := by
  constructor
  · intro address member
    obtain ⟨b, inMarkers, rfl⟩ := mem_live.mp member
    exact Finset.mem_insert.mpr
      (.inr (Finset.mem_image.mpr ⟨b.key, Finset.mem_range.mpr (marker_key_allocated state good b inMarkers), rfl⟩))
  · intro address
    rw [mem_live]
    change _ ↔ (((markers state.agenda).map (entry request)).lookup address).isSome
    rw [List.lookup_isSome_iff]
    constructor
    · rintro ⟨scope, present, same⟩
      exact ⟨entry request scope, List.mem_map_of_mem present, by
        change (address == site request scope.key) = true
        simp [same]⟩
    · rintro ⟨tag, present, equals⟩
      obtain ⟨scope, whereFound, rfl⟩ := List.mem_map.mp present
      exact ⟨scope, whereFound, (beq_iff_eq.mp equals).symm⟩

theorem mark_of_boundary (request : Request) {state : State} (good : WellFormed state)
    {scope : Boundary} (present : scope ∈ markers state.agenda) :
    (ledger request state).mark (site request scope.key) = some (entry request scope).2 := by
  change List.lookup (site request scope.key) ((markers state.agenda).map (entry request)) = _
  apply lookup_write
  · rw [List.map_map]
    change ((markers state.agenda).map (site request ∘ Boundary.key)).Nodup
    rw [← List.map_map]
    apply List.Nodup.map _ (marker_keys_unique state good)
    intro _ _ same
    exact Option.some.inj (congrArg Prod.snd same)
  · exact List.mem_map_of_mem (f := entry request) present

/-- Even when two callers have identical frames and local delimiter
numbers, an address from the other request finds no ticket here. -/
theorem foreign_request_has_no_mark {request other : Request} (different : other ≠ request)
    (state : State) (key : Nat) :
    (ledger request state).mark (site other key) = none := by
  apply List.lookup_eq_none_iff.mpr
  intro mark present
  obtain ⟨scope, _, rfl⟩ := List.mem_map.mp present
  have apart : site other key ≠ site request scope.key := fun same => different (congrArg Prod.fst same)
  simpa only [entry, bne_iff_ne] using apart

theorem dead_address_has_no_mark (request : Request) {state : State} (good : WellFormed state)
    {address : Address Request} (dead : address ∉ live request state) :
    (ledger request state).mark address = none := by
  cases found : (ledger request state).mark address with
  | none => rfl
  | some tag => exact (dead ((ledger_covers request state good).2 address |>.mpr (by rw [found]; rfl))).elim

private theorem retired_effect (request : Request) {before after : State}
    (goodBefore : WellFormed before) (goodAfter : WellFormed after)
    (noBirth : after.nextBoundary = before.nextBoundary)
    (retained : (markers after.agenda).Sublist (markers before.agenda)) :
    ∃ (picked : Selection (Address Request)) (out : Vector (Mark (Address Request) Boundary) picked.made.length),
      Enabled (fun _ : Address Request => ()) (live request before) (picked.commit (T := Unit)) ∧
      (ledger request before).Fresh picked ∧
      fire (live request before) (picked.commit (T := Unit)) = live request after ∧
      (ledger request before).advance (live request before) picked out = ledger request after := by
  let picked : Selection (Address Request) := ⟨(live request before \ live request after).toList, [], []⟩
  let out : Vector (Mark (Address Request) Boundary) picked.made.length := #v[]
  have inclusion : live request after ⊆ live request before := by
    intro a present
    obtain ⟨scope, known, same⟩ := mem_live.mp present
    exact mem_live.mpr ⟨scope, retained.subset known, same⟩
  have qualified : Enabled (fun _ : Address Request => ()) (live request before) (picked.commit (T := Unit)) :=
    ⟨by simp [Selection.commit, picked], by simp [Selection.commit, picked],
     by simp [Selection.commit, picked], by simp [Selection.commit, picked],
     fun _ member => by simp [Selection.commit] at member⟩
  have reached : fire (live request before) (picked.commit (T := Unit)) = live request after := by
    ext address
    by_cases present : address ∈ live request after
    · simp [fire, Selection.commit, picked, present, inclusion present]
    · simp [fire, Selection.commit, picked, present]
  refine ⟨picked, out, qualified, by simp [Ledger.Fresh, picked], reached, ?_⟩
  apply Ledger.eq_of_parts
  · funext address
    by_cases kept : address ∈ live request after
    · have remains : address ∈ fire (live request before) (picked.commit (T := Unit)) := reached ▸ kept
      rw [Ledger.mark_retained _ out remains (by simp [picked])]
      obtain ⟨scope, present, rfl⟩ := mem_live.mp kept
      rw [mark_of_boundary request goodBefore (retained.subset present), mark_of_boundary request goodAfter present]
    · rw [dead_address_has_no_mark request goodAfter kept]
      simp [Ledger.advance, reached, kept]
  · change (issued request before.nextBoundary ∪ picked.made.toFinset) = issued request after.nextBoundary
    simp [picked, noBirth]

private theorem born_effect (request : Request) {before after : State}
    (goodBefore : WellFormed before) (goodAfter : WellFormed after)
    (born : Boundary) (identity : born.key = before.nextBoundary)
    (increment : after.nextBoundary = before.nextBoundary + 1)
    (stack : markers after.agenda = born :: markers before.agenda) :
    ∃ (picked : Selection (Address Request)) (out : Vector (Mark (Address Request) Boundary) picked.made.length),
      Enabled (fun _ : Address Request => ()) (live request before) (picked.commit (T := Unit)) ∧
      (ledger request before).Fresh picked ∧
      fire (live request before) (picked.commit (T := Unit)) = live request after ∧
      (ledger request before).advance (live request before) picked out = ledger request after := by
  let key := site request born.key
  let picked : Selection (Address Request) := ⟨[], [], [key]⟩
  let out : Vector (Mark (Address Request) Boundary) picked.made.length := #v[(entry request born).2]
  have unused : key ∉ issued request before.nextBoundary := by
    intro existsKey
    rcases Finset.mem_insert.mp existsKey with root | older
    · have impossible : some born.key = none := congrArg Prod.snd root
      cases impossible
    · obtain ⟨index, earlier, equal⟩ := Finset.mem_image.mp older
      have same : index = born.key := Option.some.inj (congrArg Prod.snd equal)
      have limit := Finset.mem_range.mp earlier
      omega
  have fresh : (ledger request before).Fresh picked := by
    change Disjoint ([key].toFinset) (issued request before.nextBoundary)
    simpa using unused
  have separate : Disjoint picked.made.toFinset (live request before) := by
    exact Disjoint.mono_right (ledger_covers request before goodBefore).1 fresh
  have qualified : Enabled (fun _ : Address Request => ()) (live request before) (picked.commit (T := Unit)) :=
    ⟨by simp [Selection.commit, picked], by simp [Selection.commit, picked], by simp [Selection.commit, picked],
      separate, fun _ member => by simp [Selection.commit] at member⟩
  have reached : fire (live request before) (picked.commit (T := Unit)) = live request after := by
    ext address
    simp only [live, stack, List.map_cons, Function.comp_apply, List.toFinset_cons,
      fire, Selection.commit, picked, List.toFinset_nil, Finset.sdiff_empty,
      Finset.mem_union, Finset.mem_insert, Finset.notMem_empty, or_false, key]
    exact or_comm
  refine ⟨picked, out, qualified, fresh, reached, ?_⟩
  apply Ledger.eq_of_parts
  · funext address
    by_cases existsNow : address ∈ live request after
    · by_cases new : address = key
      · subst address
        have installed := Ledger.mark_installed (ledger request before) (live request before) out
          (by simp [picked]) (o := key) (tag := (entry request born).2) (by simp [picked, out])
        exact installed.trans (mark_of_boundary request goodAfter (by rw [stack]; exact List.mem_cons_self)).symm
      · have remains : address ∈ fire (live request before) (picked.commit (T := Unit)) := reached ▸ existsNow
        rw [Ledger.mark_retained _ out remains (by simp [picked, new])]
        have different : (address == key) = false := by simpa using new
        change ((markers before.agenda).map (entry request)).lookup address =
          ((markers after.agenda).map (entry request)).lookup address
        rw [stack, List.map_cons]
        change _ = List.lookup address ((key, (entry request born).2) :: (markers before.agenda).map (entry request))
        simp only [List.lookup_cons, different]
    · rw [dead_address_has_no_mark request goodAfter existsNow]
      simp [Ledger.advance, reached, existsNow]
  · change issued request before.nextBoundary ∪ [key].toFinset = issued request after.nextBoundary
    rw [increment]
    ext address
    simp [issued, Finset.range_add_one, key, identity]

/-- The marker projection of every actual streaming transition is one
admitted occurrence update of the shared authority ledger. A cut may
retire multiple markers. An opening issues one, and bank writes preserve
the mark with its exact saved caller. This projects the control effects;
the already proved execution correspondence carries the evaluator world. -/
theorem transition_ledger (request : Request) {registry : SpaceSemantics.Program} {before after : State}
    (transition : Transition registry before after) (good : WellFormed before) :
    ∃ (picked : Selection (Address Request)) (out : Vector (Mark (Address Request) Boundary) picked.made.length),
      Enabled (fun _ : Address Request => ()) (live request before) (picked.commit (T := Unit)) ∧
      (ledger request before).Fresh picked ∧
      fire (live request before) (picked.commit (T := Unit)) = live request after ∧
      (ledger request before).advance (live request before) picked out = ledger request after := by
  have final := transition_wellFormed transition good
  rcases transition_marker_delta transition with ⟨same, retained⟩ | ⟨born, identity, increment, stack⟩
  · exact retired_effect request good final same retained
  · exact born_effect request good final born identity increment stack

theorem issued_marker_stays_dead (request : Request) {registry : SpaceSemantics.Program} {before after : State}
    (good : WellFormed before) (path : Relation.ReflTransGen (Transition registry) before after) {key : Nat}
    (allocated : key < before.nextBoundary) (dead : site request key ∉ live request before) :
    (ledger request after).mark (site request key) = none := by
  apply dead_address_has_no_mark request (path_wellFormed path good)
  intro member
  obtain ⟨scope, inAfter, equal⟩ := mem_live.mp member
  have retired : ∀ b ∈ markers before.agenda, b.key ≠ key := by
    intro b prior same
    exact dead (mem_live.mpr ⟨b, prior, by rw [same]⟩)
  exact path_no_reissue path allocated retired scope inAfter (Option.some.inj (congrArg Prod.snd equal))

/-- The top returned packet's saved collection frame names its actual
later bank, including the bank's own saved caller. This uses the real
agenda links, not equality of returned values or of caller syntax. -/
theorem collection_mark (request : Request) {state : State}
    {answer : Unifying.Answer} {more : List Unifying.Answer} {key : Nat} {caller : List Frame} {older : List Job}
    (good : WellFormed state)
    (agenda : state.agenda = .execute ⟨.returned (answer :: more), .collection key :: caller⟩ :: older) :
    (ledger request state).mark (site request key) = some (entry request (.collection key caller)).2 := by
  obtain ⟨pre, post, marks, _⟩ := (head_and_tail good agenda).1
  apply mark_of_boundary request good (scope := .collection key caller)
  rw [agenda]
  change Boundary.collection key caller ∈ markers older
  rw [marks]
  exact List.mem_append_right _ List.mem_cons_self

/-- A stamped handoff may trigger the already pending collector reply.
It cannot inject an answer, alter a continuation, or change which
source transition is taken. The request coordinate must come from
the invocation that earned the response. -/
def commitCollection (registry : SpaceSemantics.Program) (request : Request)
    (presented : Address Request) (state : State) : Option State :=
  match state.agenda with
  | .execute ⟨.returned (_ :: _), .collection key :: _⟩ :: _ =>
      if presented = site request key then
        match (ledger request state).mark presented with
        | some (.control _ (.collection _ _)) => step registry state
        | _ => none
      else none
  | _ => none

theorem commit_collection_exact (registry : SpaceSemantics.Program) (request : Request)
    (presented : Address Request) {state : State}
    {answer : Unifying.Answer} {more : List Unifying.Answer} {key : Nat} {caller : List Frame} {older : List Job}
    (good : WellFormed state)
    (agenda : state.agenda = .execute ⟨.returned (answer :: more), .collection key :: caller⟩ :: older) :
    commitCollection registry request presented state =
      if presented = site request key then step registry state else none := by
  cases choice : decide (presented = site request key) with
  | false =>
    have apart : presented ≠ site request key := of_decide_eq_false choice
    simp [commitCollection, agenda, apart]
  | true =>
    have same : presented = site request key := of_decide_eq_true choice
    subst presented
    simp [commitCollection, agenda, collection_mark request good agenda, entry]

/-- A correctly stamped return is the actual bank write. It appends one
answer at the selected occurrence, preserves the bank's caller, and does
not move the issuance counter, the world, or the shared ledger. -/
theorem owned_collection_appends (registry : SpaceSemantics.Program) (request : Request) {state : State}
    {answer : Unifying.Answer} {more : List Unifying.Answer} {key : Nat} {caller : List Frame} {older : List Job}
    (good : WellFormed state)
    (agenda : state.agenda = .execute ⟨.returned (answer :: more), .collection key :: caller⟩ :: older) :
    let pending := laterAnswers more (.collection key :: caller) older
    ∃ (left right : List Job) (bindings : Mettapedia.Languages.ProcessCalculi.MORK.Subst)
      (bank : List Unifying.Answer),
      pending = left ++ .collect key bindings caller bank :: right ∧
      let after := { state with agenda := left ++ .collect key bindings caller (bank ++ [answer]) :: right }
      commitCollection registry request (site request key) state = some after ∧
      Transition registry state after ∧ ledger request after = ledger request state := by
  dsimp only
  let pending := laterAnswers more (.collection key :: caller) older
  obtain ⟨fits, validOlder⟩ := head_and_tail good agenda
  have linked : framesFit (markers pending) (.collection key :: caller) := by
    simpa only [pending, markers_later_answers, jobFits] using fits
  have orderedPending : ordered state.nextBoundary (markers pending) := by
    simpa only [pending, markers_later_answers] using validOlder.1
  obtain ⟨changed, recorded⟩ := collection_resolves (answer := answer) linked
  obtain ⟨left, bindings, bank, right, shape, rfl, _⟩ := collection_associated orderedPending linked recorded
  have actual := Transition.answer (registry := registry) agenda (.collection recorded)
  refine ⟨left, right, bindings, bank, shape, ?_, actual, ?_⟩
  · rw [commit_collection_exact registry request _ good agenda]
    simpa using actual.computed
  · apply Ledger.eq_of_parts
    · funext address
      have sameMarkers := collection_markers recorded
      change markers (left ++ .collect key bindings caller (bank ++ [answer]) :: right) =
        markers (laterAnswers more (.collection key :: caller) older) at sameMarkers
      change List.lookup address ((markers (left ++ .collect key bindings caller (bank ++ [answer]) :: right)).map
        (entry request)) = List.lookup address ((markers state.agenda).map (entry request))
      rw [sameMarkers, markers_later_answers, agenda]
      rfl
    · rfl

end Custody

/-- These wrappers retain proofs of the actual state, not a second controller. -/
def enterLinked (world : World) (expression : Atom) : {state : State // WellFormed state} :=
  ⟨enter world expression,enter_wellFormed world expression⟩

def advanceLinked (registry : SpaceSemantics.Program) (fuel : Nat)
    (source : {state : State // WellFormed state}) : {state : State // WellFormed state} :=
  ⟨advance registry fuel source.val,advance_wellFormed registry fuel source.val source.property⟩

end Mettapedia.Languages.MeTTa.PeTTa.Streaming.Regions
