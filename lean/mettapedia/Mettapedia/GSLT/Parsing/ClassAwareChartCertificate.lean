import Mettapedia.GSLT.Parsing.ClassAwareChartCoverage
import Mettapedia.GSLT.Parsing.ClassAwareNativeForestReachabilityFrontier

/-! Warm-started whole-input coverage. Instead of iterating the reference
chart from the empty state, it is iterated from a candidate: the families of
the forest under test, with requests closed from the root by a worklist. The
candidate is not trusted. Every chart step only adds consequences, and any
fixed point is saturated, so the result is root complete exactly as the
iterated reference chart is. Exhausted allowances are unfinished, never
acceptance. -/

set_option autoImplicit false

namespace Mettapedia.GSLT.Parsing.ClassAwareChartCertificate

open ClassAwarePackedForest ClassAwareGroundedChart ClassAwareChartClosure
open ClassAwareNativeForestContract ClassAwareNativeForestIdentityWire
open ClassAwareNativeForestIdentityInventory ClassAwareNativeForestFamilyWitness
open ClassAwareNativeForestFamilyCompleteness ClassAwareNativeForestQualification
open ClassAwareNativeForestParserCompleteness ClassAwareParserPackCorrespondence ParserProfileSemantics
open ClassAwarePackedForestSaturation ClassAwareParserPackEnumeration
open ClassAwareChartDemand

/-- The requests one request demands, given the recognized keys. -/
def demand (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (index : ClassAwareChartIndex.Index) (request : Request) : List Request :=
  plan.structural.flatMap fun production =>
    if production.resultSort == request.1 then
      indexedBodyRequests index profile input production.items request.2
    else []

/-- Worklist closure from pending requests; `none` when the allowance runs out. -/
def close (next : Request → List Request) : Nat → List Request → Std.HashSet Request →
    List Request → Option (List Request)
  | 0, _, _, _ => none
  | _ + 1, [], _, found => some found.reverse
  | fuel + 1, request :: pending, seen, found =>
    if seen.contains request then close next fuel pending seen found
    else close next fuel (next request ++ pending) (seen.insert request) (request :: found)

/-- The candidate chart state for a forest's families. -/
def candidate? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (families : List Family) (fuel : Nat) : Option State := do
  let index := ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys ⟨[], families⟩) input.length
  let requests ← close (demand profile plan input index) fuel [(plan.lexical.startSort, 0)] {} []
  pure ⟨requests, families⟩

/-! ### One chart step without positional list indexing

The step below enumerates production positions with their rows, as the
original step does through `List.finRange` and `List.get`, and is proved to
be the same step. -/

theorem finRange_flatMap_get {α β : Type} (f : α → Nat → List β) :
    ∀ (rows : List α) (offset : Nat),
      (List.finRange rows.length).flatMap (fun position => f (rows.get position) (position.val + offset)) =
        (rows.zipIdx offset).flatMap (fun entry => f entry.1 entry.2)
  | [], _ => rfl
  | row :: rows, offset => by
    change (List.finRange (rows.length + 1)).flatMap
        (fun position => f ((row :: rows).get position) (position.val + offset)) = _
    rw [List.finRange_succ, List.flatMap_cons, List.zipIdx_cons, List.flatMap_cons, List.flatMap_map]
    have tail := finRange_flatMap_get f rows (offset + 1)
    simp only [Fin.val_succ, Fin.val_zero, List.get_cons_zero, Nat.zero_add]
    rw [← tail]
    congr 2
    funext position
    rw [Nat.add_assoc, Nat.add_comm 1 offset]
    rfl

def fastLexical (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Family :=
  state.requests.flatMap fun request =>
    (plan.lexical.productions.zipIdx 0).flatMap fun entry =>
      if entry.1.resultSort == request.1 then
        match terminalMatch? profile input entry.1.matcher request.2 with
        | none => []
        | some (stop, _) => [⟨⟨entry.1.resultSort, request.2, stop⟩,
          .lexical entry.2, [.terminal entry.1.matcher request.2 stop]⟩]
      else []

theorem fastLexical_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    fastLexical profile plan input state = expectedLexical profile plan input state := by
  unfold fastLexical expectedLexical
  congr 1
  funext request
  have rows := finRange_flatMap_get (fun (production : CompiledLexicalProduction) (position : Nat) =>
      if production.resultSort == request.1 then
        match terminalMatch? profile input production.matcher request.2 with
        | none => []
        | some (stop, _) => [(⟨⟨production.resultSort, request.2, stop⟩,
          .lexical position, [.terminal production.matcher request.2 stop]⟩ : Family)]
      else []) plan.lexical.productions 0
  simp only [Nat.add_zero] at rows
  exact rows.symm

def fastStructural (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : List Family :=
  let index := ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys (forest state)) input.length
  state.requests.flatMap fun request =>
    (plan.structural.zipIdx 0).flatMap fun entry =>
      if entry.1.resultSort == request.1 then
        (ClassAwareChartIndex.items index profile input entry.1.items request.2).map fun body =>
          ⟨⟨entry.1.resultSort, request.2, body.stop⟩, .structural entry.2, body.children⟩
      else []

theorem fastStructural_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    fastStructural profile plan input state = indexedStructural profile plan input state := by
  unfold fastStructural indexedStructural
  dsimp only
  congr 1
  funext request
  have rows := finRange_flatMap_get (fun (production : CompiledStructuralProduction) (position : Nat) =>
      if production.resultSort == request.1 then
        (ClassAwareChartIndex.items (ClassAwareChartIndex.build
            (ClassAwareChartIndex.recognizedKeys (forest state)) input.length)
          profile input production.items request.2).map fun body =>
          (⟨⟨production.resultSort, request.2, body.stop⟩, .structural position, body.children⟩ : Family)
      else []) plan.structural 0
  simp only [Nat.add_zero] at rows
  exact rows.symm

def fastStep (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) : State := {
  requests := Mettapedia.Util.LinearHash.eraseDupsFast
    ((plan.lexical.startSort, 0) :: (state.requests ++ indexedRequests profile plan input state))
  families := Mettapedia.Util.LinearHash.eraseDupsFast
    (state.families ++ fastLexical profile plan input state ++ fastStructural profile plan input state) }

theorem fastStep_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    fastStep profile plan input state = ClassAwareChartDemand.step profile plan input state := by
  simp only [fastStep, ClassAwareChartDemand.step, fastLexical_eq, fastStructural_eq]

def fastFinish? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat) :
    Nat → State → Option Forest
  | 0, _ => none
  | rounds + 1, state =>
    let next := fastStep profile plan input state
    if next == state then
      ClassAwareChartPruning.prune? (ClassAwareChartClosure.recognizedForest plan input state.families)
    else fastFinish? profile plan input rounds next

theorem fastFinish?_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat) :
    ∀ (rounds : Nat) (state : State),
      fastFinish? profile plan input rounds state = ClassAwareChartDemand.finish? profile plan input rounds state
  | 0, _ => rfl
  | rounds + 1, state => by
    simp only [fastFinish?, ClassAwareChartDemand.finish?, fastStep_eq, fastFinish?_eq profile plan input rounds]

/-- The reference chart, iterated from the candidate rather than from the
empty state. Any fixed point of a chart step is saturated, whatever its
starting state, so the result is root complete; `none` is unfinished. -/
def reference? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (families : List Family) (fuel rounds : Nat) : Option Forest :=
  (candidate? profile plan input families fuel).bind fun state => fastFinish? profile plan input rounds state

theorem reference?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {families : List Family} {fuel rounds : Nat} {result : Forest}
    (certified : reference? profile plan input families fuel rounds = some result) :
    RootParserComplete result profile plan input := by
  obtain ⟨state, _, finished⟩ := Option.bind_eq_some_iff.mp certified
  rw [fastFinish?_eq] at finished
  exact ClassAwareChartDemand.finish?_complete rounds state result finished

/-- Whole-input coverage of a backend forest by the warm-started reference. -/
def coverage? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (backend : Forest) (fuel rounds : Nat) : Option Bool :=
  (reference? profile plan input backend.families fuel rounds).map fun reference =>
    validateForestCovers reference backend

theorem coverage?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {backend : Forest} {fuel rounds : Nat}
    (accepted : coverage? profile plan input backend fuel rounds = some true) :
    RootParserComplete backend profile plan input := by
  obtain ⟨reference, finished, covered⟩ := Option.map_eq_some_iff.mp accepted
  exact rootParserComplete_of_covers (validateForestCovers_sound covered) (reference?_complete finished)

/-! ### The same chart over an input array and productions grouped by sort

Codepoints are read from an array instead of a list, productions are found by
the requested sort instead of scanned, and one index serves a whole step. Each
piece is proved equal to the corresponding definition above. -/

def terminalAt? (profile : ParserProfileLayer) (input : Array Nat) (matcher : TerminalMatcher)
    (start : Nat) : Option (Nat × List PresentationExprSemantics.CST) :=
  match matcher with
  | .any => input[start]?.map fun codepoint => (start + 1, [.terminal [codepoint] start (start + 1)])
  | .eof => if start = input.size then some (start, []) else none
  | .char expected =>
      match input[start]? with
      | some codepoint =>
          if expected = codepoint then some (start + 1, [.terminal [codepoint] start (start + 1)])
          else none
      | none => none
  | .class className =>
      match input[start]? with
      | some codepoint =>
          if profile.classAccepts? className codepoint = some true then
            some (start + 1, [.terminal [codepoint] start (start + 1)])
          else none
      | none => none

theorem terminalAt?_eq (profile : ParserProfileLayer) (input : List Nat) (matcher : TerminalMatcher)
    (start : Nat) :
    terminalAt? profile input.toArray matcher start = terminalMatch? profile input matcher start := by
  cases matcher <;> simp only [terminalAt?, terminalMatch?, List.getElem?_toArray, List.size_toArray] <;>
    cases input[start]? <;> rfl

def itemsAt (index : ClassAwareChartIndex.Index) (profile : ParserProfileLayer) (input : Array Nat) :
    List PackItem → Nat → List RecognizedItemsRow
  | [], cursor => [⟨cursor, []⟩]
  | .terminal matcher :: rest, cursor =>
    match terminalAt? profile input matcher cursor with
    | none => []
    | some (middle, _) => (itemsAt index profile input rest middle).map fun tail =>
      ⟨tail.stop, .terminal matcher cursor middle :: tail.children⟩
  | .nonterminal sort :: rest, cursor =>
    (ClassAwareChartIndex.lookup index sort cursor).flatMap fun key =>
      (itemsAt index profile input rest key.stop).map fun tail =>
        ⟨tail.stop, .node key :: tail.children⟩

theorem itemsAt_eq (index : ClassAwareChartIndex.Index) (profile : ParserProfileLayer)
    (input : List Nat) (body : List PackItem) (start : Nat) :
    itemsAt index profile input.toArray body start =
      ClassAwareChartIndex.items index profile input body start := by
  induction body generalizing start with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | terminal matcher =>
      simp only [itemsAt, ClassAwareChartIndex.items, terminalAt?_eq]
      cases terminalMatch? profile input matcher start with
      | none => rfl
      | some result => cases result; simp only [ih]
    | nonterminal sort => simp only [itemsAt, ClassAwareChartIndex.items, ih]

def bodyRequestsAt (index : ClassAwareChartIndex.Index) (profile : ParserProfileLayer)
    (input : Array Nat) : List PackItem → Nat → List Request
  | [], _ => []
  | .terminal matcher :: rest, cursor =>
    match terminalAt? profile input matcher cursor with
    | none => []
    | some (middle, _) => bodyRequestsAt index profile input rest middle
  | .nonterminal sort :: rest, cursor =>
    (sort, cursor) :: ((ClassAwareChartIndex.lookup index sort cursor).flatMap
      fun key => bodyRequestsAt index profile input rest key.stop)

theorem bodyRequestsAt_eq (index : ClassAwareChartIndex.Index) (profile : ParserProfileLayer)
    (input : List Nat) (body : List PackItem) (start : Nat) :
    bodyRequestsAt index profile input.toArray body start =
      indexedBodyRequests index profile input body start := by
  induction body generalizing start with
  | nil => rfl
  | cons item rest ih =>
    cases item with
    | terminal matcher =>
      simp only [bodyRequestsAt, indexedBodyRequests, terminalAt?_eq]
      cases terminalMatch? profile input matcher start with
      | none => rfl
      | some result => cases result; simp only [ih]
    | nonterminal sort => simp only [bodyRequestsAt, indexedBodyRequests, ih]

/-- Rows with their positions, grouped by sort; each group keeps authored order. -/
def groupBySort {α : Type} (sort : α → String) (rows : List α) :
    Std.HashMap String (List (α × Nat)) :=
  (rows.zipIdx 0).foldr (fun entry table =>
    table.insert (sort entry.1) (entry :: table.getD (sort entry.1) [])) {}

theorem foldr_group_getD {α : Type} (sort : α → String) (entries : List (α × Nat)) (key : String) :
    (entries.foldr (fun entry table =>
        table.insert (sort entry.1) (entry :: table.getD (sort entry.1) []))
      ({} : Std.HashMap String (List (α × Nat)))).getD key [] =
      entries.filter fun entry => sort entry.1 == key := by
  induction entries with
  | nil => simp
  | cons first rest ih =>
    rw [List.foldr_cons, Std.HashMap.getD_insert, List.filter_cons]
    by_cases same : sort first.1 = key
    · subst same
      simp [ih]
    · have different : (sort first.1 == key) = false := by simpa using same
      simp only [different, Bool.false_eq_true, if_false, ih]

theorem groupBySort_getD {α : Type} (sort : α → String) (rows : List α) (key : String) :
    (groupBySort sort rows).getD key [] = (rows.zipIdx 0).filter fun entry => sort entry.1 == key :=
  foldr_group_getD sort (rows.zipIdx 0) key

theorem filter_flatMap_ite {α β : Type} (entries : List α) (keep : α → Bool) (f : α → List β) :
    (entries.filter keep).flatMap f = entries.flatMap fun entry => if keep entry then f entry else [] := by
  induction entries with
  | nil => rfl
  | cons first rest ih => by_cases kept : keep first = true <;> simp [kept, ih]

theorem filter_zipIdx_flatMap {α β : Type} (rows : List α) (keep : α → Bool) (f : α → List β)
    (offset : Nat) :
    ((rows.zipIdx offset).filter fun entry => keep entry.1).flatMap (fun entry => f entry.1) =
      rows.flatMap fun row => if keep row then f row else [] := by
  induction rows generalizing offset with
  | nil => rfl
  | cons first rest ih =>
    by_cases kept : keep first = true <;> simp [List.zipIdx_cons, kept, ih]

/-- Input codepoints as an array and productions grouped by result sort. -/
structure Tables where
  input : Array Nat
  lexical : Std.HashMap String (List (CompiledLexicalProduction × Nat))
  structural : Std.HashMap String (List (CompiledStructuralProduction × Nat))

def tables (plan : CompiledParserPackPlan) (input : List Nat) : Tables :=
  ⟨input.toArray, groupBySort CompiledLexicalProduction.resultSort plan.lexical.productions,
    groupBySort CompiledStructuralProduction.resultSort plan.structural⟩

def lexicalAt (profile : ParserProfileLayer) (tables : Tables) (state : State) : List Family :=
  state.requests.flatMap fun request =>
    (tables.lexical.getD request.1 []).flatMap fun entry =>
      match terminalAt? profile tables.input entry.1.matcher request.2 with
      | none => []
      | some (stop, _) => [⟨⟨entry.1.resultSort, request.2, stop⟩,
        .lexical entry.2, [.terminal entry.1.matcher request.2 stop]⟩]

theorem lexicalAt_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    lexicalAt profile (tables plan input) state = fastLexical profile plan input state := by
  unfold lexicalAt fastLexical tables
  dsimp only
  congr 1
  funext request
  rw [groupBySort_getD, filter_flatMap_ite]
  simp only [terminalAt?_eq]

def structuralAt (profile : ParserProfileLayer) (tables : Tables) (index : ClassAwareChartIndex.Index)
    (state : State) : List Family :=
  state.requests.flatMap fun request =>
    (tables.structural.getD request.1 []).flatMap fun entry =>
      (itemsAt index profile tables.input entry.1.items request.2).map fun body =>
        ⟨⟨entry.1.resultSort, request.2, body.stop⟩, .structural entry.2, body.children⟩

theorem structuralAt_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    structuralAt profile (tables plan input)
        (ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys (forest state)) input.length) state =
      fastStructural profile plan input state := by
  unfold structuralAt fastStructural tables
  dsimp only
  congr 1
  funext request
  rw [groupBySort_getD, filter_flatMap_ite]
  simp only [itemsAt_eq]

def requestsAt (profile : ParserProfileLayer) (tables : Tables) (index : ClassAwareChartIndex.Index)
    (request : Request) : List Request :=
  (tables.structural.getD request.1 []).flatMap fun entry =>
    bodyRequestsAt index profile tables.input entry.1.items request.2

theorem requestsAt_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (index : ClassAwareChartIndex.Index) (request : Request) :
    requestsAt profile (tables plan input) index request = demand profile plan input index request := by
  unfold requestsAt demand tables
  dsimp only
  rw [groupBySort_getD]
  have rows := filter_zipIdx_flatMap plan.structural
    (fun production => production.resultSort == request.1)
    (fun production => indexedBodyRequests index profile input production.items request.2) 0
  simp only [bodyRequestsAt_eq]
  exact rows

def stepAt (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (tables : Tables)
    (state : State) : State :=
  let index := ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys (forest state)) tables.input.size
  { requests := Mettapedia.Util.LinearHash.eraseDupsFast
      ((plan.lexical.startSort, 0) :: (state.requests ++ state.requests.flatMap (requestsAt profile tables index)))
    families := Mettapedia.Util.LinearHash.eraseDupsFast
      (state.families ++ lexicalAt profile tables state ++ structuralAt profile tables index state) }

theorem indexedRequests_eq_demand (profile : ParserProfileLayer) (plan : CompiledParserPackPlan)
    (input : List Nat) (state : State) :
    indexedRequests profile plan input state =
      state.requests.flatMap (demand profile plan input
        (ClassAwareChartIndex.build (ClassAwareChartIndex.recognizedKeys (forest state)) input.length)) := by
  rfl

theorem stepAt_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (state : State) : stepAt profile plan (tables plan input) state = fastStep profile plan input state := by
  have size : (tables plan input).input.size = input.length := by simp [tables]
  have requests : ∀ index : ClassAwareChartIndex.Index,
      requestsAt profile (tables plan input) index = demand profile plan input index := fun index =>
    funext (requestsAt_eq profile plan input index)
  simp only [stepAt, fastStep, size, requests, lexicalAt_eq, structuralAt_eq, indexedRequests_eq_demand]

def finishAt? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (tables : Tables)
    (input : List Nat) : Nat → State → Option Forest
  | 0, _ => none
  | rounds + 1, state =>
    let next := stepAt profile plan tables state
    if next == state then
      ClassAwareChartPruning.prune? (ClassAwareChartClosure.recognizedForest plan input state.families)
    else finishAt? profile plan tables input rounds next

theorem finishAt?_eq (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat) :
    ∀ (rounds : Nat) (state : State),
      finishAt? profile plan (tables plan input) input rounds state = fastFinish? profile plan input rounds state
  | 0, _ => rfl
  | rounds + 1, state => by
    simp only [finishAt?, fastFinish?, stepAt_eq, finishAt?_eq profile plan input rounds]

/-! ### An untrusted closure for the reference chart

The chart above is iterated naively: each round derives every family again,
and dead items deepen by one level per round. The candidate below is built
once by an Earley-style worklist instead: each request starts its productions
once, each partial body waits on the key it needs next, and each new key
resumes the bodies waiting on it. Nothing about it is trusted. The checked
step must find it fixed, and any fixed point is saturated. -/

/-- A structural body of `sort` from `start`, with its remaining items. -/
structure Partial where
  sort : String
  start : Nat
  production : Nat
  rest : List PackItem
  cursor : Nat
  /-- Children read so far, newest first. -/
  children : List ChildRef

inductive Event where
  | request (request : Request)
  | advance (item : Partial)
  | key (key : NodeKey)

structure Closure where
  requests : Array Request
  requestSeen : Std.HashSet Request
  families : Array Family
  familySeen : Std.HashSet Family
  /-- Recognized stops for each sort and start. -/
  stops : Std.HashMap Request (List Nat)
  /-- Bodies waiting on a key of each sort and start. -/
  waiting : Std.HashMap Request (List Partial)

def addRequest (closure : Closure) (request : Request) (pending : List Event) : Closure × List Event :=
  if closure.requestSeen.contains request then (closure, pending)
  else ({ closure with
      requests := closure.requests.push request
      requestSeen := closure.requestSeen.insert request }, .request request :: pending)

def addFamily (closure : Closure) (family : Family) (pending : List Event) : Closure × List Event :=
  if closure.familySeen.contains family then (closure, pending)
  else
    let closure := { closure with
      families := closure.families.push family
      familySeen := closure.familySeen.insert family }
    let slot : Request := (family.parent.resultSort, family.parent.start)
    let known := closure.stops.getD slot []
    if known.contains family.parent.stop then (closure, pending)
    else ({ closure with stops := closure.stops.insert slot (family.parent.stop :: known) },
      .key family.parent :: pending)

def resume (item : Partial) (rest : List PackItem) (key : NodeKey) : Event :=
  .advance { item with rest, cursor := key.stop, children := .node key :: item.children }

def handle (profile : ParserProfileLayer) (tables : Tables) (closure : Closure) :
    Event → List Event → Closure × List Event
  | .request (sort, start), pending =>
    let lexical := (tables.lexical.getD sort []).foldl (fun (current : Closure × List Event) entry =>
      match terminalAt? profile tables.input entry.1.matcher start with
      | none => current
      | some (stop, _) => addFamily current.1
          ⟨⟨entry.1.resultSort, start, stop⟩, .lexical entry.2, [.terminal entry.1.matcher start stop]⟩
          current.2) (closure, pending)
    (lexical.1, (tables.structural.getD sort []).foldl (fun pending entry =>
      .advance ⟨sort, start, entry.2, entry.1.items, start, []⟩ :: pending) lexical.2)
  | .advance item, pending =>
    match item.rest with
    | [] => addFamily closure
        ⟨⟨item.sort, item.start, item.cursor⟩, .structural item.production, item.children.reverse⟩ pending
    | .terminal matcher :: rest =>
      match terminalAt? profile tables.input matcher item.cursor with
      | none => (closure, pending)
      | some (middle, _) => (closure, .advance { item with
          rest, cursor := middle, children := .terminal matcher item.cursor middle :: item.children } :: pending)
    | .nonterminal sort :: rest =>
      let slot : Request := (sort, item.cursor)
      let requested := addRequest closure slot pending
      let closure := { requested.1 with
        waiting := requested.1.waiting.insert slot (item :: requested.1.waiting.getD slot []) }
      (closure, (closure.stops.getD slot []).foldl (fun pending stop =>
        resume item rest ⟨sort, item.cursor, stop⟩ :: pending) requested.2)
  | .key key, pending =>
    (closure, (closure.waiting.getD (key.resultSort, key.start) []).foldl (fun pending item =>
      match item.rest with
      | .nonterminal _ :: rest => resume item rest key :: pending
      | _ => pending) pending)

/-- Process events until none remain; `none` when the allowance runs out. -/
def run (profile : ParserProfileLayer) (tables : Tables) : Nat → Closure → List Event → Option Closure
  | 0, _, _ => none
  | _ + 1, closure, [] => some closure
  | fuel + 1, closure, event :: pending =>
    let handled := handle profile tables closure event pending
    run profile tables fuel handled.1 handled.2

def closedCandidate? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (tables : Tables)
    (fuel : Nat) : Option State := do
  let empty : Closure := ⟨#[], {}, #[], {}, {}, {}⟩
  let started := addRequest empty (plan.lexical.startSort, 0) []
  let closure ← run profile tables fuel started.1 started.2
  pure ⟨closure.requests.toList, closure.families.toList⟩

/-- The checked chart started from the untrusted closure. -/
def referenceAt? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (fuel rounds : Nat) : Option Forest :=
  let prepared := tables plan input
  (closedCandidate? profile plan prepared fuel).bind fun state =>
    finishAt? profile plan prepared input rounds state

theorem referenceAt?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {fuel rounds : Nat} {result : Forest}
    (certified : referenceAt? profile plan input fuel rounds = some result) :
    RootParserComplete result profile plan input := by
  obtain ⟨state, _, finished⟩ := Option.bind_eq_some_iff.mp certified
  rw [finishAt?_eq, fastFinish?_eq] at finished
  exact ClassAwareChartDemand.finish?_complete rounds state result finished

def coverageAt? (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (input : List Nat)
    (backend : Forest) (fuel rounds : Nat) : Option Bool :=
  (referenceAt? profile plan input fuel rounds).map fun reference =>
    validateForestCovers reference backend

theorem coverageAt?_complete {profile : ParserProfileLayer} {plan : CompiledParserPackPlan}
    {input : List Nat} {backend : Forest} {fuel rounds : Nat}
    (accepted : coverageAt? profile plan input backend fuel rounds = some true) :
    RootParserComplete backend profile plan input := by
  obtain ⟨reference, finished, covered⟩ := Option.map_eq_some_iff.mp accepted
  exact rootParserComplete_of_covers (validateForestCovers_sound covered) (referenceAt?_complete finished)

/-- The snapshot-level check, as `ClassAwareChartCoverage.validate?`, with the
representation check over frontier rounds. -/
def validate? (snapshot : Snapshot) (view : ForestView)
    (profile : ParserProfileLayer) (plan : CompiledParserPackPlan) (fuel rounds : Nat) : Option Bool := do
  match snapshot.resolveInventory? plan with
  | none => some false
  | some inventory =>
    if ClassAwareNativeForestReachabilityFrontier.validateExactFamilyRepresentationFrontier
        view inventory profile plan then
      coverageAt? profile plan view.codepoints (decodedForestData view inventory profile) fuel rounds
    else some false

theorem validate?_sound {snapshot : Snapshot} {view : ForestView}
    {profile : ParserProfileLayer} {plan : CompiledParserPackPlan} {fuel rounds : Nat}
    (accepted : validate? snapshot view profile plan fuel rounds = some true) :
    ∃ inventory : Inventory, snapshot.resolveInventory? plan = some inventory ∧
      ∃ inputs : RootedFamilyDecodingInputs view inventory profile plan,
        ParserCompleteRepresentation view inventory profile plan
          (decodedForest inputs.families (enumerateFamilyWitnesses view)) := by
  unfold validate? at accepted
  cases resolved : snapshot.resolveInventory? plan with
  | none => simp [resolved] at accepted
  | some inventory =>
    simp only [resolved] at accepted
    split at accepted
    · rename_i valid
      rw [ClassAwareNativeForestReachabilityFrontier.validateExactFamilyRepresentationFrontier_eq] at valid
      obtain ⟨inputs, represents⟩ := validateExactFamilyRepresentation_sound valid
      have complete := coverageAt?_complete accepted
      rw [← decodedForest_eq_data inputs.families] at complete
      exact ⟨inventory, rfl, inputs, ⟨represents, complete⟩⟩
    · cases accepted

#print axioms coverage?_complete
#print axioms validate?_sound
#print axioms coverageAt?_complete

end Mettapedia.GSLT.Parsing.ClassAwareChartCertificate
