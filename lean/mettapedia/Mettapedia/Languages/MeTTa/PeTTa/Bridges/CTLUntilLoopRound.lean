import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopFrames
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopStore

/-!
# Increment and named-round phases of the authored EU loop

Fresh producer aliases and evaluated operand slots are the actual source
allocations. Reached readings and pending caller locals are transported
through their equations; source expressions are not replaced by their values.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopRound

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilSourceRows (number)
open CTLUntilLoopSource (Names InitialFrame increment afterIncrement afterRound incrementCaller incrementSlot incremented)
open CTLUntilLoopFrames (IncrementFrame RoundFrame)

variable {Context Label : Type}

private theorem active_support (control : Control) (expression destination : Atom) (older : List Goal)
    (active : control.goals = .evaluate expression destination :: older) (name : String)
    (occurs : name ∈ (encode expression).freeVars ∨ name ∈ (encode destination).freeVars) :
    name ∈ control.support := by
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  rcases occurs with sourceName | resultName
  · exact Or.inr ⟨expression, by simp [active, Goal.atoms], sourceName⟩
  · exact Or.inr ⟨destination, by simp [active, Goal.atoms], resultName⟩

private theorem remainder_name (names : Names) (name : String)
    (member : name = names.count ∨ name = names.dropped) :
    name ∈ (encode (afterIncrement names)).freeVars := by
  rw [afterIncrement, ScopedLetSource.source, CapturedPatternSupport.mem_expression_names]
  rcases member with rfl | rfl
  · exact ⟨.var names.count, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  · refine ⟨afterRound names, by simp, ?_⟩
    rw [afterRound, ScopedLetSource.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var names.dropped, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

private theorem let_body_name (name binder : String) (producer body : Atom)
    (used : name ∈ (encode body).freeVars) :
    name ∈ (encode (ScopedLetSource.source binder producer body)).freeVars := by
  rw [ScopedLetSource.source, CapturedPatternSupport.mem_expression_names]
  exact ⟨body, by simp, used⟩

theorem incremented_inherited (caller : Control) (names : Names) (round : Nat)
    (environment : Environment) (solved : Solves environment (incremented caller names round).bindings) :
    Solves environment caller.bindings :=
  ScopedLetSource.inherited caller names.next (increment names) (afterIncrement names) (.var names.result) environment
    (ScopedAtomicPrimitive.returned_inherited (incrementCaller caller names) "+" [.var names.current, number 1]
      (.var (incrementSlot caller names)) (number (round + 1)) environment solved)

theorem incremented_next (caller : Control) (names : Names) (round : Nat)
    (environment : Environment) (solved : Solves environment (incremented caller names round).bindings) :
    read environment (.var names.next) = number (round + 1) :=
  ScopedLetSource.aliased_value caller names.next (increment names) (afterIncrement names) (.var names.result)
    (number (round + 1)) environment
    (ScopedAtomicPrimitive.returned_inherited (incrementCaller caller names) "+" [.var names.current, number 1]
      (.var (incrementSlot caller names)) (number (round + 1)) environment solved)
    (ScopedAtomicPrimitive.returned_value (incrementCaller caller names) "+" [.var names.current, number 1]
      (.var (incrementSlot caller names)) (number (round + 1)) environment solved
      (CTLUntilSourceCapture.number_closed (round + 1)))

theorem incremented_fresh (caller : Control) (names : Names) (round : Nat) (name : String)
    (member : name ∈ [names.count, names.dropped, names.result]) (fresh : FreshFor name caller.bindings) :
    FreshFor name (incremented caller names round).bindings := by
  have memberShape := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at memberShape
  have distinct := names.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  have notNext : name ≠ names.next := by rcases memberShape with rfl | rfl | rfl <;> tauto
  have notCurrent : name ≠ names.current := by rcases memberShape with rfl | rfl | rfl <;> tauto
  have remainder : name ∈ (encode (afterIncrement names)).freeVars ∨ name ∈ (encode (.var names.result)).freeVars := by
    rcases memberShape with rfl | rfl | rfl
    · exact Or.inl (remainder_name names _ (Or.inl rfl))
    · exact Or.inl (remainder_name names _ (Or.inr rfl))
    · exact Or.inr (by simp [encode, Mettapedia.Logic.LP.Term.freeVars])
  have outerKept : name ∈ (ScopedLetSource.entry caller names.next (increment names) (afterIncrement names) (.var names.result)).support :=
    active_support _ _ _ _ rfl name (remainder.imp (let_body_name name names.next (increment names) (afterIncrement names)) id)
  have producerFresh := ScopedLetSource.producer_fresh_of_entry_support caller names.next
    (increment names) (afterIncrement names) (.var names.result) name fresh outerKept notNext
  have producerKept : name ∈ (incrementCaller caller names).support := active_support _ _ _ _ rfl name remainder
  have slotApart : name ≠ incrementSlot caller names := by
    intro same
    have held : incrementSlot caller names ∈
        (ScopedLetSource.entry caller names.next (increment names) (afterIncrement names) (.var names.result)).support :=
      same ▸ outerKept
    exact freshName_not_mem _ 0 held
  apply ScopedAtomicPrimitive.returned_fresh (incrementCaller caller names) "+" [.var names.current, number 1]
    (.var (incrementSlot caller names)) (number (round + 1)) name producerFresh producerKept
  · intro operand present
    simp only [List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl
    · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using notCurrent
    · simp [number, encode, Mettapedia.Logic.LP.Term.freeVars]
  · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using slotApart
  · simp [number, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem increment_frame (codec : Codec Label) (label holds : Label) (round : Nat) (names : Names)
    (caller : Control) (frame : InitialFrame codec label holds round names caller) :
    Nonempty (IncrementFrame codec label holds round names (incremented caller names round)) := by
  obtain ⟨producerPrincipal, representative, producerResolved, producerUnbound⟩ :=
    ScopedLetSource.producer_unbound caller names.next (increment names) (afterIncrement names) (.var names.result)
      frame.principal frame.resolved (frame.fresh _ (by simp))
  obtain ⟨principal, resolved⟩ := ScopedAtomicPrimitive.returned_consistent (incrementCaller caller names) "+"
    [.var names.current, number 1] (.var (incrementSlot caller names)) (number (round + 1))
    producerPrincipal representative producerResolved producerUnbound (CTLUntilSourceCapture.number_closed (round + 1))
  have solved := resolve_sound resolved
  have inherited := incremented_inherited caller names round principal solved
  exact ⟨{
    principal, resolved
    formula := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.formula
      (LiteralQuerySource.read_literal _ (codec.literal label)) principal inherited
    operand := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.operand
      (LiteralQuerySource.read_literal _ (codec.literal holds)) principal inherited
    current := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.current
      (CTLUntilSourceCapture.number_closed round) principal inherited
    next := incremented_next caller names round principal solved
    fresh := fun name member => incremented_fresh caller names round name member
      (frame.fresh name (List.mem_cons_of_mem names.next member)) }⟩

def base (caller : Control) (older : List Goal) : Control := {caller with goals := older}
def operands (names : Names) : List Atom := [.var names.formula, .var names.operand, .var names.current, .var names.next]
def producer (caller : Control) (names : Names) (older : List Goal) : Control :=
  ScopedLetSource.producerCaller (base caller older) names.count (CTLUntilLoopSource.roundCall names)
    (afterRound names) (.var names.result)
def slot (caller : Control) (names : Names) (older : List Goal) : String :=
  ScopedLetSource.slot (base caller older) names.count (CTLUntilLoopSource.roundCall names)
    (afterRound names) (.var names.result)
def prepared (caller : Control) (names : Names) (older : List Goal) : Control :=
  ScopedAtomicCallOperands.ready (producer caller names older) "eu-round" (operands names) (.var (slot caller names older))
def arguments (caller : Control) (names : Names) (older : List Goal) : List Atom :=
  (ScopedAtomicCallOperands.slotNames (producer caller names older) "eu-round" (operands names)
    (.var (slot caller names older))).map Atom.var

private theorem phase_names (names : Names) (name : String) (member : name ∈ [names.dropped, names.result]) :
    name ∈ (encode (afterRound names)).freeVars ∨ name ∈ (encode (.var names.result)).freeVars := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · left
    rw [afterRound, ScopedLetSource.source, CapturedPatternSupport.mem_expression_names]
    exact ⟨.var names.dropped, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩
  · exact Or.inr (by simp [encode, Mettapedia.Logic.LP.Term.freeVars])

theorem slot_apart (caller : Control) (names : Names) (older : List Goal) (name : String)
    (member : name ∈ [names.dropped, names.result]) : name ≠ slot caller names older := by
  have used := phase_names names name member
  have kept : name ∈ (ScopedLetSource.entry (base caller older) names.count (CTLUntilLoopSource.roundCall names)
      (afterRound names) (.var names.result)).support :=
    active_support _ _ _ _ rfl name
      (used.imp (let_body_name name names.count (CTLUntilLoopSource.roundCall names) (afterRound names)) id)
  intro same
  have present : slot caller names older ∈
      (ScopedLetSource.entry (base caller older) names.count (CTLUntilLoopSource.roundCall names)
        (afterRound names) (.var names.result)).support := same ▸ kept
  exact freshName_not_mem _ 0 present

theorem prepared_keeps (caller : Control) (names : Names) (older : List Goal) (name : String)
    (member : name ∈ [names.dropped, names.result]) : name ∈ (prepared caller names older).support := by
  have kept : name ∈ (producer caller names older).support :=
    active_support _ _ _ _ rfl name (phase_names names name member)
  exact ClosedOnceQueryFrame.support_mono (producer caller names older) (prepared caller names older) rfl
    (by intro _ present; exact present) (by intro _ present; exact List.mem_append_left _ present)
    (by intro _ present; exact List.mem_cons_of_mem _ present) kept

theorem prepared_fresh (caller : Control) (names : Names) (older : List Goal) (name : String)
    (member : name ∈ [names.dropped, names.result]) (fresh : FreshFor name caller.bindings) :
    FreshFor name (prepared caller names older).bindings := by
  have distinct := names.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at distinct
  have memberShape := member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at memberShape
  have notCount : name ≠ names.count := by rcases memberShape with rfl | rfl <;> tauto
  have used := phase_names names name member
  have kept : name ∈ (ScopedLetSource.entry (base caller older) names.count (CTLUntilLoopSource.roundCall names)
      (afterRound names) (.var names.result)).support :=
    active_support _ _ _ _ rfl name
      (used.imp (let_body_name name names.count (CTLUntilLoopSource.roundCall names) (afterRound names)) id)
  have producerFresh := ScopedLetSource.producer_fresh_of_entry_support (base caller older) names.count
    (CTLUntilLoopSource.roundCall names) (afterRound names) (.var names.result) name fresh kept notCount
  apply ScopedAtomicCallOperands.ready_fresh_of_entry_support (producer caller names older) "eu-round" (operands names)
    (.var (slot caller names older)) name producerFresh
  · exact ClosedOnceQueryFrame.support_mono (producer caller names older)
      (ScopedAtomicCallOperands.entry (producer caller names older) "eu-round" (operands names) (.var (slot caller names older))) rfl
      (by intro _ present; exact present) (by intro _ present; exact present)
      (by intro _ present; exact List.mem_cons_of_mem _ present)
      (active_support _ _ _ _ rfl name used)
  · intro operand present
    simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at present
    rcases present with rfl | rfl | rfl | rfl <;>
      simp only [encode, Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] <;>
      rcases memberShape with rfl | rfl <;> tauto

theorem prepared_inherited (caller : Control) (names : Names) (older : List Goal)
    (environment : Environment) (solved : Solves environment (prepared caller names older).bindings) :
    Solves environment caller.bindings :=
  ScopedLetSource.inherited (base caller older) names.count (CTLUntilLoopSource.roundCall names) (afterRound names)
    (.var names.result) environment
    (ScopedAtomicCallOperands.ready_inherited (producer caller names older) "eu-round" (operands names)
      (.var (slot caller names older)) environment solved)

theorem prepared_frame (codec : Codec Label) (label holds : Label) (round : Nat) (names : Names)
    (caller : Control) (older : List Goal) (frame : IncrementFrame codec label holds round names caller) :
    ∃ principal representative,
      resolve (prepared caller names older).bindings = some principal ∧
      read principal (.var (slot caller names older)) = .var representative ∧
      (arguments caller names older).map (read principal) = CTLUntilNamedRound.values codec label holds round := by
  obtain ⟨producerPrincipal, representative, producerResolved, producerUnbound⟩ :=
    ScopedLetSource.producer_unbound (base caller older) names.count (CTLUntilLoopSource.roundCall names)
      (afterRound names) (.var names.result) frame.principal frame.resolved (frame.fresh _ (by simp))
  have inherited := ScopedLetSource.inherited (base caller older) names.count (CTLUntilLoopSource.roundCall names)
    (afterRound names) (.var names.result) producerPrincipal (resolve_sound producerResolved)
  have formula := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.formula
    (LiteralQuerySource.read_literal _ (codec.literal label)) producerPrincipal inherited
  have operand := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.operand
    (LiteralQuerySource.read_literal _ (codec.literal holds)) producerPrincipal inherited
  have current := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.current
    (CTLUntilSourceCapture.number_closed round) producerPrincipal inherited
  have next := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.next
    (CTLUntilSourceCapture.number_closed (round + 1)) producerPrincipal inherited
  have values : (operands names).map (read producerPrincipal) = CTLUntilNamedRound.values codec label holds round := by
    simp only [operands, List.map_cons, List.map_nil, formula, operand, current, next, CTLUntilNamedRound.values]
  obtain ⟨principal, name, resolved, unbound⟩ := ScopedAtomicCallOperands.ready_unbound (producer caller names older)
    "eu-round" (operands names) (.var (slot caller names older)) producerPrincipal representative producerResolved producerUnbound
  refine ⟨principal, name, resolved, unbound, ?_⟩
  apply Eq.trans (ScopedAtomicPrimitive.readings (producer caller names older) "eu-round" (operands names)
    (.var (slot caller names older)) producerPrincipal principal producerResolved resolved ?_) values
  intro atom member environment
  apply CTLUntilNamedRound.values_closed codec label holds round _ ?_ environment
  rw [← values]
  exact List.mem_map.mpr ⟨atom, member, rfl⟩

variable [DecidableEq Label]

structure Profile (codec : Codec Label) (label : Label) (program : SpaceSemantics.Program) where
  query : CTLUntilScopedRound.Query
  distinct : (CTLUntilRoundSyntax.sourceNames query).Nodup
  occurrence : Nat
  row : program.equations[occurrence]? = some
    (CTLUntilRoundSyntax.definition query (CTLUntilRoundSyntax.formals_distinct query distinct)).declaration
  otherHeads : ∀ index equation, program.equations[index]? = some equation → index ≠ occurrence → equation.head ≠ "eu-round"
  guard : CTLUntilLeafAdmission.GuardProfile codec label query program
  allSelf : ∀ handle ∈ query.handles, handle = .self
  strict : ∀ index, index < 4 → Eval.argumentIsRaw program "eu-round" index = false

def namedCall {codec : Codec Label} {label : Label} {program : SpaceSemantics.Program}
    (profile : Profile codec label program) (state : NamedGuardedCandidateBatch.State Context) (caller : Control)
    (names : Names) (older : List Goal) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    CTLUntilNamedRound.Call Context := {
  program, state, control := prepared caller names older, context, origins, pending
  arguments := arguments caller names older, destination := .var (slot caller names older)
  older := (producer caller names older).goals
  query := profile.query, distinct := profile.distinct, occurrence := profile.occurrence }

omit [DecidableEq Label] in
theorem prepare_prefix {codec : Codec Label} {label holds : Label} {round : Nat} {program : SpaceSemantics.Program}
    (profile : Profile codec label program) (state : NamedGuardedCandidateBatch.State Context)
    (caller : Control) (names : Names) (older : List Goal) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (frame : IncrementFrame codec label holds round names caller)
    (active : caller.goals = .evaluate (afterIncrement names) (.var names.result) :: older) :
    (ScopedQuerySource.machine .relational program).run 12
      (placed state.allocator state.world state.scope state.parents caller context origins pending) =
      ([], .exhausted (namedCall profile state caller names older context origins pending).before) := by
  have same : ScopedLetSource.entry (base caller older) names.count (CTLUntilLoopSource.roundCall names)
      (afterRound names) (.var names.result) = caller := by
    change {caller with goals := .evaluate (afterIncrement names) (.var names.result) :: older} = caller
    rw [← active]
  have first := ScopedLetSource.preparation program state.allocator state.world state.scope state.parents
    (base caller older) context origins pending names.count (CTLUntilLoopSource.roundCall names)
    (afterRound names) (.var names.result) ⟨frame.principal, resolve_sound frame.resolved⟩
  rw [same] at first
  have refined := ScopedLetSource.refined (base caller older) names.count (CTLUntilLoopSource.roundCall names)
    (afterRound names) (.var names.result) ⟨frame.principal, resolve_sound frame.resolved⟩
  have declared : program.equations.any (·.head == "eu-round") = true := by
    apply List.any_eq_true.mpr
    obtain ⟨bounded, actual⟩ := List.getElem?_eq_some_iff.mp profile.row
    exact ⟨_, actual ▸ List.getElem_mem bounded, by simp [CTLUntilRoundSyntax.definition, ScopedClosedEquationSource.Definition.declaration]⟩
  have last := ScopedAtomicCallOperands.preparation .relational program state.allocator state.world state.scope state.parents
    (producer caller names older) context origins pending "eu-round" (operands names) (.var (slot caller names older))
    (by
      intro atom member
      simp only [operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> exact .variable _)
    (by decide) rfl rfl (by simp [callable, declared]) (by simpa [operands] using profile.strict)
    (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  change (ScopedQuerySource.machine .relational program).run 9
    (placed state.allocator state.world state.scope state.parents
      (ScopedLetSource.producing (base caller older) names.count (CTLUntilLoopSource.roundCall names)
        (afterRound names) (.var names.result)) context origins pending) =
    ([], .exhausted (namedCall profile state caller names older context origins pending).before) at last
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 3 9 _ _ [] first
  rw [last] at joined
  simpa only [List.nil_append] using joined

set_option maxHeartbeats 1600000 in
theorem round_prefix {codec : Codec Label} {label holds : Label} {round : Nat} {program : SpaceSemantics.Program}
    (profile : Profile codec label program) (state : NamedGuardedCandidateBatch.State Context)
    (caller : Control) (names : Names) (older : List Goal) (context : Context) (origins : List Nat)
    (pending : List (CollectionWork Context)) (frame : IncrementFrame codec label holds round names caller)
    (active : caller.goals = .evaluate (afterIncrement names) (.var names.result) :: older)
    (edges : List (Nat × Nat)) (holding : List Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat)
    (stored : CTLUntilLoopStore.Stored codec label holds edges holding round bag state.world.state)
    (reserve : (Mettapedia.Machines.CTLUntilCandidateBag.candidates edges holding bag.delta).length ≤ state.allocator.usableCount) :
    ∃ (budget : Nat) (after : NamedGuardedCandidateBatch.State Context) (control : Control),
      Nonempty (RoundFrame codec label holds round (Mettapedia.Machines.CTLUntilCandidateBag.advance edges holding bag).delta.length names control) ∧
      CTLUntilLoopStore.RoundStored codec label holds edges holding round bag after.world.state ∧
      after.scope = state.scope ∧ after.parents = state.parents ∧
      control.goals = .evaluate (afterRound names) (.var names.result) :: older ∧
      control.destination = caller.destination ∧ control.cutBoundary = caller.cutBoundary ∧
      after.allocator.usableCount + (Mettapedia.Machines.CTLUntilCandidateBag.candidates edges holding bag.delta).length = state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational program).run budget
        (placed state.allocator state.world state.scope state.parents caller context origins pending) =
        ([], .exhausted (placed after.allocator after.world after.scope after.parents control context
          (origins ++ [profile.occurrence, 0]) pending)) := by
  let call := namedCall profile state caller names older context origins pending
  obtain ⟨principal, representative, resolved, unbound, readings⟩ := prepared_frame codec label holds round names caller older frame
  obtain ⟨atoms, rows, snapshot, decoded, views⟩ := stored
  have allDecoded : CTLUntilScopedRound.Decoded codec profile.query.handles state := by
    intro handle member
    exact ⟨atoms, rows, by simpa only [profile.allSelf handle member] using snapshot, decoded⟩
  let evidence : CTLUntilNamedRound.Evidence codec label holds round call := {
    atCall := rfl, principal, resolved, readings, representative, unbound
    row := profile.row, otherHeads := profile.otherHeads, profile := profile.guard, decoded := allDecoded
    frontAtoms := atoms, graphAtoms := atoms, factAtoms := atoms, fronts := rows, graph := rows, facts := rows
    frontRead := by
      change state.world.state.read profile.query.frontierHandle = some atoms
      simpa only [profile.allSelf profile.query.frontierHandle (by simp [CTLUntilScopedRound.Query.handles])] using snapshot
    frontDecode := decoded
    graphRead := by
      change state.world.state.read profile.query.edgeHandle = some atoms
      simpa only [profile.allSelf profile.query.edgeHandle (by simp [CTLUntilScopedRound.Query.handles])] using snapshot
    graphDecode := decoded
    factRead := by
      change state.world.state.read profile.query.operandHandle = some atoms
      simpa only [profile.allSelf profile.query.operandHandle (by simp [CTLUntilScopedRound.Query.handles])] using snapshot
    factDecode := decoded
    initialKnown := bag.known, initialFrontier := []
    knownRead := by
      change CTLUntilRoundPublication.observe codec (CTLUntilMixedStore.satisfactionView label) profile.query.satisfactionHandle state.world.state = _
      rw [profile.allSelf profile.query.satisfactionHandle (by simp [CTLUntilScopedRound.Query.handles]),
        CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded, views.known]
    frontierRead := by
      change CTLUntilRoundPublication.observe codec (List.filterMap (CTLUntilMixedStore.frontSelect label (round + 1)))
        profile.query.nextFrontierHandle state.world.state = _
      rw [profile.allSelf profile.query.nextFrontierHandle (by simp [CTLUntilScopedRound.Query.handles]),
        CTLUntilRoundPublication.observe_decoded codec _ _ _ _ _ snapshot decoded, CTLUntilLoopStore.next_frontier_empty views] }
  have stored : CTLUntilLoopStore.Stored codec label holds edges holding round bag state.world.state := ⟨atoms, rows, snapshot, decoded, views⟩
  obtain ⟨wordEq, knownEq, frontierEq, addedEq⟩ := CTLUntilLoopStore.evidence_views evidence profile.allSelf edges holding bag stored
  obtain ⟨childAfter, allocator, afterDecoded, preserved, other, known, frontier, capacity,
    ⟨finalPrincipal, finalResolved, finalValue⟩, returned⟩ := CTLUntilNamedRound.returns_data_frontier evidence views.separate
      (by change evidence.word.length ≤ state.allocator.usableCount; simpa only [wordEq] using reserve)
  let count := (Mettapedia.Machines.CTLUntilCandidateBag.advance edges holding bag).delta.length
  let output := call.returned (CTLUntilNamedRound.values codec label holds round) count
  have finalResolved' : resolve output.bindings = some finalPrincipal := by simpa only [addedEq] using finalResolved
  have finalValue' : read finalPrincipal (.var (slot caller names older)) = number count := by
    change read finalPrincipal (.var (slot caller names older)) = number evidence.added.length at finalValue
    simpa only [addedEq, count] using finalValue
  have preparedSolved := CTLUntilNamedRound.returned_inherits call (CTLUntilNamedRound.values codec label holds round)
    count finalPrincipal (resolve_sound finalResolved')
  have inherited := prepared_inherited caller names older finalPrincipal preparedSolved
  let finalFrame : RoundFrame codec label holds round count names output := {
    principal := finalPrincipal, resolved := finalResolved'
    formula := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.formula
      (LiteralQuerySource.read_literal _ (codec.literal label)) finalPrincipal inherited
    operand := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.operand
      (LiteralQuerySource.read_literal _ (codec.literal holds)) finalPrincipal inherited
    current := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.current
      (CTLUntilSourceCapture.number_closed round) finalPrincipal inherited
    next := CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.next
      (CTLUntilSourceCapture.number_closed (round + 1)) finalPrincipal inherited
    count := ScopedLetSource.aliased_value (base caller older) names.count (CTLUntilLoopSource.roundCall names)
      (afterRound names) (.var names.result) (number count) finalPrincipal
      (ScopedAtomicCallOperands.ready_inherited (producer caller names older) "eu-round" (operands names)
        (.var (slot caller names older)) finalPrincipal preparedSolved) finalValue'
    fresh := by
      intro name member
      exact CTLUntilNamedRound.returned_fresh codec label holds round call count name
        (prepared_fresh caller names older name member (frame.fresh name (List.mem_cons_of_mem names.count member)))
        (prepared_keeps caller names older name member)
        (by
          change name ∉ (encode (.var (slot caller names older))).freeVars
          simpa only [encode, Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] using slot_apart caller names older name member) }
  have knownAfter : CTLUntilRoundPublication.known codec label profile.query childAfter.world.state =
      some (Mettapedia.Machines.CTLUntilCandidateBag.advance edges holding bag).known := by
    change CTLUntilRoundPublication.known codec label profile.query childAfter.world.state =
      some (evidence.initialKnown ++ evidence.added) at known
    simpa only [knownEq, addedEq, Mettapedia.Machines.CTLUntilCandidateBag.advance] using known
  have nextAfter : CTLUntilRoundPublication.frontier codec label round profile.query childAfter.world.state =
      some (Mettapedia.Machines.CTLUntilCandidateBag.advance edges holding bag).delta := by
    change CTLUntilRoundPublication.frontier codec label round profile.query childAfter.world.state =
      some (evidence.initialFrontier ++ evidence.added) at frontier
    simpa only [frontierEq, addedEq, List.nil_append] using frontier
  have finalStore := CTLUntilLoopStore.round_views codec label holds edges holding round bag profile.query state childAfter
    profile.allSelf stored afterDecoded preserved other knownAfter nextAfter
  have first := prepare_prefix profile state caller names older context origins pending frame active
  let runBudget := 1 + (2 + (call.countInput (CTLUntilNamedRound.values codec label holds round)).childExecution.budget + 1 + 3) + 1
  have called : (ScopedQuerySource.machine .relational program).run runBudget call.before =
      ([], .exhausted (placed allocator childAfter.world state.scope state.parents output context
        ((origins ++ [profile.occurrence]) ++ [0]) pending)) := by
    rw [addedEq] at returned
    exact returned
  change (ScopedQuerySource.machine .relational program).run 12
    (placed state.allocator state.world state.scope state.parents caller context origins pending) =
    ([], .exhausted call.before) at first
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 12 runBudget _ _ [] first
  rw [called] at joined
  refine ⟨12 + runBudget, {state with allocator, world := childAfter.world}, output,
    ⟨finalFrame⟩, finalStore, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · change allocator.usableCount + evidence.word.length = state.allocator.usableCount at capacity
    simpa only [wordEq] using capacity
  · simpa only [List.nil_append, List.append_assoc, List.cons_append] using joined

theorem from_body {codec : Codec Label} {label holds : Label} {round : Nat} {program : SpaceSemantics.Program}
    (profile : Profile codec label program) (state : NamedGuardedCandidateBatch.State Context)
    (caller : Control) (names : Names) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : InitialFrame codec label holds round names caller)
    (edges : List (Nat × Nat)) (holding : List Nat) (bag : Mettapedia.Machines.CTLUntilCandidateBag.State Nat)
    (stored : CTLUntilLoopStore.Stored codec label holds edges holding round bag state.world.state)
    (reserve : (Mettapedia.Machines.CTLUntilCandidateBag.candidates edges holding bag.delta).length ≤ state.allocator.usableCount)
    (strict : ∀ index, index < 2 → Eval.argumentIsRaw program "+" index = false) :
    ∃ (budget : Nat) (after : NamedGuardedCandidateBatch.State Context) (control : Control),
      Nonempty (RoundFrame codec label holds round (Mettapedia.Machines.CTLUntilCandidateBag.advance edges holding bag).delta.length names control) ∧
      CTLUntilLoopStore.RoundStored codec label holds edges holding round bag after.world.state ∧
      after.scope = state.scope ∧ after.parents = state.parents ∧
      control.goals = .evaluate (afterRound names) (.var names.result) :: caller.goals ∧
      control.destination = caller.destination ∧ control.cutBoundary = caller.cutBoundary ∧
      after.allocator.usableCount + (Mettapedia.Machines.CTLUntilCandidateBag.candidates edges holding bag.delta).length = state.allocator.usableCount ∧
      (ScopedQuerySource.machine .relational program).run budget
        (placed state.allocator state.world state.scope state.parents (CTLUntilLoopSource.entry caller names) context origins pending) =
        ([], .exhausted (placed after.allocator after.world after.scope after.parents control context
          (origins ++ [0, profile.occurrence, 0]) pending)) := by
  have first := CTLUntilLoopSource.increment_prefix codec label holds round names program state.allocator state.world state.scope
    state.parents caller context origins pending frame strict
  obtain ⟨incrementFrame⟩ := increment_frame codec label holds round names caller frame
  obtain ⟨budget, after, control, finalFrame, finalStore, scope, parents, goals, destination, boundary, capacity, executed⟩ :=
    round_prefix profile state (incremented caller names round) names caller.goals context (origins ++ [0]) pending
      incrementFrame rfl edges holding bag stored reserve
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 11 budget _ _ [] first
  rw [executed] at joined
  refine ⟨11 + budget, after, control, finalFrame, finalStore, scope, parents, goals, destination, boundary, capacity, ?_⟩
  simpa only [List.nil_append, List.append_assoc, List.cons_append] using joined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopRound
