import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopFrames
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilDriverControls

/-!
# The reached EU cleanup-let and following source branch

The producer runs from the actual post-round equations. Its let alias and
evaluated operand slots are retained through the named cleanup, then the
existing branch worker reads the reached count and next-round bindings.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS.Destination
open NamedGuardedCandidateBatch (State)
open FlatQueryRowCodec (Codec)
open ClosedOnceQueryFrame (FreshFor placed)
open CTLUntilSourceRows (number)
open CTLUntilMixedStore (Row render decodeRows frontSelect)
open CTLUntilLoopSource (Names cleanupCall afterRound branch)
open CTLUntilLoopFrames (RoundFrame BranchFrame branchNames)

structure Input (Context : Type) where
  program : SpaceSemantics.Program
  state : State Context
  control : Control
  names : Names
  older : List Goal
  context : Context
  origins : List Nat
  pending : List (CollectionWork Context)
  occurrence : Nat

variable {Context Label : Type} [DecidableEq Label]

def Input.base (input : Input Context) : Control := {input.control with goals := input.older}
def Input.before (input : Input Context) : ScopedCursor Context :=
  placed input.state.allocator input.state.world input.state.scope input.state.parents
    input.control input.context input.origins input.pending
def Input.producer (input : Input Context) : Control :=
  ScopedLetSource.producerCaller input.base input.names.dropped (cleanupCall input.names)
    (branch input.names) (.var input.names.result)
def Input.slot (input : Input Context) : String :=
  ScopedLetSource.slot input.base input.names.dropped (cleanupCall input.names) (branch input.names) (.var input.names.result)
def Input.operands (input : Input Context) : List Atom := [.var input.names.formula, .var input.names.current]
def Input.ready (input : Input Context) : Control :=
  ScopedAtomicCallOperands.ready input.producer "drop" input.operands (.var input.slot)
def Input.arguments (input : Input Context) : List Atom :=
  (ScopedAtomicCallOperands.slotNames input.producer "drop" input.operands (.var input.slot)).map Atom.var
def Input.named (input : Input Context) : CTLUntilNamedCleanup.Call Context := {
  program := input.program, state := input.state, control := input.ready, context := input.context
  origins := input.origins, pending := input.pending, arguments := input.arguments, destination := .var input.slot
  older := input.producer.goals, handle := .self, formulaName := "f", roundName := "k", nodeName := "x"
  distinct := by decide, occurrence := input.occurrence }
def Input.returned (input : Input Context) (codec : Codec Label) (label : Label) (round removed : Nat) : Control :=
  input.named.returned (CTLUntilNamedCleanup.values codec label round) removed
def Input.branchCaller (input : Input Context) (codec : Codec Label) (label : Label) (round removed : Nat) : Control :=
  {input.returned codec label round removed with goals := input.older}
def Input.returnOrigins (input : Input Context) : List Nat := (input.origins ++ [input.occurrence]) ++ [0]

structure Entry (codec : Codec Label) (label holds : Label) (round count : Nat) (input : Input Context) where
  atGoal : input.control.goals = .evaluate (afterRound input.names) (.var input.names.result) :: input.older
  frame : RoundFrame codec label holds round count input.names input.control
  row : input.program.equations[input.occurrence]? = some ScopedQuerySource.CTLUntilDriverControls.dropEquation
  otherHeads : ∀ index equation, input.program.equations[index]? = some equation →
    index ≠ input.occurrence → equation.head ≠ "drop"
  strict : ∀ index, index < 2 → Eval.argumentIsRaw input.program "drop" index = false
  atoms : List Atom
  rows : List (Row Label)
  snapshot : input.state.world.state.read .self = some atoms
  decoded : decodeRows codec atoms = some rows

def Entry.removed {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input) : Nat := (entry.rows.filterMap (frontSelect label round)).length

omit [DecidableEq Label] in
private theorem root_retained (input : Input Context) :
    input.names.result ∈ (ScopedLetSource.entry input.base input.names.dropped (cleanupCall input.names)
      (branch input.names) (.var input.names.result)).support := by
  apply GuardedInsertionPairSource.goal_atom_support _ (.var input.names.result) input.names.result
  · simp [ScopedLetSource.entry, Goal.atoms]
  · simp [encode, Mettapedia.Logic.LP.Term.freeVars]

omit [DecidableEq Label] in
theorem root_ne_slot (input : Input Context) : input.names.result ≠ input.slot := by
  intro same
  apply freshName_not_mem (ScopedLetSource.entry input.base input.names.dropped (cleanupCall input.names)
    (branch input.names) (.var input.names.result)) 0
  change input.slot ∈ _
  rw [← same]
  exact root_retained input

omit [DecidableEq Label] in
theorem input_declared {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input) : callable input.program "drop" = true := by
  unfold callable
  apply Bool.or_eq_true_iff.mpr
  right
  apply List.any_eq_true.mpr
  obtain ⟨bound, found⟩ := List.getElem?_eq_some_iff.mp entry.row
  exact ⟨_, List.getElem_mem bound, by rw [found]; rfl⟩

omit [DecidableEq Label] in
theorem prepared_frame {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input) :
    ∃ principal representative,
      resolve input.ready.bindings = some principal ∧ read principal (.var input.slot) = .var representative ∧
      input.arguments.map (read principal) = CTLUntilNamedCleanup.values codec label round ∧
      FreshFor input.names.result input.ready.bindings := by
  obtain ⟨before, representative, producerResolved, producerUnbound⟩ := ScopedLetSource.producer_unbound input.base
    input.names.dropped (cleanupCall input.names) (branch input.names) (.var input.names.result)
    entry.frame.principal entry.frame.resolved (entry.frame.fresh _ (by simp))
  have producerInherited := ScopedLetSource.inherited input.base input.names.dropped (cleanupCall input.names)
    (branch input.names) (.var input.names.result) before (resolve_sound producerResolved)
  have formula := CapturedQueryOperands.resolved_forces entry.frame.resolved (.var input.names.formula) (codec.encode label)
    entry.frame.formula (LiteralQuerySource.read_literal _ (codec.literal label)) before producerInherited
  have current := CapturedQueryOperands.resolved_forces entry.frame.resolved (.var input.names.current) (number round)
    entry.frame.current (CTLUntilSourceCapture.number_closed round) before producerInherited
  obtain ⟨principal, result, resolved, unbound⟩ := ScopedAtomicCallOperands.ready_unbound input.producer "drop"
    input.operands (.var input.slot) before representative producerResolved producerUnbound
  have readings := ScopedAtomicPrimitive.readings input.producer "drop" input.operands (.var input.slot)
    before principal producerResolved resolved (by
      intro atom member environment
      simp only [Input.operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · rw [formula]; exact LiteralQuerySource.read_literal _ (codec.literal label) environment
      · rw [current]; exact CTLUntilSourceCapture.number_closed round environment)
  have names := input.names.distinct
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
  have producerFresh : FreshFor input.names.result input.producer.bindings := by
    apply ScopedLetSource.producer_fresh_of_entry_support
    · exact entry.frame.fresh _ (by simp)
    · exact root_retained input
    · tauto
  have fresh : FreshFor input.names.result input.ready.bindings := by
    apply ScopedAtomicCallOperands.ready_fresh_of_entry_support input.producer "drop" input.operands (.var input.slot)
      input.names.result producerFresh
    · apply GuardedInsertionPairSource.goal_atom_support _ (.var input.names.result) input.names.result
      · simp [ScopedAtomicCallOperands.entry, Input.producer, ScopedLetSource.producerCaller, Goal.atoms]
      · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
    · intro atom member
      simp only [Input.operands, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [encode, Mettapedia.Logic.LP.Term.freeVars, Finset.mem_singleton] <;> tauto
  exact ⟨principal, result, resolved, unbound,
    by simpa only [Input.arguments, Input.operands, CTLUntilNamedCleanup.values, List.map_cons, List.map_nil, formula, current] using readings,
    fresh⟩

omit [DecidableEq Label] in
theorem prepare_prefix {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input) :
    (ScopedQuerySource.machine .relational input.program).run 8 input.before = ([], .exhausted input.named.before) := by
  have first := ScopedLetSource.preparation input.program input.state.allocator input.state.world input.state.scope input.state.parents
    input.base input.context input.origins input.pending input.names.dropped (cleanupCall input.names) (branch input.names)
    (.var input.names.result) ⟨entry.frame.principal, resolve_sound entry.frame.resolved⟩
  have restored : ScopedLetSource.entry input.base input.names.dropped (cleanupCall input.names)
      (branch input.names) (.var input.names.result) = input.control := by
    change {input.control with goals := .evaluate (afterRound input.names) (.var input.names.result) :: input.older} = _
    rw [← entry.atGoal]
  rw [restored] at first
  obtain ⟨principal, representative, producerResolved, _unbound⟩ := ScopedLetSource.producer_unbound input.base
    input.names.dropped (cleanupCall input.names) (branch input.names) (.var input.names.result)
    entry.frame.principal entry.frame.resolved (entry.frame.fresh _ (by simp))
  have prepared := ScopedAtomicCallOperands.preparation .relational input.program input.state.allocator input.state.world
    input.state.scope input.state.parents input.producer input.context input.origins input.pending "drop" input.operands (.var input.slot)
    (by intro atom member; simp only [Input.operands, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact .variable _)
    (by decide) rfl rfl (input_declared entry) entry.strict ⟨principal, resolve_sound producerResolved⟩
  change (ScopedQuerySource.machine .relational input.program).run 5
    (placed input.state.allocator input.state.world input.state.scope input.state.parents
      (ScopedLetSource.producing input.base input.names.dropped (cleanupCall input.names) (branch input.names) (.var input.names.result))
      input.context input.origins input.pending) = ([], .exhausted input.named.before) at prepared
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending 3 5 _ _ [] first
  rw [prepared] at joined
  simpa only [List.nil_append, Input.before] using joined

omit [DecidableEq Label] in
theorem returned_inherits (input : Input Context) (codec : Codec Label) (label : Label) (round removed : Nat)
    (environment : Environment) (solved : Solves environment (input.returned codec label round removed).bindings) :
    Solves environment input.control.bindings :=
  ScopedLetSource.inherited input.base input.names.dropped (cleanupCall input.names) (branch input.names) (.var input.names.result)
    environment (ScopedAtomicCallOperands.ready_inherited input.producer "drop" input.operands (.var input.slot)
      environment (CTLUntilNamedCleanup.returned_inherits input.named _ removed environment solved))

omit [DecidableEq Label] in
theorem returned_branch (input : Input Context) (codec : Codec Label) (label : Label) (round removed : Nat) :
    input.returned codec label round removed =
      CTLUntilLoopBranch.entry (input.branchCaller codec label round removed) (branchNames input.names) := rfl

structure Receipt {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input) where
  after : State Context
  allocator : Allocator
  budget : Nat
  reading : after.world.state.read .self = some ((CTLUntilCleanup.remaining label round entry.rows).map (render codec))
  decoded : decodeRows codec ((CTLUntilCleanup.remaining label round entry.rows).map (render codec)) =
    some (CTLUntilCleanup.remaining label round entry.rows)
  outside : ∀ other, other ≠ .self → after.world.state.read other = input.state.world.state.read other
  cells : after.world.state.cells = input.state.world.state.cells
  debit : allocator.usableCount + entry.removed = input.state.allocator.usableCount
  frame : BranchFrame codec label holds round count input.names (input.branchCaller codec label round entry.removed)
  exact : (ScopedQuerySource.machine .relational input.program).run budget input.before =
    ([], .exhausted (placed allocator after.world input.state.scope input.state.parents
      (input.returned codec label round entry.removed) input.context input.returnOrigins input.pending))

theorem executes {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input)
    (reserve : entry.removed ≤ input.state.allocator.usableCount) : Nonempty (Receipt entry) := by
  obtain ⟨principal, representative, resolved, unbound, readings, rootFresh⟩ := prepared_frame entry
  let evidence : CTLUntilNamedCleanup.Evidence codec label round input.named := {
    atCall := rfl, principal, resolved, readings, representative, unbound
    row := entry.row, otherHeads := entry.otherHeads
    atoms := entry.atoms, rows := entry.rows, snapshot := entry.snapshot, decoded := entry.decoded }
  obtain ⟨after, allocator, reading, decoded, outside, cells, debit, ⟨finalPrincipal, finalResolved, _value⟩, executed⟩ :=
    CTLUntilNamedCleanup.returns evidence reserve
  have inherited := returned_inherits input codec label round entry.removed finalPrincipal (resolve_sound finalResolved)
  have retained : input.names.result ∈ input.ready.support := by
    apply GuardedInsertionPairSource.goal_atom_support _ (.var input.names.result) input.names.result
    · simp [Input.ready, ScopedAtomicCallOperands.ready, Input.producer, ScopedLetSource.producerCaller, Goal.atoms]
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  have keptRoot := CTLUntilNamedCleanup.returned_fresh codec label round input.named entry.removed input.names.result rootFresh retained
    (by simpa [Input.named, encode, Mettapedia.Logic.LP.Term.freeVars] using root_ne_slot input)
  have branchFrame : BranchFrame codec label holds round count input.names (input.branchCaller codec label round entry.removed) := {
    principal := finalPrincipal, resolved := finalResolved
    formula := CapturedQueryOperands.resolved_forces entry.frame.resolved _ _ entry.frame.formula
      (LiteralQuerySource.read_literal _ (codec.literal label)) finalPrincipal inherited
    operand := CapturedQueryOperands.resolved_forces entry.frame.resolved _ _ entry.frame.operand
      (LiteralQuerySource.read_literal _ (codec.literal holds)) finalPrincipal inherited
    nextValue := CapturedQueryOperands.resolved_forces entry.frame.resolved _ _ entry.frame.next
      (CTLUntilSourceCapture.number_closed (round + 1)) finalPrincipal inherited
    countValue := CapturedQueryOperands.resolved_forces entry.frame.resolved _ _ entry.frame.count
      (CTLUntilSourceCapture.number_closed count) finalPrincipal inherited
    rootFresh := keptRoot
    rootApart := by
      have names := input.names.distinct
      simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or] at names
      change input.names.result ∉ [input.names.formula, input.names.operand, input.names.next, input.names.count]
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
      tauto }
  let budget := 1 + (2 + (CTLUntilCountedCleanup.childExecution
    (input.named.countInput (CTLUntilNamedCleanup.values codec label round)) .self
    (input.named.name "f") (input.named.name "k") (input.named.name "x")).budget + 1 + 3) + 1
  change (ScopedQuerySource.machine .relational input.program).run budget input.named.before = _ at executed
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending 8 budget _ _ [] (prepare_prefix entry)
  rw [executed] at joined
  change (ScopedQuerySource.machine .relational input.program).run (8 + budget) input.before =
    ([] ++ [], .exhausted (placed allocator after.world input.state.scope input.state.parents
      (input.returned codec label round entry.removed) input.context input.returnOrigins input.pending)) at joined
  exact ⟨{
    after, allocator, budget := 8 + budget, reading, decoded, outside, cells, debit
    frame := branchFrame
    exact := by simpa only [List.nil_append] using joined }⟩

theorem quiet_returns {codec : Codec Label} {label holds : Label} {round : Nat} {input : Input Context}
    (entry : Entry codec label holds round 0 input)
    (reserve : entry.removed ≤ input.state.allocator.usableCount)
    (strict : ∀ index, index < 2 → Eval.argumentIsRaw input.program "==" index = false) :
    ∃ receipt : Receipt entry, ∃ principal,
      resolve (CTLUntilLoopBranch.quietReturned (input.branchCaller codec label round entry.removed) (branchNames input.names)).bindings = some principal ∧
      read principal (.var input.names.result) = number (round + 1) ∧
      (ScopedQuerySource.machine .relational input.program).run (receipt.budget + 11) input.before =
        ([], .exhausted (placed receipt.allocator receipt.after.world input.state.scope input.state.parents
          (CTLUntilLoopBranch.quietReturned (input.branchCaller codec label round entry.removed) (branchNames input.names))
          input.context (input.returnOrigins ++ [0]) input.pending)) := by
  obtain ⟨receipt⟩ := executes entry reserve
  obtain ⟨principal, resolved, reading, last⟩ := CTLUntilLoopBranch.quiet_prefix codec label holds (round + 1)
    (branchNames input.names) input.program receipt.allocator receipt.after.world input.state.scope input.state.parents
    (input.branchCaller codec label round entry.removed) input.context input.returnOrigins input.pending receipt.frame strict
  have first := receipt.exact
  rw [returned_branch] at first
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending receipt.budget 11 _ _ [] first
  rw [last] at joined
  exact ⟨receipt, principal, resolved, reading, by simpa only [List.nil_append] using joined⟩

theorem recursive_prepared {codec : Codec Label} {label holds : Label} {round count : Nat} {input : Input Context}
    (entry : Entry codec label holds round count input) (nonzero : count ≠ 0)
    (reserve : entry.removed ≤ input.state.allocator.usableCount)
    (equalityStrict : ∀ index, index < 2 → Eval.argumentIsRaw input.program "==" index = false)
    (declared : callable input.program "eu-loop" = true)
    (recursiveStrict : ∀ index, index < 3 → Eval.argumentIsRaw input.program "eu-loop" index = false) :
    ∃ receipt : Receipt entry, ∃ principal,
      resolve (CTLUntilLoopBranch.recursiveReady (input.branchCaller codec label round entry.removed) (branchNames input.names) count).bindings = some principal ∧
      (CTLUntilLoopBranch.recursiveArguments (input.branchCaller codec label round entry.removed) (branchNames input.names) count).map (read principal) =
        [codec.encode label, codec.encode holds, number (round + 1)] ∧
      FreshFor input.names.result (CTLUntilLoopBranch.recursiveReady
        (input.branchCaller codec label round entry.removed) (branchNames input.names) count).bindings ∧
      read principal (.var input.names.result) = .var input.names.result ∧
      (ScopedQuerySource.machine .relational input.program).run (receipt.budget + 16) input.before =
        ([], .exhausted (placed receipt.allocator receipt.after.world input.state.scope input.state.parents
          (CTLUntilLoopBranch.recursiveReady (input.branchCaller codec label round entry.removed) (branchNames input.names) count)
          input.context (input.returnOrigins ++ [0]) input.pending)) := by
  obtain ⟨receipt⟩ := executes entry reserve
  obtain ⟨principal, resolved, readings, fresh, unbound, last⟩ := CTLUntilLoopBranch.recursive_prefix codec label holds (round + 1) count
    (branchNames input.names) input.program receipt.allocator receipt.after.world input.state.scope input.state.parents
    (input.branchCaller codec label round entry.removed) input.context input.returnOrigins input.pending
    receipt.frame nonzero equalityStrict declared recursiveStrict
  have first := receipt.exact
  rw [returned_branch] at first
  have joined := (ScopedQuerySource.machine .relational input.program).established_and_pending receipt.budget 16 _ _ [] first
  rw [last] at joined
  exact ⟨receipt, principal, resolved, readings, fresh, unbound, by simpa only [List.nil_append] using joined⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop.quiet_returns
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopDrop.recursive_prepared
