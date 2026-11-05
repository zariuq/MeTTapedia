import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicPrimitive
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilSourceCapture
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.FlatQueryRowCodec
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedInsertionPairSource

/-!
# The EU loop's actual quiet-or-recursive source branch

The source equality is evaluated once into its fresh condition slot. Quiet
execution refines the outer result with the next round number; productive
execution prepares the actual recursive invocation and retains its caller.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)
open FlatQueryRowCodec (Codec)
open CTLUntilSourceRows (number)

structure Names where
  formula : String
  operand : String
  next : String
  count : String
  root : String

def arguments (names : Names) : List Atom := [.var names.formula, .var names.operand, .var names.next]
def recurse (names : Names) : Atom := ScopedAtomicCallOperands.source "eu-loop" (arguments names)
def condition (names : Names) : Atom := ScopedAtomicCallOperands.source "==" [.var names.count, number 0]
def source (names : Names) : Atom := .expression [.symbol "if", condition names, .var names.next, recurse names]
def entry (caller : Control) (names : Names) : Control :=
  {caller with goals := .evaluate (source names) (.var names.root) :: caller.goals}
def slot (caller : Control) (names : Names) : String := freshName (entry caller names) 0
def waiting (caller : Control) (names : Names) : Control :=
  {caller with goals := .branch (.var (slot caller names)) (.var names.next) (recurse names) (.var names.root) :: caller.goals}
def compared (caller : Control) (names : Names) (count : Nat) : Control :=
  ScopedAtomicPrimitive.returned (waiting caller names) "==" [.var names.count, number 0]
    (.var (slot caller names)) (Effects.boolean (decide (count = 0)))
def selectedCaller (caller : Control) (names : Names) (count : Nat) : Control :=
  {compared caller names count with goals := caller.goals}
def selected (caller : Control) (names : Names) (count : Nat) : Control :=
  {selectedCaller caller names count with
    goals := .evaluate (if count = 0 then .var names.next else recurse names) (.var names.root) :: caller.goals}
def quietReturned (caller : Control) (names : Names) : Control :=
  {selectedCaller caller names 0 with bindings := (selectedCaller caller names 0).bindings ++ [(.var names.next, .var names.root)]}
def recursiveReady (caller : Control) (names : Names) (count : Nat) : Control :=
  ScopedAtomicCallOperands.ready (selectedCaller caller names count) "eu-loop" (arguments names) (.var names.root)
def recursiveArguments (caller : Control) (names : Names) (count : Nat) : List Atom :=
  (ScopedAtomicCallOperands.slotNames (selectedCaller caller names count) "eu-loop" (arguments names) (.var names.root)).map Atom.var

variable {Context Label : Type}

structure Frame (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names) (caller : Control) where
  principal : Environment
  resolved : resolve caller.bindings = some principal
  formula : read principal (.var names.formula) = codec.encode label
  operand : read principal (.var names.operand) = codec.encode holds
  nextValue : read principal (.var names.next) = number next
  countValue : read principal (.var names.count) = number count
  rootFresh : FreshFor names.root caller.bindings
  rootApart : names.root ∉ [names.formula, names.operand, names.next, names.count]

theorem slot_fresh (caller : Control) (names : Names) : FreshFor (slot caller names) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (entry caller names) _ (freshName_not_mem _ _)

private theorem root_retained (caller : Control) (names : Names) : names.root ∈ (entry caller names).support := by
  apply GuardedInsertionPairSource.goal_atom_support _ (.var names.root) names.root
  · simp [entry, Goal.atoms]
  · simp [encode, Mettapedia.Logic.LP.Term.freeVars]

theorem root_ne_slot (caller : Control) (names : Names) : names.root ≠ slot caller names := by
  intro same
  apply freshName_not_mem (entry caller names) 0
  change slot caller names ∈ (entry caller names).support
  rw [← same]
  exact root_retained caller names

theorem entry_prefix (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control) (names : Names)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context)) :
    (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (entry caller names) context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        (ScopedAtomicCallOperands.entry (waiting caller names) "==" [.var names.count, number 0] (.var (slot caller names)))
        context origins pending)) := by
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, waiting, slot, condition, ScopedAtomicCallOperands.entry]

theorem comparison_prefix (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : Frame codec label holds next count names caller)
    (strict : ∀ index, index < 2 → Eval.argumentIsRaw program "==" index = false) :
    (ScopedQuerySource.machine .relational program).run 8
      (placed allocator world scope parents (entry caller names) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (compared caller names count)
        context (origins ++ [0]) pending)) := by
  have fresh := slot_fresh caller names
  have unbound := ClosedOnceQueryFrame.fresh_read caller.bindings _ frame.principal fresh frame.resolved
  have applied : StdLib.apply world.state "==" ([.var names.count, number 0].map (read frame.principal)) =
      .ok (world.state, [Effects.boolean (decide (count = 0))]) := by
    simp only [List.map_cons, List.map_nil, frame.countValue, CTLUntilSourceCapture.number_closed, StdLib.structural_equality]
    simp [number, beq_eq_decide]
  have evaluated := ScopedAtomicPrimitive.source_prefix program allocator world scope parents (waiting caller names)
    context origins pending "==" [.var names.count, number 0] (.var (slot caller names))
    (Effects.boolean (decide (count = 0))) frame.principal (slot caller names)
    (by intro atom member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl; exact .variable _; exact .grounded _)
    (by decide) rfl rfl (by simp [callable, StdLib.known]) strict frame.resolved unbound
    (by intro atom member environment; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · rw [frame.countValue]; exact CTLUntilSourceCapture.number_closed count environment
        · rw [CTLUntilSourceCapture.number_closed]; exact CTLUntilSourceCapture.number_closed 0 environment)
    (by decide) (by decide) (by decide) (by decide) (by decide) applied (PresenceGuardSource.read_boolean _)
  change (ScopedQuerySource.machine .relational program).run 7
    (placed allocator world scope parents
      (ScopedAtomicCallOperands.entry (waiting caller names) "==" [.var names.count, number 0] (.var (slot caller names)))
      context origins pending) =
    ([], .exhausted (placed allocator world scope parents (compared caller names count) context (origins ++ [0]) pending)) at evaluated
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 1 7 _ _ []
    (entry_prefix program allocator world scope parents caller names context origins pending)
  rw [evaluated] at joined
  simpa only [List.nil_append] using joined

theorem compared_resolves (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names)
    (caller : Control) (frame : Frame codec label holds next count names caller) :
    ∃ environment, resolve (compared caller names count).bindings = some environment := by
  exact ScopedAtomicPrimitive.returned_consistent (waiting caller names) "==" [.var names.count, number 0]
    (.var (slot caller names)) (Effects.boolean (decide (count = 0))) frame.principal (slot caller names)
    frame.resolved (ClosedOnceQueryFrame.fresh_read caller.bindings _ frame.principal (slot_fresh caller names) frame.resolved)
    (PresenceGuardSource.read_boolean _)

theorem compared_inherits (caller : Control) (names : Names) (count : Nat) (environment : Environment)
    (solved : Solves environment (compared caller names count).bindings) : Solves environment caller.bindings :=
  ScopedAtomicPrimitive.returned_inherited (waiting caller names) "==" [.var names.count, number 0]
    (.var (slot caller names)) (Effects.boolean (decide (count = 0))) environment solved

theorem compared_fresh (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names)
    (caller : Control) (frame : Frame codec label holds next count names caller) :
    FreshFor names.root (compared caller names count).bindings := by
  apply ScopedAtomicPrimitive.returned_fresh_of_entry_support (waiting caller names) "==" [.var names.count, number 0]
    (.var (slot caller names)) (Effects.boolean (decide (count = 0))) names.root frame.rootFresh
  · apply GuardedInsertionPairSource.goal_atom_support _ (.var names.root) names.root
    · simp [ScopedAtomicCallOperands.entry, waiting, Goal.atoms]
    · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
  · intro atom member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · have different : names.root ≠ names.count := by intro same; exact frame.rootApart (by simp [same])
      simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using different
    · simp [number, encode, Mettapedia.Logic.LP.Term.freeVars]
  · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using root_ne_slot caller names
  · simp [Effects.boolean, encode, Mettapedia.Logic.LP.Term.freeVars]

theorem selected_prefix (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : Frame codec label holds next count names caller)
    (strict : ∀ index, index < 2 → Eval.argumentIsRaw program "==" index = false) :
    (ScopedQuerySource.machine .relational program).run 9
      (placed allocator world scope parents (entry caller names) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (selected caller names count)
        context (origins ++ [0]) pending)) := by
  obtain ⟨environment, resolved⟩ := compared_resolves codec label holds next count names caller frame
  have value := ScopedAtomicPrimitive.returned_value (waiting caller names) "==" [.var names.count, number 0]
    (.var (slot caller names)) (Effects.boolean (decide (count = 0))) environment (resolve_sound resolved)
    (PresenceGuardSource.read_boolean _)
  have chosen := PresenceConditionalSource.branch_step program allocator world scope parents (compared caller names count)
    context (origins ++ [0]) pending (.var (slot caller names)) (.var names.next) (recurse names) (.var names.root)
    caller.goals environment rfl resolved
  rw [value] at chosen
  have step := ScopedQuerySource.Guards.placed_ordinary_step .relational program allocator world scope parents
    (compared caller names count) context (origins ++ [0]) pending
    (.branch (.var (slot caller names)) (.var names.next) (recurse names) (.var names.root)) caller.goals rfl rfl
  rw [chosen] at step
  have last : (ScopedQuerySource.machine .relational program).run 1
      (placed allocator world scope parents (compared caller names count) context (origins ++ [0]) pending) =
      ([], .exhausted (placed allocator world scope parents (selected caller names count) context (origins ++ [0]) pending)) := by
    simp only [Machine.run, step]
    by_cases quiet : count = 0 <;> simp [quiet, Effects.boolean, selected, selectedCaller]
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 8 1 _ _ []
    (comparison_prefix codec label holds next count names program allocator world scope parents caller context origins pending frame strict)
  rw [last] at joined
  simpa only [List.nil_append] using joined

theorem selected_frame (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names)
    (caller : Control) (frame : Frame codec label holds next count names caller) :
    ∃ environment, resolve (selectedCaller caller names count).bindings = some environment ∧
      read environment (.var names.formula) = codec.encode label ∧
      read environment (.var names.operand) = codec.encode holds ∧
      read environment (.var names.next) = number next ∧
      FreshFor names.root (selectedCaller caller names count).bindings := by
  obtain ⟨environment, resolved⟩ := compared_resolves codec label holds next count names caller frame
  have inherited := compared_inherits caller names count environment (resolve_sound resolved)
  exact ⟨environment, resolved,
    CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.formula
      (LiteralQuerySource.read_literal _ (codec.literal label)) environment inherited,
    CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.operand
      (LiteralQuerySource.read_literal _ (codec.literal holds)) environment inherited,
    CapturedQueryOperands.resolved_forces frame.resolved _ _ frame.nextValue
      (CTLUntilSourceCapture.number_closed next) environment inherited,
    compared_fresh codec label holds next count names caller frame⟩

theorem quiet_prefix (codec : Codec Label) (label holds : Label) (next : Nat) (names : Names)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : Frame codec label holds next 0 names caller)
    (strict : ∀ index, index < 2 → Eval.argumentIsRaw program "==" index = false) :
    ∃ environment, resolve (quietReturned caller names).bindings = some environment ∧
      read environment (.var names.root) = number next ∧
      (ScopedQuerySource.machine .relational program).run 11
        (placed allocator world scope parents (entry caller names) context origins pending) =
        ([], .exhausted (placed allocator world scope parents (quietReturned caller names)
          context (origins ++ [0]) pending)) := by
  obtain ⟨principal, resolved, _formula, _operand, nextValue, fresh⟩ := selected_frame codec label holds next 0 names caller frame
  have apart : names.root ≠ names.next := by intro same; exact frame.rootApart (by simp [same])
  have refined := ScopedMutationSource.refine_fresh_operand (selectedCaller caller names 0).bindings names.root (.var names.next)
    fresh (by simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using apart) ⟨principal, resolve_sound resolved⟩
  have last : (ScopedQuerySource.machine .relational program).run 2
      (placed allocator world scope parents (selected caller names 0) context (origins ++ [0]) pending) =
      ([], .exhausted (placed allocator world scope parents (quietReturned caller names) context (origins ++ [0]) pending)) := by
    simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
      ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
      placed, selected, quietReturned, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
      prepare, replace, installChild, retainChild, refined]
    rfl
  obtain ⟨environment, finalResolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
  have inherited : Solves environment (selectedCaller caller names 0).bindings := by
    intro pair member
    exact resolve_sound finalResolved pair (List.mem_append_left _ member)
  have nextAfter := CapturedQueryOperands.resolved_forces resolved (.var names.next) (number next) nextValue
    (CTLUntilSourceCapture.number_closed next) environment inherited
  have bound := resolve_sound finalResolved (.var names.next, .var names.root) (List.mem_append_right _ (by simp))
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 9 2 _ _ []
    (selected_prefix codec label holds next 0 names program allocator world scope parents caller context origins pending frame strict)
  rw [last] at joined
  exact ⟨environment, finalResolved, bound.symm.trans nextAfter, by simpa only [List.nil_append] using joined⟩

theorem recursive_inherits (caller : Control) (names : Names) (count : Nat) (environment : Environment)
    (solved : Solves environment (recursiveReady caller names count).bindings) : Solves environment caller.bindings :=
  compared_inherits caller names count environment
    (ScopedAtomicCallOperands.ready_inherited (selectedCaller caller names count) "eu-loop" (arguments names)
      (.var names.root) environment solved)

theorem recursive_prefix (codec : Codec Label) (label holds : Label) (next count : Nat) (names : Names)
    (program : SpaceSemantics.Program) (allocator : Allocator) (world : World)
    (scope : CollectionScope Context) (parents : List (CollectionScope Context)) (caller : Control)
    (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (frame : Frame codec label holds next count names caller) (nonzero : count ≠ 0)
    (equalityStrict : ∀ index, index < 2 → Eval.argumentIsRaw program "==" index = false)
    (declared : callable program "eu-loop" = true)
    (recursiveStrict : ∀ index, index < 3 → Eval.argumentIsRaw program "eu-loop" index = false) :
    ∃ environment, resolve (recursiveReady caller names count).bindings = some environment ∧
      (recursiveArguments caller names count).map (read environment) = [codec.encode label, codec.encode holds, number next] ∧
      FreshFor names.root (recursiveReady caller names count).bindings ∧
      read environment (.var names.root) = .var names.root ∧
      (ScopedQuerySource.machine .relational program).run 16
        (placed allocator world scope parents (entry caller names) context origins pending) =
        ([], .exhausted (placed allocator world scope parents (recursiveReady caller names count)
          context (origins ++ [0]) pending)) := by
  obtain ⟨principal, resolved, formula, operand, nextValue, fresh⟩ := selected_frame codec label holds next count names caller frame
  have prepared := ScopedAtomicCallOperands.preparation .relational program allocator world scope parents
    (selectedCaller caller names count) context (origins ++ [0]) pending "eu-loop" (arguments names) (.var names.root)
    (by intro atom member; simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> exact .variable _)
    (by decide) rfl rfl declared recursiveStrict ⟨principal, resolve_sound resolved⟩
  have fromSelected : (ScopedQuerySource.machine .relational program).run 7
      (placed allocator world scope parents (selected caller names count) context (origins ++ [0]) pending) =
      ([], .exhausted (placed allocator world scope parents (recursiveReady caller names count)
        context (origins ++ [0]) pending)) := by
    simpa only [selected, if_neg nonzero, ScopedAtomicCallOperands.entry, recurse, arguments, List.length_cons,
      List.length_nil, recursiveReady, selectedCaller] using prepared
  obtain ⟨environment, finalResolved⟩ := resolve_complete
    (ScopedAtomicCallOperands.ready_consistent (selectedCaller caller names count) "eu-loop" (arguments names) (.var names.root)
      ⟨principal, resolve_sound resolved⟩)
  have rootFresh : FreshFor names.root (recursiveReady caller names count).bindings := by
    apply ScopedAtomicCallOperands.ready_fresh_of_entry_support (selectedCaller caller names count) "eu-loop"
      (arguments names) (.var names.root) names.root fresh
    · apply GuardedInsertionPairSource.goal_atom_support _ (.var names.root) names.root
      · simp [ScopedAtomicCallOperands.entry, Goal.atoms]
      · simp [encode, Mettapedia.Logic.LP.Term.freeVars]
    · intro atom member
      simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;>
        simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using
          (show names.root ≠ _ from fun same => frame.rootApart (by simp [same]))
  have readings := ScopedAtomicPrimitive.readings (selectedCaller caller names count) "eu-loop" (arguments names)
    (.var names.root) principal environment resolved finalResolved (by
      intro atom member environment
      simp only [arguments, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · rw [formula]; exact LiteralQuerySource.read_literal _ (codec.literal label) environment
      · rw [operand]; exact LiteralQuerySource.read_literal _ (codec.literal holds) environment
      · rw [nextValue]; exact CTLUntilSourceCapture.number_closed next environment)
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending 9 7 _ _ []
    (selected_prefix codec label holds next count names program allocator world scope parents caller context origins pending frame equalityStrict)
  rw [fromSelected] at joined
  refine ⟨environment, finalResolved, ?_, rootFresh,
    ClosedOnceQueryFrame.fresh_read _ names.root environment rootFresh finalResolved, ?_⟩
  · simpa only [recursiveArguments, arguments, List.map_cons, List.map_nil, formula, operand, nextValue] using readings
  · simpa only [List.nil_append] using joined

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch.quiet_prefix
#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.CTLUntilLoopBranch.recursive_prefix
