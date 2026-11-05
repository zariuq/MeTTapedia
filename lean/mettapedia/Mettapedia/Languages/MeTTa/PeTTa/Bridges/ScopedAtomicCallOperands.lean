import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedCallOperands

/-!
# Atomic operands in the actual scoped call frame

An evaluated atomic operand adds one equation to its fresh slot. In particular,
reading a captured variable does not turn the captured value into executable
syntax. The source scheduler prepares an arbitrary finite argument list in
one entry step and two steps per operand, retaining the caller's continuation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

inductive Atomic : Atom → Prop where
  | variable (name : String) : Atomic (.var name)
  | symbol (name : String) : Atomic (.symbol name)
  | grounded (value : GroundedValue) : Atomic (.grounded value)

def source (head : String) (operands : List Atom) : Atom :=
  .expression (.symbol head :: operands)

def entry (caller : Control) (head : String) (operands : List Atom) (destination : Atom) : Control :=
  {caller with goals := .evaluate (source head operands) destination :: caller.goals}

def slotNames (caller : Control) (head : String) (operands : List Atom) (destination : Atom) : List String :=
  (List.range operands.length).map (freshName (entry caller head operands destination))

def pairs (caller : Control) (head : String) (operands : List Atom) (destination : Atom) : List (Atom × String) :=
  operands.zip (slotNames caller head operands destination)

def equationsFor (operands : List (Atom × String)) : Equations :=
  operands.map fun pair => (pair.1, .var pair.2)

def goalsFor (operands : List (Atom × String)) : List Goal :=
  operands.map fun pair => .evaluate pair.1 (.var pair.2)

def ready (caller : Control) (head : String) (operands : List Atom) (destination : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ equationsFor (pairs caller head operands destination)
    goals := .invoke head ((slotNames caller head operands destination).map Atom.var) destination :: caller.goals}

theorem names_length (caller : Control) (head : String) (operands : List Atom) (destination : Atom) :
    (slotNames caller head operands destination).length = operands.length := by simp [slotNames]

theorem pairs_length (caller : Control) (head : String) (operands : List Atom) (destination : Atom) :
    (pairs caller head operands destination).length = operands.length := by simp [pairs, names_length]

theorem names_distinct (caller : Control) (head : String) (operands : List Atom) (destination : Atom) :
    (slotNames caller head operands destination).Nodup :=
  List.Nodup.map (freshName_injective _) List.nodup_range

theorem name_fresh (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (name : String) (member : name ∈ slotNames caller head operands destination) :
    FreshFor name caller.bindings := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact ClosedOnceQueryFrame.fresh_for_bindings (entry caller head operands destination) _
    (freshName_not_mem _ _)

theorem name_operand_apart (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (name : String) (member : name ∈ slotNames caller head operands destination)
    (operand : Atom) (occurs : operand ∈ operands) : name ∉ (encode operand).freeVars := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  intro present
  apply freshName_not_mem (entry caller head operands destination) index
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  refine Or.inr ⟨source head operands, ?_, ?_⟩
  · simp [entry, Goal.atoms]
  · rw [source, CapturedPatternSupport.mem_expression_names]
    exact ⟨operand, List.mem_cons_of_mem _ occurs, present⟩

theorem name_destination_apart (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (name : String) (member : name ∈ slotNames caller head operands destination) :
    name ∉ (encode destination).freeVars := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  intro present
  apply freshName_not_mem (entry caller head operands destination) index
  apply Finset.mem_union_right
  apply (ClosedOnceQueryFrame.fold_support_iff _ _ _).mpr
  exact Or.inr ⟨destination, by simp [entry, Goal.atoms], present⟩

/-- Fresh slots are disjoint both from the reached equations and from all
the original operands, including operands processed later. -/
def FreshOperands (bindings : Equations) (operands : List (Atom × String)) : Prop :=
  (operands.map Prod.snd).Nodup ∧
    (∀ pair ∈ operands, FreshFor pair.2 bindings) ∧
    ∀ pair ∈ operands, ∀ other ∈ operands, pair.2 ∉ (encode other.1).freeVars

theorem pairs_fresh (caller : Control) (head : String) (operands : List Atom) (destination : Atom) :
    FreshOperands caller.bindings (pairs caller head operands destination) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [pairs, List.map_snd_zip (by simp [names_length])]
    exact names_distinct caller head operands destination
  · intro pair member
    exact name_fresh caller head operands destination pair.2 (List.of_mem_zip member).2
  · intro pair member other present
    exact name_operand_apart caller head operands destination pair.2
      (List.of_mem_zip member).2 other.1 (List.of_mem_zip present).1

theorem FreshOperands.tail {bindings : Equations} {pair : Atom × String} {operands : List (Atom × String)}
    (fresh : FreshOperands bindings (pair :: operands)) :
    FreshOperands (bindings ++ [(pair.1, .var pair.2)]) operands := by
  have distinct := List.nodup_cons.mp fresh.1
  refine ⟨distinct.2, ?_, ?_⟩
  · intro other member equation present
    rcases List.mem_append.mp present with old | added
    · exact fresh.2.1 other (List.mem_cons_of_mem _ member) equation old
    · cases List.mem_singleton.mp added
      refine ⟨fresh.2.2 other (by simp [member]) pair (by simp), ?_⟩
      have apart : other.2 ≠ pair.2 := by
        intro same
        exact distinct.1 (same ▸ List.mem_map.mpr ⟨other, member, rfl⟩)
      simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using apart
  · intro first firstMember second secondMember
    exact fresh.2.2 first (by simp [firstMember]) second (by simp [secondMember])

theorem equations_consistent (bindings : Equations) (operands : List (Atom × String))
    (fresh : FreshOperands bindings operands) (consistent : ∃ environment, Solves environment bindings) :
    ∃ environment, Solves environment (bindings ++ equationsFor operands) := by
  induction operands generalizing bindings with
  | nil => simpa [equationsFor] using consistent
  | cons pair rest ih =>
    have step := ScopedMutationSource.refine_fresh_operand bindings pair.2 pair.1
      (fresh.2.1 pair (by simp)) (fresh.2.2 pair (by simp) pair (by simp)) consistent
    simpa [equationsFor, List.append_assoc] using
      ih _ fresh.tail (ClosedOnceQueryFrame.refined_consistent _ _ _ step)

theorem ready_consistent (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    ∃ environment, Solves environment (ready caller head operands destination).bindings :=
  equations_consistent _ _ (pairs_fresh caller head operands destination) consistent

theorem ready_inherited (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (environment : Environment) (solved : Solves environment (ready caller head operands destination).bindings) :
    Solves environment caller.bindings := by
  intro pair member
  exact solved pair (List.mem_append_left _ member)

theorem ready_slot_reading (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (environment : Environment) (solved : Solves environment (ready caller head operands destination).bindings)
    (operand : Atom) (name : String) (member : (operand, name) ∈ pairs caller head operands destination) :
    read environment (.var name) = read environment operand :=
  (solved (operand, .var name) (List.mem_append_right _ (List.mem_map.mpr ⟨(operand, name), member, rfl⟩))).symm

theorem ready_closed_reading (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (before after : Environment) (operand value : Atom) (name : String)
    (beforeResolved : resolve caller.bindings = some before)
    (afterResolved : resolve (ready caller head operands destination).bindings = some after)
    (member : (operand, name) ∈ pairs caller head operands destination)
    (reading : read before operand = value) (closed : ∀ environment, read environment value = value) :
    read after (.var name) = value := by
  have solved := resolve_sound afterResolved
  exact (ready_slot_reading caller head operands destination after solved operand name member).trans
    (CapturedQueryOperands.resolved_forces beforeResolved operand value reading closed after
      (ready_inherited caller head operands destination after solved))

theorem equations_unbound (bindings : Equations) (operands : List (Atom × String))
    (destination : Atom) (principal : Environment) (representative : String)
    (fresh : FreshOperands bindings operands)
    (apart : ∀ pair ∈ operands, pair.2 ∉ (encode destination).freeVars)
    (resolved : resolve bindings = some principal) (unbound : read principal destination = .var representative) :
    ∃ next name, resolve (bindings ++ equationsFor operands) = some next ∧
      read next destination = .var name := by
  induction operands generalizing bindings principal representative with
  | nil => exact ⟨principal, representative, by simpa [equationsFor] using resolved, unbound⟩
  | cons pair rest ih =>
    obtain ⟨next, name, nextResolved, nextUnbound⟩ :=
      ScopedMutationSource.unbound_after_fresh_operand bindings principal destination pair.1 representative pair.2
        resolved unbound (fresh.2.1 pair (by simp)) (apart pair (by simp))
        (fresh.2.2 pair (by simp) pair (by simp))
    simpa [equationsFor, List.append_assoc] using ih _ next name fresh.tail
      (fun other member => apart other (by simp [member])) nextResolved nextUnbound

theorem ready_unbound (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (principal : Environment) (representative : String)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var representative) :
    ∃ next name, resolve (ready caller head operands destination).bindings = some next ∧
      read next destination = .var name :=
  equations_unbound _ _ _ _ _ (pairs_fresh caller head operands destination)
    (fun pair member => name_destination_apart caller head operands destination pair.2 (List.of_mem_zip member).2)
    resolved unbound

private theorem strict_fold (program : SpaceSemantics.Program) (head : String)
    (rows : List ((Atom × Atom) × Nat)) (pending : List Goal) (ready : List Atom)
    (strict : ∀ row ∈ rows, Eval.argumentIsRaw program head row.2 = false) :
    rows.foldl (fun (pending, ready) ((argument, slot), index) =>
      if Eval.argumentIsRaw program head index then (pending, ready ++ [argument])
      else (pending ++ [.evaluate argument slot], ready ++ [slot])) (pending, ready) =
      (pending ++ rows.map (fun row => Goal.evaluate row.1.1 row.1.2),
        ready ++ rows.map (fun row => row.1.2)) := by
  induction rows generalizing pending ready with
  | nil => simp
  | cons row rest ih =>
    simp only [List.foldl_cons, strict row (by simp), Bool.false_eq_true, ↓reduceIte]
    rw [ih _ _ (fun other member => strict other (by simp [member]))]
    simp [List.append_assoc]

theorem callArguments_strict (program : SpaceSemantics.Program) (head : String)
    (arguments slots : List Atom)
    (strict : ∀ index, index < arguments.length → Eval.argumentIsRaw program head index = false) :
    callArguments program head arguments slots =
      ((arguments.zip slots).map (fun row => Goal.evaluate row.1 row.2),
        (arguments.zip slots).map Prod.snd) := by
  unfold callArguments
  rw [strict_fold program head _ [] [] ?_]
  · simp only [List.nil_append]
    apply Prod.ext
    · simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (fun row : Atom × Atom => Goal.evaluate row.1 row.2))
          (List.zipIdx_map_fst 0 (arguments.zip slots))
    · simpa only [List.map_map, Function.comp_def] using
        congrArg (List.map (Prod.snd : Atom × Atom → Atom))
          (List.zipIdx_map_fst 0 (arguments.zip slots))
  · intro row member
    have indexed := List.mk_mem_zipIdx_iff_getElem?.mp member
    have bound := (List.getElem?_eq_some_iff.mp indexed).1
    exact strict row.2 (lt_of_lt_of_le bound (by simp [List.length_zip]))

set_option maxHeartbeats 1200000 in
theorem operands_prefix {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (operands : List (Atom × String)) (older : List Goal)
    (atomic : ∀ pair ∈ operands, Atomic pair.1) (fresh : FreshOperands caller.bindings operands)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine policy program).run (2 * operands.length)
      (placed allocator world scope parents {caller with goals := goalsFor operands ++ older} context origins pending) =
      ([], .exhausted (placed allocator world scope parents
        {caller with bindings := caller.bindings ++ equationsFor operands, goals := older} context origins pending)) := by
  induction operands generalizing caller with
  | nil => simp [goalsFor, equationsFor, Machine.run]
  | cons pair rest ih =>
    have refined := ScopedMutationSource.refine_fresh_operand caller.bindings pair.2 pair.1
      (fresh.2.1 pair (by simp)) (fresh.2.2 pair (by simp) pair (by simp)) consistent
    have two : (ScopedQuerySource.machine policy program).run 2
        (placed allocator world scope parents {caller with goals := goalsFor (pair :: rest) ++ older} context origins pending) =
        ([], .exhausted (placed allocator world scope parents
          {caller with bindings := caller.bindings ++ [(pair.1, .var pair.2)], goals := goalsFor rest ++ older}
          context origins pending)) := by
      obtain atomicPair := atomic pair (by simp)
      rcases pair with ⟨operand, name⟩
      cases atomicPair <;>
        simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
          ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
          placed, goalsFor, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
          prepare, replace, installChild, retainChild, refined]
    have tail := ih {caller with bindings := caller.bindings ++ [(pair.1, .var pair.2)]}
      (fun other member => atomic other (by simp [member])) fresh.tail
      (ClosedOnceQueryFrame.refined_consistent _ _ _ refined)
    rw [show 2 * (pair :: rest).length = 2 + 2 * rest.length by simp; omega,
      Machine.established_and_pending _ _ _ _ _ _ two]
    simpa [goalsFor, equationsFor, List.append_assoc] using tail

set_option maxHeartbeats 1200000 in
theorem preparation {Context : Type} (policy : Policy) (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context)
    (parents : List (CollectionScope Context)) (caller : Control) (context : Context)
    (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (operands : List Atom) (destination : Atom)
    (atomic : ∀ operand ∈ operands, Atomic operand)
    (ordinary : head ≠ "let*") (lexical : Source.lexicalForm (source head operands) = false)
    (unscoped : Source.scopedForm (source head operands) = false)
    (declared : callable program head = true)
    (strict : ∀ index, index < operands.length → Eval.argumentIsRaw program head index = false)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine policy program).run (1 + 2 * operands.length)
      (placed allocator world scope parents (entry caller head operands destination) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (ready caller head operands destination) context origins pending)) := by
  let slots := (slotNames caller head operands destination).map Atom.var
  let next : Control := {caller with goals := goalsFor (pairs caller head operands destination) ++
    (.invoke head slots destination :: caller.goals)}
  have arguments : callArguments program head operands
      (freshSlots (entry caller head operands destination) operands.length) =
      (goalsFor (pairs caller head operands destination), slots) := by
    rw [callArguments_strict program head _ _ strict]
    have freshSlotsEq : freshSlots (entry caller head operands destination) operands.length = slots := by
      simp [freshSlots, slots, slotNames, List.map_map]
    rw [freshSlotsEq]
    apply Prod.ext
    · simp [slots, pairs, goalsFor, List.zip_map_right, List.map_map]
    · exact List.map_snd_zip (by simp [slots, names_length])
  have prepared := Source.Prepared.application (policy := policy) (program := program)
    (control := entry caller head operands destination) (destination := destination) (older := caller.goals)
    head operands lexical declared
  have nextPrepared : Source.Prepared policy program (entry caller head operands destination)
      destination caller.goals (source head operands) next := by
    rw [arguments] at prepared
    simpa [source, next, entry, replace, List.append_assoc] using prepared
  have localStep : Source.Step policy program
      (⟨world, entry caller head operands destination, context⟩ : Cursor Context)
      (.silent ⟨world, next, context⟩) :=
    .expanded _ _ _ _ rfl unscoped nextPrepared
  have step : (ScopedQuerySource.machine policy program).step
      (placed allocator world scope parents (entry caller head operands destination) context origins pending) =
      some (.silent (placed allocator world scope parents next context origins pending)) := by
    rw [ScopedQuerySource.Guards.placed_ordinary_step policy program allocator world scope parents
      (entry caller head operands destination) context origins pending
      (.evaluate (source head operands) destination) caller.goals rfl
      (by simp [ScopedQuerySource.Guards.ordinaryGoal, source, ordinary])]
    have actual := Source.source_step_scope policy program allocator world
      {scope with frontier := (entry caller head operands destination, context, origins) :: pending}
      parents (entry caller head operands destination) context origins pending rfl _ localStep
    simpa [placed, installChild, retainChild] using congrArg some actual
  have one : (ScopedQuerySource.machine policy program).run 1
      (placed allocator world scope parents (entry caller head operands destination) context origins pending) =
      ([], .exhausted (placed allocator world scope parents next context origins pending)) := by
    simp [Machine.run, step]
  have tail := operands_prefix policy program allocator world scope parents caller context origins pending
    (pairs caller head operands destination) (.invoke head slots destination :: caller.goals)
    (fun pair member => atomic pair.1 (List.of_mem_zip member).1)
    (pairs_fresh caller head operands destination) consistent
  rw [Machine.established_and_pending _ _ _ _ _ _ one]
  simpa [pairs_length, next, ready, slots] using tail

theorem ready_fresh_of_entry_support (caller : Control) (head : String)
    (operands : List Atom) (destination : Atom) (name : String)
    (fresh : FreshFor name caller.bindings)
    (kept : name ∈ (entry caller head operands destination).support)
    (operandsApart : ∀ operand ∈ operands, name ∉ (encode operand).freeVars) :
    FreshFor name (ready caller head operands destination).bindings := by
  intro equation member
  rcases List.mem_append.mp member with inherited | added
  · exact fresh equation inherited
  · obtain ⟨pair, present, rfl⟩ := List.mem_map.mp added
    refine ⟨operandsApart pair.1 (List.of_mem_zip present).1, ?_⟩
    have named := (List.of_mem_zip present).2
    obtain ⟨index, _, renamed⟩ := List.mem_map.mp named
    intro mentioned
    have same : name = pair.2 := by
      simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using mentioned
    apply freshName_not_mem (entry caller head operands destination) index
    rw [renamed, ← same]
    exact kept

theorem captured_variable_is_atomic (name : String) : Atomic (.var name) := .variable name

theorem expression_requires_separate_evaluation (children : List Atom) : ¬ Atomic (.expression children) := by
  intro atomic
  cases atomic

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands
