import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands

/-! Atomic argument preparation followed by the actual pure primitive
invocation and result refinement used by the EU loop's arithmetic/tests. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicPrimitive

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (placed)
open ScopedAtomicCallOperands (Atomic source entry ready slotNames pairs)

def returned (caller : Control) (head : String) (operands : List Atom) (destination value : Atom) : Control :=
  {ready caller head operands destination with
    bindings := (ready caller head operands destination).bindings ++ [(value, destination)]
    goals := caller.goals}

theorem readings (caller : Control) (head : String) (operands : List Atom) (destination : Atom)
    (before after : Environment) (resolved : resolve caller.bindings = some before)
    (prepared : resolve (ready caller head operands destination).bindings = some after)
    (closed : ∀ operand ∈ operands, ∀ environment, read environment (read before operand) = read before operand) :
    ((slotNames caller head operands destination).map Atom.var).map (read after) = operands.map (read before) := by
  have left : (pairs caller head operands destination).map Prod.snd = slotNames caller head operands destination :=
    List.map_snd_zip (by simp [ScopedAtomicCallOperands.names_length])
  have right : (pairs caller head operands destination).map Prod.fst = operands :=
    List.map_fst_zip (by simp [ScopedAtomicCallOperands.names_length])
  have leftLift := congrArg (fun names : List String => (names.map Atom.var).map (read after)) left
  have rightLift := congrArg (List.map (read before)) right
  simp only [List.map_map, Function.comp_def] at leftLift rightLift
  simp only [List.map_map, Function.comp_def]
  apply leftLift.symm.trans
  apply Eq.trans _ rightLift
  apply List.map_congr_left
  intro pair member
  exact ScopedAtomicCallOperands.ready_closed_reading caller head operands destination before after pair.1
    (read before pair.1) pair.2 resolved prepared member rfl (closed pair.1 (List.of_mem_zip member).1)

theorem source_prefix {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (head : String) (operands : List Atom) (destination value : Atom) (principal : Environment) (representative : String)
    (atomic : ∀ operand ∈ operands, Atomic operand)
    (notLet : head ≠ "let*") (lexical : Source.lexicalForm (source head operands) = false)
    (unscoped : Source.scopedForm (source head operands) = false)
    (declared : callable program head = true)
    (strict : ∀ index, index < operands.length → Eval.argumentIsRaw program head index = false)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var representative)
    (closed : ∀ operand ∈ operands, ∀ environment, read environment (read principal operand) = read principal operand)
    (known : StdLib.known head = true) (notParse : head ≠ "parse") (notMatch : head ≠ "match")
    (notAdd : head ≠ "add-atom") (notRemove : head ≠ "remove-atom")
    (applied : StdLib.apply world.state head (operands.map (read principal)) = .ok (world.state, [value]))
    (valueClosed : ∀ environment, read environment value = value) :
    (ScopedQuerySource.machine .relational program).run (1 + 2 * operands.length + 2)
      (placed allocator world scope parents (entry caller head operands destination) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (returned caller head operands destination value)
        context (origins ++ [0]) pending)) := by
  have first := ScopedAtomicCallOperands.preparation .relational program allocator world scope parents caller context origins pending
    head operands destination atomic notLet lexical unscoped declared strict ⟨principal, resolve_sound resolved⟩
  obtain ⟨environment, result, prepared, stillUnbound⟩ := ScopedAtomicCallOperands.ready_unbound caller head operands destination
    principal representative resolved unbound
  have readSlots := readings caller head operands destination principal environment resolved prepared closed
  have last := ScopedMutationSource.primitive_prefix .relational program allocator world
    {scope with frontier := (ready caller head operands destination, context, origins) :: pending} parents
    (ready caller head operands destination) context origins pending head ((slotNames caller head operands destination).map Atom.var)
    destination result caller.goals environment world.state value rfl rfl prepared stillUnbound valueClosed known notParse notMatch
    (by intro impossible; rcases impossible with add | remove; exact (notAdd add).elim; exact (notRemove remove).elim)
    (by rw [readSlots]; exact applied)
  change (ScopedQuerySource.machine .relational program).run 2
    (placed allocator world scope parents (ready caller head operands destination) context origins pending) =
    ([], .exhausted (placed allocator world scope parents (returned caller head operands destination value)
      context (origins ++ [0]) pending)) at last
  have joined := (ScopedQuerySource.machine .relational program).established_and_pending
    (1 + 2 * operands.length) 2 _ _ [] first
  rw [last] at joined
  simpa only [List.nil_append] using joined

theorem returned_consistent (caller : Control) (head : String) (operands : List Atom) (destination value : Atom)
    (principal : Environment) (representative : String) (resolved : resolve caller.bindings = some principal)
    (unbound : read principal destination = .var representative) (closed : ∀ environment, read environment value = value) :
    ∃ environment, resolve (returned caller head operands destination value).bindings = some environment := by
  obtain ⟨environment, result, prepared, stillUnbound⟩ := ScopedAtomicCallOperands.ready_unbound caller head operands destination
    principal representative resolved unbound
  exact resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _
    (ScopedMutationSource.refine_unbound _ environment destination value result prepared stillUnbound closed))

theorem returned_inherited (caller : Control) (head : String) (operands : List Atom) (destination value : Atom)
    (environment : Environment) (solved : Solves environment (returned caller head operands destination value).bindings) :
    Solves environment caller.bindings := by
  apply ScopedAtomicCallOperands.ready_inherited caller head operands destination environment
  intro pair member
  exact solved pair (List.mem_append_left _ member)

theorem returned_value (caller : Control) (head : String) (operands : List Atom) (destination value : Atom)
    (environment : Environment) (solved : Solves environment (returned caller head operands destination value).bindings)
    (closed : ∀ environment, read environment value = value) : read environment destination = value := by
  have equation := solved (value, destination) (List.mem_append_right _ (by simp))
  exact equation.symm.trans (closed environment)

theorem returned_fresh_of_entry_support (caller : Control) (head : String) (operands : List Atom) (destination value : Atom)
    (name : String) (fresh : ClosedOnceQueryFrame.FreshFor name caller.bindings)
    (kept : name ∈ (entry caller head operands destination).support)
    (operandsApart : ∀ operand ∈ operands, name ∉ (encode operand).freeVars)
    (destinationApart : name ∉ (encode destination).freeVars) (valueApart : name ∉ (encode value).freeVars) :
    ClosedOnceQueryFrame.FreshFor name (returned caller head operands destination value).bindings := by
  intro equation member
  rcases List.mem_append.mp member with old | output
  · rcases List.mem_append.mp old with inherited | added
    · exact fresh equation inherited
    · obtain ⟨pair, present, rfl⟩ := List.mem_map.mp added
      refine ⟨operandsApart pair.1 (List.of_mem_zip present).1, ?_⟩
      have named := (List.of_mem_zip present).2
      obtain ⟨index, _inside, renamed⟩ := List.mem_map.mp named
      intro mentioned
      have same : name = pair.2 := by simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using mentioned
      apply freshName_not_mem (entry caller head operands destination) index
      rw [renamed, ← same]
      exact kept
  · cases List.mem_singleton.mp output
    exact ⟨valueApart, destinationApart⟩

theorem returned_fresh (caller : Control) (head : String) (operands : List Atom) (destination value : Atom)
    (name : String) (fresh : ClosedOnceQueryFrame.FreshFor name caller.bindings) (retained : name ∈ caller.support)
    (operandsApart : ∀ operand ∈ operands, name ∉ (encode operand).freeVars)
    (destinationApart : name ∉ (encode destination).freeVars) (valueApart : name ∉ (encode value).freeVars) :
    ClosedOnceQueryFrame.FreshFor name (returned caller head operands destination value).bindings :=
  returned_fresh_of_entry_support caller head operands destination value name fresh
    (ClosedOnceQueryFrame.support_mono caller (entry caller head operands destination) rfl
      (by intro _ member; exact member) (by intro _ member; exact member)
      (by intro goal member; exact List.mem_cons_of_mem _ member) retained)
    operandsApart destinationApart valueApart

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicPrimitive
