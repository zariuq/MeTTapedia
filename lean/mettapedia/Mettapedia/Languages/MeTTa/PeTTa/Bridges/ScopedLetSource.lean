import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedAtomicCallOperands
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedInsertionSequence

/-! The authored variable-let entry used by the EU driver. It retains the
actual alias equation and older continuation; the producer is not evaluated
or replaced by a value in this entry theorem. -/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedLetSource

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.MetavariableFrameStore.Shared (Allocator)
open Mettapedia.GSLT.Distinction.ProductiveBlocks
open EagerDFS (World)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor placed)

def source (name : String) (producer body : Atom) : Atom := .expression [.symbol "let", .var name, producer, body]
def entry (caller : Control) (name : String) (producer body destination : Atom) : Control :=
  {caller with goals := .evaluate (source name producer body) destination :: caller.goals}
def slot (caller : Control) (name : String) (producer body destination : Atom) : String :=
  freshName (entry caller name producer body destination) 0
def producerCaller (caller : Control) (name : String) (producer body destination : Atom) : Control :=
  {caller with
    bindings := caller.bindings ++ [(.var name, .var (slot caller name producer body destination))]
    goals := .evaluate body destination :: caller.goals}
def producing (caller : Control) (name : String) (producer body destination : Atom) : Control :=
  {producerCaller caller name producer body destination with
    goals := .evaluate producer (.var (slot caller name producer body destination)) ::
      (producerCaller caller name producer body destination).goals}

theorem slot_fresh (caller : Control) (name : String) (producer body destination : Atom) :
    FreshFor (slot caller name producer body destination) caller.bindings :=
  ClosedOnceQueryFrame.fresh_for_bindings (entry caller name producer body destination) _ (freshName_not_mem _ _)

theorem slot_apart (caller : Control) (name : String) (producer body destination : Atom) :
    slot caller name producer body destination ≠ name := by
  have notUsed := ScopedInsertionSequence.fresh_for_goal_atom (entry caller name producer body destination) 0
    (source name producer body) (by simp [entry, Goal.atoms])
  intro same
  apply notUsed
  change slot caller name producer body destination ∈ _
  rw [same, source, CapturedPatternSupport.mem_expression_names]
  exact ⟨.var name, by simp, by simp [encode, Mettapedia.Logic.LP.Term.freeVars]⟩

theorem refined (caller : Control) (name : String) (producer body destination : Atom)
    (consistent : ∃ environment, Solves environment caller.bindings) :
    refine caller.bindings (.var name) (.var (slot caller name producer body destination)) =
      some (producerCaller caller name producer body destination).bindings :=
  ScopedMutationSource.refine_fresh_operand _ _ _ (slot_fresh caller name producer body destination)
    (by simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using slot_apart caller name producer body destination) consistent

theorem preparation {Context : Type} (program : SpaceSemantics.Program)
    (allocator : Allocator) (world : World) (scope : CollectionScope Context) (parents : List (CollectionScope Context))
    (caller : Control) (context : Context) (origins : List Nat) (pending : List (CollectionWork Context))
    (name : String) (producer body destination : Atom) (consistent : ∃ environment, Solves environment caller.bindings) :
    (ScopedQuerySource.machine .relational program).run 3
      (placed allocator world scope parents (entry caller name producer body destination) context origins pending) =
      ([], .exhausted (placed allocator world scope parents (producing caller name producer body destination) context origins pending)) := by
  have actual := refined caller name producer body destination consistent
  simp only [producerCaller, slot, entry, source] at actual
  simp [Machine.run, ScopedQuerySource.machine, ScopedQuerySource.step, ScopedQuerySource.syntaxStep,
    ScopedQuerySource.constrainedCall, ScopedQuerySource.mutationCall, ScopedQuerySource.queryStep,
    placed, entry, source, scopeStep, enterCollapse?, enterSuperpose?, EagerDFS.Destination.machine,
    prepare, replace, installChild, retainChild, letGoals, rigid, producing, producerCaller, slot, actual]

theorem producer_unbound (caller : Control) (name : String) (producer body destination : Atom)
    (principal : Environment) (resolved : resolve caller.bindings = some principal)
    (fresh : FreshFor name caller.bindings) :
    ∃ next representative, resolve (producerCaller caller name producer body destination).bindings = some next ∧
      read next (.var (slot caller name producer body destination)) = .var representative := by
  have notUsed : slot caller name producer body destination ∉ (encode (.var name)).freeVars := by
    simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using slot_apart caller name producer body destination
  obtain ⟨next, representative, nextResolved, unbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal (.var name) (.var name) name (slot caller name producer body destination)
    resolved (ClosedOnceQueryFrame.fresh_read _ name principal fresh resolved)
    (slot_fresh caller name producer body destination) notUsed notUsed
  refine ⟨next, representative, nextResolved, ?_⟩
  have linked := resolve_sound nextResolved (.var name, .var (slot caller name producer body destination))
    (List.mem_append_right _ (by simp))
  exact linked.symm.trans unbound

theorem inherited (caller : Control) (name : String) (producer body destination : Atom)
    (environment : Environment) (solved : Solves environment (producerCaller caller name producer body destination).bindings) :
    Solves environment caller.bindings := fun pair member => solved pair (List.mem_append_left _ member)

theorem producer_fresh_of_entry_support (caller : Control) (name : String) (producer body destination : Atom) (other : String)
    (fresh : FreshFor other caller.bindings)
    (kept : other ∈ (entry caller name producer body destination).support) (apart : other ≠ name) :
    FreshFor other (producerCaller caller name producer body destination).bindings := by
  have slotApart : other ≠ slot caller name producer body destination := by
    intro same
    apply freshName_not_mem (entry caller name producer body destination) 0
    change slot caller name producer body destination ∈ _
    rw [← same]
    exact kept
  intro pair member
  rcases List.mem_append.mp member with old | added
  · exact fresh pair old
  · cases List.mem_singleton.mp added
    simp [encode, Mettapedia.Logic.LP.Term.freeVars, apart, slotApart]

theorem producer_fresh (caller : Control) (name : String) (producer body destination : Atom) (other : String)
    (fresh : FreshFor other caller.bindings) (retained : other ∈ caller.support) (apart : other ≠ name) :
    FreshFor other (producerCaller caller name producer body destination).bindings :=
  producer_fresh_of_entry_support caller name producer body destination other fresh
    (ClosedOnceQueryFrame.support_mono caller (entry caller name producer body destination) rfl
      (by intro _ member; exact member) (by intro _ member; exact member)
      (by intro goal member; exact List.mem_cons_of_mem _ member) retained) apart

theorem aliased_value (caller : Control) (name : String) (producer body destination value : Atom)
    (environment : Environment)
    (solved : Solves environment (producerCaller caller name producer body destination).bindings)
    (reading : read environment (.var (slot caller name producer body destination)) = value) :
    read environment (.var name) = value :=
  (solved (.var name, .var (slot caller name producer body destination)) (List.mem_append_right _ (by simp))).trans reading

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.ScopedLetSource
