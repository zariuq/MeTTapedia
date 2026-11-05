import Mettapedia.Languages.MeTTa.PeTTa.Bridges.CountedSourceEntry
import Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturn

/-!
# Caller frames after a counted collection returns

The tuple and numeric result equations extend, rather than replace, the
caller. An originally unbound output still admits the numeric result after
the generated tuple slot is refined. Other fresh retained names remain free.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturnFrame

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open EagerDFS.Destination
open ClosedOnceQueryFrame (FreshFor)
open GuardedCountReturn (counted value)

theorem counted_resolves (caller : Control) (slot : String) (destination : Atom) (count : Nat)
    (principal : Environment) (representative : String)
    (resolved : resolve caller.bindings = some principal) (unbound : read principal destination = .var representative)
    (fresh : FreshFor slot caller.bindings) (apart : slot ∉ (encode destination).freeVars) :
    ∃ after, resolve (counted caller slot destination count).bindings = some after ∧
      read after destination = value count := by
  have tupleApart : slot ∉ (encode (GuardedQueryCollection.tuple count)).freeVars := by
    rw [CapturedPatternSupport.literal_names_empty _ (GuardedCountReturn.tuple_literal count)]
    simp
  obtain ⟨tuplePrincipal, tupleName, tupleResolved, tupleUnbound⟩ := ScopedMutationSource.unbound_after_fresh_operand
    caller.bindings principal destination (GuardedQueryCollection.tuple count)
    representative slot resolved unbound fresh apart tupleApart
  have numeric := ScopedMutationSource.refine_unbound _ tuplePrincipal destination (value count)
    tupleName tupleResolved tupleUnbound (fun environment => ConstantQuerySource.Scalar.read (.grounded _) environment)
  obtain ⟨after, afterResolved⟩ := resolve_complete (ClosedOnceQueryFrame.refined_consistent _ _ _ numeric)
  exact ⟨after, afterResolved, GuardedCountReturn.counted_value caller slot destination count after (resolve_sound afterResolved)⟩

theorem counted_inherits (caller : Control) (slot : String) (destination : Atom) (count : Nat)
    (environment : Environment) (solved : Solves environment (counted caller slot destination count).bindings) :
    Solves environment caller.bindings := by
  intro equation member
  exact solved equation (List.mem_append_left _ (List.mem_append_left _ member))

theorem counted_fresh {Context : Type} (input : CountedSourceEntry.Input Context) (count : Nat) (name : String)
    (fresh : FreshFor name input.caller.bindings) (retained : name ∈ input.entry.support)
    (notOutput : name ∉ (encode input.destination).freeVars) :
    FreshFor name (counted input.caller input.slot input.destination count).bindings := by
  have slotApart : name ≠ input.slot := by
    intro same
    apply freshName_not_mem input.entry 0
    change input.slot ∈ input.entry.support
    rw [← same]
    exact retained
  intro equation member
  rcases List.mem_append.mp member with beforeNumber | numeric
  · rcases List.mem_append.mp beforeNumber with beforeTuple | tuple
    · exact fresh equation beforeTuple
    · cases List.mem_singleton.mp tuple
      constructor
      · rw [CapturedPatternSupport.literal_names_empty _ (GuardedCountReturn.tuple_literal count)]
        exact Finset.notMem_empty name
      · simpa [encode, Mettapedia.Logic.LP.Term.freeVars] using slotApart
  · cases List.mem_singleton.mp numeric
    exact ⟨by simp [value, encode, Mettapedia.Logic.LP.Term.freeVars], notOutput⟩

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturnFrame

#print axioms Mettapedia.Languages.MeTTa.PeTTa.Bridges.GuardedCountReturnFrame.counted_resolves
