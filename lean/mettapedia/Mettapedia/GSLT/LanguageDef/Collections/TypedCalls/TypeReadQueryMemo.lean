import Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryRecursive
import Mettapedia.Machines.RevisionedQueryFacts

/-!
# Recursive memoization of completed retained type replies

The existing revisioned fact table supplies authority-and-call lookup. The
existing adaptive inference body still performs every miss, and recursive
children share the updated table. Hits return a completed immutable family
without advancing the private-name supply. Missing, malformed and open
replies are not inserted as empty or persistent answers.

The admission callback can disable either lookup or publication at any call.
Explicitly budgeted native requests must disable both; the recursion depth
here is the evaluator's mathematical approximation, not a work allowance.
Physical node identities, compressed stamps and table storage remain separate
from this operational adapter.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemo

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Machines
open NativeTypeCallGraph NativeTypeSourcePorts
open TypeReadSupply (Supply)
open RetainedTypePayloads (ExternalView)

abbrev Cache := RevisionedQueryFacts.Cache Nat Call Atom

structure State where
  supply : Supply
  cache : Cache

/-- The modeled memo fragment uses stable ground expression subjects.
Other inquiry roles and unretained carriers execute their ordinary misses. -/
def eligible : Call → Bool
  | .infer _ (.expression children) => RetainedTypePayloads.admittedList children
  | _ => false

mutual
theorem admitted_variables : ∀ atom,
    RetainedTypePayloads.admitted atom = true → atomVariables atom = []
  | .symbol _, _ => rfl
  | .var _, impossible => by cases impossible
  | .grounded _, _ => rfl
  | .expression children, accepted => admittedList_variables children accepted
theorem admittedList_variables : ∀ atoms,
    RetainedTypePayloads.admittedList atoms = true → atomListVariables atoms = []
  | [], _ => rfl
  | atom :: atoms, accepted => by
      have both := Bool.and_eq_true_iff.mp accepted
      simp only [atomListVariables, admitted_variables atom both.1, admittedList_variables atoms both.2,
        List.nil_append]
end

mutual
theorem admitted_rename_eq (names : String → String) : ∀ atom,
    RetainedTypePayloads.admitted (renameAtom names atom) = RetainedTypePayloads.admitted atom
  | .symbol _ => rfl
  | .var _ => rfl
  | .grounded _ => rfl
  | .expression children => admittedList_rename_eq names children
theorem admittedList_rename_eq (names : String → String) : ∀ atoms,
    RetainedTypePayloads.admittedList (renameAtomList names atoms) = RetainedTypePayloads.admittedList atoms
  | [] => rfl
  | atom :: atoms => by
      simp only [renameAtomList, RetainedTypePayloads.admittedList, admitted_rename_eq,
        admittedList_rename_eq]
end

theorem eligible_names (call : Call) (accepted : eligible call = true) :
    TypeReadQueryWorlds.questionNames (.inr call) = [] := by
  cases call with
  | tuplePart _ _ | operatorRows _ => cases accepted
  | infer direct atom =>
      cases atom with
      | symbol _ | var _ | grounded _ => cases accepted
      | expression children => exact admittedList_variables children accepted

theorem retained_reflexive (world : TypeReadQueryWorlds.Coordinates) (types : List Atom)
    (retained : RetainedTypePayloads.admittedList types = true) :
    TypeReadQueryWorlds.TypesRelated world types types := by
  refine ⟨TypeRowFreshening.admittedList_resourceFree types retained, ?_, ?_⟩
  · simp only [admittedList_variables types retained, List.nil_subset]
  · rw [← renameAtomList_eq_map, TypeRowFreshening.admittedList_rename world.names types retained]

theorem retained_right_equal {world : TypeReadQueryWorlds.Coordinates} {first second : List Atom}
    (related : TypeReadQueryWorlds.TypesRelated world first second)
    (retained : RetainedTypePayloads.admittedList second = true) : first = second := by
  have firstRetained : RetainedTypePayloads.admittedList first = true := by
    rw [related.2.2, ← renameAtomList_eq_map, admittedList_rename_eq] at retained
    exact retained
  exact (TypeReadQueryRecursive.retained_types_equal related firstRetained).symm

def publish (authority : Nat) (allow : Call → Bool) (call : Call)
    (reply : Option Reply) (state : State) : State :=
  match reply with
  | some (.types types) =>
      if allow call && eligible call && RetainedTypePayloads.admittedList types &&
          (RevisionedQueryFacts.lookup authority call state.cache).isNone then
        { state with cache := ⟨authority, call, types⟩ :: state.cache }
      else state
  | _ => state

theorem publish_supply (authority : Nat) (allow : Call → Bool) (call : Call)
    (reply : Option Reply) (state : State) : (publish authority allow call reply state).supply = state.supply := by
  cases reply with
  | none => rfl
  | some reply => cases reply with
      | kind _ | class_ _ => rfl
      | types types => simp only [publish]; split <;> rfl

def finish (authority : Nat) (allow : Call → Bool) (call : Call)
    (result : QueryState.Observation Question (Option Reply) (Option (Except Unit Reply)) State) :
    Option Reply × State :=
  let answer := NativeTypeRecursiveDriver.completed result.answer
  let retained := { result.state with supply := NativeTypeScopedReads.retain result.state.supply answer }
  (answer, publish authority allow call answer retained)

def evaluate (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (authority : Nat) (allow : Call → Bool) :
    Nat → Call → State → Option Reply × State
  | 0, _, state => (none, state)
  | depth + 1, call, state =>
      let hit := if allow call && eligible call then RevisionedQueryFacts.lookup authority call state.cache else none
      match hit with
      | some types => (some (.types types), state)
      | none =>
          let service : State → Question → Option Reply × State := fun current => fun
            | .inl key =>
                let result := NativeTypeScopedReads.primitive source external current.supply key
                (result.1, { current with supply := result.2 })
            | .inr child => evaluate ops source external authority allow depth child current
          finish authority allow call
            (QueryState.run service (ReadOnlyQueryDemand.demand (body ops call)) state)

theorem hit (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (authority : Nat) (allow : Call → Bool)
    (depth : Nat) (call : Call) (state : State) (types : List Atom)
    (allowed : allow call = true) (admitted : eligible call = true)
    (found : RevisionedQueryFacts.lookup authority call state.cache = some types) :
    evaluate ops source external authority allow (depth + 1) call state = (some (.types types), state) := by
  simp only [evaluate, allowed, admitted, Bool.and_self, if_true, found]

theorem evaluate_remembers (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (authority : Nat) (allow : Call → Bool) (depth : Nat) :
    ∀ call state, state.supply.used ⊆ (evaluate ops source external authority allow depth call state).2.supply.used := by
  induction depth with
  | zero => intro call state; exact fun _ member => member
  | succ depth ih =>
      intro call state
      simp only [evaluate]
      split
      · exact fun _ member => member
      · simp only [finish, publish_supply]
        intro name member
        apply NativeTypeScopedReads.retain_old
        apply QueryState.state_extends
          (rel := fun before after : State => before.supply.used ⊆ after.supply.used)
          _ (fun _ _ present => present)
          (fun _ _ _ first second _ present => second (first present))
          (fun current key => by
            cases key with
            | inl primitive => exact NativeTypeScopedReads.primitive_remembers source external current.supply primitive
            | inr child => exact ih child current) _ state member

/-- Historical provenance for one immutable entry. The source inquiry
really returned the retained family; a fabricated empty list is not evidence. -/
structure Recorded (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (completionDepth : Call → Nat)
    (call : Call) (types : List Atom) : Prop where
  key : eligible call = true
  retained : RetainedTypePayloads.admittedList types = true
  history : ∃ supply, (NativeTypeScopedReads.evaluate ops source external (completionDepth call) call supply).1 =
    some (.types types)

def Valid (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (completionDepth : Call → Nat)
    (authority : Nat) (cache : Cache) : Prop :=
  ∀ entry ∈ cache, entry.stamp = authority → Recorded ops source external completionDepth entry.key entry.facts

theorem lookup_recorded (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (completionDepth : Call → Nat)
    (authority : Nat) (cache : Cache) (valid : Valid ops source external completionDepth authority cache)
    (call : Call) (types : List Atom) (found : RevisionedQueryFacts.lookup authority call cache = some types) :
    Recorded ops source external completionDepth call types := by
  induction cache with
  | nil => simp [RevisionedQueryFacts.lookup] at found
  | cons entry rest ih =>
      simp only [RevisionedQueryFacts.lookup] at found
      split at found
      · rename_i same
        have recorded := valid entry (by simp) same.1
        cases Option.some.inj found
        simpa only [same.2] using recorded
      · exact ih (fun item member => valid item (List.mem_cons_of_mem _ member)) found

theorem publish_valid (ops : NativeTypeViews.Ops Atom TypeScopeMatcher.State Atom)
    (source : Source) (external : ExternalView) (completionDepth : Call → Nat)
    (authority : Nat) (allow : Call → Bool) (call : Call) (reply : Option Reply) (state : State)
    (valid : Valid ops source external completionDepth authority state.cache)
    (earned : ∀ types, reply = some (.types types) → RetainedTypePayloads.admittedList types = true →
      ∃ supply, (NativeTypeScopedReads.evaluate ops source external (completionDepth call) call supply).1 =
        some (.types types)) :
    Valid ops source external completionDepth authority (publish authority allow call reply state).cache := by
  cases reply with
  | none => exact valid
  | some reply => cases reply with
      | kind _ | class_ _ => exact valid
      | types types =>
          simp only [publish]
          split
          · rename_i accepted
            have flags := Bool.and_eq_true_iff.mp accepted
            have input := Bool.and_eq_true_iff.mp flags.1
            have key := Bool.and_eq_true_iff.mp input.1
            intro entry member current
            rcases List.mem_cons.mp member with rfl | prior
            · exact ⟨key.2, input.2, earned types rfl input.2⟩
            · exact valid entry prior current
          · exact valid

end Mettapedia.GSLT.LanguageDef.Collections.TypedCalls.TypeReadQueryMemo
