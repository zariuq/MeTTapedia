import Mettapedia.GSLT.LanguageDef.NativeOpsMemory

/-!
Finite ownership of completed six-argument native executions. The source
interface selects an owned observation from a finite registry; the native
interface traverses the scope's node sequence before inspecting any payload.
Request comparison covers code and both inputs. Output length is stored in
the completed request and is checked separately by a guest.

The physical call is an explicit contract. Only its successful completion
extends the registry. Release removes a live observation, and an address may
be reused after release. These interfaces describe the external scope API;
pointer realization and the generated caller's body are separate bridges.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.NativeExecutionScope

open NativeOps (Address)
open NativeWord64 (Word)

structure Inputs where
  code : List UInt8
  input1 : List UInt8
  input2 : List UInt8
  deriving DecidableEq, Repr

structure Request where
  inputs : Inputs
  outputLength : Word
  deriving DecidableEq, Repr

structure Observation where
  request : Request
  output : List UInt8
  deriving DecidableEq, Repr

abbrev Contract := Request → List UInt8 → Prop

def Observation.realized (contract : Contract) (observation : Observation) : Prop :=
  contract observation.request observation.output ∧
    observation.output.length = observation.request.outputLength.val

structure Entry where
  handle : Address
  observation : Observation
  deriving DecidableEq, Repr

abbrev Scope := List Entry

def sourceRead (scope : Scope) (handle : Option Address) : Option Observation := do
  let requested ← handle
  let entry ← scope.find? (fun entry => entry.handle == requested)
  some entry.observation

def targetFind : Scope → Address → Option Observation
  | [], _ => none
  | entry :: rest, handle =>
      if entry.handle = handle then some entry.observation else targetFind rest handle

def targetRead (scope : Scope) (handle : Option Address) : Option Observation :=
  match handle with
  | none => none
  | some requested => targetFind scope requested

theorem find_correspondence (scope : Scope) (handle : Address) :
    targetFind scope handle =
      (scope.find? (fun entry => entry.handle == handle)).map Entry.observation := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      by_cases same : entry.handle = handle
      · simp [targetFind, List.find?, same]
      · have different : (entry.handle == handle) = false := beq_eq_false_iff_ne.mpr same
        simp [targetFind, List.find?, same, different, ih]

theorem read_correspondence (scope : Scope) (handle : Option Address) :
    targetRead scope handle = sourceRead scope handle := by
  cases handle with
  | none => rfl
  | some requested =>
      rw [targetRead, find_correspondence]
      change (scope.find? (fun entry => entry.handle == requested)).map Entry.observation =
        (scope.find? (fun entry => entry.handle == requested)).bind
          (fun entry => some entry.observation)
      cases scope.find? (fun entry => entry.handle == requested) <;> rfl

theorem find_member {scope : Scope} {handle : Address} {observation : Observation}
    (found : targetFind scope handle = some observation) :
    ⟨handle, observation⟩ ∈ scope := by
  induction scope with
  | nil => cases found
  | cons entry rest ih =>
      by_cases same : entry.handle = handle
      · rw [targetFind, if_pos same] at found
        have payload : entry.observation = observation := Option.some.inj found
        have equal : entry = ⟨handle, observation⟩ := by
          cases entry
          simp_all only
        exact List.mem_cons.mpr (Or.inl equal.symm)
      · rw [targetFind, if_neg same] at found
        exact List.mem_cons.mpr (Or.inr (ih found))

theorem read_member {scope : Scope} {handle : Option Address} {observation : Observation}
    (found : targetRead scope handle = some observation) :
    ∃ requested, handle = some requested ∧ ⟨requested, observation⟩ ∈ scope := by
  cases handle with
  | none => cases found
  | some requested => exact ⟨requested, rfl, find_member found⟩

def sourceOutput (scope : Scope) (handle : Option Address) : Option (List UInt8) :=
  (sourceRead scope handle).map Observation.output

def targetOutput (scope : Scope) (handle : Option Address) : Option (List UInt8) :=
  match targetRead scope handle with
  | none => none
  | some observation => some observation.output

theorem output_correspondence (scope : Scope) (handle : Option Address) :
    targetOutput scope handle = sourceOutput scope handle := by
  rw [targetOutput, sourceOutput, read_correspondence]
  cases sourceRead scope handle <;> rfl

def sourceMatches (scope : Scope) (handle : Option Address)
    (inputs : Inputs) (output : List UInt8) : Bool :=
  match sourceRead scope handle with
  | none => false
  | some observation => decide (observation.request.inputs = inputs ∧ observation.output = output)

def targetMatches (scope : Scope) (handle : Option Address)
    (inputs : Inputs) (output : List UInt8) : Bool :=
  match targetRead scope handle with
  | none => false
  | some observation =>
      (observation.request.inputs.code == inputs.code) &&
      (observation.request.inputs.input1 == inputs.input1) &&
      (observation.request.inputs.input2 == inputs.input2) &&
      (observation.output == output)

theorem matches_correspondence (scope : Scope) (handle : Option Address)
    (inputs : Inputs) (output : List UInt8) :
    targetMatches scope handle inputs output = sourceMatches scope handle inputs output := by
  rw [targetMatches, sourceMatches, read_correspondence]
  cases sourceRead scope handle with
  | none => rfl
  | some observation =>
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
      cases observation.request.inputs
      cases inputs
      simp only [Inputs.mk.injEq]
      constructor
      · rintro ⟨⟨⟨code, input1⟩, input2⟩, bytes⟩
        exact ⟨⟨code, input1, input2⟩, bytes⟩
      · rintro ⟨⟨code, input1, input2⟩, bytes⟩
        exact ⟨⟨⟨code, input1⟩, input2⟩, bytes⟩

theorem matches_iff (scope : Scope) (handle : Option Address)
    (inputs : Inputs) (output : List UInt8) :
    targetMatches scope handle inputs output = true ↔
      ∃ observation, targetRead scope handle = some observation ∧
        observation.request.inputs = inputs ∧ observation.output = output := by
  rw [matches_correspondence]
  cases found : sourceRead scope handle with
  | none => simp [sourceMatches, found, read_correspondence]
  | some observation => simp [sourceMatches, found, read_correspondence]

def sourceRelease (scope : Scope) (handle : Option Address) : Scope :=
  match handle with
  | none => scope
  | some requested => scope.filter (fun entry => entry.handle != requested)

def targetRemove : Scope → Address → Scope
  | [], _ => []
  | entry :: rest, requested =>
      if entry.handle = requested then rest else entry :: targetRemove rest requested

def targetRelease (scope : Scope) (handle : Option Address) : Scope :=
  match handle with
  | none => scope
  | some requested => targetRemove scope requested

def Unique (scope : Scope) : Prop := (scope.map Entry.handle).Nodup

def Valid (contract : Contract) (scope : Scope) : Prop :=
  Unique scope ∧ ∀ entry ∈ scope, entry.observation.realized contract

theorem filter_absent (scope : Scope) (handle : Address)
    (absent : handle ∉ scope.map Entry.handle) :
    scope.filter (fun entry => entry.handle != handle) = scope := by
  apply List.filter_eq_self.mpr
  intro entry member
  have different : entry.handle ≠ handle := by
    intro same
    exact absent (List.mem_map.mpr ⟨entry, member, same⟩)
  simp [different]

theorem remove_correspondence (scope : Scope) (handle : Address) (unique : Unique scope) :
    targetRemove scope handle = scope.filter (fun entry => entry.handle != handle) := by
  induction scope with
  | nil => rfl
  | cons entry rest ih =>
      obtain ⟨absent, remaining⟩ := List.nodup_cons.mp unique
      by_cases same : entry.handle = handle
      · rw [targetRemove, if_pos same]
        simp only [List.filter_cons, same, bne_self_eq_false, Bool.false_eq_true, if_false]
        exact (filter_absent rest handle (by simpa [same] using absent)).symm
      · simp only [targetRemove, if_neg same]
        rw [ih remaining]
        simp [same]

theorem release_correspondence (scope : Scope) (handle : Option Address) (unique : Unique scope) :
    targetRelease scope handle = sourceRelease scope handle := by
  cases handle with
  | none => rfl
  | some requested => exact remove_correspondence scope requested unique

theorem release_members_subset (scope : Scope) (handle : Option Address) :
    ∀ entry ∈ sourceRelease scope handle, entry ∈ scope := by
  cases handle with
  | none => exact fun _ member => member
  | some requested => exact fun _ member => (List.mem_filter.mp member).1

theorem release_preserves_valid (contract : Contract) (scope : Scope)
    (handle : Option Address) (valid : Valid contract scope) :
    Valid contract (sourceRelease scope handle) := by
  constructor
  · cases handle with
    | none => exact valid.1
    | some requested =>
        unfold Unique sourceRelease
        have sublist : (scope.filter (fun entry => entry.handle != requested)).Sublist scope :=
          List.filter_sublist
        exact (sublist.map Entry.handle).nodup valid.1
  · intro entry member
    exact valid.2 entry (release_members_subset scope handle entry member)

def complete (scope : Scope) (handle : Address) (observation : Observation) : Scope :=
  ⟨handle, observation⟩ :: scope

theorem completion_preserves_valid (contract : Contract) (scope : Scope)
    (handle : Address) (observation : Observation) (valid : Valid contract scope)
    (fresh : handle ∉ scope.map Entry.handle) (physical : observation.realized contract) :
    Valid contract (complete scope handle observation) := by
  constructor
  · exact List.nodup_cons.mpr ⟨fresh, valid.1⟩
  · intro entry member
    rcases List.mem_cons.mp member with current | previous
    · subst entry
      exact physical
    · exact valid.2 entry previous

inductive Reached (contract : Contract) : Scope → Prop where
  | initial : Reached contract []
  | completed {before : Scope} {handle : Address} {observation : Observation} :
      Reached contract before → handle ∉ before.map Entry.handle →
      observation.realized contract → Reached contract (complete before handle observation)
  | released {before : Scope} (handle : Option Address) :
      Reached contract before → Reached contract (sourceRelease before handle)

theorem reached_valid {contract : Contract} {scope : Scope}
    (reached : Reached contract scope) : Valid contract scope := by
  induction reached with
  | initial => exact ⟨List.nodup_nil, fun _ impossible => False.elim (List.not_mem_nil impossible)⟩
  | completed _ fresh physical prior => exact completion_preserves_valid _ _ _ _ prior fresh physical
  | released handle _ prior => exact release_preserves_valid _ _ handle prior

theorem reached_read_realized {contract : Contract} {scope : Scope}
    (reached : Reached contract scope) {handle : Option Address} {observation : Observation}
    (found : targetRead scope handle = some observation) : observation.realized contract := by
  obtain ⟨requested, _, member⟩ := read_member found
  exact (reached_valid reached).2 ⟨requested, observation⟩ member

theorem released_handle_unreadable (scope : Scope) (handle : Address) (unique : Unique scope) :
    targetRead (targetRelease scope (some handle)) (some handle) = none := by
  rw [release_correspondence scope (some handle) unique]
  change targetFind (scope.filter (fun entry => entry.handle != handle)) handle = none
  cases found : targetFind (scope.filter (fun entry => entry.handle != handle)) handle with
  | none => rfl
  | some observation =>
      have member := find_member found
      have different := (List.mem_filter.mp member).2
      simp at different

theorem absent_handle_never_matches (scope : Scope) (handle : Option Address)
    (absent : targetRead scope handle = none) (inputs : Inputs) (output : List UInt8) :
    targetMatches scope handle inputs output = false := by simp [targetMatches, absent]

end Mettapedia.GSLT.LanguageDef.NativeExecutionScope
