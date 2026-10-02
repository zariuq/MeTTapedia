import Mettapedia.Languages.VibeITP.Native.RadixCounters
import Mettapedia.Languages.VibeITP.Spec.InstructionBounds
import Mettapedia.Languages.VibeITP.Spec.Protocol
import Mathlib.Tactic

/-!
The pre-execution slot measurement: independent natural capacities and unsigned
native updates. The largest word cannot name a representable slot-array extent.
Other allocation and physical byte-extent refusals remain resource outcomes.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.VibeITP.Native.SlotMeasurement

open Spec

abbrev Capacities := Space → Nat
abbrev NativeCapacities := Space → BitVec 64
abbrev Use := Space × Nat
abbrev NativeUse := Space × BitVec 64

inductive Fault where
  | unrepresentableExtent
  deriving DecidableEq, Repr

def initial : Capacities
  | .symbol => 13
  | _ => 1

def nativeInitial : NativeCapacities
  | .symbol => 13
  | _ => 1

def decode (capacities : NativeCapacities) : Capacities :=
  fun space => (capacities space).toNat

theorem initial_correspondence : decode nativeInitial = initial := by
  funext space
  cases space <;> rfl

def slot (capacities : Capacities) (space : Space) (index : Nat) : Except Fault Capacities :=
  if index + 1 < wordBound then
    .ok (fun candidate => if candidate = space then max (capacities candidate) (index + 1)
      else capacities candidate)
  else .error .unrepresentableExtent

def nativeSlot (capacities : NativeCapacities) (space : Space) (index : BitVec 64) :
    Except Fault NativeCapacities :=
  if index = BitVec.allOnes 64 then .error .unrepresentableExtent
  else .ok (fun candidate =>
    if candidate = space then
      if capacities candidate ≤ index then index + 1 else capacities candidate
    else capacities candidate)

theorem maximum_word_iff (index : BitVec 64) :
    index = BitVec.allOnes 64 ↔ index.toNat + 1 = wordBound := by
  rw [← BitVec.toNat_inj, BitVec.toNat_allOnes]
  have bounded := index.isLt
  change index.toNat < wordBound at bounded
  change index.toNat = wordBound - 1 ↔ _
  have positive : 0 < wordBound := Nat.two_pow_pos _
  constructor <;> intro hypothesis <;> omega

theorem slot_correspondence (capacities : NativeCapacities) (space : Space) (index : BitVec 64) :
    (nativeSlot capacities space index).map decode = slot (decode capacities) space index.toNat := by
  unfold nativeSlot slot
  by_cases maximum : index = BitVec.allOnes 64
  · have extent := (maximum_word_iff index).mp maximum
    have outside : ¬ index.toNat + 1 < wordBound := by rw [extent]; exact Nat.lt_irrefl _
    rw [if_pos maximum, if_neg outside]
    rfl
  · have extent : index.toNat + 1 < wordBound := by
      have bounded := index.isLt
      have notMaximum := (maximum_word_iff index).not.mp maximum
      change index.toNat < wordBound at bounded
      omega
    have nonzero : index + 1 ≠ 0 := by
      intro zero
      have full := (RadixCounters.word_increment_zero_iff index).mp zero
      omega
    simp only [maximum, if_false, extent, if_true, Except.map]
    congr 1
    funext candidate
    unfold decode
    by_cases same : candidate = space
    · simp only [same, if_true]
      by_cases below : capacities space ≤ index
      · rw [if_pos below, RadixCounters.word_increment_no_carry index nonzero, max_eq_right]
        have ordered := BitVec.le_def.mp below
        omega
      · rw [if_neg below, max_eq_left]
        have ordered : index.toNat < (capacities space).toNat := by
          simpa only [BitVec.le_def, not_le] using below
        omega
    · simp only [same, if_false]

theorem slot_capacity_monotone (before after : Capacities) (space : Space) (index : Nat)
    (completed : slot before space index = .ok after) :
    ∀ candidate, before candidate ≤ after candidate := by
  unfold slot at completed
  split at completed
  · cases completed
    intro candidate
    by_cases same : candidate = space <;> simp [same]
  · cases completed

theorem slot_covers_index (before after : Capacities) (space : Space) (index : Nat)
    (completed : slot before space index = .ok after) : index < after space := by
  unfold slot at completed
  split at completed
  · cases completed
    simp only [if_true]
    exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)
  · cases completed

theorem slot_preserves_word_bounds (before after : Capacities) (space : Space) (index : Nat)
    (bounded : ∀ candidate, before candidate < wordBound)
    (completed : slot before space index = .ok after) :
    ∀ candidate, after candidate < wordBound := by
  unfold slot at completed
  split at completed
  · rename_i representable
    cases completed
    intro candidate
    by_cases same : candidate = space
    · simp only [same, if_true]
      exact max_lt (bounded space) representable
    · simpa only [same, if_false] using bounded candidate
  · cases completed

def uses : Capacities → List Use → Except Fault Capacities
  | capacities, [] => .ok capacities
  | capacities, (space, index) :: rest => do
    let next ← slot capacities space index
    uses next rest

def nativeUses : NativeCapacities → List NativeUse → Except Fault NativeCapacities
  | capacities, [] => .ok capacities
  | capacities, (space, index) :: rest => do
    let next ← nativeSlot capacities space index
    nativeUses next rest

def decodeUses (references : List NativeUse) : List Use :=
  references.map (fun pair => (pair.1, pair.2.toNat))

theorem uses_correspondence (capacities : NativeCapacities) (references : List NativeUse) :
    (nativeUses capacities references).map decode = uses (decode capacities) (decodeUses references) := by
  induction references generalizing capacities with
  | nil => rfl
  | cons reference rest ih =>
    rcases reference with ⟨space, index⟩
    simp only [nativeUses, decodeUses, List.map_cons, uses]
    have first := slot_correspondence capacities space index
    cases source : nativeSlot capacities space index with
    | error error =>
      simp only [source, Except.map] at first
      rw [← first]
      rfl
    | ok next =>
      simp only [source, Except.map] at first
      rw [← first]
      simpa only [bind, Except.bind, decodeUses] using ih next

theorem uses_capacity_monotone (before after : Capacities) (references : List Use)
    (completed : uses before references = .ok after) :
    ∀ space, before space ≤ after space := by
  induction references generalizing before with
  | nil => cases completed; exact fun _ => le_rfl
  | cons reference rest ih =>
    rcases reference with ⟨space, index⟩
    unfold uses at completed
    cases first : slot before space index with
    | error error => simp [first, bind, Except.bind] at completed
    | ok next =>
      simp only [first, bind, Except.bind] at completed
      intro candidate
      exact le_trans (slot_capacity_monotone before next space index first candidate)
        (ih next completed candidate)

theorem uses_covers_every_reference (before after : Capacities) (references : List Use)
    (completed : uses before references = .ok after) :
    ∀ space index, (space, index) ∈ references → index < after space := by
  induction references generalizing before with
  | nil => simp
  | cons reference rest ih =>
    rcases reference with ⟨headSpace, headIndex⟩
    unfold uses at completed
    cases first : slot before headSpace headIndex with
    | error error => simp [first, bind, Except.bind] at completed
    | ok next =>
      simp only [first, bind, Except.bind] at completed
      intro space index member
      rcases List.mem_cons.mp member with same | later
      · cases same
        exact Nat.lt_of_lt_of_le (slot_covers_index before next headSpace headIndex first)
          (uses_capacity_monotone next after rest completed headSpace)
      · exact ih next completed space index later

theorem uses_preserves_word_bounds (before after : Capacities) (references : List Use)
    (bounded : ∀ candidate, before candidate < wordBound)
    (completed : uses before references = .ok after) :
    ∀ candidate, after candidate < wordBound := by
  induction references generalizing before with
  | nil => cases completed; exact bounded
  | cons reference rest ih =>
    rcases reference with ⟨space, index⟩
    unfold uses at completed
    cases first : slot before space index with
    | error error => simp [first, bind, Except.bind] at completed
    | ok next =>
      simp only [first, bind, Except.bind] at completed
      exact ih next (slot_preserves_word_bounds before next space index bounded first) completed

/-- Slot references in the actual measurement order. Numeric literal operands
and definition hints are words, not slot references. -/
def references : Instr → List Use
  | .fvarNew _ dst => [(.symbol, dst)]
  | .constNew _ dst => [(.symbol, dst)]
  | .symbolSwap first second => [(.symbol, first), (.symbol, second)]
  | .symbolFree slot => [(.symbol, slot)]
  | .termNewBVar _ dst => [(.term, dst)]
  | .termNewLiteral _ dst => [(.term, dst)]
  | .termNewApp symbol arguments dst =>
      [(.symbol, symbol), (.term, dst)] ++ arguments.map (.term, ·)
  | .termSwap first second => [(.term, first), (.term, second)]
  | .termFree slot => [(.term, slot)]
  | .addAxiom statement dst => [(.term, statement), (.theorem, dst)]
  | .thmExchange theoremSlot statement => [(.theorem, theoremSlot), (.term, statement)]
  | .thmFree slot => [(.theorem, slot)]
  | .thmSwap first second => [(.theorem, first), (.theorem, second)]
  | .challengeAdd statement dst => [(.term, statement), (.challenge, dst)]
  | .challengeSatisfy challenge theoremSlot => [(.challenge, challenge), (.theorem, theoremSlot)]
  | .modusPonens implication premise dst => [(.theorem, implication), (.theorem, premise), (.theorem, dst)]
  | .thmInstantiate theoremSlot fvar value dst =>
      [(.theorem, theoremSlot), (.symbol, fvar), (.term, value), (.theorem, dst)]
  | .defineConst fvars _ value dstSymbol dstTheorem =>
      [(.term, value), (.symbol, dstSymbol), (.theorem, dstTheorem)] ++ fvars.map (.symbol, ·)
  | .litIsNat _ dst => [(.theorem, dst)]
  | .litLt _ _ dst => [(.theorem, dst)]
  | .litAdd _ _ dst => [(.theorem, dst)]
  | .litMul _ _ dst => [(.theorem, dst)]
  | .litDiv _ _ dst => [(.theorem, dst)]
  | .litLength term dst => [(.term, term), (.theorem, dst)]
  | .litGet term _ dst => [(.term, term), (.theorem, dst)]
  | .jit safe dst dstTerm => [(.theorem, safe), (.theorem, dst), (.term, dstTerm)]

def instruction (capacities : Capacities) (operation : Instr) : Except Fault Capacities :=
  uses capacities (references operation)

theorem references_machine_bounded (operation : Instr) (bounded : operation.MachineBounded) :
    ∀ reference ∈ references operation, reference.2 < wordBound := by
  intro reference member
  have included : reference.2 ∈ operation.machineWords := by
    cases operation <;>
      simp_all [references, Instr.machineWords, List.mem_map]
    all_goals aesop
  exact bounded reference.2 included

def encodeUses (references : List Use) : List NativeUse :=
  references.map (fun pair => (pair.1, BitVec.ofNat 64 pair.2))

theorem encoded_references_round_trip (references : List Use)
    (bounded : ∀ reference ∈ references, reference.2 < wordBound) :
    decodeUses (encodeUses references) = references := by
  induction references with
  | nil => rfl
  | cons reference rest ih =>
    have head := bounded reference (by simp)
    have tail : ∀ reference ∈ rest, reference.2 < wordBound := by
      intro reference member
      exact bounded reference (List.mem_cons_of_mem _ member)
    change reference.2 < 2 ^ 64 at head
    simp only [decodeUses, encodeUses, List.map_cons, BitVec.toNat_ofNat, Nat.mod_eq_of_lt head]
    rw [show (reference.1, reference.2) = reference from Prod.eta _]
    exact congrArg (reference :: ·) (ih tail)

def nativeInstruction (capacities : NativeCapacities) (operation : Instr) :
    Except Fault NativeCapacities := nativeUses capacities (encodeUses (references operation))

theorem instruction_correspondence (capacities : NativeCapacities) (operation : Instr)
    (bounded : operation.MachineBounded) :
    (nativeInstruction capacities operation).map decode = instruction (decode capacities) operation := by
  rw [nativeInstruction, uses_correspondence,
    encoded_references_round_trip _ (references_machine_bounded operation bounded)]
  rfl

def instructions : Capacities → List Instr → Except Fault Capacities
  | capacities, [] => .ok capacities
  | capacities, operation :: rest => do
    let next ← instruction capacities operation
    instructions next rest

theorem instructions_capacity_monotone (before after : Capacities) (operations : List Instr)
    (completed : instructions before operations = .ok after) :
    ∀ space, before space ≤ after space := by
  induction operations generalizing before with
  | nil => cases completed; exact fun _ => le_rfl
  | cons operation rest ih =>
    unfold instructions at completed
    cases first : instruction before operation with
    | error error => simp [first, bind, Except.bind] at completed
    | ok next =>
      simp only [first, bind, Except.bind] at completed
      intro space
      exact le_trans (uses_capacity_monotone before next (references operation) first space)
        (ih next completed space)

theorem instructions_cover_every_reference (before after : Capacities) (operations : List Instr)
    (completed : instructions before operations = .ok after) :
    ∀ operation ∈ operations, ∀ space index, (space, index) ∈ references operation → index < after space := by
  induction operations generalizing before with
  | nil => simp
  | cons head rest ih =>
    unfold instructions at completed
    cases first : instruction before head with
    | error error => simp [first, bind, Except.bind] at completed
    | ok next =>
      simp only [first, bind, Except.bind] at completed
      intro operation member space index reference
      rcases List.mem_cons.mp member with same | later
      · subst operation
        exact Nat.lt_of_lt_of_le
          (uses_covers_every_reference before next (references head) first space index reference)
          (instructions_capacity_monotone next after rest completed space)
      · exact ih next completed operation later space index reference

theorem initial_word_bounds : ∀ space, initial space < wordBound := by
  intro space
  cases space <;> decide +kernel

theorem maximum_slot_refused (capacities : NativeCapacities) (space : Space) :
    nativeSlot capacities space (BitVec.allOnes 64) = .error .unrepresentableExtent := by
  simp [nativeSlot]

theorem largest_representable_extent (capacities : NativeCapacities) :
    (nativeSlot capacities .term (BitVec.ofNat 64 (wordBound - 2))).map (fun next => (next .term).toNat) =
      .ok (max (capacities .term).toNat (wordBound - 1)) := by
  have correspondence := slot_correspondence capacities .term (BitVec.ofNat 64 (wordBound - 2))
  have project := congrArg (fun outcome => outcome.map (fun next => next Space.term)) correspondence
  cases result : nativeSlot capacities .term (BitVec.ofNat 64 (wordBound - 2)) with
  | error error =>
    rw [result] at project
    simp [slot, decode, Except.map, wordBound] at project
  | ok next =>
    rw [result] at project
    simpa [slot, decode, Except.map, wordBound] using project

end Mettapedia.Languages.VibeITP.Native.SlotMeasurement
