import Mettapedia.Machines.AdditiveFoldInference
import Mettapedia.Machines.LiveWordRegions
import Mettapedia.Machines.InterleavedProtocolRegions

/-!
# Inferred fold certificates with live word admission

A static additive certificate licenses a summary. A live check separately
qualifies conversion and word addition. The source observation profile decides
whether final values, logical fold counts, or every prefix state is observable.
The word worker handles the first two and declines the third. Declaration
changes are checked against the actual current program before cached evidence
is used. Refusal executes the reference with its full result type.

Requests delimit completed atomic IR operations. The interleaving theorem
preserves boundaries between those requests; it does not fuse across source
yield points or establish C allocation and linearization properties.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.InferredWordFold

open AdditiveFoldInference Cursor Cursor.LiveAdmission
open Mettapedia.TypeTheory
open Mettapedia.TypeTheory.IndexedPolynomial

abbrev Registers (n : Nat) := Fin n → Nat

structure WordPlan (n : Nat) where
  initial : Fin n → UInt64
  contribution : Fin n → UInt64

def prepareWords {n : Nat} (initial contribution : Registers n) : Option (WordPlan n) :=
  if ∀ i, initial i + contribution i < UInt64.size then
    some ⟨fun i => UInt64.ofNat (initial i), fun i => UInt64.ofNat (contribution i)⟩
  else none

def executeWords {n : Nat} (plan : WordPlan n) : Registers n :=
  fun i => (plan.initial i + plan.contribution i).toNat

theorem prepareWords_correct {n : Nat} (initial contribution : Registers n) (plan : WordPlan n)
    (accepted : prepareWords initial contribution = some plan) :
    executeWords plan = initial + contribution := by
  unfold prepareWords at accepted
  split at accepted
  next fits =>
    cases accepted
    funext i
    exact LiveWordRegions.addCode_correct (initial i) (contribution i) _
      (LiveWordRegions.addCode_of_fits _ _ (fits i))
  next => simp at accepted

theorem word_admission_iff {n : Nat} (initial contribution : Registers n) :
    (prepareWords initial contribution).isSome = true ↔ ∀ i, initial i + contribution i < UInt64.size := by
  simp [prepareWords]

theorem final_bound_covers_prefix {n : Nat} (weights : Fin n → Weight)
    (initial : Registers n) (first later : List Nat)
    (fits : ∀ i, initial i + summary weights (first ++ later) i < UInt64.size) :
    ∀ i, initial i + summary weights first i < UInt64.size := by
  intro i
  have bound := fits i
  rw [summary_append] at bound
  change initial i + (summary weights first i + summary weights later i) < UInt64.size at bound
  omega

theorem certificate_run {n : Nat} {program : Program n} (certificate : Certificate program)
    (inputs : List Nat) (initial : Registers n) :
    sourceRun program inputs initial = initial + summary certificate.weights inputs := by
  induction inputs generalizing initial with
  | nil => funext i; simp [sourceRun, summary]
  | cons input rest ih =>
    rw [sourceRun, List.foldl_cons]
    change sourceRun program rest (sourceStep program initial input) = _
    rw [ih, certificate.transition]
    funext i
    simp [summary, Nat.add_assoc]

inductive Profile
  | value | counted | prefixes
  deriving DecidableEq

inductive Request (n : Nat)
  | run (profile : Profile) (inputs : List Nat)
  | load (destination : Fin n) (value : Nat)
  | read (source : Fin n)

abbrev Reply {n : Nat} : Request n → Type
  | .run .value _ => Registers n
  | .run .counted _ => Nat × Registers n
  | .run .prefixes _ => List (Registers n)
  | .load _ _ => Unit
  | .read _ => Nat

abbrev protocol (n : Nat) : IndexedPolynomial Unit (fun _ => Unit) where
  Shape _ _ := Request n
  Position := Reply
  next _ _ := ()

structure World (n : Nat) where
  program : Program n
  registers : Registers n

def reference (n : Nat) : Provider (protocol n) where
  State _ _ := World n
  step world request := match request with
    | .run profile inputs =>
      let values := sourceRun world.program inputs world.registers
      let after := {world with registers := values}
      match profile with
      | .value => ⟨values, after⟩
      | .counted => ⟨(inputs.length, values), after⟩
      | .prefixes => ⟨inputs.scanl (sourceStep world.program) world.registers, after⟩
    | .load destination value => ⟨(), {world with registers := Function.update world.registers destination value}⟩
    | .read source => ⟨world.registers source, world⟩

def cachedValues {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (inputs : List Nat) : Option (Registers n) :=
  if world.program = saved then
    (prepareWords world.registers (summary certificate.weights inputs)).map executeWords
  else none

theorem cachedValues_correct {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (inputs : List Nat) (values : Registers n)
    (accepted : cachedValues certificate world inputs = some values) :
    values = sourceRun world.program inputs world.registers := by
  unfold cachedValues at accepted
  split at accepted
  next same =>
    obtain ⟨plan, planned, equal⟩ := Option.map_eq_some_iff.mp accepted
    rw [← equal, prepareWords_correct _ _ _ planned, same, certificate_run]
  next => simp at accepted

def attempt {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (request : Request n) :
    Option (Response (reference n) (base := ()) (index := ()) request) :=
  match request with
  | .run .value inputs => (cachedValues certificate world inputs).map fun values =>
      ⟨values, {world with registers := values}⟩
  | .run .counted inputs => (cachedValues certificate world inputs).map fun values =>
      ⟨(inputs.length, values), {world with registers := values}⟩
  | .run .prefixes _ | .load _ _ | .read _ => none

theorem attempt_correct {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (request : Request n)
    (result : Response (reference n) (base := ()) (index := ()) request)
    (accepted : attempt certificate world request = some result) :
    result = (reference n).step world request := by
  cases request with
  | load destination value => simp [attempt] at accepted
  | read source => simp [attempt] at accepted
  | run profile inputs =>
    cases profile with
    | prefixes => simp [attempt] at accepted
    | value =>
      obtain ⟨values, planned, equal⟩ := Option.map_eq_some_iff.mp accepted
      rw [← equal, cachedValues_correct certificate world inputs values planned]
      rfl
    | counted =>
      obtain ⟨values, planned, equal⟩ := Option.map_eq_some_iff.mp accepted
      rw [← equal, cachedValues_correct certificate world inputs values planned]
      rfl

def worker {n : Nat} {saved : Program n} (certificate : Certificate saved) : PartialWorker (reference n) where
  attempt := fun {_ _} world request => attempt certificate world request
  correct := fun {_ _} world request result accepted => attempt_correct certificate world request result accepted

theorem live_exact {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (request : Request n) :
    (worker certificate).execute (base := ()) (index := ()) world request = (reference n).step world request :=
  (worker certificate).execute_exact world request

theorem prefixes_decline {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (inputs : List Nat) : attempt certificate world (.run .prefixes inputs) = none := rfl

theorem changed_declaration_declines {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (inputs : List Nat) (changed : world.program ≠ saved) :
    cachedValues certificate world inputs = none := by simp [cachedValues, changed]

/-- Structural program equality is the explicit conservative cache check in
this model. A native revision stamp needs its own refinement to this condition. -/
theorem cached_admission_iff {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (world : World n) (inputs : List Nat) :
    (cachedValues certificate world inputs).isSome = true ↔
      world.program = saved ∧ ∀ i, world.registers i + summary certificate.weights inputs i < UInt64.size := by
  by_cases current : world.program = saved
  · simp [cachedValues, current, word_admission_iff]
  · simp [cachedValues, current]

def environmentBoundary {n : Nat} {saved : Program n} (certificate : Certificate saved)
    (change : World n → World n) : InterleavedRegions.Boundary (worker certificate).hom where
  changeActual := fun {_ _} => change
  changeReference := fun {_ _} => change
  commutes := fun _ => rfl

/-- Reuses the existing interleaving law with an independently computed word
worker. Clients may adapt later requests to earlier replies. -/
theorem interleaved_exact {n : Nat} {saved : Program n} (certificate : Certificate saved)
    {Return : Unit → Unit → Type} (client : Client (P := protocol n) (Return := Return))
    (history : List (InterleavedRegions.Event (worker certificate).hom))
    (receipt : InterleavedRegions.Receipt client (worker certificate).provider ()) :
    InterleavedRegions.mapReceipt client (worker certificate).hom
      (InterleavedRegions.actualHistory client history receipt) =
    InterleavedRegions.referenceHistory client history
      (InterleavedRegions.mapReceipt client (worker certificate).hom receipt) :=
  InterleavedRegions.history_exact client (worker certificate).hom history receipt

namespace Controls

def counter : Program 1 := fun i => .add (.register i) (.weight (.constant 1))
def proof : Certificate counter :=
  ⟨fun _ => .add (.constant 0) (.constant 1), accepted_transition counter _ (by decide)⟩
def small : World 1 := ⟨counter, fun _ => 5⟩

theorem word_result : (cachedValues proof small [9, 8]).map (fun values => values 0) = some 7 := by decide

theorem overflowing_result_declines :
    (cachedValues proof ⟨counter, fun _ => UInt64.size - 1⟩ [9]).isNone = true := by decide

theorem observation_profile_matters :
    (attempt proof small (.run .value [9])).isSome = true ∧
    (attempt proof small (.run .prefixes [9])).isNone = true := by decide

theorem changed_body_declines :
    (cachedValues proof ⟨AdditiveFoldInference.Controls.orderedDecimal, fun _ => 0⟩ [1, 2]).isNone = true := by decide

theorem changed_body_falls_back :
    ((worker proof).execute (base := ()) (index := ())
      ⟨AdditiveFoldInference.Controls.orderedDecimal, fun _ => 0⟩ (.run .value [1, 2])).1 0 = 12 := by
  rw [live_exact]
  decide

theorem overflow_falls_back_without_wrapping :
    ((worker proof).execute (base := ()) (index := ())
      ⟨counter, fun _ => UInt64.size - 1⟩ (.run .value [9])).1 0 = UInt64.size := by
  rw [live_exact]
  decide

theorem counted_profile_keeps_logical_steps :
    ((worker proof).execute (base := ()) (index := ()) small (.run .counted [9, 8])).1.1 = 2 := by
  rw [live_exact]
  decide

end Controls
end Mettapedia.Machines.InferredWordFold
