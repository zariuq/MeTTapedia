import Mettapedia.GSLT.Dynamics.RegionPortfolio
import Mettapedia.Machines.ReadOnlyQuery
import Mettapedia.Machines.RegionDependencyStability

/-!
# Live validation for source-indexed region certificates

Prepared evidence keeps exact consulted readings and generation-bearing root
references. Validation is against the current call, not an earlier binding
image. Source or profile mismatch uses that current call's reference semantics.
Missing roots, changed readings and insufficient capacity also select the
reference path. Root completeness and native atomic validation are separate
implementation obligations: these laws do not turn a generation check into a
collector proof or an execution permission.

Once an effect prefix has been published, settlement exposes a residual or a
fault. The fallback dispatcher has no branch that restarts such a prefix.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.ObservationQualified

open Mettapedia.Machines

universe u v

structure LiveContext (Profile Source Key Reading Root : Type u) where
  profile : Profile
  source : Source
  read : Key → Reading
  rootGeneration : Root → Option Nat
  capacity : Nat

structure Requirements (Key Reading Root : Type u) where
  reads : ReadOnlyQuery.Reads Key Reading
  roots : List (Root × Nat)
  capacity : Nat

namespace Requirements

variable {Profile Source Key Reading Root : Type u}

def valid [DecidableEq Reading] (requirements : Requirements Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) : Bool :=
  ReadOnlyQuery.checkReads live.read requirements.reads &&
    requirements.roots.all (fun root => live.rootGeneration root.1 == some root.2) &&
    decide (requirements.capacity ≤ live.capacity)

theorem valid_iff [DecidableEq Reading] (requirements : Requirements Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) :
    requirements.valid live = true ↔
      ReadOnlyQuery.Agrees live.read requirements.reads ∧
      (∀ root ∈ requirements.roots, live.rootGeneration root.1 = some root.2) ∧
      requirements.capacity ≤ live.capacity := by
  simp [valid, ReadOnlyQuery.checkReads_iff, List.all_eq_true, and_assoc]

/-- Unchanged actual readings suffice, even when other parts of the world
changed. Equal root generations and adequate capacity are checked separately. -/
theorem survives [DecidableEq Reading] (requirements : Requirements Key Reading Root)
    (before after : LiveContext Profile Source Key Reading Root)
    (validated : requirements.valid before = true)
    (unaffected : RegionDependencyStability.retains requirements.reads before.read after.read)
    (roots : ∀ root ∈ requirements.roots,
      after.rootGeneration root.1 = before.rootGeneration root.1)
    (capacity : requirements.capacity ≤ after.capacity) :
    requirements.valid after = true := by
  obtain ⟨readings, kept, _⟩ := (valid_iff requirements before).mp validated
  apply (valid_iff requirements after).mpr
  exact ⟨RegionDependencyStability.certificate_survives _ _ _ readings unaffected,
    fun root member => (roots root member).trans (kept root member), capacity⟩

theorem changed_read_refuses [DecidableEq Reading] (requirements : Requirements Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (key : Key) (value : Reading)
    (recorded : (key, value) ∈ requirements.reads) (changed : live.read key ≠ value) :
    requirements.valid live = false := by
  apply Bool.eq_false_iff.mpr
  intro valid
  exact changed (((valid_iff requirements live).mp valid).1 (key, value) recorded)

theorem missing_or_reused_root_refuses [DecidableEq Reading]
    (requirements : Requirements Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (root : Root) (generation : Nat)
    (recorded : (root, generation) ∈ requirements.roots)
    (changed : live.rootGeneration root ≠ some generation) :
    requirements.valid live = false := by
  apply Bool.eq_false_iff.mpr
  intro valid
  exact changed (((valid_iff requirements live).mp valid).2.1 (root, generation) recorded)

end Requirements

structure PreparedRegion {Profile Source Input Result Summary : Type u} (Regime : Type v)
    (boundary : Profile → Source → Boundary Input Result Summary) (Key Reading Root : Type u) where
  profile : Profile
  source : Source
  candidate : Candidate (boundary profile source) Regime
  requirements : Requirements Key Reading Root

namespace PreparedRegion

variable {Profile Source Input Result Summary Key Reading Root : Type u} {Regime : Type v}
variable {boundary : Profile → Source → Boundary Input Result Summary}

def execute [DecidableEq Profile] [DecidableEq Source] [DecidableEq Reading]
    (prepared : PreparedRegion Regime boundary Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (input : Input) : Summary :=
  if live.profile = prepared.profile ∧ live.source = prepared.source ∧
      prepared.requirements.valid live = true then
    prepared.candidate.region.execute input
  else (boundary live.profile live.source).reference input

theorem execute_exact [DecidableEq Profile] [DecidableEq Source] [DecidableEq Reading]
    (prepared : PreparedRegion Regime boundary Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (input : Input) :
    prepared.execute live input = (boundary live.profile live.source).reference input := by
  unfold execute
  split
  · rename_i admitted
    rw [CertifiedRegion.execute_eq_reference, admitted.1, admitted.2.1]
  · rfl

theorem changed_profile_uses_current_reference
    [DecidableEq Profile] [DecidableEq Source] [DecidableEq Reading]
    (prepared : PreparedRegion Regime boundary Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (input : Input)
    (changed : live.profile ≠ prepared.profile) :
    prepared.execute live input = (boundary live.profile live.source).reference input := by
  simp [execute, changed]

theorem changed_source_uses_current_reference
    [DecidableEq Profile] [DecidableEq Source] [DecidableEq Reading]
    (prepared : PreparedRegion Regime boundary Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (input : Input)
    (changed : live.source ≠ prepared.source) :
    prepared.execute live input = (boundary live.profile live.source).reference input := by
  simp [execute, changed]

theorem invalid_uses_reference
    [DecidableEq Profile] [DecidableEq Source] [DecidableEq Reading]
    (prepared : PreparedRegion Regime boundary Key Reading Root)
    (live : LiveContext Profile Source Key Reading Root) (input : Input)
    (invalid : prepared.requirements.valid live = false) :
    prepared.execute live input = (boundary live.profile live.source).reference input := by
  simp [execute, invalid]

end PreparedRegion

/-- These are settlement categories, not source answers. A published prefix
requires its actual residual, including any committed stores and bindings. -/
inductive Settlement (Input Answer Event Residual Fault : Type u) where
  | declined (restored : Input)
  | completed (answer : Answer)
  | published (first : Event) (later : List Event) (residual : Residual)
  | faulted (published : List Event) (fault : Fault) (residual : Residual)

inductive Delivery (Answer Event Residual Fault : Type u) where
  | answer (value : Answer)
  | suspended (published : List Event) (residual : Residual)
  | faulted (published : List Event) (fault : Fault) (residual : Residual)
  deriving DecidableEq

def settle {Input Answer Event Residual Fault : Type u} (reference : Input → Answer) :
    Settlement Input Answer Event Residual Fault → Delivery Answer Event Residual Fault
  | .declined restored => .answer (reference restored)
  | .completed answer => .answer answer
  | .published first later residual => .suspended (first :: later) residual
  | .faulted events fault residual => .faulted events fault residual

theorem published_does_not_restart {Input Answer Event Residual Fault : Type u}
    (reference : Input → Answer) (first : Event) (later : List Event) (residual : Residual)
    (answer : Answer) :
    settle reference (Settlement.published (Fault := Fault) first later residual) ≠
      Delivery.answer answer := by simp [settle]

theorem published_preserves_prefix_and_residual {Input Answer Event Residual Fault : Type u}
    (reference : Input → Answer) (first : Event) (later : List Event) (residual : Residual) :
    settle reference (Settlement.published (Fault := Fault) first later residual) =
      Delivery.suspended (first :: later) residual := rfl

namespace PreparedControls

def requirements : Requirements Nat Nat Nat := ⟨[(0, 7)], [(4, 3)], 10⟩

def live : LiveContext Bool Nat Nat Nat Nat :=
  ⟨false, 1, fun _ => 7, fun root => if root = 4 then some 3 else none, 10⟩

theorem valid_initial : requirements.valid live = true := by decide

theorem unrelated_change_is_reusable :
    requirements.valid {live with read := Function.update live.read 9 100} = true := by decide

theorem changed_equation_invalidates :
    requirements.valid {live with read := Function.update live.read 0 8} = false := by decide

theorem recycled_root_is_not_the_saved_root :
    requirements.valid {live with rootGeneration := fun _ => some 4} = false := by decide

theorem missing_root_invalidates :
    requirements.valid {live with rootGeneration := fun _ => none} = false := by decide

theorem insufficient_capacity_declines :
    requirements.valid {live with capacity := 9} = false := by decide

/-- Replaying a source which appends one effect would duplicate the already
published occurrence. Keeping the residual instead retains exactly one. -/
theorem replay_changes_visible_effects :
    ([7] : List Nat) ++ [7] ≠ [7] ∧
      settle (fun (_ : Unit) => (0 : Nat))
        (Settlement.published (Fault := Bool) 7 [] 9) = Delivery.suspended [7] 9 := by decide

end PreparedControls

#print axioms Requirements.valid_iff
#print axioms Requirements.survives
#print axioms PreparedRegion.execute_exact
#print axioms published_does_not_restart

end Mettapedia.GSLT.Dynamics.ObservationQualified
