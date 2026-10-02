import Mettapedia.Languages.ProcessCalculi.MORK.MM2MatchingBatch

/-!
# Physical MM2 queue order and regenerated-work starvation

A source program captures its selected exec through the read snapshot and
reinstalls it at the same lower physical key. The other enabled exec never
runs, at any finite exact-fuel prefix. Thus a well-order on a finite set of
keys is insufficient for fairness when work at a smaller key can regenerate.

Separately, nested locations give an infinite descending chain for the actual
compact-byte order. These are properties of the existing MM2 source executor
and encoder, not a claim that a replacement runtime has been verified.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MORK.MM2QueueFairness

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open ReflectiveComputable WQComputable

/-- Both occurrences of the captured input and output are template captures,
so reinstatement preserves the executable's actual variable syntax. -/
def looping : Atom := .expression [.symbol "exec", .symbol "a",
  .expression [.symbol ",", .expression [.symbol "exec", .symbol "a", .var "p", .var "t"]],
  .expression [.symbol ",", .expression [.symbol "exec", .symbol "a", .var "p", .var "t"]]]

def fired : Atom := .expression [.symbol "fired", .symbol "b"]

def waiting : Atom := .expression [.symbol "exec", .symbol "b", .expression [.symbol ","],
  .expression [.symbol ",", fired]]

def workspace : List Atom := [waiting, looping]

theorem physical_lower_key :
    lexLt (totalMorkCompactKey looping) (totalMorkCompactKey waiting) = true := by decide

theorem both_physically_representable :
    (morkCompactKey? looping).isSome = true ∧
      (morkCompactKey? waiting).isSome = true := by decide

/-- The deferred job is enabled even without facts: its input is the empty join. -/
theorem waiting_is_enabled :
    cReflectiveSourceWorkQueueStep .consume [waiting] = some [fired] := by decide

/-- The selected executable is consumed live, read back from the pinned
snapshot, and recreated by a real reflective sink. -/
theorem regeneration_step :
    cReflectiveSourceWorkQueueStep .consume workspace = some workspace := by decide

theorem every_prefix_regenerates (fuel : Nat) :
    cReflectiveSourceWorkQueueRunN .consume fuel workspace = (workspace, fuel) := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simp only [cReflectiveSourceWorkQueueRunN, regeneration_step, ih]

theorem enabled_job_is_starved (fuel : Nat) :
    waiting ∈ (cReflectiveSourceWorkQueueRunN .consume fuel workspace).1 ∧
      fired ∉ (cReflectiveSourceWorkQueueRunN .consume fuel workspace).1 := by
  rw [every_prefix_regenerates]
  change waiting ∈ workspace ∧ fired ∉ workspace
  decide

/-- The same infinite run exists through actual completed matching batches;
no empty-ready-queue or bounded-prefix observation establishes saturation. -/
theorem every_step_has_a_completed_matcher :
    MM2MatchingBatch.CompletedStep .consume workspace workspace := by
  exact (MM2MatchingBatch.completed_step_iff _ _ _).2 regeneration_step

/-- A finite alphabet is not enough: compact lexicographic order sees a new
expression arity byte before the previous terminal symbol byte. -/
def nested : Nat → Atom
  | 0 => .symbol "a"
  | n + 1 => .expression [.symbol "s", nested n]

def nestedBytes : Nat → List Nat
  | 0 => [193, 97]
  | n + 1 => [2, 193, 115] ++ nestedBytes n

theorem nested_encoding (n : Nat) (environment : List String) :
    morkCompactEncodeAtom environment (nested n) = some (nestedBytes n, environment) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [nested, morkCompactEncodeAtom]
      rw [if_pos (by simp)]
      simp only [morkCompactEncodeAtom.encodeList]
      have symbolExact : morkCompactEncodeAtom environment (.symbol "s") =
          some ([193, 115], environment) := rfl
      rw [symbolExact]
      simp only
      rw [ih]
      simp [nestedBytes]

theorem nested_key (n : Nat) :
    morkCompactKey? (nested n) = some (nestedBytes n) := by
  simp [morkCompactKey?, nested_encoding]

theorem deeper_location_sorts_first (n : Nat) :
    lexLt (nestedBytes (n + 1)) (nestedBytes n) = true := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [nestedBytes, List.cons_append, List.nil_append, lexLt, Nat.lt_irrefl, if_false] using ih

theorem physical_locations_descend (n : Nat) :
    lexLt (totalMorkCompactKey (nested (n + 1)))
      (totalMorkCompactKey (nested n)) = true := by
  simpa only [totalMorkCompactKey, nested_key, Option.getD_some] using
    deeper_location_sorts_first n


/-- A concrete valid executable family; locations occur before both bodies
in the full compact key selected by the actual work queue. -/
def nestedExec (n : Nat) : Atom := .expression [.symbol "exec", nested n,
  .expression [.symbol ","], .expression [.symbol ",", fired]]

def execKey (n : Nat) : List Nat :=
  [4, 196, 101, 120, 101, 99] ++ nestedBytes n ++
    [1, 193, 44, 2, 193, 44, 2, 197, 102, 105, 114, 101, 100, 193, 98]

theorem full_exec_encoding (n : Nat) :
    morkCompactKey? (nestedExec n) = some (execKey n) := by
  simp only [morkCompactKey?, nestedExec, morkCompactEncodeAtom]
  rw [if_pos (by simp)]
  simp only [morkCompactEncodeAtom.encodeList]
  have execEncoded : morkCompactEncodeAtom [] (.symbol "exec") =
      some ([196, 101, 120, 101, 99], []) := rfl
  rw [execEncoded]
  simp only
  rw [nested_encoding]
  simp only
  rfl

theorem nested_bytes_with_tails (n : Nat) (left right : List Nat) :
    lexLt (nestedBytes (n + 1) ++ left) (nestedBytes n ++ right) = true := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa only [nestedBytes, List.append_assoc, List.cons_append, List.nil_append,
        lexLt, Nat.lt_irrefl, if_false] using ih

theorem full_exec_keys_descend (n : Nat) :
    lexLt (totalMorkCompactKey (nestedExec (n + 1)))
      (totalMorkCompactKey (nestedExec n)) = true := by
  simp only [totalMorkCompactKey, full_exec_encoding, Option.getD_some]
  change lexLt (nestedBytes (n + 1) ++ _) (nestedBytes n ++ _) = true
  exact nested_bytes_with_tails n _ _

/-- Non-well-foundedness belongs to the pinned compact key relation itself,
not merely to an approximation by syntactic nesting depth. -/
theorem physical_exec_order_not_wellFounded :
    ¬ WellFounded (fun left right : Atom =>
      lexLt (totalMorkCompactKey left) (totalMorkCompactKey right) = true) := by
  intro wellFounded
  have notAccessible : ¬ Acc (fun left right : Atom =>
      lexLt (totalMorkCompactKey left) (totalMorkCompactKey right) = true) (nestedExec 0) :=
    (not_acc_iff_exists_descending_chain).2
    ⟨nestedExec, rfl, full_exec_keys_descend⟩
  exact notAccessible (wellFounded.apply (nestedExec 0))

#print axioms every_prefix_regenerates
#print axioms enabled_job_is_starved
#print axioms every_step_has_a_completed_matcher
#print axioms physical_locations_descend
#print axioms full_exec_keys_descend
#print axioms physical_exec_order_not_wellFounded

end Mettapedia.Languages.ProcessCalculi.MORK.MM2QueueFairness
