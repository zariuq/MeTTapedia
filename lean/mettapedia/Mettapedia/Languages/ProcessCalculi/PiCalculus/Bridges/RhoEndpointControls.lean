import Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointOperational

/-!
# Positive and negative endpoint controls

These networks exercise two independent communications, duplicate messages,
an input continuation with a retained binder, and the distinction between a
one-step variable convention and invariant prefix safety.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.PiCalculus
open Mettapedia.Languages.ProcessCalculi.PiCalculus.ForwardSimulation
open Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpoint

def independent : List Process :=
  [.input "a" "x" (.output "A" "x"), .output "a" "z",
    .input "b" "x" (.output "B" "x"), .output "b" "w"]

def afterFirst : List Process :=
  [.output "A" "z", .input "b" "x" (.output "B" "x"), .output "b" "w"]

def afterBoth : List Process := [.output "B" "w", .output "A" "z"]

theorem independent_variable_invariant : OutputContinuationNetwork "x" independent := by
  intro process membership
  simp only [independent, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl | rfl
  all_goals simp [SendsOnly]

theorem independent_first : NetworkStep independent afterFirst := by
  have selected := NetworkStep.comm (processes := independent) 0 (by decide) 0 (by decide)
    "a" "x" "z" (.output "A" "x") rfl rfl
  simpa [independent, afterFirst, components, Process.substitute_output] using selected

theorem independent_second : NetworkStep afterFirst afterBoth := by
  have selected := NetworkStep.comm (processes := afterFirst) 1 (by decide) 1 (by decide)
    "b" "x" "w" (.output "B" "x") rfl rfl
  simpa [afterFirst, afterBoth, components, Process.substitute_output] using selected

theorem independent_source_path : Relation.ReflTransGen NetworkStep independent afterBoth :=
  (Relation.ReflTransGen.single independent_first).tail independent_second

theorem independent_actual_rho_path (n v : String) :
    Relation.ReflTransGen CanonicalFiring (canonicalNetwork independent n v)
      (canonicalNetwork afterBoth n v) :=
  network_path_preserved independent_source_path independent_variable_invariant.flat
    independent_variable_invariant.reachableSafe n v

/-- Every supplied rho path from this nonempty qualified input has its own
named endpoint, not merely another successful execution. -/
theorem independent_arbitrary_endpoint (n v : String) (target : Pattern) :
    Relation.ReflTransGen CanonicalFiring (canonicalNetwork independent n v) target ↔
      ∃ next, Relation.ReflTransGen NetworkStep independent next ∧ target = canonicalNetwork next n v :=
  canonical_path_iff independent_variable_invariant.flat independent_variable_invariant.reachableSafe n v target

def duplicated : List Process :=
  [.input "c" "x" (.output "x" "x"), .output "c" "z", .output "c" "z"]

def afterDuplicate : List Process := [.output "z" "z", .output "c" "z"]

theorem duplicate_variable_invariant : OutputContinuationNetwork "x" duplicated := by
  intro process membership
  simp only [duplicated, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl | rfl
  all_goals simp [SendsOnly]

theorem duplicate_first_selected : NetworkStep duplicated afterDuplicate := by
  have selected := NetworkStep.comm (processes := duplicated) 0 (by decide) 0 (by decide)
    "c" "x" "z" (.output "x" "x") rfl rfl
  simpa [duplicated, afterDuplicate, components, Process.substitute_output] using selected

theorem duplicate_second_selected : NetworkStep duplicated afterDuplicate := by
  have selected := NetworkStep.comm (processes := duplicated) 0 (by decide) 1 (by decide)
    "c" "x" "z" (.output "x" "x") rfl rfl
  simpa [duplicated, afterDuplicate, components, Process.substitute_output] using selected

theorem duplicate_consumes_one_occurrence :
    duplicated.count (.output "c" "z") = 2 ∧ afterDuplicate.count (.output "c" "z") = 1 := by
  decide +kernel

theorem duplicate_actual_rho_endpoint (n v : String) :
    CanonicalFiring (canonicalNetwork duplicated n v) (canonicalNetwork afterDuplicate n v) :=
  duplicate_second_selected.canonical_firing duplicate_variable_invariant.flat
    duplicate_variable_invariant.safe n v

def guarded : List Process :=
  [.input "c" "x" (.input "d" "w" (.output "x" "w")), .output "c" "z"]

def afterGuarded : List Process := [.input "d" "w" (.output "z" "w")]

theorem guarded_flat : Flat guarded := by
  intro process membership
  simp only [guarded, List.mem_cons, List.not_mem_nil, or_false] at membership
  rcases membership with rfl | rfl
  all_goals simp [Atom, RestrictionFree]

theorem guarded_safe : Safe guarded := by
  intro channel binder datum body input output
  simp only [guarded, List.mem_cons, List.not_mem_nil, or_false] at input output
  rcases input with input | input
  · cases input
    rcases output with output | output
    · cases output
    · cases output
      simp [BarendregtFor]
  · cases input

theorem guarded_selected : NetworkStep guarded afterGuarded := by
  have selected := NetworkStep.comm (processes := guarded) 0 (by decide) 0 (by decide)
    "c" "x" "z" (.input "d" "w" (.output "x" "w")) rfl rfl
  simpa [guarded, afterGuarded, components, Process.substitute, Process.replaceName, Process.freeNames] using selected

theorem retained_binder_actual_rho_endpoint (n v : String) :
    CanonicalFiring (canonicalNetwork guarded n v) (canonicalNetwork afterGuarded n v) :=
  guarded_selected.canonical_firing guarded_flat guarded_safe n v

def initiallySafe : List Process :=
  [.input "a" "x" (.input "b" "w" .nil), .output "a" "z", .output "b" "w"]

def unsafePrefix : List Process := [.input "b" "w" .nil, .output "b" "w"]

theorem initially_safe : Safe initiallySafe := by
  intro channel binder datum body input output
  simp only [initiallySafe, List.mem_cons, List.not_mem_nil, or_false] at input output
  rcases input with input | input | input
  · cases input
    rcases output with output | output | output
    · cases output
    · cases output
      simp [BarendregtFor]
    · simp at output
  · cases input
  · cases input

theorem becomes_unsafe : NetworkStep initiallySafe unsafePrefix := by
  have selected := NetworkStep.comm (processes := initiallySafe) 0 (by decide) 0 (by decide)
    "a" "x" "z" (.input "b" "w" .nil) rfl rfl
  simpa [initiallySafe, unsafePrefix, components, Process.substitute, Process.replaceName,
    Process.freeNames] using selected

theorem unsafe_prefix : ¬ Safe unsafePrefix := by
  intro safe
  have impossible := (safe "b" "w" "w" .nil (by simp [unsafePrefix]) (by simp [unsafePrefix])).1
  exact impossible rfl

theorem initial_safe_does_not_imply_reachable_safe :
    Safe initiallySafe ∧ ¬ ReachableSafe initiallySafe := by
  refine ⟨initially_safe, ?_⟩
  intro invariant
  exact unsafe_prefix (invariant unsafePrefix (Relation.ReflTransGen.single becomes_unsafe))

end Mettapedia.Languages.ProcessCalculi.PiCalculus.Bridges.RhoEndpointControls
