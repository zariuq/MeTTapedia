/-!
# Network startup across PCI preflight deferral

The held device view has already been prepared. Each service turn observes a
command result. Preflight deferral leaves the phase and its effects intact.
Commands that settle successfully advance from checking the boot command, to
preparing DMA, to enabling the rings. The native adapter checks the returned
command bits and carries out each phase's hardware work.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.Kernel.NetworkStartup

inductive Phase where
  | query | memory | dma | ready | failed
  deriving DecidableEq, Repr

inductive Observation where
  | deferred | confirmed | terminal
  deriving DecidableEq, Repr

inductive Effect where
  | prepareDma | enableRings
  deriving DecidableEq, Repr

def step (phase : Phase) : Observation → Phase × List Effect
  | .deferred => (phase, [])
  | .terminal =>
      match phase with
      | .ready | .failed => (phase, [])
      | _ => (.failed, [])
  | .confirmed =>
      match phase with
      | .query => (.memory, [])
      | .memory => (.dma, [.prepareDma])
      | .dma => (.ready, [.enableRings])
      | .ready | .failed => (phase, [])

def run (phase : Phase) : List Observation → Phase × List Effect
  | [] => (phase, [])
  | observation :: rest =>
      let (next, effects) := step phase observation
      let (last, remaining) := run next rest
      (last, effects ++ remaining)

def settled : Observation → Bool
  | .deferred => false
  | .confirmed | .terminal => true

theorem remove_deferrals (phase : Phase) (trace : List Observation) :
    run phase (trace.filter settled) = run phase trace := by
  induction trace generalizing phase with
  | nil => rfl
  | cons observation rest ih =>
      cases observation <;> cases phase <;> simp [List.filter_cons, run, settled, step, ih]

theorem ready_absorbs_observations (trace : List Observation) :
    run .ready trace = (.ready, []) := by
  induction trace with
  | nil => rfl
  | cons observation rest ih => cases observation <;> simp [run, step, ih]

theorem accepted_startup_executes_each_phase_once (trace : List Observation)
    (completed : trace.filter settled = [.confirmed, .confirmed, .confirmed]) :
    run .query trace = (.ready, [.prepareDma, .enableRings]) := by
  rw [← remove_deferrals .query trace, completed]
  rfl

example : run .dma [.deferred, .deferred, .confirmed, .confirmed] =
    (.ready, [.enableRings]) := by decide

example : run .memory [.deferred, .terminal, .confirmed] = (.failed, []) := by decide

#print axioms remove_deferrals
#print axioms accepted_startup_executes_each_phase_once

end Mettapedia.Machines.Kernel.NetworkStartup
