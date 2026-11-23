/-!
# A rollback target keeps the operator's stop, whichever path carries it

The deployment watch rolls a failing candidate back to the previous generation
only if the operator can still pause and resume cognition there: an operator's
/stop and /start must reach the lifecycle, and the loop's turns must wait on
it. Two command paths have carried those commands: the Python client, in older
generations, and the native command responder, which every generation since it
has, and which is the only one once the Python command path is removed.

The earlier fence recognised only the Python path. It refused every generation
whose commands only the responder carries, although its operator can stop and
resume it (`earlier_refuses_responder_only`), so a failed candidate could not
be rolled back to such a generation (`earlier_strands_rollback`).

The fence kept here admits a generation when either path carries both commands
and the loop is gated. It admits only generations where the operator can stop
and resume cognition (`fence_sound`), every gated generation whose responder
carries both (`responder_only_admitted`) and every generation the earlier
fence admitted (`fence_extends_earlier`); a path that gains a command never
loses admission (`fence_monotone`). It stays conservative: commands split
across the two paths are refused (`split_paths_refused`). A fence that skipped
the gate would admit a generation whose stop does not stop cognition
(`ungated_fence_unsound`).

These are protocol-level statements about an abstract generation, not a
refinement proof of the runtime.
-/

set_option autoImplicit false

namespace Mettapedia.Protocols.Agents.RollbackLifecycleAuthority

/-- One command path: whether it takes /start, and /stop, to the lifecycle. -/
structure Path where
  start : Bool
  stop : Bool
  deriving DecidableEq, Repr

/-- The path carries both lifecycle commands. -/
def Path.carries (p : Path) : Bool := p.start && p.stop

/-- `a ≤ b`: every command `a` carries, `b` carries too. -/
def Path.le (a b : Path) : Prop :=
  (a.start = true → b.start = true) ∧ (a.stop = true → b.stop = true)

/-- What a generation's source shows the fence. -/
structure Generation where
  python : Path
  responder : Path
  /-- The loop's turn and wait candidates ask the lifecycle. -/
  gated : Bool
  deriving DecidableEq, Repr

/-- The operator can stop cognition: some path takes /stop to the lifecycle,
and cognition waits on it. -/
def canStop (g : Generation) : Prop :=
  (g.python.stop = true ∨ g.responder.stop = true) ∧ g.gated = true

/-- The operator can resume cognition. -/
def canResume (g : Generation) : Prop :=
  (g.python.start = true ∨ g.responder.start = true) ∧ g.gated = true

/-- The fence kept here. -/
def fence (g : Generation) : Bool :=
  (g.python.carries || g.responder.carries) && g.gated

/-- The earlier fence: the Python path only. -/
def earlier (g : Generation) : Bool := g.python.carries && g.gated

/-- A fence that does not ask whether the loop is gated. -/
def ungated (g : Generation) : Bool := g.python.carries || g.responder.carries

/-- A rollback to `previous` is attempted only when the fence admits it. -/
def rollbackAllowed (f : Generation → Bool) (previous : Generation) : Bool :=
  f previous

theorem fence_sound (g : Generation) (h : fence g = true) :
    canStop g ∧ canResume g := by
  obtain ⟨⟨ps, pt⟩, ⟨rs, rt⟩, gate⟩ := g
  cases ps <;> cases pt <;> cases rs <;> cases rt <;> cases gate <;>
    simp_all [fence, Path.carries, canStop, canResume]

theorem responder_only_admitted (g : Generation)
    (hr : g.responder.carries = true) (hg : g.gated = true) :
    fence g = true := by
  simp [fence, hr, hg]

theorem fence_extends_earlier (g : Generation) (h : earlier g = true) :
    fence g = true := by
  obtain ⟨⟨ps, pt⟩, ⟨rs, rt⟩, gate⟩ := g
  cases ps <;> cases pt <;> cases rs <;> cases rt <;> cases gate <;>
    simp_all [fence, earlier, Path.carries]

theorem fence_monotone (g g' : Generation)
    (hp : g.python.le g'.python) (hr : g.responder.le g'.responder)
    (hg : g.gated = g'.gated) (h : fence g = true) : fence g' = true := by
  obtain ⟨⟨ps, pt⟩, ⟨rs, rt⟩, gate⟩ := g
  obtain ⟨⟨ps', pt'⟩, ⟨rs', rt'⟩, gate'⟩ := g'
  simp only [Path.le] at hp hr
  simp only at hg
  subst hg
  cases ps <;> cases pt <;> cases rs <;> cases rt <;> cases gate <;>
    simp_all [fence, Path.carries]

/-- The generation the engine roll brings: the Python command path is gone and
the responder carries both commands. -/
def rolled : Generation :=
  { python := ⟨false, false⟩, responder := ⟨true, true⟩, gated := true }

/-- The generation before it: both paths carry the commands. -/
def beforeRoll : Generation :=
  { python := ⟨true, true⟩, responder := ⟨true, true⟩, gated := true }

theorem earlier_refuses_responder_only :
    canStop rolled ∧ canResume rolled ∧ earlier rolled = false ∧
      fence rolled = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [canStop, canResume, earlier, fence, rolled, Path.carries]

/-- Once the roll is the previous generation, the earlier fence refuses every
rollback to it; the fence kept here allows it, and still allows the
generation before. -/
theorem earlier_strands_rollback :
    rollbackAllowed earlier rolled = false ∧
      rollbackAllowed fence rolled = true ∧
      rollbackAllowed fence beforeRoll = true := by
  decide

/-- Commands split across the paths: /start only in Python, /stop only in the
responder. -/
def split : Generation :=
  { python := ⟨true, false⟩, responder := ⟨false, true⟩, gated := true }

/-- The operator could stop and resume `split`, but no one path carries both,
and the fence refuses it: conservative, not unsound. -/
theorem split_paths_refused :
    canStop split ∧ canResume split ∧ fence split = false := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [canStop, canResume, fence, split, Path.carries]

theorem ungated_fence_unsound :
    ∃ g : Generation, ungated g = true ∧ ¬ canStop g := by
  refine ⟨{ python := ⟨false, false⟩, responder := ⟨true, true⟩, gated := false }, ?_, ?_⟩
  · decide
  · simp [canStop]

end Mettapedia.Protocols.Agents.RollbackLifecycleAuthority
