/-
# Request pacing: per-host spacing of an agent's reads

An agent that reads pages for a task spaces its requests to one host. The
scheduler keeps the time it last served each host; a request asked at time
`asked` to a host last served at `l` is served at the later of `asked` and
`l + gap`, and never before a time the host asked the agent to wait until
(`hold`, as from an HTTP `Retry-After`). Times are milliseconds.

Results:
* `schedule_respects`: no request is served before it was asked, nor before
  the hold.
* `schedule_spaced`: consecutive serving times to one host are at least the
  gap apart.
* `spaced_lower`: in a spaced sequence the `i`-th request after the first is
  served at least `gap * (i + 1)` after it.
* `window_count`: requests served at least a gap apart that all fall within a
  window of length `w` number at most `w / gap + 1`. A 1 s gap therefore keeps
  a host to at most 61 requests a minute; a cap of 30 a minute needs a gap of
  at least 2069 ms.
* `schedule_after_last`: the first request after one served at `l` waits until
  `l + gap`.

The scheduler is the one an agent's page reads run: each read starts at
`serveAt` of its host's last start, which the agent keeps across reads.
Core Lean only.
-/

namespace Mettapedia.Protocols.Web.RequestPacing

/-- The least gap between two requests to one host. -/
structure Policy where
  gap : Nat

/-- When a request asked at `asked` is served, given the host's last serving
time (none for the first) and its hold. -/
def serveAt (p : Policy) (last : Option Nat) (hold : Nat) (asked : Nat) : Nat :=
  match last with
  | none => max asked hold
  | some l => max (max asked (l + p.gap)) hold

/-- Serving the requests to one host in the order they were asked. -/
def schedule (p : Policy) (hold : Nat) : Option Nat → List Nat → List Nat
  | _, [] => []
  | last, a :: rest =>
    let t := serveAt p last hold a
    t :: schedule p hold (some t) rest

theorem serveAt_ge_asked (p : Policy) (last : Option Nat) (hold asked : Nat) :
    asked ≤ serveAt p last hold asked := by
  cases last <;> simp [serveAt] <;> omega

theorem serveAt_ge_hold (p : Policy) (last : Option Nat) (hold asked : Nat) :
    hold ≤ serveAt p last hold asked := by
  cases last <;> simp [serveAt] <;> omega

theorem serveAt_spaced (p : Policy) (l hold asked : Nat) :
    l + p.gap ≤ serveAt p (some l) hold asked := by
  simp [serveAt]; omega

/-- Consecutive elements at least `gap` apart. -/
def Spaced (gap : Nat) : List Nat → Prop
  | [] => True
  | [_] => True
  | x :: y :: rest => x + gap ≤ y ∧ Spaced gap (y :: rest)

theorem schedule_spaced (p : Policy) (hold : Nat) :
    ∀ (last : Option Nat) (asked : List Nat), Spaced p.gap (schedule p hold last asked)
  | _, [] => by simp [schedule, Spaced]
  | last, [a] => by simp [schedule, Spaced]
  | last, a :: b :: rest => by
    have ih := schedule_spaced p hold (some (serveAt p last hold a)) (b :: rest)
    simp only [schedule] at ih ⊢
    exact ⟨serveAt_spaced p _ hold b, ih⟩

/-- Each request served no earlier than it was asked and than the hold. -/
def Respects (hold : Nat) : List Nat → List Nat → Prop
  | [], [] => True
  | a :: as, t :: ts => a ≤ t ∧ hold ≤ t ∧ Respects hold as ts
  | _, _ => False

theorem schedule_respects (p : Policy) (hold : Nat) :
    ∀ (last : Option Nat) (asked : List Nat), Respects hold asked (schedule p hold last asked)
  | _, [] => by simp [schedule, Respects]
  | last, a :: rest => by
    simp only [schedule, Respects]
    exact ⟨serveAt_ge_asked p last hold a, serveAt_ge_hold p last hold a,
      schedule_respects p hold _ rest⟩

theorem schedule_after_last (p : Policy) (hold l a : Nat) (rest : List Nat) :
    ∃ t ts, schedule p hold (some l) (a :: rest) = t :: ts ∧ l + p.gap ≤ t :=
  ⟨_, _, rfl, serveAt_spaced p l hold a⟩

theorem spaced_lower (gap : Nat) :
    ∀ (x : Nat) (xs : List Nat), Spaced gap (x :: xs) →
      ∀ i (h : i < xs.length), x + gap * (i + 1) ≤ xs[i]
  | x, [], _, i, h => by simp at h
  | x, y :: ys, hs, i, h => by
    obtain ⟨hxy, hrest⟩ := hs
    cases i with
    | zero => simp; omega
    | succ j =>
      have hj : j < ys.length := by simp at h; omega
      have hl := spaced_lower gap y ys hrest j hj
      simp only [List.getElem_cons_succ]
      rw [Nat.mul_succ]
      omega

theorem spaced_window (gap w x : Nat) (xs : List Nat) (hs : Spaced gap (x :: xs))
    (hw : ∀ y ∈ xs, y ≤ x + w) : gap * xs.length ≤ w := by
  cases hlen : xs.length with
  | zero => simp
  | succ n =>
    have hn : n < xs.length := by omega
    have hlow := spaced_lower gap x xs hs n hn
    have hhigh := hw _ (List.getElem_mem hn)
    omega

theorem window_count (gap w x : Nat) (xs : List Nat) (hgap : 0 < gap)
    (hs : Spaced gap (x :: xs)) (hw : ∀ y ∈ xs, y ≤ x + w) :
    (x :: xs).length ≤ w / gap + 1 := by
  have h := spaced_window gap w x xs hs hw
  have : xs.length ≤ w / gap :=
    (Nat.le_div_iff_mul_le hgap).2 (by rw [Nat.mul_comm]; exact h)
  simp; omega

/-- A schedule of requests to one host stays within the window bound. -/
theorem schedule_window (p : Policy) (hold : Nat) (last : Option Nat) (asked : List Nat)
    (hgap : 0 < p.gap) (w : Nat) :
    ∀ x xs, schedule p hold last asked = x :: xs → (∀ y ∈ xs, y ≤ x + w) →
      (x :: xs).length ≤ w / p.gap + 1 := by
  intro x xs hsched hw
  have hs := schedule_spaced p hold last asked
  rw [hsched] at hs
  exact window_count p.gap w x xs hgap hs hw

example : schedule ⟨1000⟩ 0 none [0, 10, 20, 5000] = [0, 1000, 2000, 5000] := by decide
example : schedule ⟨1000⟩ 3000 none [0, 10] = [3000, 4000] := by decide
example : schedule ⟨2069⟩ 0 none [0, 0, 0] = [0, 2069, 4138] := by decide

end Mettapedia.Protocols.Web.RequestPacing
