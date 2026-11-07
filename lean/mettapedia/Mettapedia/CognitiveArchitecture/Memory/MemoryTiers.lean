/-!
# Memory tiers: who may write each tier, what enters the prompt, and forgetting

Long-lived agents separate memories by trust. This model takes the tier
discipline of OpenClaw's memory core (`docs/concepts/memory-architecture.md`,
`memory-provenance.md`) and states it as write authority, injection and
provenance laws, so it can be compared with other designs. One example is the
attention-ranked context of a MeTTa agent.

Tiers:
* `instructions`: written by a human only, always injected.
* `curated`: a small core. It is written by a human request, or by
  consolidation through a promotion gate, and injected within a budget.
* `episodic`: the agent's own notes. Injected only when recalled.
* `prospective`: standing intents, set by the owner. Injected only when
  their trigger fires.
* `review`: consolidation reports for humans. Never injected.

Each operation names its writer by its form: `instruct` and `request` are a
human's, `note` the agent's, `promote` and `dream` consolidation's, and
`intend` the owner's. Every curated entry that consolidation writes carries
its provenance, the sessions whose notes support it.

Results:
* The agent alone never changes instructions or the curated core
  (`notes_keep_core`). Nothing crosses from episodic to curated except
  through the gate.
* Every promoted curated entry is supported by at least `threshold`
  distinct sessions. This holds after every operation, forgetting included
  (`run_supported`).
* With `threshold = 2`, one session repeating a note never promotes it, while
  two sessions do (`one_session_never_promotes`, `two_sessions_promote`).
  That is the poisoning boundary.
* A forgotten session stays forgotten: no entry cites it afterwards, and no
  later operation brings it back (`run_forgotten_absent`). Forgetting a
  session drops its notes and every promoted entry whose support falls below
  the gate (`forget_purges`).
* Review entries never reach the prompt, episodic entries arrive only through
  recall, and the injected size is bounded by the tier budgets
  (`view_excludes_review`, `view_length_le`).

**Status: a model of one external design, OpenClaw's, not a theory of memory tiers.**
**What this file is.** It is descriptive mathematics. It neither recommends
nor requires anything of any agent. In godelclaw, agents keep full write
authority over their own memory, prompts, timers and instructions, and
nothing here constrains that. These
choices are that design's, not derived:
- the five tiers and who may write each;
- distinct-session counting as the gate's evidence;
- support snapshotted at promotion;
- the budgets, such as three fired intents.

The theorems check that the design is coherent: its invariants hold under
every operation, forgetting included. Most hold because `apply` enforces
them. They do not show the choices are necessary or optimal.

Three questions would make this theory:
1. Forgetting as counterfactual replay: forgetting a session after a trace
   should equal running that trace without the session's operations. Which
   choices make that hold? Snapshot or live support is one of them.
2. Gate soundness from independent evidence: counting distinct sessions is
   sound only if a writer cannot mint sessions. A PLN-style confidence over
   independent sources would derive the threshold instead of fixing it.
3. Write authority as non-interference: a tier is safe from a class of
   sources exactly when every path from those sources passes a gate.

Outside the model: how recall ranks candidates (see `RecallProvenance` and
the retrieval contract), how triggers match, and whether text identity is
the right notion of "the same memory".
-/

namespace Mettapedia.CognitiveArchitecture.Memory.MemoryTiers

inductive Tier where
  | instructions
  | curated
  | episodic
  | prospective
  | review
  deriving DecidableEq, Repr

structure Entry where
  tier : Tier
  text : Nat
  sources : List Nat
  byHuman : Bool
  deriving DecidableEq, Repr

structure State where
  entries : List Entry
  forgotten : List Nat
  deriving DecidableEq, Repr

inductive Op where
  | instruct (text : Nat)
  | request (text : Nat)
  | note (session text : Nat)
  | promote (text : Nat)
  | intend (text : Nat)
  | dream (text : Nat)
  | forget (session : Nat)
  deriving DecidableEq, Repr

/-- The sessions whose episodic notes say `text`. -/
def support (s : State) (text : Nat) : List Nat :=
  (s.entries.filter (fun e => e.tier == Tier.episodic && e.text == text)).flatMap Entry.sources

def scrub (session : Nat) (e : Entry) : Entry :=
  { e with sources := e.sources.filter (fun x => x != session) }

/-- What survives forgetting: human entries, notes with a remaining source,
promoted entries whose support still passes the gate, and the rest. -/
def keep (threshold : Nat) (e : Entry) : Bool :=
  e.byHuman ||
    match e.tier with
    | .episodic => !e.sources.isEmpty
    | .curated => decide (threshold ≤ e.sources.eraseDups.length)
    | _ => true

def purge (threshold session : Nat) (entries : List Entry) : List Entry :=
  (entries.map (scrub session)).filter (keep threshold)

def apply (threshold : Nat) (s : State) : Op → State
  | .instruct t => { s with entries := ⟨.instructions, t, [], true⟩ :: s.entries }
  | .request t => { s with entries := ⟨.curated, t, [], true⟩ :: s.entries }
  | .note session t =>
      if session ∈ s.forgotten then s
      else { s with entries := ⟨.episodic, t, [session], false⟩ :: s.entries }
  | .promote t =>
      if threshold ≤ (support s t).eraseDups.length then
        { s with entries := ⟨.curated, t, support s t, false⟩ :: s.entries }
      else s
  | .intend t => { s with entries := ⟨.prospective, t, [], true⟩ :: s.entries }
  | .dream t => { s with entries := ⟨.review, t, [], false⟩ :: s.entries }
  | .forget session =>
      { entries := purge threshold session s.entries, forgotten := session :: s.forgotten }

def run (threshold : Nat) (s : State) (ops : List Op) : State :=
  ops.foldl (apply threshold) s

/-! ## The agent alone never changes the core -/

def core (s : State) : List Entry :=
  s.entries.filter (fun e => e.tier == Tier.instructions || e.tier == Tier.curated)

def isNote : Op → Bool
  | .note _ _ => true
  | _ => false

theorem note_keeps_core (threshold : Nat) (s : State) (op : Op) (h : isNote op = true) :
    core (apply threshold s op) = core s := by
  cases op with
  | note session t =>
    by_cases hf : session ∈ s.forgotten
    · simp [apply, hf]
    · simp [apply, hf, core]
  | _ => simp [isNote] at h

theorem notes_keep_core (threshold : Nat) (s : State) (ops : List Op)
    (agent_only : ∀ op ∈ ops, isNote op = true) :
    core (run threshold s ops) = core s := by
  induction ops generalizing s with
  | nil => rfl
  | cons op rest ih =>
    simp only [run, List.foldl_cons]
    have hop : isNote op = true := agent_only op (by simp)
    have hrest : ∀ o ∈ rest, isNote o = true := fun o ho => agent_only o (by simp [ho])
    have := ih (apply threshold s op) hrest
    simp only [run] at this
    rw [this, note_keeps_core threshold s op hop]

/-! ## Promoted entries stay supported -/

def Supported (threshold : Nat) (s : State) : Prop :=
  ∀ e ∈ s.entries, e.tier = Tier.curated → e.byHuman = false →
    threshold ≤ e.sources.eraseDups.length

theorem apply_supported (threshold : Nat) (s : State) (op : Op)
    (h : Supported threshold s) : Supported threshold (apply threshold s op) := by
  intro e he htier hhuman
  cases op with
  | instruct t =>
    simp [apply] at he
    rcases he with rfl | he
    · simp at htier
    · exact h e he htier hhuman
  | request t =>
    simp [apply] at he
    rcases he with rfl | he
    · simp at hhuman
    · exact h e he htier hhuman
  | note session t =>
    by_cases hf : session ∈ s.forgotten
    · simp [apply, hf] at he; exact h e he htier hhuman
    · simp [apply, hf] at he
      rcases he with rfl | he
      · simp at htier
      · exact h e he htier hhuman
  | promote t =>
    by_cases hg : threshold ≤ (support s t).eraseDups.length
    · simp [apply, hg] at he
      rcases he with rfl | he
      · exact hg
      · exact h e he htier hhuman
    · simp [apply, hg] at he; exact h e he htier hhuman
  | intend t =>
    simp [apply] at he
    rcases he with rfl | he
    · simp at htier
    · exact h e he htier hhuman
  | dream t =>
    simp [apply] at he
    rcases he with rfl | he
    · simp at htier
    · exact h e he htier hhuman
  | forget session =>
    simp only [apply, purge, List.mem_filter, List.mem_map] at he
    obtain ⟨_, hkeep⟩ := he
    simp [keep, htier, hhuman] at hkeep
    exact hkeep

theorem run_supported (threshold : Nat) (s : State) (ops : List Op)
    (h : Supported threshold s) : Supported threshold (run threshold s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih _ (apply_supported threshold s op h)

/-! ## A forgotten session stays forgotten -/

def ForgottenAbsent (s : State) : Prop :=
  ∀ f ∈ s.forgotten, ∀ e ∈ s.entries, f ∉ e.sources

theorem mem_support {s : State} {t x : Nat} (hx : x ∈ support s t) :
    ∃ e ∈ s.entries, x ∈ e.sources := by
  simp only [support, List.mem_flatMap, List.mem_filter] at hx
  obtain ⟨e, ⟨he, _⟩, hxe⟩ := hx
  exact ⟨e, he, hxe⟩

theorem apply_forgotten_absent (threshold : Nat) (s : State) (op : Op)
    (h : ForgottenAbsent s) : ForgottenAbsent (apply threshold s op) := by
  intro f hf e he
  cases op with
  | instruct t =>
    simp [apply] at hf he
    rcases he with rfl | he
    · simp
    · exact h f hf e he
  | request t =>
    simp [apply] at hf he
    rcases he with rfl | he
    · simp
    · exact h f hf e he
  | note session t =>
    by_cases hs : session ∈ s.forgotten
    · simp [apply, hs] at hf he; exact h f hf e he
    · simp [apply, hs] at hf he
      rcases he with rfl | he
      · intro hmem
        simp at hmem
        subst hmem
        exact hs hf
      · exact h f hf e he
  | promote t =>
    by_cases hg : threshold ≤ (support s t).eraseDups.length
    · simp [apply, hg] at hf he
      rcases he with rfl | he
      · intro hmem
        obtain ⟨e', he', hx⟩ := mem_support hmem
        exact h f hf e' he' hx
      · exact h f hf e he
    · simp [apply, hg] at hf he; exact h f hf e he
  | intend t =>
    simp [apply] at hf he
    rcases he with rfl | he
    · simp
    · exact h f hf e he
  | dream t =>
    simp [apply] at hf he
    rcases he with rfl | he
    · simp
    · exact h f hf e he
  | forget session =>
    simp only [apply, purge, List.mem_filter, List.mem_map, List.mem_cons] at hf he
    obtain ⟨⟨e₀, he₀, rfl⟩, _⟩ := he
    intro hmem
    simp only [scrub, List.mem_filter] at hmem
    obtain ⟨hmem₀, hne⟩ := hmem
    rcases hf with rfl | hf
    · simp at hne
    · exact h f hf e₀ he₀ hmem₀

theorem run_forgotten_absent (threshold : Nat) (s : State) (ops : List Op)
    (h : ForgottenAbsent s) : ForgottenAbsent (run threshold s ops) := by
  induction ops generalizing s with
  | nil => exact h
  | cons op rest ih => exact ih _ (apply_forgotten_absent threshold s op h)

/-- Forgetting a session leaves no entry citing it, and no promoted entry
below the gate. -/
theorem forget_purges (threshold session : Nat) (s : State) :
    ∀ e ∈ (apply threshold s (.forget session)).entries,
      session ∉ e.sources ∧
      (e.tier = Tier.curated → e.byHuman = false → threshold ≤ e.sources.eraseDups.length) := by
  intro e he
  simp only [apply, purge, List.mem_filter, List.mem_map] at he
  obtain ⟨⟨e₀, _, rfl⟩, hkeep⟩ := he
  refine ⟨?_, ?_⟩
  · simp [scrub]
  · intro htier hhuman
    simp [keep, htier, hhuman] at hkeep
    exact hkeep

/-! ## The poisoning boundary, concretely -/

def empty : State := ⟨[], []⟩

/-- One session repeating a note three times never passes a gate of two. -/
theorem one_session_never_promotes :
    run 2 empty [.note 7 1, .note 7 1, .note 7 1, .promote 1] =
      run 2 empty [.note 7 1, .note 7 1, .note 7 1] := by
  decide

/-- Two sessions saying the same thing do. -/
theorem two_sessions_promote :
    (run 2 empty [.note 7 1, .note 8 1, .promote 1]).entries.head? =
      some ⟨.curated, 1, [8, 7], false⟩ := by
  decide

/-! ## What enters the prompt -/

/-- The injected view: all instructions, the curated core within `budget`,
at most `k` recalled episodic entries, at most three fired intents. -/
def view (s : State) (budget k : Nat) (recalled fired : List Entry) : List Entry :=
  s.entries.filter (fun e => e.tier == Tier.instructions) ++
    (s.entries.filter (fun e => e.tier == Tier.curated)).take budget ++
    (recalled.filter (fun e => e.tier == Tier.episodic)).take k ++
    (fired.filter (fun e => e.tier == Tier.prospective)).take 3

theorem view_excludes_review (s : State) (budget k : Nat) (recalled fired : List Entry) :
    ∀ e ∈ view s budget k recalled fired, e.tier ≠ Tier.review := by
  intro e he
  simp only [view, List.mem_append] at he
  rcases he with ((he | he) | he) | he
  · simp only [List.mem_filter] at he
    intro h; simp [h] at he
  · have := List.mem_of_mem_take he
    simp only [List.mem_filter] at this
    intro h; simp [h] at this
  · have := List.mem_of_mem_take he
    simp only [List.mem_filter] at this
    intro h; simp [h] at this
  · have := List.mem_of_mem_take he
    simp only [List.mem_filter] at this
    intro h; simp [h] at this

theorem view_length_le (s : State) (budget k : Nat) (recalled fired : List Entry) :
    (view s budget k recalled fired).length ≤
      (s.entries.filter (fun e => e.tier == Tier.instructions)).length + budget + k + 3 := by
  simp only [view, List.length_append, List.length_take]
  have h1 := Nat.min_le_left budget (s.entries.filter (fun e => e.tier == Tier.curated)).length
  have h2 := Nat.min_le_left k (recalled.filter (fun e => e.tier == Tier.episodic)).length
  have h3 := Nat.min_le_left 3 (fired.filter (fun e => e.tier == Tier.prospective)).length
  omega

#print axioms notes_keep_core
#print axioms run_supported
#print axioms run_forgotten_absent
#print axioms forget_purges
#print axioms one_session_never_promotes
#print axioms two_sessions_promote
#print axioms view_excludes_review
#print axioms view_length_le

end Mettapedia.CognitiveArchitecture.Memory.MemoryTiers
