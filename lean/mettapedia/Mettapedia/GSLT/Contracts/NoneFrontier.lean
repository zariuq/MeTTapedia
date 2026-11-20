import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert
import Mathlib.Logic.Relation

/-!
# A frontier for none queries in a self-modifying space

The space holds atoms, some of which are executables.  Firing an executable
removes it, may remove other atoms, and adds atoms drawn from its outputs,
which may themselves be executables (`Step`).  This over-approximates every
firing of an MM2 executable: its output sinks instantiate templates, `add`
sinks contribute outputs, `remove` sinks only remove, and the firing
executable consumes itself.

An **none read** of a pattern `P` asks that no atom of the space match `P`.
A **frontier** for `P` is a state in which no pending executable may
eventually produce a match of `P`, directly or through executables it creates
(`MayProduce`, `Frontier`).

* **The none query at a frontier is final** (`noneMatch_frontier_step`,
  `noneMatch_of_reaches`): from a state where `P` is not present at a frontier, every
  reachable state lacks `P` and is again at a frontier.  So an executable
  gated on that none reads the same verdict whenever it fires afterwards.
* **Frontiers are inductive invariants** (`frontier_iff_closedRegion`): `P` is
  not present at a frontier exactly when the space lies inside a region closed
  under outputs that contains no match of `P`.  An implementation can
  therefore check a frontier statically, for example by head symbols of
  output templates, and any closed region it proves is sound.
* **Without a frontier, the none query is a snapshot** (`Controls.snapshot_none_flips`):
  one pending producer turns a none query that held into a presence.
* **The none query as evidence** (`Controls.negative_evidence_unsound_without_frontier`,
  `negative_evidence_sound_at_frontier`): reading a snapshot none queries as
  evidence that `P` will never hold is unsound; at a frontier it is sound.
  In an open world, the none query is no evidence; a frontier closes the world for
  `P`.

**The none query in time** (`no_perfect_detector`, `bounded_delay_detector`): a
missing message is a negative read of the network.  In an asynchronous
network no detector that decides from what it has seen is both complete
(eventually suspects a crashed process) and accurate (never suspects a live
one): a crash and a slow process look the same up to any finite time.  A known
bound on delays is a frontier in time; after it, the none query is final and the
detector is perfect.  This is the elementary core of the impossibility of
perfect failure detection without synchrony (Chandra and Toueg; Fischer, Lynch
and Paterson).

A native none source for MM2 is then: an input conjunct `(none P)`
satisfied when no atom matches `P` and the state is at a frontier for `P`,
with the frontier established by a closed region.  The MM2 kernel results
that none query is not eliminable by replacing inputs, and that a downward stage
decides it in a context without executables, are the special case of a region
that contains no producer at all.  In a concurrent store the verdict carries
its negative footprint, the gap of `Mettapedia.Machines.Cursor.GapObservation`,
which a commit validates.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Contracts.NoneFrontier

universe u v

variable {Atom : Type u} {Pattern : Type v}

/-- A self-modifying space: which atoms are executables, what each may add,
and which atoms fit (match) which patterns. -/
structure SpaceModel (Atom : Type u) (Pattern : Type v) where
  isExec : Atom → Prop
  outputs : Atom → Set Atom
  fits : Pattern → Atom → Prop

variable (model : SpaceModel Atom Pattern)

/-- One firing: an executable of the space is consumed; what remains is drawn
from the rest of the space and the executable's outputs. -/
def Step (space next : Set Atom) : Prop :=
  ∃ exec ∈ space, model.isExec exec ∧ next ⊆ (space \ {exec}) ∪ model.outputs exec

/-- No atom of the space matches `P`. -/
def NoneMatch (pattern : Pattern) (space : Set Atom) : Prop :=
  ∀ atom ∈ space, ¬ model.fits pattern atom

/-- An executable may eventually produce a match of `P`, directly or through an
executable it adds. -/
inductive MayProduce (pattern : Pattern) : Atom → Prop
  | direct {exec atom : Atom} : atom ∈ model.outputs exec → model.fits pattern atom →
      MayProduce pattern exec
  | indirect {exec atom : Atom} : atom ∈ model.outputs exec → model.isExec atom →
      MayProduce pattern atom → MayProduce pattern exec

/-- **A frontier for `P`**: no pending executable may eventually produce a
match of `P`. -/
def Frontier (pattern : Pattern) (space : Set Atom) : Prop :=
  ∀ exec ∈ space, model.isExec exec → ¬ MayProduce model pattern exec

/-- **The none query at a frontier survives a firing.** -/
theorem noneMatch_frontier_step {pattern : Pattern} {space next : Set Atom}
    (missing : NoneMatch model pattern space) (frontier : Frontier model pattern space)
    (step : Step model space next) :
    NoneMatch model pattern next ∧ Frontier model pattern next := by
  obtain ⟨exec, member, isExec, sub⟩ := step
  have quiet := frontier exec member isExec
  constructor
  · intro atom inNext matched
    rcases sub inNext with old | added
    · exact missing atom old.1 matched
    · exact quiet (.direct added matched)
  · intro atom inNext atomExec produces
    rcases sub inNext with old | added
    · exact frontier atom old.1 atomExec produces
    · exact quiet (.indirect added atomExec produces)

/-- **The none query at a frontier is final**: it holds in every reachable state. -/
theorem noneMatch_of_reaches {pattern : Pattern} {space later : Set Atom}
    (missing : NoneMatch model pattern space) (frontier : Frontier model pattern space)
    (reaches : Relation.ReflTransGen (Step model) space later) :
    NoneMatch model pattern later ∧ Frontier model pattern later := by
  induction reaches with
  | refl => exact ⟨missing, frontier⟩
  | tail _ step ih => exact noneMatch_frontier_step model ih.1 ih.2 step

/-- A region closed under outputs. -/
def ClosedRegion (region : Set Atom) : Prop :=
  ∀ exec ∈ region, model.isExec exec → model.outputs exec ⊆ region

/-- **Frontiers are inductive invariants**: none queries at a frontier is exactly
containment in a closed region without matches of `P`. -/
theorem frontier_iff_closedRegion (pattern : Pattern) (space : Set Atom) :
    (NoneMatch model pattern space ∧ Frontier model pattern space) ↔
      ∃ region : Set Atom, space ⊆ region ∧ ClosedRegion model region ∧
        NoneMatch model pattern region := by
  constructor
  · rintro ⟨missing, frontier⟩
    refine ⟨{atom | ¬ model.fits pattern atom ∧
        (model.isExec atom → ¬ MayProduce model pattern atom)}, ?_, ?_, ?_⟩
    · intro atom member
      exact ⟨missing atom member, frontier atom member⟩
    · intro exec inRegion isExec atom output
      refine ⟨fun matched => inRegion.2 isExec (.direct output matched), ?_⟩
      intro atomExec produces
      exact inRegion.2 isExec (.indirect output atomExec produces)
    · intro atom inRegion
      exact inRegion.1
  · rintro ⟨region, sub, closed, noneRegion⟩
    refine ⟨fun atom member => noneRegion atom (sub member), ?_⟩
    have noProducer : ∀ exec, MayProduce model pattern exec → exec ∈ region →
        model.isExec exec → False := by
      intro exec produces
      induction produces with
      | direct output matched =>
          intro inRegion isExec
          exact noneRegion _ (closed _ inRegion isExec output) matched
      | indirect output atomExec _ ih =>
          intro inRegion isExec
          exact ih (closed _ inRegion isExec output) atomExec
    intro exec member isExec produces
    exact noProducer exec produces (sub member) isExec

/-- **Negative evidence is sound at a frontier**: none read there is never
contradicted later. -/
theorem negative_evidence_sound_at_frontier {pattern : Pattern} {space : Set Atom}
    (missing : NoneMatch model pattern space) (frontier : Frontier model pattern space) :
    ∀ later, Relation.ReflTransGen (Step model) space later →
      ∀ atom ∈ later, ¬ model.fits pattern atom :=
  fun _ reaches => (noneMatch_of_reaches model missing frontier reaches).1

/-! ## The none query in time: crashes and delays -/

section Time

/-- An execution: when the first message of the watched process arrives, if
ever.  A crashed process sends none. -/
abbrev Execution := Option ℕ

/-- Whether a message has arrived by time `t`. -/
def seen : Execution → ℕ → Bool
  | none, _ => false
  | some arrival, t => decide (arrival ≤ t)

/-- A failure detector suspects the process at time `t` from what it has seen
up to `t`. -/
structure Detector where
  suspect : (ℕ → Bool) → ℕ → Bool
  causal : ∀ (view view' : ℕ → Bool) (t : ℕ), (∀ s ≤ t, view s = view' s) →
    suspect view t = suspect view' t

/-- Complete: a crashed process is eventually suspected. -/
def Complete (detector : Detector) : Prop := ∃ t, detector.suspect (seen none) t = true

/-- Accurate on the admissible executions: a live process is never suspected. -/
def Accurate (detector : Detector) (admissible : Execution → Prop) : Prop :=
  ∀ arrival, admissible (some arrival) → ∀ t, detector.suspect (seen (some arrival)) t = false

/-- **No perfect detector without a delay bound**: a complete detector
suspects a process whose message is merely late. -/
theorem no_perfect_detector (detector : Detector) (complete : Complete detector) :
    ¬ Accurate detector fun _ => True := by
  obtain ⟨t, suspected⟩ := complete
  intro accurate
  have same : ∀ s ≤ t, seen none s = seen (some (t + 1)) s := by
    intro s le
    simp only [seen]
    exact (decide_eq_false (by omega)).symm
  rw [detector.causal _ _ t same] at suspected
  rw [accurate (t + 1) trivial t] at suspected
  exact Bool.false_ne_true suspected

/-- Suspect once the delay bound has passed with nothing seen. -/
def boundedDelay (bound : ℕ) : Detector where
  suspect view t := decide (bound ≤ t) && !view t
  causal view view' t same := by rw [same t le_rfl]

/-- **A delay bound is a frontier in time**: the bounded-delay detector is
complete and accurate on executions whose messages arrive within the bound. -/
theorem bounded_delay_detector (bound : ℕ) :
    Complete (boundedDelay bound) ∧
      Accurate (boundedDelay bound) fun execution => ∀ arrival, execution = some arrival →
        arrival ≤ bound := by
  constructor
  · exact ⟨bound, by simp [boundedDelay, seen]⟩
  · intro arrival within t
    have := within arrival rfl
    simp only [boundedDelay, seen]
    by_cases late : bound ≤ t
    · simp [late, show arrival ≤ t by omega]
    · simp [late]

end Time

/-! ## Controls -/

namespace Controls

/-- A producer, the atom it adds, and an inert fact. -/
inductive Item
  | producer
  | target
  | fact
  deriving DecidableEq

/-- The producer adds the target; the target matches the pattern. -/
def items : SpaceModel Item Unit where
  isExec atom := atom = .producer
  outputs atom := if atom = .producer then {.target} else ∅
  fits _ atom := atom = .target

/-- The producer fires. -/
theorem fire : Step items {.producer, .fact} {.fact, .target} := by
  refine ⟨.producer, by simp, rfl, ?_⟩
  intro atom member
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at member
  rcases member with rfl | rfl
  · left; simp
  · right; simp [items]

/-- **A snapshot the none query flips**: the pattern is not present before the producer
fires and present after. -/
theorem snapshot_none_flips :
    NoneMatch items () {.producer, .fact} ∧ ¬ NoneMatch items () {.fact, .target} ∧
      ¬ Frontier items () {.producer, .fact} := by
  refine ⟨?_, ?_, ?_⟩
  · intro atom member matched
    simp only [items] at matched
    subst matched
    simp at member
  · intro missing
    exact missing .target (by simp) rfl
  · intro frontier
    exact frontier .producer (by simp) rfl (.direct (by simp [items]) rfl)

/-- **Reading snapshot none queries as negative evidence is unsound**: a reachable
state contradicts it. -/
theorem negative_evidence_unsound_without_frontier :
    NoneMatch items () {.producer, .fact} ∧
      ∃ later, Relation.ReflTransGen (Step items) {.producer, .fact} later ∧
        ∃ atom ∈ later, items.fits () atom :=
  ⟨snapshot_none_flips.1, {.fact, .target}, Relation.ReflTransGen.single fire,
    .target, by simp, rfl⟩

/-- Without the producer the none query is at a frontier. -/
theorem fact_alone_frontier : NoneMatch items () {.fact} ∧ Frontier items () {.fact} := by
  constructor
  · intro atom member matched
    simp only [Set.mem_singleton_iff] at member
    subst member
    cases matched
  · intro exec member isExec
    simp only [Set.mem_singleton_iff] at member
    subst member
    cases isExec

end Controls

end Mettapedia.GSLT.Contracts.NoneFrontier
