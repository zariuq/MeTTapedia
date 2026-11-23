import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Logic.Relation

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# Grace periods through pinned generations

Safe memory reclamation in the form that epoch-based reclamation, RCU and
generation-based clause garbage collection share: an object is reclaimed only
after a *grace period* in which no reader can still reach it.

Objects live from a birth generation until the generation at which they are
erased.  Readers *pin* generations; a reader may hold an object only if it
found the object visible at one of its pins.  A collector run takes the
current generation as its start, marks the pins of every reader, and frees
the objects that are invisible from the start on and at every marked pin.
An object may be a container that leads to other objects, such as an index:
a reader that walks it holds the container as well as what it finds there.

* `Step` is the protocol.  A reader adds a pin at the current generation
  (`pin`), and may replace its pins by a subset of them (`repin`) only while
  every object it holds stays visible at a remaining pin.  The collector
  marks a reader's pins in one step (`scan`): it reads them atomically with
  respect to the reader's own pin updates.
* `inv_step`, `safe_of_reach`: no reachable state has a reader holding a
  freed object, for every interleaving of readers, writers and collector.
* Three counterexamples show that each condition is needed:
  - `unpinned_view_unsafe`: a reader reads at a generation it has not
    pinned;
  - `unchecked_repin_unsafe`: a reader moves its pin to the current
    generation while it still holds an object only the old pin protects;
  - `slotwise_scan_unsafe`: the collector reads a reader's pins one at a
    time, and the reader moves a pin between two of these reads, even though
    each reader step keeps everything it holds covered.

Address reuse, liveness of the collector and weak-memory orderings are
outside this model: every step is atomic and sequentially consistent.  A
system implements the scan assumption with a lock (or an equivalent
handshake) that the collector holds while it reads one reader's pins.

Reference: Gotsman, Rinetzky and Yang, "Verifying concurrent memory
reclamation algorithms with grace" (ESOP 2013), identify the grace period as
the pattern that hazard pointers, RCU and epoch-based reclamation share, and
verify such algorithms with it.
-/

namespace Mettapedia.Machines.GracePeriodPins

/-- An object exists from generation `born` on, up to but excluding `died`
once it is erased. -/
structure Life where
  born : ℕ
  died : Option ℕ

/-- The object exists at generation `g`. -/
def Life.Visible (l : Life) (g : ℕ) : Prop :=
  l.born ≤ g ∧ ∀ d, l.died = some d → g < d

/-- An object erased at the next generation is still visible at every
generation up to the current one. -/
theorem Life.visible_erase {l : Life} {g n : ℕ}
    (hv : l.Visible g) (hg : g ≤ n) : (Life.mk l.born (some (n + 1))).Visible g := by
  refine ⟨hv.1, ?_⟩
  intro d hd
  simp only [Option.some.injEq] at hd
  omega

/-- A collector between runs, or during a run with its start generation, the
generations it marked so far and the readers it scanned. -/
inductive Phase (R : Type) where
  | idle
  | running (start : ℕ) (marks : Set ℕ) (scanned : Set R)

structure St (R O : Type) where
  gen : ℕ
  life : O → Life
  freed : Set O
  pins : R → List ℕ
  held : R → List O
  phase : Phase R

variable {R O : Type} [DecidableEq R] [DecidableEq O]

/-- Invisible from the run's start on, and at every marked generation. -/
def Garbage (s : St R O) (start : ℕ) (marks : Set ℕ) (o : O) : Prop :=
  (∃ d, (s.life o).died = some d ∧ d ≤ start) ∧ ∀ m ∈ marks, ¬ (s.life o).Visible m

/-- The reclamation protocol. -/
inductive Step : St R O → St R O → Prop where
  /-- A writer adds an object: generations advance. -/
  | tick (s : St R O) : Step s { s with gen := s.gen + 1 }
  /-- A writer erases a live object at the next generation. -/
  | erase (s : St R O) (o : O) (h : (s.life o).died = none) :
      Step s { s with gen := s.gen + 1,
                      life := Function.update s.life o ⟨(s.life o).born, some (s.gen + 1)⟩ }
  /-- A reader pins the current generation. -/
  | pin (s : St R O) (r : R) :
      Step s { s with pins := Function.update s.pins r (s.pins r ++ [s.gen]) }
  /-- A reader keeps a subset of its pins that still covers what it holds. -/
  | repin (s : St R O) (r : R) (ps : List ℕ)
      (hsub : ∀ p ∈ ps, p ∈ s.pins r)
      (hcov : ∀ o ∈ s.held r, ∃ p ∈ ps, (s.life o).Visible p) :
      Step s { s with pins := Function.update s.pins r ps }
  /-- A reader takes an unfreed object visible at one of its pins. -/
  | acquire (s : St R O) (r : R) (o : O) (hfree : o ∉ s.freed)
      (hvis : ∃ p ∈ s.pins r, (s.life o).Visible p) :
      Step s { s with held := Function.update s.held r (o :: s.held r) }
  /-- A reader lets go of an object. -/
  | release (s : St R O) (r : R) (o : O) :
      Step s { s with held := Function.update s.held r ((s.held r).erase o) }
  /-- A collector run starts at the current generation. -/
  | start (s : St R O) (h : s.phase = .idle) :
      Step s { s with phase := .running s.gen ∅ ∅ }
  /-- The collector marks all pins of one reader in one step. -/
  | scan (s : St R O) (r : R) (S : ℕ) (M : Set ℕ) (Sc : Set R)
      (h : s.phase = .running S M Sc) :
      Step s { s with phase := .running S (M ∪ {p | p ∈ s.pins r}) (insert r Sc) }
  /-- Once every reader is scanned, the garbage is freed. -/
  | finish (s : St R O) (S : ℕ) (M : Set ℕ) (Sc : Set R)
      (h : s.phase = .running S M Sc) (hall : ∀ r, r ∈ Sc) :
      Step s { s with freed := s.freed ∪ {o | Garbage s S M o}, phase := .idle }

/-- The invariant: pins are not in the future, every held object is visible
at a pin of its reader and unfreed, and a running collector has marked, for
each reader it scanned, every pin older than its start. -/
structure Inv (s : St R O) : Prop where
  pins_le : ∀ r p, p ∈ s.pins r → p ≤ s.gen
  covered : ∀ r o, o ∈ s.held r → ∃ p ∈ s.pins r, (s.life o).Visible p
  safe : ∀ r o, o ∈ s.held r → o ∉ s.freed
  running : ∀ S M Sc, s.phase = .running S M Sc →
    S ≤ s.gen ∧ ∀ r ∈ Sc, ∀ p ∈ s.pins r, p ∈ M ∨ S ≤ p

theorem inv_step {s t : St R O} (hs : Inv s) (h : Step s t) : Inv t := by
  cases h with
  | tick =>
    refine ⟨fun r p hp => Nat.le_succ_of_le (hs.pins_le r p hp), hs.covered, hs.safe, ?_⟩
    intro S M Sc hph
    obtain ⟨hle, hsc⟩ := hs.running S M Sc hph
    exact ⟨Nat.le_succ_of_le hle, hsc⟩
  | erase o _ =>
    refine ⟨fun r p hp => Nat.le_succ_of_le (hs.pins_le r p hp), ?_, hs.safe, ?_⟩
    · intro r o' ho'
      obtain ⟨p, hp, hv⟩ := hs.covered r o' ho'
      refine ⟨p, hp, ?_⟩
      by_cases he : o' = o
      · subst he
        simp only [Function.update_self]
        exact Life.visible_erase hv (hs.pins_le r p hp)
      · simpa only [Function.update_of_ne he] using hv
    · intro S M Sc hph
      obtain ⟨hle, hsc⟩ := hs.running S M Sc hph
      exact ⟨Nat.le_succ_of_le hle, hsc⟩
  | pin r =>
    refine ⟨?_, ?_, hs.safe, ?_⟩
    · intro r' p hp
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hs.pins_le r' p hp
        · exact le_rfl
      · simp only [Function.update_of_ne he] at hp
        exact hs.pins_le r' p hp
    · intro r' o ho
      obtain ⟨p, hp, hv⟩ := hs.covered r' o ho
      refine ⟨p, ?_, hv⟩
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self, List.mem_append]
        exact Or.inl hp
      · simpa only [Function.update_of_ne he] using hp
    · intro S M Sc hph
      obtain ⟨hle, hsc⟩ := hs.running S M Sc hph
      refine ⟨hle, ?_⟩
      intro r' hr' p hp
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self, List.mem_append, List.mem_singleton] at hp
        rcases hp with hp | rfl
        · exact hsc r' hr' p hp
        · exact Or.inr hle
      · simp only [Function.update_of_ne he] at hp
        exact hsc r' hr' p hp
  | repin r ps hsub hcov =>
    refine ⟨?_, ?_, hs.safe, ?_⟩
    · intro r' p hp
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self] at hp
        exact hs.pins_le r' p (hsub p hp)
      · simp only [Function.update_of_ne he] at hp
        exact hs.pins_le r' p hp
    · intro r' o ho
      by_cases he : r' = r
      · subst he
        simpa only [Function.update_self] using hcov o ho
      · simpa only [Function.update_of_ne he] using hs.covered r' o ho
    · intro S M Sc hph
      obtain ⟨hle, hsc⟩ := hs.running S M Sc hph
      refine ⟨hle, ?_⟩
      intro r' hr' p hp
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self] at hp
        exact hsc r' hr' p (hsub p hp)
      · simp only [Function.update_of_ne he] at hp
        exact hsc r' hr' p hp
  | acquire r o hfree hvis =>
    refine ⟨hs.pins_le, ?_, ?_, hs.running⟩
    · intro r' o' ho'
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self, List.mem_cons] at ho'
        rcases ho' with rfl | ho'
        · exact hvis
        · exact hs.covered r' o' ho'
      · simp only [Function.update_of_ne he] at ho'
        exact hs.covered r' o' ho'
    · intro r' o' ho'
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self, List.mem_cons] at ho'
        rcases ho' with rfl | ho'
        · exact hfree
        · exact hs.safe r' o' ho'
      · simp only [Function.update_of_ne he] at ho'
        exact hs.safe r' o' ho'
  | release r o =>
    refine ⟨hs.pins_le, ?_, ?_, hs.running⟩
    · intro r' o' ho'
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self] at ho'
        exact hs.covered r' o' (List.mem_of_mem_erase ho')
      · simp only [Function.update_of_ne he] at ho'
        exact hs.covered r' o' ho'
    · intro r' o' ho'
      by_cases he : r' = r
      · subst he
        simp only [Function.update_self] at ho'
        exact hs.safe r' o' (List.mem_of_mem_erase ho')
      · simp only [Function.update_of_ne he] at ho'
        exact hs.safe r' o' ho'
  | start h =>
    refine ⟨hs.pins_le, hs.covered, hs.safe, ?_⟩
    intro S M Sc hph
    simp only [Phase.running.injEq] at hph
    obtain ⟨rfl, rfl, rfl⟩ := hph
    exact ⟨le_rfl, fun r hr => absurd hr (Set.notMem_empty r)⟩
  | scan r S M Sc h =>
    refine ⟨hs.pins_le, hs.covered, hs.safe, ?_⟩
    intro S' M' Sc' hph
    simp only [Phase.running.injEq] at hph
    obtain ⟨rfl, rfl, rfl⟩ := hph
    obtain ⟨hle, hsc⟩ := hs.running S M Sc h
    refine ⟨hle, ?_⟩
    intro r' hr' p hp
    rcases hr' with rfl | hr'
    · exact Or.inl (Or.inr hp)
    · rcases hsc r' hr' p hp with hm | hS
      · exact Or.inl (Or.inl hm)
      · exact Or.inr hS
  | finish S M Sc h hall =>
    refine ⟨hs.pins_le, hs.covered, ?_, ?_⟩
    · intro r o ho hfr
      rcases hfr with hfr | ⟨⟨d, hd, hdS⟩, hinv⟩
      · exact hs.safe r o ho hfr
      · obtain ⟨p, hp, hv⟩ := hs.covered r o ho
        obtain ⟨_, hsc⟩ := hs.running S M Sc h
        rcases hsc r (hall r) p hp with hm | hS
        · exact hinv p hm hv
        · have := hv.2 d hd
          omega
    · intro S' M' Sc' hph
      cases hph

/-- Reachability under the protocol. -/
abbrev Reach : St R O → St R O → Prop := Relation.ReflTransGen Step

theorem inv_of_reach {s t : St R O} (hs : Inv s) (h : Reach s t) : Inv t := by
  induction h with
  | refl => exact hs
  | tail _ hst ih => exact inv_step ih hst

/-- Safety: from a state satisfying the invariant, no reader ever holds a
freed object. -/
theorem safe_of_reach {s t : St R O} (hs : Inv s) (h : Reach s t) :
    ∀ r o, o ∈ t.held r → o ∉ t.freed :=
  (inv_of_reach hs h).safe

/-- A state with no holdings and an idle collector satisfies the invariant
when its pins are not in the future. -/
theorem inv_init (s : St R O) (hpins : ∀ r p, p ∈ s.pins r → p ≤ s.gen)
    (hheld : ∀ r, s.held r = []) (hidle : s.phase = .idle) : Inv s := by
  refine ⟨hpins, ?_, ?_, ?_⟩
  · intro r o ho
    simp [hheld r] at ho
  · intro r o ho
    simp [hheld r] at ho
  · intro S M Sc hph
    rw [hidle] at hph
    cases hph

/-! ## Each condition is needed

The counterexamples use one reader and two objects.  `false` is an object
born at generation `0`; `true` is born at generation `1`, after the reader
pinned generation `0`. -/

section Counterexamples

/-- The protocol with extra steps. -/
inductive StepWith {R O : Type} [DecidableEq R] [DecidableEq O]
    (extra : St R O → St R O → Prop) : St R O → St R O → Prop where
  | base {s t : St R O} : Step s t → StepWith extra s t
  | extra {s t : St R O} : extra s t → StepWith extra s t

/-- One reader, two objects. -/
def mk (gen : ℕ) (life : Bool → Life) (freed : Set Bool) (pins : List ℕ) (held : List Bool)
    (phase : Phase Unit) : St Unit Bool :=
  ⟨gen, life, freed, fun _ => pins, fun _ => held, phase⟩

theorem update_unit {β : Type} (f : Unit → β) (v : β) : Function.update f () v = fun _ => v := by
  funext x
  cases x
  simp

theorem step_to {s t t' : St Unit Bool} (h : Step s t) (e : t = t') : Step s t' := e ▸ h

theorem all_unit (r : Unit) : r ∈ (insert () ∅ : Set Unit) := by
  cases r
  exact Or.inl rfl

/-- `false` is born at generation `0`, `true` at generation `1`. -/
def lives : Bool → Life := fun o => if o then ⟨1, none⟩ else ⟨0, none⟩

theorem inv_start (pins : List ℕ) (g : ℕ) (h : ∀ p ∈ pins, p ≤ g) :
    Inv (mk g lives ∅ pins [] .idle) :=
  inv_init _ (fun _ p hp => h p hp) (fun _ => rfl) rfl

/-- Reading at a generation the reader has not pinned, as a frame whose
generation is refreshed without moving the pin. -/
def UnpinnedAcquire (s t : St Unit Bool) : Prop :=
  ∃ r o g, g ≤ s.gen ∧ o ∉ s.freed ∧ (s.life o).Visible g ∧
    t = { s with held := Function.update s.held r (o :: s.held r) }

/-- The reader pins generation `0` and reads `true` at generation `1`; a writer
erases it; a collector run marks only the pin `0` and frees it while the
reader holds it. -/
theorem unpinned_view_unsafe :
    Inv (mk 0 lives ∅ [0] [] .idle) ∧
    ∃ t, Relation.ReflTransGen (StepWith UnpinnedAcquire) (mk 0 lives ∅ [0] [] .idle) t ∧
      true ∈ t.held () ∧ true ∈ t.freed := by
  refine ⟨inv_start [0] 0 (by simp), ?_⟩
  let erased : Bool → Life := Function.update lives true ⟨1, some 2⟩
  let s5 := mk 3 erased ∅ [0] [true] (.running 3 ∅ ∅)
  let M : Set ℕ := ∅ ∪ {p | p ∈ s5.pins ()}
  have h1 : StepWith UnpinnedAcquire (mk 0 lives ∅ [0] [] .idle) (mk 1 lives ∅ [0] [] .idle) :=
    .base (Step.tick _)
  have h2 : StepWith UnpinnedAcquire (mk 1 lives ∅ [0] [] .idle) (mk 1 lives ∅ [0] [true] .idle) :=
    .extra ⟨(), true, 1, le_rfl, by simp [mk],
      ⟨by simp [mk, lives], fun d hd => by simp [mk, lives] at hd⟩,
      by simp [mk, update_unit]⟩
  have h3 : StepWith UnpinnedAcquire (mk 1 lives ∅ [0] [true] .idle) (mk 2 erased ∅ [0] [true] .idle) :=
    .base (step_to (Step.erase _ true (by simp [mk, lives])) (by simp [mk, erased, lives]))
  have h4 : StepWith UnpinnedAcquire (mk 2 erased ∅ [0] [true] .idle) (mk 3 erased ∅ [0] [true] .idle) :=
    .base (Step.tick _)
  have h5 : StepWith UnpinnedAcquire (mk 3 erased ∅ [0] [true] .idle) s5 :=
    .base (Step.start _ rfl)
  have h6 := StepWith.base (extra := UnpinnedAcquire) (Step.scan s5 () 3 ∅ ∅ rfl)
  have h7 := StepWith.base (extra := UnpinnedAcquire)
    (Step.finish { s5 with phase := .running 3 M (insert () ∅) } 3 M (insert () ∅) rfl all_unit)
  refine ⟨_, .tail (.tail (.tail (.tail (.tail (.tail (.single h1) h2) h3) h4) h5) h6) h7, ?_, ?_⟩
  · simp [s5, mk]
  · refine Or.inr ⟨⟨2, by simp [s5, mk, erased], by omega⟩, ?_⟩
    intro m hm hv
    simp [M, s5, mk] at hm
    subst hm
    simp [Life.Visible, s5, mk, erased] at hv

/-- Moving the pin in place to the current generation, without checking what
the reader still holds. -/
def UncheckedRepin (s t : St Unit Bool) : Prop :=
  ∃ r, t = { s with pins := Function.update s.pins r [s.gen] }

/-- The reader holds `false`, found at its pin `0`; a writer erases it; the
reader moves its pin to the current generation, where `false` is invisible;
a collector run frees it while the reader holds it. -/
theorem unchecked_repin_unsafe :
    Inv (mk 0 lives ∅ [0] [] .idle) ∧
    ∃ t, Relation.ReflTransGen (StepWith UncheckedRepin) (mk 0 lives ∅ [0] [] .idle) t ∧
      false ∈ t.held () ∧ false ∈ t.freed := by
  refine ⟨inv_start [0] 0 (by simp), ?_⟩
  let erased : Bool → Life := Function.update lives false ⟨0, some 1⟩
  let s5 := mk 2 erased ∅ [1] [false] (.running 2 ∅ ∅)
  let M : Set ℕ := ∅ ∪ {p | p ∈ s5.pins ()}
  have h1 : StepWith UncheckedRepin (mk 0 lives ∅ [0] [] .idle) (mk 0 lives ∅ [0] [false] .idle) :=
    .base (step_to (Step.acquire _ () false (by simp [mk])
      ⟨0, by simp [mk], by simp [mk, lives], fun d hd => by simp [mk, lives] at hd⟩)
      (by simp [mk, update_unit]))
  have h2 : StepWith UncheckedRepin (mk 0 lives ∅ [0] [false] .idle)
      (mk 1 erased ∅ [0] [false] .idle) :=
    .base (step_to (Step.erase _ false (by simp [mk, lives])) (by simp [mk, erased, lives]))
  have h3 : StepWith UncheckedRepin (mk 1 erased ∅ [0] [false] .idle)
      (mk 1 erased ∅ [1] [false] .idle) :=
    .extra ⟨(), by simp [mk, update_unit]⟩
  have h4 : StepWith UncheckedRepin (mk 1 erased ∅ [1] [false] .idle)
      (mk 2 erased ∅ [1] [false] .idle) :=
    .base (Step.tick _)
  have h5 : StepWith UncheckedRepin (mk 2 erased ∅ [1] [false] .idle) s5 :=
    .base (Step.start _ rfl)
  have h6 := StepWith.base (extra := UncheckedRepin) (Step.scan s5 () 2 ∅ ∅ rfl)
  have h7 := StepWith.base (extra := UncheckedRepin)
    (Step.finish { s5 with phase := .running 2 M (insert () ∅) } 2 M (insert () ∅) rfl all_unit)
  refine ⟨_, .tail (.tail (.tail (.tail (.tail (.tail (.single h1) h2) h3) h4) h5) h6) h7, ?_, ?_⟩
  · simp [s5, mk]
  · refine Or.inr ⟨⟨1, by simp [s5, mk, erased], by omega⟩, ?_⟩
    intro m hm hv
    simp [M, s5, mk] at hm
    subst hm
    simp [Life.Visible, s5, mk, erased] at hv

/-- A collector that reads one reader's pins in two steps: the first pin, and
later the others. -/
def SlotwiseScan (s t : St Unit Bool) : Prop :=
  (∃ r S M Sc p ps, s.phase = .running S M Sc ∧ s.pins r = p :: ps ∧
    t = { s with phase := .running S (M ∪ {p}) Sc }) ∨
  (∃ r S M Sc, s.phase = .running S M Sc ∧
    t = { s with phase := .running S (M ∪ {q | q ∈ (s.pins r).tail}) (insert r Sc) })

/-- The reader pins `0`, pins `1` and holds `true`, found at `1`; a writer
erases it.  The collector reads the first pin, `0`.  The reader then keeps
only its pin `1`, which still covers `true`: a protocol step.  The collector
reads the remaining pins, of which there are none, and frees `true`. -/
theorem slotwise_scan_unsafe :
    Inv (mk 0 lives ∅ [0] [] .idle) ∧
    ∃ t, Relation.ReflTransGen (StepWith SlotwiseScan) (mk 0 lives ∅ [0] [] .idle) t ∧
      true ∈ t.held () ∧ true ∈ t.freed := by
  refine ⟨inv_start [0] 0 (by simp), ?_⟩
  let erased : Bool → Life := Function.update lives true ⟨1, some 2⟩
  let s9 := mk 3 erased ∅ [1] [true] (.running 3 (∅ ∪ {0} ∪ {q | q ∈ ([1] : List ℕ).tail}) (insert () ∅))
  have h1 : StepWith SlotwiseScan (mk 0 lives ∅ [0] [] .idle) (mk 1 lives ∅ [0] [] .idle) :=
    .base (Step.tick _)
  have h2 : StepWith SlotwiseScan (mk 1 lives ∅ [0] [] .idle) (mk 1 lives ∅ [0, 1] [] .idle) :=
    .base (step_to (Step.pin _ ()) (by simp [mk, update_unit]))
  have h3 : StepWith SlotwiseScan (mk 1 lives ∅ [0, 1] [] .idle) (mk 1 lives ∅ [0, 1] [true] .idle) :=
    .base (step_to (Step.acquire _ () true (by simp [mk])
      ⟨1, by simp [mk], by simp [mk, lives], fun d hd => by simp [mk, lives] at hd⟩)
      (by simp [mk, update_unit]))
  have h4 : StepWith SlotwiseScan (mk 1 lives ∅ [0, 1] [true] .idle)
      (mk 2 erased ∅ [0, 1] [true] .idle) :=
    .base (step_to (Step.erase _ true (by simp [mk, lives])) (by simp [mk, erased, lives]))
  have h5 : StepWith SlotwiseScan (mk 2 erased ∅ [0, 1] [true] .idle)
      (mk 3 erased ∅ [0, 1] [true] .idle) :=
    .base (Step.tick _)
  have h6 : StepWith SlotwiseScan (mk 3 erased ∅ [0, 1] [true] .idle)
      (mk 3 erased ∅ [0, 1] [true] (.running 3 ∅ ∅)) :=
    .base (Step.start _ rfl)
  have h7 : StepWith SlotwiseScan (mk 3 erased ∅ [0, 1] [true] (.running 3 ∅ ∅))
      (mk 3 erased ∅ [0, 1] [true] (.running 3 (∅ ∪ {0}) ∅)) :=
    .extra (Or.inl ⟨(), 3, ∅, ∅, 0, [1], rfl, rfl, by simp [mk]⟩)
  have h8 : StepWith SlotwiseScan (mk 3 erased ∅ [0, 1] [true] (.running 3 (∅ ∪ {0}) ∅))
      (mk 3 erased ∅ [1] [true] (.running 3 (∅ ∪ {0}) ∅)) :=
    .base (step_to (Step.repin _ () [1] (by simp [mk])
      (by
        intro o ho
        simp [mk] at ho
        subst ho
        exact ⟨1, by simp, by simp [mk, erased], fun d hd => by simp [mk, erased] at hd; omega⟩))
      (by simp [mk, update_unit]))
  have h9 : StepWith SlotwiseScan (mk 3 erased ∅ [1] [true] (.running 3 (∅ ∪ {0}) ∅)) s9 :=
    .extra (Or.inr ⟨(), 3, ∅ ∪ {0}, ∅, rfl, by simp [s9, mk]⟩)
  have h10 := StepWith.base (extra := SlotwiseScan)
    (Step.finish s9 3 (∅ ∪ {0} ∪ {q | q ∈ ([1] : List ℕ).tail}) (insert () ∅) rfl all_unit)
  refine ⟨_, .tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.tail (.single h1) h2) h3)
    h4) h5) h6) h7) h8) h9) h10, ?_, ?_⟩
  · simp [s9, mk]
  · refine Or.inr ⟨⟨2, by simp [s9, mk, erased], by omega⟩, ?_⟩
    intro m hm hv
    simp at hm
    subst hm
    simp [Life.Visible, s9, mk, erased] at hv

end Counterexamples

end Mettapedia.Machines.GracePeriodPins
