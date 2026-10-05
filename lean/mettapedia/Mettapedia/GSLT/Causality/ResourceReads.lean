import Mettapedia.GSLT.Causality.ResourceExploration
import Mathlib.Algebra.BigOperators.Group.Multiset.Defs
import Mathlib.Data.Multiset.Lattice

/-!
# Shared reads: steps, linear renderings, and ordered access

Two firings are concurrent exactly when both consumptions fit beside the union
of their reads: the step rule of nets with read arcs. A finite step, whose
consumptions fit beside the union of all its reads, fires in every order, and
every order reaches one bag. Firings concurrent in pairs need not form a step.

A read can be rendered linearly: one atomic firing takes the resource and
publishes it again. The rendering has the same individual steps and runs; for one stored
atom this is `SpaceChannelBoundary.persistentRead_iff_takeThenRepublish`. It
does not have the same concurrency. Firings that shared a read contend for it
once it is taken, so their two orders, one trace before the rendering, become
two traces. A replicated receiver rendered this way is a linear receiver that
installs itself again. Exposing an intermediate state between the take and
republishing is a different protocol and needs its own observation contract.

A firing that reads a resource present once, and a firing that consumes it,
are ordered: the reader may go first, and after the consumer it is disabled.
A retracted equation strands a call that would have matched it.

Both orders of two firings may be possible and meet although the firings are
not concurrent; the rendering of a shared read is the example. Such a square
is concurrency when neither firing produces what the other needs.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

open Mettapedia.GSLT
open Mettapedia.GSLT.Causality.OccurrenceHistory
open Mettapedia.GSLT.Causality.EventConcurrency

universe uRes uRule

namespace System

variable {R : Type uRes} [DecidableEq R] (S : System.{uRes, uRule} R)

/-! ## Steps with shared reads -/

/-- **Concurrency is the step rule for shared reads**: both consumptions fit
beside the union of the two reads. -/
theorem concurrent_iff_union (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) :
    S.Concurrent M i j ↔ S.consume i + S.consume j + (S.read i ∪ S.read j) ≤ M := by
  rw [Multiset.add_union_distrib, Multiset.union_le_iff]
  rfl

/-- What a finite step of instances consumes. -/
def stepConsume (U : Multiset S.Entry) : Multiset R :=
  (U.map fun entry => S.consume entry.2).sum

/-- What a step produces. -/
def stepProduce (U : Multiset S.Entry) : Multiset R :=
  (U.map fun entry => S.produce entry.2).sum

/-- What a step reads: each resource as often as its most demanding reader. -/
def stepRead (U : Multiset S.Entry) : Multiset R :=
  (U.map fun entry => S.read entry.2).sup

/-- A step is enabled when its consumptions fit beside its shared reads. -/
def StepEnables (M : Multiset R) (U : Multiset S.Entry) : Prop :=
  S.stepConsume U + S.stepRead U ≤ M

/-- A step of two instances is enabled exactly when they are concurrent. -/
theorem stepEnables_pair_iff (M : Multiset R) (a b : S.Entry) :
    S.StepEnables M {a, b} ↔ S.Concurrent M a.2 b.2 := by
  rw [concurrent_iff_union]
  simp [StepEnables, stepConsume, stepRead]

/-- **An enabled step fires in any order**, reaching the bag without its
consumption and with its production. -/
theorem fires_of_stepEnables : ∀ (order : List S.Entry) (M : Multiset R),
    S.StepEnables M order → S.Fires order M (M - S.stepConsume order + S.stepProduce order)
  | [], M, _ => by
      change M - S.stepConsume ([] : List S.Entry) + S.stepProduce ([] : List S.Entry) = M
      simp [stepConsume, stepProduce]
  | entry :: rest, M, enabled => by
      have consumeSplit : S.stepConsume (entry :: rest : List S.Entry) =
          S.consume entry.2 + S.stepConsume rest := by
        simp [stepConsume]
      have produceSplit : S.stepProduce (entry :: rest : List S.Entry) =
          S.produce entry.2 + S.stepProduce rest := by
        simp [stepProduce]
      have readSplit : S.stepRead (entry :: rest : List S.Entry) =
          S.read entry.2 ∪ S.stepRead rest := by
        simp [stepRead]
      unfold StepEnables at enabled
      rw [consumeSplit, readSplit] at enabled
      rw [consumeSplit, produceSplit]
      have headEnabled : S.Enables M entry.2 :=
        le_trans (add_le_add (Multiset.le_add_right _ _) Multiset.le_union_left) enabled
      have restFits : S.consume entry.2 + (S.stepConsume rest + S.stepRead rest) ≤ M := by
        rw [← add_assoc]
        exact le_trans (add_le_add le_rfl Multiset.le_union_right) enabled
      have restEnabled : S.StepEnables (S.fire M entry.2) rest :=
        le_trans (le_tsub_of_add_le_left restFits) (Multiset.le_add_right _ _)
      have restConsumed : S.stepConsume rest ≤ M - S.consume entry.2 :=
        le_tsub_of_add_le_left
          (le_trans (add_le_add le_rfl (Multiset.le_add_right _ _)) restFits)
      have target : S.fire M entry.2 - S.stepConsume rest + S.stepProduce rest =
          M - (S.consume entry.2 + S.stepConsume rest) +
            (S.produce entry.2 + S.stepProduce rest) := by
        unfold fire
        rw [← tsub_add_eq_add_tsub restConsumed, tsub_tsub, add_assoc]
      refine ⟨headEnabled, ?_⟩
      rw [← target]
      exact fires_of_stepEnables rest (S.fire M entry.2) restEnabled

/-- **Every order of an enabled step reaches one bag.** -/
theorem step_orders_meet {order order' : List S.Entry} (perm : order.Perm order')
    {M : Multiset R} (enabled : S.StepEnables M order) :
    S.Fires order M (M - S.stepConsume order + S.stepProduce order) ∧
      S.Fires order' M (M - S.stepConsume order + S.stepProduce order) := by
  have same : (order : Multiset S.Entry) = order' := Multiset.coe_eq_coe.mpr perm
  refine ⟨S.fires_of_stepEnables order M enabled, ?_⟩
  rw [same] at enabled ⊢
  exact S.fires_of_stepEnables order' M enabled

/-! ## The linear rendering of reads -/

/-- Reads rendered linearly: one atomic firing takes what it read and
publishes it again. Intermediate take states are not exposed by this system. -/
abbrev takeRepublish : System R where
  Site := S.Site
  Instance := S.Instance
  consume := fun i => S.consume i + S.read i
  read := fun _ => 0
  produce := fun i => S.produce i + S.read i

omit [DecidableEq R] in
theorem takeRepublish_enables_iff (M : Multiset R) {site : S.Site} (i : S.Instance site) :
    S.takeRepublish.Enables M i ↔ S.Enables M i := by
  change S.consume i + S.read i + 0 ≤ M ↔ S.consume i + S.read i ≤ M
  rw [add_zero]

theorem takeRepublish_fire (M : Multiset R) {site : S.Site} (i : S.Instance site)
    (enabled : S.Enables M i) : S.takeRepublish.fire M i = S.fire M i := by
  change M - (S.consume i + S.read i) + (S.produce i + S.read i) = M - S.consume i + S.produce i
  have readFits : S.read i ≤ M - S.consume i := le_tsub_of_add_le_left enabled
  rw [← tsub_tsub, add_comm (S.produce i), ← add_assoc, tsub_add_cancel_of_le readFits]

/-- **The rendering keeps every step.** -/
theorem takeRepublish_step_iff (M N : Multiset R) :
    S.takeRepublish.theory.Step M N ↔ S.theory.Step M N := by
  constructor
  · rintro ⟨site, i, enabled, rfl⟩
    have enabled' : S.Enables M i := (S.takeRepublish_enables_iff M i).mp enabled
    exact ⟨site, i, enabled', S.takeRepublish_fire M i enabled'⟩
  · rintro ⟨site, i, enabled, rfl⟩
    exact ⟨site, i, (S.takeRepublish_enables_iff M i).mpr enabled,
      (S.takeRepublish_fire M i enabled).symm⟩

private theorem flatMap_congr {α β : Type _} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      rw [List.flatMap_cons, List.flatMap_cons, h a List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem a hx))]

theorem takeRepublish_enabledAt (catalogue : List S.Entry) (M : Multiset R) :
    S.takeRepublish.enabledAt catalogue M = S.enabledAt catalogue M := by
  unfold enabledAt
  congr 1
  funext entry
  change decide (S.consume entry.2 + S.read entry.2 + 0 ≤ M) =
    decide (S.consume entry.2 + S.read entry.2 ≤ M)
  rw [add_zero]

/-- **The rendering has the same runs.** -/
theorem takeRepublish_runs (catalogue : List S.Entry) :
    ∀ (fuel : ℕ) (M : Multiset R),
      S.takeRepublish.runs catalogue fuel M = S.runs catalogue fuel M
  | 0, M => by
      unfold runs
      rw [takeRepublish_enabledAt]
  | fuel + 1, M => by
      unfold runs
      rw [takeRepublish_enabledAt]
      split
      · rfl
      · apply flatMap_congr
        intro entry member
        have enabled : S.Enables M entry.2 :=
          (S.enabledB_iff M entry).mp (List.mem_filter.mp member).2
        rw [S.takeRepublish_fire M entry.2 enabled, takeRepublish_runs catalogue fuel]

omit [DecidableEq R] in
theorem takeRepublish_concurrent_iff (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂) :
    S.takeRepublish.Concurrent M i j ↔
      S.consume i + S.read i + (S.consume j + S.read j) ≤ M := by
  change (S.consume i + S.read i + (S.consume j + S.read j) + 0 ≤ M ∧
      S.consume i + S.read i + (S.consume j + S.read j) + 0 ≤ M) ↔ _
  rw [add_zero, and_self]

omit [DecidableEq R] in
/-- The rendering loses concurrency and never gains it. -/
theorem concurrent_of_takeRepublish {M : Multiset R} {site₁ site₂ : S.Site}
    {i : S.Instance site₁} {j : S.Instance site₂}
    (h : S.takeRepublish.Concurrent M i j) : S.Concurrent M i j := by
  rw [takeRepublish_concurrent_iff] at h
  constructor
  · refine le_trans ?_ h
    calc S.consume i + S.consume j + S.read i = S.consume i + S.read i + S.consume j := by
          abel
      _ ≤ S.consume i + S.read i + (S.consume j + S.read j) :=
          add_le_add le_rfl (Multiset.le_add_right _ _)
  · refine le_trans ?_ h
    calc S.consume i + S.consume j + S.read j = S.consume i + (S.consume j + S.read j) := by
          rw [add_assoc]
      _ ≤ S.consume i + S.read i + (S.consume j + S.read j) :=
          add_le_add (Multiset.le_add_right _ _) le_rfl

/-! ## Reading before consumption -/

/-- **A reader goes before the consumer of what it reads, never after.** When
one firing reads a resource present once, and another consumes it without
restoring it, the two are not concurrent, and after the consumer the reader is
disabled. -/
theorem read_then_consume (M : Multiset R) {site₁ site₂ : S.Site}
    (reader : S.Instance site₁) (consumer : S.Instance site₂) (r : R)
    (inRead : r ∈ S.read reader) (inConsume : r ∈ S.consume consumer)
    (once : M.count r ≤ 1) (notBack : r ∉ S.produce consumer) :
    ¬ S.Concurrent M reader consumer ∧ ¬ S.Enables (S.fire M consumer) reader := by
  have countRead := Multiset.count_pos.mpr inRead
  have countConsume := Multiset.count_pos.mpr inConsume
  constructor
  · intro h
    have fits := Multiset.count_le_of_le r h.1
    rw [Multiset.count_add, Multiset.count_add] at fits
    omega
  · intro h
    have fits := Multiset.count_le_of_le r (le_trans (Multiset.le_add_left _ _) h)
    rw [fire, Multiset.count_add, Multiset.count_sub,
      Multiset.count_eq_zero.mpr notBack] at fits
    omega

/-- A second firing stays enabled after a first whenever it fits beside the
first's consumption. -/
theorem enables_after (M : Multiset R) {site₁ site₂ : S.Site} (first : S.Instance site₁)
    (second : S.Instance site₂)
    (fits : S.consume first + (S.consume second + S.read second) ≤ M) :
    S.Enables (S.fire M first) second :=
  le_trans (le_tsub_of_add_le_left fits) (Multiset.le_add_right _ _)

/-! ## Commuting squares -/

/-- Both orders of two firings are possible, and they meet. -/
structure Square (M : Multiset R) {site₁ site₂ : S.Site} (i : S.Instance site₁)
    (j : S.Instance site₂) : Prop where
  first : S.Enables M i
  second : S.Enables M j
  secondAfter : S.Enables (S.fire M i) j
  firstAfter : S.Enables (S.fire M j) i
  meet : S.fire (S.fire M i) j = S.fire (S.fire M j) i

theorem square_of_concurrent {M : Multiset R} {site₁ site₂ : S.Site}
    {i : S.Instance site₁} {j : S.Instance site₂} (h : S.Concurrent M i j) :
    S.Square M i j where
  first := le_trans (add_le_add (Multiset.le_add_right _ _) le_rfl) h.1
  second := le_trans (add_le_add (Multiset.le_add_left _ _) le_rfl) h.2
  secondAfter := S.enables_fire h
  firstAfter := S.enables_fire (S.concurrent_symm h)
  meet := S.fire_comm h

private theorem le_of_le_add_apart {X Y Z : Multiset R} (h : X ≤ Y + Z)
    (apart : ∀ r ∈ Z, r ∉ X) : X ≤ Y := by
  rw [Multiset.le_iff_count] at h ⊢
  intro r
  have bound := h r
  rw [Multiset.count_add] at bound
  by_cases inZ : r ∈ Z
  · rw [Multiset.count_eq_zero.mpr (apart r inZ)]
    exact Nat.zero_le _
  · rw [Multiset.count_eq_zero.mpr inZ] at bound
    omega

/-- **A square is concurrency when neither firing produces what the other
needs.** -/
theorem concurrent_of_square (M : Multiset R) {site₁ site₂ : S.Site}
    (i : S.Instance site₁) (j : S.Instance site₂)
    (apartI : ∀ r ∈ S.produce i, r ∉ S.consume j + S.read j)
    (apartJ : ∀ r ∈ S.produce j, r ∉ S.consume i + S.read i)
    (square : S.Square M i j) : S.Concurrent M i j := by
  have fitsJ : S.consume j + S.read j ≤ M - S.consume i :=
    le_of_le_add_apart (Y := M - S.consume i) (Z := S.produce i) square.secondAfter apartI
  have fitsI : S.consume i + S.read i ≤ M - S.consume j :=
    le_of_le_add_apart (Y := M - S.consume j) (Z := S.produce j) square.firstAfter apartJ
  have takenI : S.consume i ≤ M := le_trans (Multiset.le_add_right _ _) square.first
  have takenJ : S.consume j ≤ M := le_trans (Multiset.le_add_right _ _) square.second
  constructor
  · calc S.consume i + S.consume j + S.read i = S.consume j + (S.consume i + S.read i) := by
          abel
      _ ≤ M := (le_tsub_iff_left takenJ).mp fitsI
  · calc S.consume i + S.consume j + S.read j = S.consume i + (S.consume j + S.read j) := by
          rw [add_assoc]
      _ ≤ M := (le_tsub_iff_left takenI).mp fitsJ

/-- The route of a square that fires `i` first. -/
def Square.route {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (square : S.Square M i j) :
    OccurrencePath S.presentation M (S.fire (S.fire M i) j) :=
  .cons ⟨site₁, ⟨i, square.first, rfl⟩⟩
    (.cons ⟨site₂, ⟨j, square.secondAfter, rfl⟩⟩ (.refl _))

/-- The route of a square that fires `j` first, arriving at the same bag. -/
def Square.swapped {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (square : S.Square M i j) :
    OccurrencePath S.presentation M (S.fire (S.fire M i) j) :=
  square.meet.symm ▸
    (.cons ⟨site₂, ⟨j, square.second, rfl⟩⟩
      (.cons ⟨site₁, ⟨i, square.firstAfter, rfl⟩⟩ (.refl _)) :
        OccurrencePath S.presentation M (S.fire (S.fire M j) i))

/-- **The two routes of a concurrent square are one trace.** -/
theorem traceEq_of_concurrent {M : Multiset R} {site₁ site₂ : S.Site}
    {i : S.Instance site₁} {j : S.Instance site₂} (h : S.Concurrent M i j) :
    TraceEq S.concurrency.tiles (S.square_of_concurrent h).route
      (S.square_of_concurrent h).swapped :=
  .tile (T := S.concurrency.tiles)
    ⟨S.event M i (S.square_of_concurrent h).first,
      S.event M j (S.square_of_concurrent h).second, h⟩

/-- The instance that a path fires first. -/
def firstInstance {M N : Multiset R} : OccurrencePath S.presentation M N → Option S.Entry
  | .refl _ => none
  | .cons o _ => some ⟨o.site, o.evidence.val⟩

theorem firstInstance_cast {M N N' : Multiset R} (h : N = N')
    (p : OccurrencePath S.presentation M N) :
    S.firstInstance (h ▸ p) = S.firstInstance p := by
  cases h
  rfl

theorem firstInstance_route {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (square : S.Square M i j) :
    S.firstInstance square.route = some ⟨site₁, i⟩ :=
  rfl

theorem firstInstance_swapped {M : Multiset R} {site₁ site₂ : S.Site} {i : S.Instance site₁}
    {j : S.Instance site₂} (square : S.Square M i j) :
    S.firstInstance square.swapped = some ⟨site₂, j⟩ := by
  unfold Square.swapped
  rw [firstInstance_cast]
  rfl

end System

/-! ## Controls -/

namespace Controls

/-- One kind of token, consumed by every firing. -/
def tokenUse : System Unit where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun _ => {()}
  read := fun _ => 0
  produce := fun _ => 0

def use (n : ℕ) : tokenUse.Entry := ⟨(), n⟩

def twoTokens : Multiset Unit := {(), ()}

/-- **Concurrent in pairs is not a step.** Three firings each need one of two
tokens: any two fit together, all three do not. -/
theorem pairwise_concurrent_not_a_step :
    tokenUse.Concurrent twoTokens (use 1).2 (use 2).2 ∧
      tokenUse.Concurrent twoTokens (use 1).2 (use 3).2 ∧
      tokenUse.Concurrent twoTokens (use 2).2 (use 3).2 ∧
      ¬ tokenUse.StepEnables twoTokens {use 1, use 2, use 3} := by
  refine ⟨by unfold System.Concurrent; decide, by unfold System.Concurrent; decide,
    by unfold System.Concurrent; decide, ?_⟩
  unfold System.StepEnables System.stepConsume System.stepRead
  decide

/-- The rendering of a replicated receiver is a linear receiver that installs
itself again. -/
theorem replicated_receiver_rendering (value : ℕ) :
    persistentReceiver.takeRepublish.consume (site := ()) (takeAgain value) =
        linearReceiver.consume (take value) ∧
      persistentReceiver.takeRepublish.produce (site := ()) (takeAgain value) =
        linearReceiver.produce (take value) + {Res.receiver} := by
  constructor
  · change ({Res.message value} : Multiset Res) + {Res.receiver} =
      {Res.message value, Res.receiver}
    rw [Multiset.singleton_add]
    rfl
  · rfl

/-- Calls, one equation, and answers. -/
inductive CallRes where
  | call (index : ℕ)
  | equation
  | answer (index : ℕ)
  deriving DecidableEq

/-- Numbered calls answered by one equation, which they read. -/
def oneEquation : System CallRes where
  Site := Unit
  Instance := fun _ => ℕ
  consume := fun index => {CallRes.call index}
  read := fun _ => {CallRes.equation}
  produce := fun index => {CallRes.answer index}

def callEntry (index : Nat) : oneEquation.Entry := ⟨(), index⟩

instance : DecidableEq oneEquation.Entry :=
  inferInstanceAs (DecidableEq (Σ _ : Unit, Nat))

def answerCall (index : ℕ) : oneEquation.Instance () := index

def twoCalls : Multiset CallRes := {CallRes.call 1, CallRes.call 2, CallRes.equation}

theorem calls_concurrent : oneEquation.Concurrent twoCalls (answerCall 1) (answerCall 2) := by
  unfold System.Concurrent
  decide

/-- Answering call `index`, in the rendering. -/
def renderedCall (index : ℕ) : oneEquation.takeRepublish.Instance () := index

/-- Rendered linearly, the two calls still answer in either order. -/
theorem rendered_square :
    oneEquation.takeRepublish.Square twoCalls (renderedCall 1) (renderedCall 2) :=
  ⟨by unfold System.Enables; decide, by unfold System.Enables; decide,
    by unfold System.Enables System.fire; decide, by unfold System.Enables System.fire; decide,
    by unfold System.fire; decide⟩

/-- **The rendering keeps the square and loses the concurrency.** -/
theorem rendered_calls_contend :
    ¬ oneEquation.takeRepublish.Concurrent twoCalls (renderedCall 1) (renderedCall 2) := by
  unfold System.Concurrent
  decide

/-- **Before the rendering, the two orders are one trace.** -/
theorem calls_one_trace :
    Trace.mk (T := oneEquation.concurrency.tiles)
        (oneEquation.square_of_concurrent calls_concurrent).route =
      Trace.mk (oneEquation.square_of_concurrent calls_concurrent).swapped :=
  Trace.mk_sound (oneEquation.traceEq_of_concurrent calls_concurrent)

private theorem equation_count_preserved {M N : Multiset CallRes}
    (o : Occurrence oneEquation.takeRepublish.presentation M N) :
    M.count CallRes.equation = 1 → N.count CallRes.equation = 1 := by
  intro single
  obtain ⟨index, _, target⟩ := o.evidence
  rw [target]
  simp [System.fire, oneEquation, single]

private theorem no_rendered_tile {M : Multiset CallRes} (single : M.count CallRes.equation = 1)
    (tile : oneEquation.takeRepublish.concurrency.tiles.Tile M) : False := by
  have fits := Multiset.count_le_of_le CallRes.equation tile.independent.1
  simp [oneEquation, single] at fits

/-- **After the rendering, the two orders are two traces**, although the
rendering has the same steps and the same runs. -/
theorem rendered_calls_two_traces :
    Trace.mk (T := oneEquation.takeRepublish.concurrency.tiles) rendered_square.route ≠
      Trace.mk rendered_square.swapped := by
  intro same
  have equal := TraceEq.eq_of_no_tile oneEquation.takeRepublish.concurrency.tiles
    (fun M => M.count CallRes.equation = 1) equation_count_preserved no_rendered_tile
    (Quotient.exact same) (by decide)
  have firsts := congrArg oneEquation.takeRepublish.firstInstance equal
  rw [oneEquation.takeRepublish.firstInstance_route rendered_square,
    oneEquation.takeRepublish.firstInstance_swapped rendered_square] at firsts
  have values := eq_of_heq (Sigma.mk.inj (Option.some.inj firsts)).2
  change (1 : ℕ) = 2 at values
  omega

/-- Calls, equations, answers and retraction requests of an editable space. -/
inductive EditRes where
  | call
  | equation (index : ℕ)
  | answer (index : ℕ)
  | retraction (index : ℕ)
  deriving DecidableEq

/-- Answering a call, or retracting an equation. -/
inductive EditSite where
  | answer
  | retract
  deriving DecidableEq

/-- A space whose equations can be retracted. An answer reads the equation and
consumes the call; a retraction consumes its request and the equation. -/
def editableSpace : System EditRes where
  Site := EditSite
  Instance := fun _ => ℕ
  consume := fun {site} index => match site with
    | .answer => {EditRes.call}
    | .retract => {EditRes.retraction index, EditRes.equation index}
  read := fun {site} index => match site with
    | .answer => {EditRes.equation index}
    | .retract => 0
  produce := fun {site} index => match site with
    | .answer => {EditRes.answer index}
    | .retract => 0

def answerEntry (index : ℕ) : editableSpace.Entry := ⟨.answer, index⟩
def retractEntry (index : ℕ) : editableSpace.Entry := ⟨.retract, index⟩

/-- One call, the equation it matches, and a request to retract it. -/
def pendingRetraction : Multiset EditRes :=
  {EditRes.call, EditRes.equation 1, EditRes.retraction 1}

/-- **A retraction strands the call.** The answer and the retraction are not
concurrent, and after the retraction the same call has no answer. -/
theorem retraction_strands_call :
    ¬ editableSpace.Concurrent pendingRetraction (answerEntry 1).2 (retractEntry 1).2 ∧
      ¬ editableSpace.Enables (editableSpace.fire pendingRetraction (retractEntry 1).2)
        (answerEntry 1).2 :=
  editableSpace.read_then_consume pendingRetraction (answerEntry 1).2 (retractEntry 1).2
    (EditRes.equation 1) (by decide) (by decide) (by decide) (by decide)

/-- The two orders end differently: an answer, or a stranded call. -/
theorem retraction_order_outcomes :
    editableSpace.outcomes [answerEntry 1, retractEntry 1] 2 pendingRetraction =
      [{EditRes.answer 1}, {EditRes.call}] := by
  decide

end Controls

#print axioms System.concurrent_iff_union
#print axioms System.fires_of_stepEnables
#print axioms System.step_orders_meet
#print axioms System.takeRepublish_step_iff
#print axioms System.takeRepublish_runs
#print axioms System.concurrent_of_takeRepublish
#print axioms System.read_then_consume
#print axioms System.concurrent_of_square
#print axioms System.traceEq_of_concurrent
#print axioms Controls.pairwise_concurrent_not_a_step
#print axioms Controls.replicated_receiver_rendering
#print axioms Controls.rendered_calls_contend
#print axioms Controls.calls_one_trace
#print axioms Controls.rendered_calls_two_traces
#print axioms Controls.retraction_strands_call
#print axioms Controls.retraction_order_outcomes

end Mettapedia.GSLT.Causality.ResourceInteraction
