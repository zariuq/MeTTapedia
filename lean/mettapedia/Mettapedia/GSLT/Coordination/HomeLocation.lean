import Mettapedia.GSLT.Coordination.ReplicaMerge
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ChannelAddressing
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Union

/-!
# One home per occurrence: takes route to the owner

Every label has a **home** location (`home : R → L`), and an occurrence lives at the home of its
label. Each location keeps the occurrences homed there. A commit runs at one location; what it
makes for another location travels as a message (**in flight**) and arrives later.

**Fault model.** Messages between locations are delayed without bound and delivered in any order;
locations run their commits one at a time. Identities are globally fresh (`used`), as with
identities qualified by the location that makes them.

## The routing rule

A placed commit is **homed at** its location when everything it takes or keeps, and the region of
each of its predicate queries, lives there (`HomedAt`): it is scoped to its site in the sense of
`OccurrenceCommits.ChannelAddressing`, except for what it makes (`scoped_iff_homedAt`). Queried
regions are **closed**: only commits at their home make occurrences in them (`ClosedQueries`).
Monotone data needs neither condition beyond its own location: what is made elsewhere simply
travels.

## Refinement

* **Every network commit is an atomic commit of the whole store** (`commit_refines`): when a homed
  commit is enabled at its location's store, it is enabled at the union of every location's store
  and the messages in flight, and the network's step is that commit's firing there.
* **Every network run is an atomic run** (`run_refines`): the commits a network run performs form a
  legal run of the atomic semantics from the initial store, ending at the union of the final
  stores and messages; deliveries are invisible.

## Controls

* `Controls.misrouted_take_refused`: a take of an occurrence homed elsewhere is not enabled at a
  location that does not keep it.
* `Controls.remote_absence_not_atomic`: an absence read of a region that receives messages from
  another location holds locally while a message for that region is in flight, so the commit is not
  an atomic step of the whole store. Closed regions are necessary.
* `Controls.reply_travels`: a commit that takes at its home and replies to another location is an
  atomic commit, and the reply arrives later without changing the atomic store.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Coordination.HomeLocation

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.GSLT.Coordination.ReplicaMerge

universe u v w

variable {O : Type u} [DecidableEq O] {R : Type v} {L : Type w} [DecidableEq L]

/-- A commit together with the location that runs it. -/
structure Placed (O : Type u) (R : Type v) (L : Type w) where
  commit : Commit O R
  site : L

/-- **Homed at its location**: everything taken or kept, and the region of every predicate query,
lives there. -/
def HomedAt (label : O → R) (home : R → L) (p : Placed O R L) : Prop :=
  (∀ o ∈ p.commit.taken ∪ p.commit.kept, home (label o) = p.site) ∧
    ∀ read ∈ p.commit.queries, ∀ r, read.region r = true → home r = p.site

/-- **Homed is scoped to the site, except for what it makes**: a placed commit is scoped to its
site in the sense of `ChannelAddressing.Scoped`, with homes as addresses, exactly when it is homed
there and makes only there. What a homed commit makes elsewhere travels as a message. -/
theorem scoped_iff_homedAt {label : O → R} {home : R → L} {p : Placed O R L} :
    Scoped label home (fun l => decide (l = p.site)) p.commit ↔
      HomedAt label home p ∧ ∀ o ∈ p.commit.made, home (label o) = p.site := by
  constructor
  · intro inScope
    refine ⟨⟨fun o used => ?_, fun read member r inRegion => ?_⟩, fun o made => ?_⟩
    · rcases Finset.mem_union.mp used with taken | kept
      · simpa using inScope.taken o taken
      · simpa using inScope.kept o kept
    · simpa using inScope.queries read member r inRegion
    · simpa using inScope.made o made
  · rintro ⟨⟨used, reads⟩, made⟩
    exact ⟨fun o taken => by simpa using used o (Finset.mem_union_left _ taken),
      fun o kept => by simpa using used o (Finset.mem_union_right _ kept),
      fun o member => by simpa using made o member,
      fun read member r inRegion => by simpa using reads read member r inRegion⟩

/-- **Closed queries**: an occurrence made inside a region that some commit queries is made at
that commit's location. -/
def ClosedQueries (label : O → R) (program : List (Placed O R L)) : Prop :=
  ∀ p ∈ program, ∀ q ∈ program, ∀ read ∈ q.commit.queries, ∀ o ∈ p.commit.made,
    read.region (label o) = true → p.site = q.site

/-- The network: each location's store, the messages in flight, and every identity used. -/
structure Net (O : Type u) (L : Type w) where
  store : L → Finset O
  inflight : Finset O
  used : Finset O

/-- A network event: run a placed commit, or deliver a message. -/
inductive Event (O : Type u) (R : Type v) (L : Type w) where
  | commit (p : Placed O R L)
  | deliver (o : O)

variable (label : O → R) (home : R → L)

/-- What a commit at `site` makes for `site` itself. -/
def madeHere (site : L) (c : Commit O R) : Finset O := c.made.filter fun o => home (label o) = site

/-- What a commit at `site` makes for other locations. -/
def madeAway (site : L) (c : Commit O R) : Finset O := c.made.filter fun o => home (label o) ≠ site

/-- A placed commit runs when it is enabled at its location's store and its identities are fresh. -/
def Accepts (net : Net O L) (p : Placed O R L) : Prop :=
  Enabled label (net.store p.site) p.commit ∧ Disjoint p.commit.made net.used

instance (net : Net O L) (p : Placed O R L) : Decidable (Accepts label net p) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- One network event. -/
def step (net : Net O L) : Event O R L → Net O L
  | .commit p =>
      if Accepts label net p then
        { store := Function.update net.store p.site
            ((net.store p.site \ p.commit.taken) ∪ madeHere label home p.site p.commit)
          inflight := net.inflight ∪ madeAway label home p.site p.commit
          used := net.used ∪ p.commit.made }
      else net
  | .deliver o =>
      if o ∈ net.inflight then
        { net with
          store := Function.update net.store (home (label o)) (insert o (net.store (home (label o))))
          inflight := net.inflight.erase o }
      else net

variable [Fintype L]

/-- The whole store: every location's occurrences and the messages in flight. -/
def whole (net : Net O L) : Finset O := Finset.univ.biUnion net.store ∪ net.inflight

omit [DecidableEq L] in
theorem mem_whole {net : Net O L} {o : O} : o ∈ whole net ↔ (∃ site, o ∈ net.store site) ∨ o ∈ net.inflight := by
  simp [whole]

/-- The network invariant for a program. -/
structure Inv (program : List (Placed O R L)) (net : Net O L) : Prop where
  used : whole net ⊆ net.used
  homed : ∀ site, ∀ o ∈ net.store site, home (label o) = site
  apart : ∀ site, Disjoint (net.store site) net.inflight
  unread : ∀ o ∈ net.inflight, ∀ q ∈ program, ∀ read ∈ q.commit.queries, read.region (label o) = false

variable {label home}

omit [Fintype L] in
theorem mem_store_commit {net : Net O L} {p : Placed O R L} (accepts : Accepts label net p)
    (site : L) (o : O) :
    o ∈ (step label home net (.commit p)).store site ↔
      if site = p.site then (o ∈ net.store p.site ∧ o ∉ p.commit.taken) ∨
        (o ∈ p.commit.made ∧ home (label o) = p.site)
      else o ∈ net.store site := by
  simp only [step, if_pos accepts, Function.update_apply]
  split_ifs with same
  · simp [madeHere, Finset.mem_sdiff]
  · rfl

omit [Fintype L] in
theorem mem_inflight_commit {net : Net O L} {p : Placed O R L} (accepts : Accepts label net p) (o : O) :
    o ∈ (step label home net (.commit p)).inflight ↔
      o ∈ net.inflight ∨ (o ∈ p.commit.made ∧ home (label o) ≠ p.site) := by
  simp [step, if_pos accepts, madeAway]

/-- **Every network commit is an atomic commit of the whole store.** -/
theorem commit_refines {program : List (Placed O R L)} {net : Net O L} (inv : Inv label home program net)
    {p : Placed O R L} (inProgram : p ∈ program) (homed : HomedAt label home p)
    (accepts : Accepts label net p) :
    Enabled label (whole net) p.commit ∧
      whole (step label home net (.commit p)) = fire (whole net) p.commit := by
  have enabled := accepts.1
  have fresh := accepts.2
  have localWhole : net.store p.site ⊆ whole net := fun o member =>
    mem_whole.mpr (Or.inl ⟨p.site, member⟩)
  have takenHome : ∀ o ∈ p.commit.taken, home (label o) = p.site := fun o taken =>
    homed.1 o (Finset.mem_union_left _ taken)
  have takenNotFlying : ∀ o ∈ p.commit.taken, o ∉ net.inflight := fun o taken flying =>
    Finset.disjoint_left.mp (inv.apart p.site) (enabled.taken_subset taken) flying
  have takenNotElsewhere : ∀ o ∈ p.commit.taken, ∀ site, o ∈ net.store site → site = p.site :=
    fun o taken site inStore => (inv.homed site o inStore).symm.trans (takenHome o taken)
  refine ⟨⟨enabled.taken_subset.trans localWhole, enabled.kept_subset.trans localWhole,
    enabled.apart, Finset.disjoint_of_subset_right inv.used fresh, fun read member => ?_⟩, ?_⟩
  · -- the queried region has the same occurrences in the whole store as at the location
    have local' := enabled.queries_hold read member
    unfold PredicateQuery.Holds at local' ⊢
    rw [← local']
    ext o
    simp only [mem_regionOf]
    constructor
    · rintro ⟨inWhole, inRegion⟩
      refine ⟨?_, inRegion⟩
      rcases mem_whole.mp inWhole with ⟨site, inStore⟩ | inFlight
      · have homeIs := inv.homed site o inStore
        rw [homed.2 read member _ inRegion] at homeIs
        exact homeIs ▸ inStore
      · rw [inv.unread o inFlight p inProgram read member] at inRegion
        exact absurd inRegion (by decide)
    · rintro ⟨inStore, inRegion⟩
      exact ⟨localWhole inStore, inRegion⟩
  · ext o
    rw [mem_whole, mem_fire, mem_whole, mem_inflight_commit accepts]
    simp only [mem_store_commit accepts]
    constructor
    · rintro (⟨site, inSite⟩ | flying | ⟨made, _⟩)
      · split_ifs at inSite with same
        · rcases inSite with ⟨inStore, notTaken⟩ | ⟨made, _⟩
          · exact Or.inl ⟨Or.inl ⟨p.site, inStore⟩, notTaken⟩
          · exact Or.inr made
        · exact Or.inl ⟨Or.inl ⟨site, inSite⟩, fun taken =>
            same (takenNotElsewhere o taken site inSite)⟩
      · exact Or.inl ⟨Or.inr flying, fun taken => takenNotFlying o taken flying⟩
      · exact Or.inr made
    · rintro (⟨⟨site, inStore⟩ | flying, notTaken⟩ | made)
      · by_cases same : site = p.site
        · subst same
          exact Or.inl ⟨p.site, by rw [if_pos rfl]; exact Or.inl ⟨inStore, notTaken⟩⟩
        · exact Or.inl ⟨site, by rw [if_neg same]; exact inStore⟩
      · exact Or.inr (Or.inl flying)
      · by_cases here : home (label o) = p.site
        · exact Or.inl ⟨p.site, by rw [if_pos rfl]; exact Or.inr ⟨made, here⟩⟩
        · exact Or.inr (Or.inr ⟨made, here⟩)

/-- A commit preserves the network invariant. -/
theorem inv_commit {program : List (Placed O R L)} (homedAll : ∀ p ∈ program, HomedAt label home p)
    (closed : ClosedQueries label program) {net : Net O L} (inv : Inv label home program net)
    {p : Placed O R L} (inProgram : p ∈ program) (accepts : Accepts label net p) :
    Inv label home program (step label home net (.commit p)) := by
  have fresh := accepts.2
  have wholeEq := (commit_refines inv inProgram (homedAll p inProgram) accepts).2
  refine ⟨?_, fun site o member => ?_, fun site => ?_, fun o member q inQ read reads => ?_⟩
  · have usedEq : (step label home net (.commit p)).used = net.used ∪ p.commit.made := by
      simp [step, if_pos accepts]
    rw [wholeEq, usedEq]
    intro o member
    rcases mem_fire.mp member with ⟨inWhole, _⟩ | made
    · exact Finset.mem_union_left _ (inv.used inWhole)
    · exact Finset.mem_union_right _ made
  · rw [mem_store_commit accepts] at member
    split_ifs at member with same
    · rcases member with ⟨inStore, _⟩ | ⟨_, homeIs⟩
      · rw [same]; exact inv.homed _ o inStore
      · rw [same]; exact homeIs
    · exact inv.homed site o member
  · refine Finset.disjoint_left.mpr fun o inStore flying => ?_
    rw [mem_store_commit accepts] at inStore
    rw [mem_inflight_commit accepts] at flying
    have unusedMade : o ∈ p.commit.made → o ∉ net.used := fun made => Finset.disjoint_left.mp fresh made
    have wholeUsed : ∀ site', o ∈ net.store site' → o ∈ net.used := fun site' member =>
      inv.used (mem_whole.mpr (Or.inl ⟨site', member⟩))
    split_ifs at inStore with same
    · rcases inStore with ⟨inStore, _⟩ | ⟨made, homeIs⟩
      · rcases flying with flying | ⟨made, _⟩
        · exact Finset.disjoint_left.mp (inv.apart p.site) inStore flying
        · exact unusedMade made (wholeUsed _ inStore)
      · rcases flying with flying | ⟨_, notHome⟩
        · exact unusedMade made (inv.used (mem_whole.mpr (Or.inr flying)))
        · exact notHome homeIs
    · rcases flying with flying | ⟨made, _⟩
      · exact Finset.disjoint_left.mp (inv.apart site) inStore flying
      · exact unusedMade made (wholeUsed _ inStore)
  · rw [mem_inflight_commit accepts] at member
    rcases member with flying | ⟨made, notHome⟩
    · exact inv.unread o flying q inQ read reads
    · cases inRegion : read.region (label o)
      · rfl
      · have atReader : home (label o) = q.site := (homedAll q inQ).2 read reads _ inRegion
        have sameSite : p.site = q.site := closed p inProgram q inQ read reads o made inRegion
        exact absurd (atReader.trans sameSite.symm) notHome

/-- A delivery moves a message to its home and changes nothing else. -/
theorem deliver_whole {net : Net O L} (o : O) : whole (step label home net (.deliver o)) = whole net := by
  simp only [step]
  split_ifs with flying
  · ext x
    simp only [mem_whole, Function.update_apply, Finset.mem_erase]
    constructor
    · rintro (⟨site, inSite⟩ | ⟨_, inFlight⟩)
      · split_ifs at inSite with same
        · rcases Finset.mem_insert.mp inSite with rfl | inStore
          · exact Or.inr flying
          · exact Or.inl ⟨_, inStore⟩
        · exact Or.inl ⟨site, inSite⟩
      · exact Or.inr inFlight
    · rintro (⟨site, inStore⟩ | inFlight)
      · refine Or.inl ⟨site, ?_⟩
        split_ifs with same
        · exact Finset.mem_insert_of_mem (same ▸ inStore)
        · exact inStore
      · by_cases same : x = o
        · subst same
          exact Or.inl ⟨home (label x), by rw [if_pos rfl]; exact Finset.mem_insert_self _ _⟩
        · exact Or.inr ⟨same, inFlight⟩
  · rfl

/-- A delivery preserves the network invariant. -/
theorem inv_deliver {program : List (Placed O R L)} {net : Net O L} (inv : Inv label home program net)
    (o : O) : Inv label home program (step label home net (.deliver o)) := by
  have wholeEq := deliver_whole (label := label) (home := home) (net := net) o
  simp only [step] at wholeEq ⊢
  split_ifs with flying
  · rw [if_pos flying] at wholeEq
    refine ⟨wholeEq ▸ inv.used, fun site x member => ?_, fun site => ?_, fun x member => ?_⟩
    · simp only [Function.update_apply] at member
      split_ifs at member with same
      · rcases Finset.mem_insert.mp member with rfl | inStore
        · exact same.symm
        · exact same ▸ inv.homed _ x inStore
      · exact inv.homed site x member
    · refine Finset.disjoint_left.mpr fun x inStore inFlight => ?_
      simp only [Function.update_apply] at inStore
      obtain ⟨notO, flying'⟩ := Finset.mem_erase.mp inFlight
      split_ifs at inStore with same
      · rcases Finset.mem_insert.mp inStore with rfl | inStore'
        · exact notO rfl
        · exact Finset.disjoint_left.mp (inv.apart _) inStore' flying'
      · exact Finset.disjoint_left.mp (inv.apart site) inStore flying'
    · exact inv.unread x (Finset.mem_of_mem_erase member)
  · exact inv

/-! ## Runs -/

variable (label home)

/-- The commits a network event performs. -/
def performed (net : Net O L) : Event O R L → List (Commit O R)
  | .commit p => if Accepts label net p then [p.commit] else []
  | .deliver _ => []

/-- A network run. -/
def runNet (net : Net O L) : List (Event O R L) → Net O L
  | [] => net
  | e :: es => runNet (step label home net e) es

/-- The commits a network run performs, in order. -/
def performedAll (net : Net O L) : List (Event O R L) → List (Commit O R)
  | [] => []
  | e :: es => performed label net e ++ performedAll (step label home net e) es

variable {label home}

/-- **Every network run is an atomic run**: the commits it performs are a legal run of the atomic
semantics from the whole initial store, ending at the whole final store. -/
theorem run_refines {program : List (Placed O R L)} (homedAll : ∀ p ∈ program, HomedAt label home p)
    (closed : ClosedQueries label program) (events : List (Event O R L))
    (inProgram : ∀ p, Event.commit p ∈ events → p ∈ program) :
    ∀ net : Net O L, Inv label home program net →
      Executable label (whole net) (performedAll label home net events) ∧
        whole (runNet label home net events) = fireList (whole net) (performedAll label home net events) := by
  induction events with
  | nil => intro net _; exact ⟨Executable.nil _, rfl⟩
  | cons e rest ih =>
      intro net inv
      have restProgram : ∀ p, Event.commit p ∈ rest → p ∈ program :=
        fun p member => inProgram p (List.mem_cons_of_mem _ member)
      cases e with
      | commit p =>
          have pIn := inProgram p (List.mem_cons_self ..)
          by_cases accepts : Accepts label net p
          · obtain ⟨enabled, wholeEq⟩ := commit_refines inv pIn (homedAll p pIn) accepts
            obtain ⟨legal, final⟩ := ih restProgram _ (inv_commit homedAll closed inv pIn accepts)
            simp only [performedAll, performed, if_pos accepts, List.singleton_append, runNet]
            rw [wholeEq] at legal final
            exact ⟨Executable.cons enabled legal, final⟩
          · have same : step label home net (.commit p) = net := by simp [step, accepts]
            simp only [performedAll, performed, if_neg accepts, List.nil_append, runNet, same]
            exact ih restProgram net inv
      | deliver o =>
          obtain ⟨legal, final⟩ := ih restProgram _ (inv_deliver inv o)
          simp only [performedAll, performed, List.nil_append, runNet]
          rw [deliver_whole] at legal final
          exact ⟨legal, final⟩

/-! ## Controls -/

namespace Controls

/-- Labels of the controls: a token and replies at their homes, and flags of a queried region at
`false`. -/
inductive Spot where
  | token
  | reply
  | flag
  | other
  deriving DecidableEq

/-- Occurrence `0` is the token, `1` a reply, `2` a flag, others other. -/
def spot : ℕ → Spot
  | 0 => .token
  | 1 => .reply
  | 2 => .flag
  | _ => .other

/-- The token lives at `true`; replies, flags and others at `false`. -/
def spotHome : Spot → Bool
  | .token => true
  | _ => false

def isFlag : Spot → Bool
  | .flag => true
  | _ => false

/-- The start: the token at its home. -/
def start : Net ℕ Bool := ⟨fun site => if site then {0} else ∅, ∅, {0}⟩

/-- Take the token and reply to `false`. -/
def takeAndReply : Commit ℕ Spot := ⟨{0}, ∅, {1}, []⟩

/-- **A take of an occurrence homed elsewhere is refused** at a location that does not keep it. -/
theorem misrouted_take_refused : ¬ Accepts spot start ⟨takeAndReply, false⟩ := by
  decide

/-- **A reply travels**: the take at the token's home is an atomic commit; the reply is in flight,
then arrives, and the whole store is the same before and after the delivery. -/
theorem reply_travels :
    let afterCommit := step spot spotHome start (.commit ⟨takeAndReply, true⟩)
    whole afterCommit = {1} ∧ afterCommit.inflight = {1} ∧
      whole (step spot spotHome afterCommit (.deliver 1)) = {1} ∧
        (step spot spotHome afterCommit (.deliver 1)).store false = {1} := by
  decide

/-- The reply program is homed and its predicate queries are closed, so its runs are atomic runs. -/
theorem reply_program_atomic :
    Executable spot (whole start) (performedAll spot spotHome start
      [.commit ⟨takeAndReply, true⟩, .deliver 1]) := by
  refine (run_refines (program := [⟨takeAndReply, true⟩]) ?_ ?_ _ ?_ start ?_).1
  · intro p member
    simp only [List.mem_singleton] at member
    subst member
    refine ⟨fun o member => ?_, fun read member => by simp [takeAndReply] at member⟩
    simp [takeAndReply] at member
    subst member
    rfl
  · intro p _ q inQ read member
    simp only [List.mem_singleton] at inQ
    subst inQ
    simp [takeAndReply] at member
  · intro p member
    simp at member
    simp [member]
  · refine ⟨by decide, fun site o member => ?_, fun site => by cases site <;> decide,
      fun o member => by simp [start] at member⟩
    cases site
    · simp [start] at member
    · simp only [start, if_true, Finset.mem_singleton] at member
      subst member
      rfl

/-- Make a flag for `false`, from `true`. -/
def remoteFlag : Commit ℕ Spot := ⟨∅, ∅, {2}, []⟩

/-- At `false`, make an output when no flag is present. -/
def unlessFlag : Commit ℕ Spot := ⟨∅, ∅, {3}, [⟨isFlag, ∅⟩]⟩

/-- **An absence read of a region written from elsewhere is not atomic**: while the flag made at
`true` is in flight, the absence read at `false` holds locally, and fails for the whole store. -/
theorem remote_absence_not_atomic :
    let flagFlying := step spot spotHome start (.commit ⟨remoteFlag, true⟩)
    flagFlying.inflight = {2} ∧ Accepts spot flagFlying ⟨unlessFlag, false⟩ ∧
      ¬ Enabled spot (whole flagFlying) unlessFlag := by
  decide

/-- That program's reads are not closed. -/
theorem remote_absence_not_closed :
    ¬ ClosedQueries spot [⟨remoteFlag, true⟩, ⟨unlessFlag, false⟩] := by
  intro closed
  have := closed ⟨remoteFlag, true⟩ (by simp) ⟨unlessFlag, false⟩ (by simp) ⟨isFlag, ∅⟩
    (by simp [unlessFlag]) 2 (by simp [remoteFlag]) rfl
  simp at this

/-! ### Homed commits, closed queries -/

/-- **Positive control**: taking the token and replying is homed at the token's home `true`. -/
theorem takeAndReply_homed : HomedAt spot spotHome ⟨takeAndReply, true⟩ :=
  ⟨by decide, by simp [takeAndReply]⟩

/-- **Negative control**: placed at `false`, the same commit takes the token away from its home. -/
theorem takeAndReply_misplaced_not_homed : ¬ HomedAt spot spotHome ⟨takeAndReply, false⟩ :=
  fun homed => absurd (homed.1 0 (by simp [takeAndReply])) (by decide)

/-- **Positive control**: with the flag maker at the flag's home `false`, where the absence query
also runs, the queried region is closed. (`remote_absence_not_closed` is the negative control.) -/
theorem colocated_flag_closed : ClosedQueries spot [⟨remoteFlag, false⟩, ⟨unlessFlag, false⟩] := by
  intro p member q member' _ _ _ _ _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member member'
  rcases member with rfl | rfl <;> rcases member' with rfl | rfl <;> rfl

end Controls

end Mettapedia.GSLT.Coordination.HomeLocation
