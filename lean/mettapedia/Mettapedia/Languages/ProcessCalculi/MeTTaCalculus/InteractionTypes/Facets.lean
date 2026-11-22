import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.FootprintTypes
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ChannelAddressing

/-!
# Facets: rights per name, checked when a commit is formed

A **facet** is one way of using a name: `send` puts an occurrence there, `receive` takes one,
`peek` keeps one, `observe` queries the name's region (absence, counts, uniqueness, folds).
The four facets are the four components of a commit, located at a name. **Rights** say which
facets a process holds at each name (`Rights`). A commit is **formed under** rights when each of
its components uses only facets held at the names it touches (`FormedUnder`). A process typed with
rights is a process all of whose commits are formed under them; a commit outside its rights is not
refused at run time, it is never formed.

## Each missing facet buys the law of its component, at the names where it is missing

The separations of the basis say which law each commit component breaks. Rights localize them:

* **Without `receive`, nothing leaves** (`restrict_subset_fireList_of_noReceive`): the occurrences
  at names where the process cannot receive survive every run of its commits.
* **Without `send`, nothing arrives** (`restrict_fireList_subset_of_noSend`).
* **Without `observe`, arrivals only help** (`Executable.frame_of_noObserve`): a run stays
  executable when occurrences arrive at names the process cannot observe, and ends with them
  added. Absence at those names is undetectable.
* **With `send` alone, the process is blind** (`blind_of_sendOnly`): two stores that agree outside
  the names where the process holds no facet but `send` run its commits alike, given that the
  identities it makes are allocated apart from both stores. Writing to a name teaches nothing
  about it.

Each law fails when the facet is granted: a receiver removes (`Controls.receiver_removes`), and an
observer of the lock's name is disabled by the lock's arrival (`Controls.observer_disabled`).

Formation implies scoping to the names where some facet is held (`FormedUnder.scoped`), so the
non-interference, garbage and stable-read laws of channel addressing apply to typed processes.

## Formation from the text

When region keys name the channel they lie at (`KeyNaming`), the facets a transform needs can be
read off its static footprint (`StaticFormed`, decidable), and every commit the transform fires is
then formed (`formedUnder_of_staticFormed`). A key that names no channel, such as the key of a
pattern variable in the channel position, needs a facet at no particular name, and formation
refuses it: receiving on an arbitrary channel is a formation error, not a run-time refusal
(`Controls.wildcard_not_formed`, `Controls.thief_not_formed`, `Controls.receiver_formed`).

## Learning facets: authority is passed, never created

Occurrences may carry facets (`carries`), as capabilities. A process **learns** the facets carried
by what it takes, keeps or sees in a predicate query (`Commit.learnedFrom`, as names are learned in
`ScopeExtrusion`), and a commit **attenuates** when everything it makes carries only facets the
process holds. For a system of processes taking formed, attenuating steps, the total authority,
the facets held by some process or carried by some occurrence, never grows
(`AuthorityStep.authority_mono`, `AuthorityRun.authority_mono`). So when no process holds and no
occurrence carries `receive` at a name, no step of the system ever takes from it
(`AuthorityRun.never_receives`). A commit that forges a capability breaks the bound
(`Controls.forging_grows_authority`). A one-process authority run is a dynamic run of
`OccurrenceCommits.ScopeExtrusion` over the names where a facet is held, and a dynamic run is an
authority run exactly when its commits make only names held before them
(`RegionPermissions.AuthorityRun.dynamicRun`, `RegionPermissions.authorityRun_iff_dynamicRun`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uO uR uN uV uT uP uK uI

/-- The four ways of using a name. -/
inductive Facet where
  | send
  | receive
  | peek
  | observe
  deriving DecidableEq, Repr

/-- Rights: which facets are held at each name. -/
abbrev Rights (N : Type uN) := N → Facet → Bool

section Formation

variable {O : Type uO} [DecidableEq O] {R : Type uR} {N : Type uN}

/-- **A commit formed under rights**: it takes only where it may receive, keeps only where it may
peek, makes only where it may send, and queries only regions where it may observe. -/
structure FormedUnder (label : O → R) (loc : R → N) (Γ : Rights N) (c : Commit O R) : Prop where
  taken : ∀ o ∈ c.taken, Γ (loc (label o)) .receive = true
  kept : ∀ o ∈ c.kept, Γ (loc (label o)) .peek = true
  made : ∀ o ∈ c.made, Γ (loc (label o)) .send = true
  queries : ∀ read ∈ c.queries, ∀ r, read.region r = true → Γ (loc r) .observe = true

/-- The names at which some facet is held. -/
def holdsSome (Γ : Rights N) (n : N) : Bool :=
  Γ n .send || Γ n .receive || Γ n .peek || Γ n .observe

variable {label : O → R} {loc : R → N} {Γ : Rights N}

omit [DecidableEq O] in
/-- **A formed commit is scoped** to the names where some facet is held. -/
theorem FormedUnder.scoped {c : Commit O R} (formed : FormedUnder label loc Γ c) :
    Scoped label loc (holdsSome Γ) c where
  taken o member := by simp [holdsSome, formed.taken o member]
  kept o member := by simp [holdsSome, formed.kept o member]
  made o member := by simp [holdsSome, formed.made o member]
  queries read member r inRegion := by simp [holdsSome, formed.queries read member r inRegion]

/-- **Non-interference for typed processes**: stores that agree on the names where the process
holds a facet run its formed commits alike. -/
theorem noninterference_of_formed {run : List (Commit O R)}
    (formed : ∀ e ∈ run, FormedUnder label loc Γ e) {first second : Finset O}
    (agree : restrict label loc (holdsSome Γ) first = restrict label loc (holdsSome Γ) second) :
    (Executable label first run ↔ Executable label second run) ∧
      restrict label loc (holdsSome Γ) (fireList first run) =
        restrict label loc (holdsSome Γ) (fireList second run) :=
  noninterference (fun e member => (formed e member).scoped) agree

/-! ### Missing receive: nothing leaves

A missing facet bounds what a formed commit writes (`FormedUnder.takesOutside`,
`FormedUnder.makesOutside`); the laws are then those of writes at a set of names
(`OccurrenceCommits.ChannelAddressing`), the frame law of regions. -/

omit [DecidableEq O] in
/-- Without `receive` at the names of `A`, a formed commit takes nothing there. -/
theorem FormedUnder.takesOutside {A : N → Bool} (noReceive : ∀ n, A n = true → Γ n .receive = false)
    {c : Commit O R} (formed : FormedUnder label loc Γ c) : TakesOutside label loc A c := by
  intro o taken
  cases atA : A (loc (label o))
  · rfl
  · have := formed.taken o taken
    rw [noReceive _ atA] at this
    exact absurd this (by decide)

omit [DecidableEq O] in
/-- Without `send` at the names of `A`, a formed commit makes nothing there. -/
theorem FormedUnder.makesOutside {A : N → Bool} (noSend : ∀ n, A n = true → Γ n .send = false)
    {c : Commit O R} (formed : FormedUnder label loc Γ c) : MakesOutside label loc A c := by
  intro o made
  cases atA : A (loc (label o))
  · rfl
  · have := formed.made o made
    rw [noSend _ atA] at this
    exact absurd this (by decide)

/-- Without `receive` at the names of `A`, a commit removes nothing there. -/
theorem restrict_subset_fire_of_noReceive {A : N → Bool}
    (noReceive : ∀ n, A n = true → Γ n .receive = false) {c : Commit O R}
    (formed : FormedUnder label loc Γ c) (S : Finset O) :
    restrict label loc A S ⊆ restrict label loc A (fire S c) :=
  restrict_subset_fire_of_takesOutside (formed.takesOutside noReceive) S

/-- **Without `receive`, nothing leaves**, along every run. -/
theorem restrict_subset_fireList_of_noReceive {A : N → Bool}
    (noReceive : ∀ n, A n = true → Γ n .receive = false) {run : List (Commit O R)}
    (formed : ∀ e ∈ run, FormedUnder label loc Γ e) (S : Finset O) :
    restrict label loc A S ⊆ restrict label loc A (fireList S run) :=
  restrict_subset_fireList_of_takesOutside (fun e member => (formed e member).takesOutside noReceive) S

/-! ### Missing send: nothing arrives -/

/-- Without `send` at the names of `A`, a commit adds nothing there. -/
theorem restrict_fire_subset_of_noSend {A : N → Bool}
    (noSend : ∀ n, A n = true → Γ n .send = false) {c : Commit O R}
    (formed : FormedUnder label loc Γ c) (S : Finset O) :
    restrict label loc A (fire S c) ⊆ restrict label loc A S :=
  restrict_fire_subset_of_makesOutside (formed.makesOutside noSend) S

/-- **Without `send`, nothing arrives**, along every run. -/
theorem restrict_fireList_subset_of_noSend {A : N → Bool}
    (noSend : ∀ n, A n = true → Γ n .send = false) {run : List (Commit O R)}
    (formed : ∀ e ∈ run, FormedUnder label loc Γ e) (S : Finset O) :
    restrict label loc A (fireList S run) ⊆ restrict label loc A S :=
  restrict_fireList_subset_of_makesOutside (fun e member => (formed e member).makesOutside noSend) S

/-! ### Missing observe: arrivals only help -/

omit [DecidableEq O] in
/-- An arrival at names where the commit cannot observe lies outside every region it queries. -/
theorem outside_queries_of_noObserve {A : N → Bool}
    (noObserve : ∀ n, A n = true → Γ n .observe = false) {c : Commit O R}
    (formed : FormedUnder label loc Γ c) {X : Finset O}
    (atA : ∀ o ∈ X, A (loc (label o)) = true) :
    ∀ read ∈ c.queries, ∀ o ∈ X, read.region (label o) = false := by
  intro read member o inX
  by_contra inRegion
  have observes := formed.queries read member (label o) (by simpa using inRegion)
  rw [noObserve _ (atA o inX)] at observes
  exact absurd observes (by decide)

/-- **Without `observe`, arrivals only help**: a run of formed commits stays executable when
occurrences arrive at names the process cannot observe, and ends with them added. -/
theorem Executable.frame_of_noObserve {A : N → Bool}
    (noObserve : ∀ n, A n = true → Γ n .observe = false) :
    ∀ {run : List (Commit O R)} {S X : Finset O}, (∀ e ∈ run, FormedUnder label loc Γ e) →
      Executable label S run → (∀ o ∈ X, A (loc (label o)) = true) → Disjoint S X →
      (∀ e ∈ run, Disjoint e.made X) →
      Executable label (S ∪ X) run ∧ fireList (S ∪ X) run = fireList S run ∪ X
  | [], _, _, _, _, _, _, _ => ⟨.nil _, rfl⟩
  | e :: rest, S, X, formed, executable, atA, apart, madeApart => by
      rw [executable_cons_iff] at executable
      obtain ⟨enabled, after⟩ := executable
      have formedE := formed e List.mem_cons_self
      have enabledFramed : Enabled label (S ∪ X) e :=
        enabled.frame (madeApart e List.mem_cons_self)
          (outside_queries_of_noObserve noObserve formedE atA)
      have takenApart : Disjoint e.taken X :=
        Finset.disjoint_of_subset_left enabled.taken_subset apart
      have nextApart : Disjoint (fire S e) X := by
        refine Finset.disjoint_left.mpr fun o inFire inX => ?_
        rcases mem_fire.mp inFire with ⟨inS, -⟩ | made
        · exact Finset.disjoint_left.mp apart inS inX
        · exact Finset.disjoint_left.mp (madeApart e List.mem_cons_self) made inX
      obtain ⟨afterFramed, endEq⟩ := Executable.frame_of_noObserve noObserve
        (fun d member => formed d (List.mem_cons_of_mem _ member)) after atA nextApart
        (fun d member => madeApart d (List.mem_cons_of_mem _ member))
      refine ⟨.cons enabledFramed ?_, ?_⟩
      · rw [fire_union_frame takenApart]
        exact afterFramed
      · simp only [fireList_cons]
        rw [fire_union_frame takenApart]
        exact endEq

/-! ### Send alone: blind -/

/-- The names where the process holds a facet other than `send`. -/
def sees (Γ : Rights N) (n : N) : Bool := Γ n .receive || Γ n .peek || Γ n .observe

omit [DecidableEq O] in
theorem sees_of_receive {n : N} (h : Γ n .receive = true) : sees Γ n = true := by simp [sees, h]

omit [DecidableEq O] in
theorem sees_of_peek {n : N} (h : Γ n .peek = true) : sees Γ n = true := by simp [sees, h]

omit [DecidableEq O] in
theorem sees_of_observe {n : N} (h : Γ n .observe = true) : sees Γ n = true := by simp [sees, h]

omit [DecidableEq O] in
/-- A formed commit with fresh identities apart from two stores is enabled at one exactly when at
the other, if the stores agree where the process sees. -/
theorem enabled_iff_of_agree_sees {c : Commit O R} (formed : FormedUnder label loc Γ c)
    {S S' : Finset O} (agree : restrict label loc (sees Γ) S = restrict label loc (sees Γ) S')
    (freshS : Disjoint c.made S) (freshS' : Disjoint c.made S') :
    Enabled label S c ↔ Enabled label S' c := by
  have transfer : ∀ {X Y : Finset O},
      restrict label loc (sees Γ) X = restrict label loc (sees Γ) Y → Disjoint c.made Y →
        Enabled label X c → Enabled label Y c := by
    intro X Y same freshY enabled
    refine ⟨fun o taken => ?_, fun o kept => ?_, enabled.apart, freshY, fun read member => ?_⟩
    · have inX := mem_restrict.mpr ⟨enabled.taken_subset taken, sees_of_receive (formed.taken o taken)⟩
      rw [same] at inX
      exact (mem_restrict.mp inX).1
    · have inX := mem_restrict.mpr ⟨enabled.kept_subset kept, sees_of_peek (formed.kept o kept)⟩
      rw [same] at inX
      exact (mem_restrict.mp inX).1
    · have holds := enabled.queries_hold read member
      have inside : ∀ r, read.region r = true → sees Γ (loc r) = true :=
        fun r inRegion => sees_of_observe (formed.queries read member r inRegion)
      unfold PredicateQuery.Holds at holds ⊢
      rw [← regionOf_restrict inside Y, ← same, regionOf_restrict inside X]
      exact holds
  exact ⟨transfer agree freshS', transfer agree.symm freshS⟩

/-- **With `send` alone, the process is blind**: two stores that agree where it holds a facet
other than `send` run its formed commits alike, given identities allocated apart from both stores,
and reach stores that agree there. -/
theorem blind_of_sendOnly :
    ∀ {run : List (Commit O R)} {S S' : Finset O}, (∀ e ∈ run, FormedUnder label loc Γ e) →
      run.Pairwise (fun d e => Disjoint d.made e.made) →
      (∀ e ∈ run, Disjoint e.made S ∧ Disjoint e.made S') →
      restrict label loc (sees Γ) S = restrict label loc (sees Γ) S' →
      (Executable label S run ↔ Executable label S' run) ∧
        restrict label loc (sees Γ) (fireList S run) = restrict label loc (sees Γ) (fireList S' run)
  | [], _, _, _, _, _, agree => ⟨⟨fun _ => .nil _, fun _ => .nil _⟩, agree⟩
  | e :: rest, S, S', formed, pairwise, allocated, agree => by
      have formedE := formed e List.mem_cons_self
      obtain ⟨freshS, freshS'⟩ := allocated e List.mem_cons_self
      have restFormed : ∀ d ∈ rest, FormedUnder label loc Γ d :=
        fun d member => formed d (List.mem_cons_of_mem _ member)
      have restPairwise := (List.pairwise_cons.mp pairwise).2
      have nextAllocated : ∀ d ∈ rest, Disjoint d.made (fire S e) ∧ Disjoint d.made (fire S' e) := by
        intro d member
        have apartE : Disjoint d.made e.made := ((List.pairwise_cons.mp pairwise).1 d member).symm
        obtain ⟨dS, dS'⟩ := allocated d (List.mem_cons_of_mem _ member)
        refine ⟨Finset.disjoint_left.mpr fun o made inFire => ?_,
          Finset.disjoint_left.mpr fun o made inFire => ?_⟩
        · rcases mem_fire.mp inFire with ⟨inS, -⟩ | madeE
          · exact Finset.disjoint_left.mp dS made inS
          · exact Finset.disjoint_left.mp apartE made madeE
        · rcases mem_fire.mp inFire with ⟨inS, -⟩ | madeE
          · exact Finset.disjoint_left.mp dS' made inS
          · exact Finset.disjoint_left.mp apartE made madeE
      have nextAgree : restrict label loc (sees Γ) (fire S e) = restrict label loc (sees Γ) (fire S' e) := by
        unfold fire
        rw [restrict_union, restrict_union, restrict_sdiff, restrict_sdiff, agree]
      obtain ⟨sameRun, sameEnd⟩ :=
        blind_of_sendOnly restFormed restPairwise nextAllocated nextAgree
      refine ⟨?_, sameEnd⟩
      rw [executable_cons_iff, executable_cons_iff,
        enabled_iff_of_agree_sees formedE agree freshS freshS', sameRun]

end Formation

/-! ## Formation from the text -/

section Static

variable {O : Type uO} [DecidableEq O] {V : Type uV} {T : Type uT} {P : Type uP} {K : Type uK}
  {N : Type uN}

/-- **Keys that name their channel**: a key naming `n` covers only values located at `n`. A key
naming no channel (`none`) is one whose values may lie anywhere. -/
structure KeyNaming (R : RegionKeys T P K) (loc : T → N) where
  nameOf : K → Option N
  sound : ∀ k t n, nameOf k = some n → R.covers k t → loc t = n

variable {R : RegionKeys T P K} {loc : T → N}

/-- Every key of a list names a channel at which the facet is held. -/
def keysHold (naming : KeyNaming R loc) (Γ : Rights N) (f : Facet) (ks : List K) : Bool :=
  ks.all fun k => match naming.nameOf k with
    | some n => Γ n f
    | none => false

/-- **A footprint type formed under rights**, read off the text. -/
def StaticFormed (naming : KeyNaming R loc) (Γ : Rights N) (st : StaticFootprint K) : Prop :=
  keysHold naming Γ .receive st.takes = true ∧ keysHold naming Γ .peek st.keeps = true ∧
    keysHold naming Γ .send st.makes = true ∧ keysHold naming Γ .observe st.queries = true

instance (naming : KeyNaming R loc) (Γ : Rights N) (st : StaticFootprint K) :
    Decidable (StaticFormed naming Γ st) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem facet_of_keysHold {naming : KeyNaming R loc} {Γ : Rights N} {f : Facet} {ks : List K}
    (hold : keysHold naming Γ f ks = true) {t : T} (covered : R.CoveredBy ks t) :
    Γ (loc t) f = true := by
  obtain ⟨k, member, covers⟩ := covered
  have := List.all_eq_true.mp hold k member
  revert this
  cases named : naming.nameOf k with
  | none => simp
  | some n =>
      intro held
      rw [naming.sound k t n named covers]
      exact held

/-- **Formation from the text is sound**: when the static footprint of a transform is formed
under rights, every commit the transform fires is formed under them. -/
theorem formedUnder_of_staticFormed {L : TermLayer V T P} {m : Matcher V T P} {label : O → T}
    (sound : Matcher.Sound L m) (keysSound : R.Sound L) (naming : KeyNaming R loc) {Γ : Rights N}
    {t : Transform V T P} (formed : StaticFormed naming Γ (t.static R)) {S : Finset O}
    {c : Commit O T} (fires : Fires L m label S t c) : FormedUnder label loc Γ c := by
  obtain ⟨x, member, -, commit⟩ := fires
  have within := static_covers sound keysSound member
  obtain ⟨takes, keeps, makes, reads⟩ := formed
  refine ⟨fun o taken => ?_, fun o kept => ?_, fun o made => ?_, fun read inQueries r inRegion => ?_⟩
  · rw [commit.taken] at taken
    exact facet_of_keysHold takes (within.takes o (Multiset.mem_toFinset.mp taken))
  · rw [commit.kept] at kept
    exact facet_of_keysHold keeps (within.keeps o (Multiset.mem_toFinset.mp kept))
  · exact facet_of_keysHold makes (commit.made_covered within made)
  · exact facet_of_keysHold reads (within.queries read ((commit.queries read).mp inQueries) r inRegion)

end Static

/-! ## Learning facets: authority is passed, never created -/

section Authority

variable {O : Type uO} [DecidableEq O] {R : Type uR} {N : Type uN} {I : Type uI} [DecidableEq I]
  (label : O → R) (loc : R → N) (carries : R → Rights N)

/-- What a commit teaches its process: the facets carried by what it takes, keeps or sees in a
predicate query (`Commit.learnedFrom`, the occurrences from which `ScopeExtrusion.learned` learns
names). -/
def learned (c : Commit O R) : Rights N :=
  fun n f => decide (∃ o ∈ c.learnedFrom, carries (label o) n f = true)

/-- **A commit attenuates** under rights: everything it makes carries only facets held. -/
def Attenuates (Γ : Rights N) (c : Commit O R) : Prop :=
  ∀ o ∈ c.made, ∀ n f, carries (label o) n f = true → Γ n f = true

/-- **The authority of a system**: a facet is held by some process or carried by some occurrence. -/
def Authority (Γ : I → Rights N) (S : Finset O) (n : N) (f : Facet) : Prop :=
  (∃ i, Γ i n f = true) ∨ ∃ o ∈ S, carries (label o) n f = true

/-- One step of a system: process `i` fires a commit formed under its rights and attenuating, and
learns what the commit teaches. -/
structure AuthorityStep (Γ : I → Rights N) (S : Finset O) (i : I) (c : Commit O R)
    (Γ' : I → Rights N) (S' : Finset O) : Prop where
  enabled : Enabled label S c
  formed : FormedUnder label loc (Γ i) c
  attenuates : Attenuates label carries (Γ i) c
  rights : Γ' = Function.update Γ i (fun n f => Γ i n f || learned label carries c n f)
  store : S' = fire S c

variable {label loc carries}

/-- **One step creates no authority.** -/
theorem AuthorityStep.authority_mono {Γ Γ' : I → Rights N} {S S' : Finset O} {i : I}
    {c : Commit O R} (step : AuthorityStep label loc carries Γ S i c Γ' S') {n : N} {f : Facet}
    (after : Authority label carries Γ' S' n f) : Authority label carries Γ S n f := by
  rcases after with ⟨j, held⟩ | ⟨o, inS', carried⟩
  · rw [step.rights] at held
    by_cases same : j = i
    · subst same
      rw [Function.update_self] at held
      rcases Bool.or_eq_true _ _ |>.mp held with old | new
      · exact Or.inl ⟨j, old⟩
      · obtain ⟨o, used, carried⟩ := of_decide_eq_true new
        exact Or.inr ⟨o, step.enabled.learnedFrom_subset used, carried⟩
    · rw [Function.update_of_ne same] at held
      exact Or.inl ⟨j, held⟩
  · rw [step.store] at inS'
    rcases mem_fire.mp inS' with ⟨inS, -⟩ | made
    · exact Or.inr ⟨o, inS, carried⟩
    · exact Or.inl ⟨i, step.attenuates o made n f carried⟩

/-- A run of a system: a sequence of steps, each by some process. -/
inductive AuthorityRun : (I → Rights N) → Finset O → List (I × Commit O R) → (I → Rights N) →
    Finset O → Prop
  | nil (Γ : I → Rights N) (S : Finset O) : AuthorityRun Γ S [] Γ S
  | cons {Γ Γ' Γ'' : I → Rights N} {S S' S'' : Finset O} {i : I} {c : Commit O R}
      {rest : List (I × Commit O R)}
      (step : AuthorityStep label loc carries Γ S i c Γ' S')
      (after : AuthorityRun Γ' S' rest Γ'' S'') : AuthorityRun Γ S ((i, c) :: rest) Γ'' S''

/-- **A run creates no authority.** -/
theorem AuthorityRun.authority_mono {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (r : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S')
    {n : N} {f : Facet} (after : Authority label carries Γ' S' n f) :
    Authority label carries Γ S n f := by
  induction r with
  | nil => exact after
  | cons step _ ih => exact step.authority_mono (ih after)

/-- **No receive without the receive facet**: when no process holds and no occurrence carries
`receive` at a name, no step of a run takes from it. -/
theorem AuthorityRun.never_receives {Γ Γ' : I → Rights N} {S S' : Finset O}
    {run : List (I × Commit O R)}
    (r : AuthorityRun (label := label) (loc := loc) (carries := carries) Γ S run Γ' S') {n : N}
    (unheld : ¬ Authority label carries Γ S n .receive) :
    ∀ x ∈ run, ∀ o ∈ x.2.taken, loc (label o) ≠ n := by
  induction r with
  | nil => simp
  | @cons Γ₀ Γ₁ Γ₂ S₀ S₁ S₂ i c rest step after ih =>
      intro x member o taken atN
      rcases List.mem_cons.mp member with rfl | inRest
      · have held := step.formed.taken o taken
        rw [atN] at held
        exact unheld (Or.inl ⟨i, held⟩)
      · refine ih (fun later => unheld ?_) x inRest o taken atN
        exact step.authority_mono later

end Authority

/-! ## Controls -/

namespace Controls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Controls

/-- Names are the atoms themselves. -/
def atomName : Atom → Atom := id

/-- The rights of a process that may receive the token and send outputs. -/
def receiverRights : Rights Atom
  | .tok, .receive => true
  | .out, .send => true
  | _, _ => false

/-- **Granting `receive` breaks "nothing leaves"**: the taker of the token is formed under rights
that receive it, and its firing removes the token. -/
theorem receiver_removes :
    FormedUnder label atomName receiverRights taker ∧
      ¬ restrict label atomName (fun a => a == .tok) {0} ⊆
        restrict label atomName (fun a => a == .tok) (fire {0} taker) := by
  refine ⟨⟨?_, ?_, ?_, ?_⟩, by decide⟩
  · intro o member
    simp only [taker, Finset.mem_singleton] at member
    subst member
    rfl
  · simp [taker]
  · intro o member
    simp only [taker, Finset.mem_singleton] at member
    subst member
    rfl
  · simp [taker]

/-- The rights of a process that observes the lock's name and sends outputs. -/
def observerRights : Rights Atom
  | .lock, .observe => true
  | .out, .send => true
  | _, _ => false

/-- **Granting `observe` breaks "arrivals only help"**: the commit guarded by the absence of a
lock is formed under rights that observe the lock's name, and a lock's arrival disables it. -/
theorem observer_disabled :
    FormedUnder label atomName observerRights unlessLocked ∧ Enabled label {0} unlessLocked ∧
      ¬ Enabled label ({0} ∪ {1}) unlessLocked := by
  refine ⟨⟨by simp [unlessLocked], by simp [unlessLocked], ?_, ?_⟩, absence_holds_empty,
    absence_not_framed⟩
  · intro o member
    simp only [unlessLocked, Finset.mem_singleton] at member
    subst member
    rfl
  · intro read member r inRegion
    simp only [unlessLocked, List.mem_singleton] at member
    subst member
    cases r <;> simp_all [isLock, observerRights, atomName]

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Controls

/-- In the source controls, the channel of a value is its head symbol. -/
def headName : Tm Sig → Sig := Tm.head

/-- Head and prefix keys name the channel of their head; the key of a variable names none. -/
def headNaming : KeyNaming headR headName where
  nameOf
    | .any => none
    | .head f => some f
    | .prefix f _ => some f
  sound k t n named covers := by
    cases k with
    | any => simp at named
    | head f =>
        simp only [Option.some.injEq] at named
        subst named
        exact covers
    | «prefix» f g =>
        simp only [Option.some.injEq] at named
        subst named
        obtain ⟨l, r, rfl, -⟩ := covers
        rfl

/-- Rights to send on `tok` only. -/
def sendTok : Rights Sig
  | .tok, .send => true
  | _, _ => false

/-- Rights to receive on `tok`. -/
def receiveTok : Rights Sig
  | .tok, .receive => true
  | _, _ => false

/-- **A thief is refused at formation**: taking a `tok` needs `receive` at `tok`, and send rights
do not give it. -/
theorem thief_not_formed : ¬ StaticFormed headNaming sendTok (takeTok.static headR) := by decide

/-- **The receiver is formed**, and so is every commit it fires. -/
theorem receiver_formed : StaticFormed headNaming receiveTok (takeTok.static headR) := by decide

theorem receiver_commits_formed {S : Finset Occ} {c : Commit Occ (Tm Sig)}
    (fires : Fires Lc mc lbl S takeTok c) : FormedUnder lbl headName receiveTok c :=
  formedUnder_of_staticFormed cmatch_sound (headKeys_sound bagComm) headNaming receiver_formed fires

/-- Take any value: a pattern variable in the channel position. -/
def takeAny : Transform ℕ (Tm Sig) (Pat ℕ Sig) := ⟨.cons (.take (.var 0)) .done, []⟩

/-- Every right at every name. -/
def allRights : Rights Sig := fun _ _ => true

/-- **Receiving on an arbitrary channel is a formation error**, even with every right at every
name: its key names no channel. -/
theorem wildcard_not_formed : ¬ StaticFormed headNaming allRights (takeAny.static headR) := by
  decide

/-- Occurrence `1` carries the right to receive at the token's name. -/
def capCarries : Atom → Rights Atom
  | .lock, .tok, .receive => true
  | _, _, _ => false

/-- Process `0` holds the right to send outputs only. -/
def senderOnly : Bool → Rights Atom
  | false, .out, .send => true
  | _, _, _ => false

/-- Make a lock, which carries the right to receive at the token's name. -/
def forge : Commit ℕ Atom := ⟨∅, ∅, {1}, []⟩

/-- **Forging grows authority**: a commit that makes a capability its process does not hold is
not attenuating, and after it the right to receive at the token's name exists where it did not. -/
theorem forging_grows_authority :
    ¬ Attenuates label capCarries (senderOnly false) forge ∧
      ¬ Authority label capCarries senderOnly (∅ : Finset ℕ) .tok .receive ∧
      Authority label capCarries senderOnly (fire ∅ forge) .tok .receive := by
  refine ⟨fun att => ?_, ?_, Or.inr ⟨1, by decide, rfl⟩⟩
  · have := att 1 (by simp [forge]) .tok .receive rfl
    exact absurd this (by decide)
  · rintro (⟨i, held⟩ | ⟨o, member, -⟩)
    · cases i <;> exact absurd held (by decide)
    · simp at member

/-- Rights to receive at the token's name, and nothing else. -/
def receiverAtTok : Rights Atom
  | .tok, .receive => true
  | _, _ => false

/-- **Attenuates, positive**: making a lock, which carries the right to receive at the token's
name, attenuates for a process that holds that right. (`forging_grows_authority` contains the
negative control.) -/
theorem forge_attenuates_for_holder : Attenuates label capCarries receiverAtTok forge := by
  intro o member n f carried
  simp only [forge, Finset.mem_singleton] at member
  subst member
  cases n <;> cases f <;> simp_all [capCarries, receiverAtTok, label]

end Controls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes
