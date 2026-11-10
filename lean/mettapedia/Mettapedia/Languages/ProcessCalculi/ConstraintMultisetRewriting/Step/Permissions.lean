import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.Spaces
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.InteractionTypes.Facets

/-!
# Permissions on the step: restrictions of firings by rights at spaces

Rights are the existing ones of `InteractionTypes.Facets`, held per space handle: `receive` permits
takes, `peek` reads, `send` makes, `observe` predicate queries (`Rights`, `FormedUnder`). A firing
is **permitted** when its commit is formed under the rights (`Permitted`); the permitted step is
the restriction of the step to such firings (`permitted`), for every instance of the interface.

## A firing without the right is refused (any instance)

`refused_without_receive`, `refused_without_peek`, `refused_without_send`. Along every permitted run,
a space where `receive` is missing only grows (`fiber_mono_without_receive`), one where `send` is
missing only shrinks (`fiber_anti_without_send`).

## The permission modules of the MeTTa calculus, placed

Every permitted run is an executable commit word whose commits are formed under the rights
(`commits_formed`), so `InteractionTypes.noninterference_of_formed` applies to it: **a permitted run
does not depend on the spaces where it holds no right** (`permitted_noninterference`).

## Read polarity: owned and shared reads (the located first-order step)

* **Universal reads need the others to lack `send`.** An absence entailed at a space stays entailed
  after any admitted firing formed under rights without `send` there (`owned_absence_preserved`);
  with `send`, one make spoils it (`Controls.shared_absence_spoiled`), and without it that make is
  refused (`Controls.owned_make_refused`).
* **Existential reads need the others to lack `receive`.** A witness at a space stays present
  after any formed firing without `receive` there (`owned_witness_present`); with `receive`, it is
  taken and the read is refused (`Controls.shared_witness_taken`).

## Tickets: the escape of the runtime's grant lineage, at the step

A **ticketed** firing takes a ticket at the space `t` for every row it makes at the space `h`, and
makes no ticket (`Ticketed`). On every run of every instance restricted to ticketed firings, the rows
made at `h` and the tickets left number at most the tickets at the start (`made_le_tickets`). The
runtime's escape was a grant that dropped its ticket requirement. At the step, rights alone permit
unboundedly many rows at `h` with no ticket at all (`Controls.rights_alone_unbounded`), while the
ticketed restriction permits none from a state without tickets (`Controls.ticketed_blocks`). The
requirement is a restriction of the firings at the space, so no holder of a right can drop it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Permissions

open Interface (Frames)
open MeTTaCalculus.OccurrenceCommits (Commit Enabled fire mem_fire Executable fireList)
open MeTTaCalculus.InteractionTypes (Facet Rights FormedUnder holdsSome noninterference_of_formed)
open Spaces (fiber mem_fiber commits run_executable toRun run_allowed spaces_fire commitAt)

/-! ## Permitted firings (any instance) -/

section Generic

universe uO uT uH uOcc uS uF uN

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH}
  {X : Frames Tm Hom} {O : Type uOcc} [DecidableEq O] {State : Type uS} {Firing : State → Type uF}
  (P : Interface.Step X O State Firing) {H : Type uN} (space : O → H) (Γ : Rights H)

/-- **A firing permitted by rights**: it takes only where it may `receive`, reads only where it may
`peek` and makes only where it may `send`. -/
def Permitted {s : State} (f : Firing s) : Prop :=
  FormedUnder space id Γ ((P.selection f).commit (T := H))

/-- **The permitted step**: the restriction of the step to the permitted firings. -/
abbrev permitted := Spaces.restrict P (fun {_} f => Permitted P space Γ f)

theorem refused_without_receive {s : State} {f : Firing s} {o : O} (taken : o ∈ (P.selection f).taken)
    (denied : Γ (space o) .receive = false) : ¬ (permitted P space Γ).Admits f := by
  rintro ⟨-, formed⟩
  have allowed := formed.taken o (by simpa [Selection.commit] using taken)
  simp [denied] at allowed

theorem refused_without_peek {s : State} {f : Firing s} {o : O} (read : o ∈ (P.selection f).read)
    (denied : Γ (space o) .peek = false) : ¬ (permitted P space Γ).Admits f := by
  rintro ⟨-, formed⟩
  have allowed := formed.kept o (by simpa [Selection.commit] using read)
  simp [denied] at allowed

theorem refused_without_send {s : State} {f : Firing s} {o : O} (made : o ∈ (P.selection f).made)
    (denied : Γ (space o) .send = false) : ¬ (permitted P space Γ).Admits f := by
  rintro ⟨-, formed⟩
  have allowed := formed.made o (by simpa [Selection.commit] using made)
  simp [denied] at allowed

/-- The commits of a permitted run are formed under the rights. -/
theorem commits_formed : ∀ {s : State} (r : (permitted P space Γ).Run s),
    ∀ e ∈ commits (H := H) (permitted P space Γ) r, FormedUnder space id Γ e
  | _, .nil _, _, member => by simp [commits] at member
  | _, .cons f admitted rest, e, member => by
      rcases List.mem_cons.mp member with rfl | member
      · exact admitted.2
      · exact commits_formed rest e member

/-- **A permitted run does not depend on the spaces where it holds no right**: from any store that
agrees with its first present occurrences at the held spaces, its commits run and reach a store that
agrees with its last present occurrences there. -/
theorem permitted_noninterference {s : State} (r : (permitted P space Γ).Run s) {other : Finset O}
    (agree : MeTTaCalculus.OccurrenceCommits.restrict space id (holdsSome Γ) (P.present s) =
      MeTTaCalculus.OccurrenceCommits.restrict space id (holdsSome Γ) other) :
    Executable space other (commits (H := H) (permitted P space Γ) r) ∧
      MeTTaCalculus.OccurrenceCommits.restrict space id (holdsSome Γ) (P.present r.last) =
        MeTTaCalculus.OccurrenceCommits.restrict space id (holdsSome Γ)
          (fireList other (commits (H := H) (permitted P space Γ) r)) := by
  obtain ⟨executable, last⟩ := run_executable (permitted P space Γ) space r
  obtain ⟨same, after⟩ := noninterference_of_formed (commits_formed P space Γ r) agree
  refine ⟨same.mp executable, ?_⟩
  rw [← after]
  exact congrArg _ last.symm

variable [DecidableEq H]

/-- **Without `receive`, a space only grows** along every permitted run. -/
theorem fiber_mono_without_receive {h : H} (denied : Γ h .receive = false) :
    ∀ {s : State} (r : (permitted P space Γ).Run s),
      fiber space h (P.present s) ⊆ fiber space h (P.present r.last)
  | _, .nil _ => le_refl _
  | _, .cons f admitted rest => by
      refine subset_trans ?_ (fiber_mono_without_receive denied rest)
      intro o member
      obtain ⟨present, atH⟩ := (mem_fiber space).mp member
      refine (mem_fiber space).mpr ⟨?_, atH⟩
      show o ∈ P.present (P.result f admitted.1)
      rw [P.present_result f admitted.1]
      refine mem_fire.mpr (Or.inl ⟨present, fun taken => ?_⟩)
      have allowed := admitted.2.taken o taken
      simp [atH, denied] at allowed

/-- **Without `send`, a space only shrinks** along every permitted run. -/
theorem fiber_anti_without_send {h : H} (denied : Γ h .send = false) :
    ∀ {s : State} (r : (permitted P space Γ).Run s),
      fiber space h (P.present r.last) ⊆ fiber space h (P.present s)
  | _, .nil _ => le_refl _
  | _, .cons f admitted rest => by
      refine subset_trans (fiber_anti_without_send denied rest) ?_
      intro o member
      obtain ⟨present, atH⟩ := (mem_fiber space).mp member
      refine (mem_fiber space).mpr ⟨?_, atH⟩
      have fired : o ∈ P.present (P.result f admitted.1) := present
      rw [P.present_result f admitted.1] at fired
      rcases mem_fire.mp fired with ⟨old, _⟩ | made
      · exact old
      · have allowed := admitted.2.made o made
        simp [atH, denied] at allowed

/-! ## Tickets -/

/-- The rows a firing makes at the space `h`. -/
def madeAt (h : H) {s : State} (f : Firing s) : ℕ :=
  (fiber space h ((P.selection f).commit (T := H)).made).card

/-- The rows a firing takes at the space `t`. -/
def takenAt (t : H) {s : State} (f : Firing s) : ℕ :=
  (fiber space t ((P.selection f).commit (T := H)).taken).card

/-- **A ticketed firing** takes a ticket at `t` for every row it makes at `h`, and makes no ticket. -/
def Ticketed (h t : H) {s : State} (f : Firing s) : Prop :=
  madeAt P space h f ≤ takenAt P space t f ∧ ∀ o ∈ ((P.selection f).commit (T := H)).made, space o ≠ t

/-- The rows a run makes at the space `h`. -/
def madeAlong (h : H) : {s : State} → P.Run s → ℕ
  | _, .nil _ => 0
  | _, .cons f _ rest => madeAt P space h f + madeAlong h rest

/-- One admitted firing that makes no ticket removes exactly the tickets it takes. -/
theorem tickets_after {s : State} {f : Firing s} (admitted : P.Admits f) (t : H)
    (noTicket : ∀ o ∈ ((P.selection f).commit (T := H)).made, space o ≠ t) :
    (fiber space t (P.present (P.result f admitted))).card + takenAt P space t f =
      (fiber space t (P.present s)).card := by
  have enabled := Spaces.enabled_located space _ (P.prepares admitted).2.1
  have fired : P.present (P.result f admitted) = fire (P.present s) ((P.selection f).commit (T := H)) :=
    P.present_result f admitted
  have noMade : fiber space t ((P.selection f).commit (T := H)).made = ∅ := by
    ext o
    simp only [mem_fiber, Finset.notMem_empty, iff_false, not_and]
    exact noTicket o
  have result : fiber space t (P.present (P.result f admitted)) =
      fiber space t (P.present s) \ fiber space t ((P.selection f).commit (T := H)).taken := by
    rw [fired]
    have := spaces_fire space (P.present s) ((P.selection f).commit (T := H)) t
    simp only [Spaces.spaces] at this
    rw [this]
    simp only [fire, commitAt, noMade, Finset.union_empty]
  rw [result]
  apply Finset.card_sdiff_add_card_eq_card
  intro o member
  obtain ⟨taken, atT⟩ := (mem_fiber space).mp member
  exact (mem_fiber space).mpr ⟨enabled.taken_subset taken, atT⟩

/-- **Rows made at `h` are bounded by tickets at `t`** on every run of the ticketed restriction,
in every instance. -/
theorem made_le_tickets (h t : H) :
    ∀ {s : State} (r : (Spaces.restrict P (fun {_} f => Ticketed P space h t f)).Run s),
      madeAlong (Spaces.restrict P (fun {_} f => Ticketed P space h t f)) space h r +
          (fiber space t (P.present r.last)).card ≤ (fiber space t (P.present s)).card
  | _, .nil _ => (Nat.zero_add _).le
  | _, .cons f admitted rest => by
      have later := made_le_tickets h t rest
      have once := tickets_after P space admitted.1 t admitted.2.2
      have bound : madeAt P space h f ≤ takenAt P space t f := admitted.2.1
      change madeAt P space h f + madeAlong _ space h rest + (fiber space t (P.present rest.last)).card ≤ _
      change _ ≤ (fiber space t (P.present (P.result f admitted.1))).card at later
      omega

end Generic

/-! ## Read polarity on the located first-order step -/

section Located

universe uT uS uH uO

variable {T : Type uT} {S : Type uS} {H : Type uH} {O : Type uO} [DecidableEq O] [DecidableEq H]
  (A : SubstitutionAction T S) (space : O → H) (payload : O → T) (Γ : Rights H)

/-- A firing of the located step formed under rights. -/
def LocatedPermitted (f : AnnotatedRuns.Firing (H × T) S O) : Prop :=
  FormedUnder space id Γ (f.selection.commit (T := H))

omit [DecidableEq H] in
/-- **Owned universal reads are stable**: an absence entailed at a space stays entailed after any
admitted firing formed under rights without `send` at that space. -/
theorem owned_absence_preserved {C : Configuration (H × T) O} {f : AnnotatedRuns.Firing (H × T) S O}
    (admitted : (Spaces.located A space payload).Admits (s := C) f)
    (formed : LocatedPermitted space Γ f) {p : H × T} (owned : Γ p.1 .send = false)
    (absent : (LocatedSubstitution.action (N := H) A).Entails C.equations
      (fun σ => (Check.absent p).Holds (LocatedSubstitution.action (N := H) A) σ
        (Spaces.label space payload) C.present)) :
    (LocatedSubstitution.action (N := H) A).Entails
      ((Spaces.located A space payload).result f admitted).equations
      (fun σ => (Check.absent p).Holds (LocatedSubstitution.action (N := H) A) σ
        (Spaces.label space payload) ((Spaces.located A space payload).result f admitted).present) := by
  intro σ model o present same
  have earlier := admitted.firing.refines σ model
  rcases mem_fire.mp present with ⟨old, _⟩ | made
  · exact absent σ earlier o old same
  · have allowed := formed.made o made
    have atP : p.1 = space o := same.1
    simp [← atP, owned] at allowed

omit [DecidableEq H] in
/-- **Owned existential reads are stable**: a witness at a space stays present after any admitted
firing formed under rights without `receive` there. -/
theorem owned_witness_present {C : Configuration (H × T) O} {f : AnnotatedRuns.Firing (H × T) S O}
    (admitted : (Spaces.located A space payload).Admits (s := C) f)
    (formed : LocatedPermitted space Γ f) {o : O} (present : o ∈ C.present)
    (owned : Γ (space o) .receive = false) :
    o ∈ ((Spaces.located A space payload).result f admitted).present := by
  refine mem_fire.mpr (Or.inl ⟨present, fun taken => ?_⟩)
  have allowed := formed.taken o taken
  simp [owned] at allowed

end Located

/-! ## Controls -/

namespace Controls

open Mettapedia.Logic.LP
open Disequality.Controls (signature app X E_iff apply_X apply_const apply_app app_eq_app
  const_eq_const)
open Spaces (located label)

abbrev B := FirstOrder.action signature

/-- Row `0` is the witness `p(1)` at space `1`; every other row is `p(3)` at space `2`. Tickets
would be at space `3`; there are none. -/
def space : Nat → Nat
  | 0 => 1
  | _ => 2

def payload : Nat → Term signature
  | 0 => app 0 (.const 1)
  | _ => app 0 (.const 3)

abbrev L := (located B space payload).toStep
abbrev Fir := AnnotatedRuns.Firing (Nat × Term signature) (Subst signature) Nat

/-- The other party holds every right. -/
def shared : Rights Nat := fun _ _ => true

/-- The other party holds neither `send` at space `2` nor `receive` at space `1`. -/
def owned : Rights Nat
  | 2, .send => false
  | 1, .receive => false
  | _, _ => true

/-- Every firing is formed under `shared`. -/
theorem shared_formed (f : Fir) : LocatedPermitted space shared f :=
  ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ _ _ => rfl⟩

def start : Configuration (Nat × Term signature) Nat := ⟨[], {0}⟩

/-- Make row `k` at space `2`. -/
def makeRow (k : Nat) : Fir := ⟨⟨[], [], [], [], [(2, app 0 (.const 3))]⟩, [], ⟨[], [], [k]⟩⟩
/-- Take the witness at space `1`. -/
def takeWitness : Fir := ⟨⟨[(1, app 0 (.const 1))], [], [], [], []⟩, [], ⟨[0], [], []⟩⟩
/-- Read the witness at space `1`. -/
def readWitness : Fir := ⟨⟨[], [(1, app 0 (.const 1))], [], [], []⟩, [], ⟨[], [0], []⟩⟩

/-- The absence of `p(3)` at space `2`. -/
def absentThree : Check (Nat × Term signature) := .absent (2, app 0 (.const 3))

theorem makeRow_admitted (C : Configuration (Nat × Term signature) Nat) (k : Nat)
    (equations : C.equations = []) (fresh : k ∉ C.present) (positive : k ≠ 0) :
    L.Admits (s := C) (makeRow k) :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, by
      cases k with
      | zero => exact absurd rfl positive
      | succ k => rfl,
      ⟨by simp [makeRow, Selection.commit], by simp [makeRow, Selection.commit],
        by simp [makeRow, Selection.commit], by simpa [makeRow, Selection.commit] using fresh,
        by simp [Selection.commit]⟩,
      ⟨B.identity, by
        intro e member
        simp [makeRow, Selection.problem, Selection.equations, equations] at member⟩,
      by simp [makeRow]⟩

theorem start_absent :
    (LocatedSubstitution.action (N := Nat) B).Entails start.equations
      (fun σ => absentThree.Holds (LocatedSubstitution.action (N := Nat) B) σ (label space payload)
        start.present) := by
  intro σ _ o present same
  simp only [start, Finset.mem_singleton] at present
  subst present
  simp [label, space] at same

/-- **Shared: one make spoils the absence.** With `send` at space `2`, the make is permitted and the
absence of `p(3)` there is no longer entailed. -/
theorem shared_absence_spoiled :
    LocatedPermitted space shared (makeRow 1) ∧
      ¬ (LocatedSubstitution.action (N := Nat) B).Entails
        (L.result (makeRow 1) (makeRow_admitted start 1 rfl (by decide) (by decide))).equations
        (fun σ => absentThree.Holds (LocatedSubstitution.action (N := Nat) B) σ (label space payload)
          (L.result (makeRow 1) (makeRow_admitted start 1 rfl (by decide) (by decide))).present) := by
  refine ⟨shared_formed _, fun entailed => ?_⟩
  refine entailed B.identity ?_ 1 (by decide) (by simp [label, space, payload])
  intro e member
  change e ∈ (makeRow 1).selection.problem (label space payload) (makeRow 1).rule start at member
  simp [makeRow, Selection.problem, Selection.equations, start] at member

/-- **Owned: the make is refused.** Without `send` at space `2` the make is not permitted. -/
theorem owned_make_refused :
    ¬ (Permissions.permitted L space owned).Admits (s := start) (makeRow 1) :=
  refused_without_send L space owned (o := 1)
    (show 1 ∈ (makeRow 1).selection.made by simp [makeRow]) rfl

/-- **Owned: the absence survives every permitted firing of the other party.** -/
theorem owned_absence_survives {f : Fir} (admitted : L.Admits (s := start) f)
    (formed : LocatedPermitted space owned f) :
    (LocatedSubstitution.action (N := Nat) B).Entails (L.result f admitted).equations
      (fun σ => absentThree.Holds (LocatedSubstitution.action (N := Nat) B) σ (label space payload)
        (L.result f admitted).present) :=
  owned_absence_preserved B space payload owned admitted formed (p := (2, app 0 (.const 3))) rfl
    start_absent

theorem takeWitness_admitted : L.Admits (s := start) takeWitness :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨B.identity, by
      intro e member
      simp [takeWitness, Selection.problem, Selection.equations, start, label] at member
      subst member
      simp [SubstitutionAction.Solves, space, payload]⟩, by simp [takeWitness]⟩

theorem readWitness_admitted : L.Admits (s := start) readWitness :=
  (PredicateQueryAdmission.valid_empty_iff _ _ _ _ _).mpr
    ⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨B.identity, by
      intro e member
      simp [readWitness, Selection.problem, Selection.equations, start, label] at member
      subst member
      simp [SubstitutionAction.Solves, space, payload]⟩, by simp [readWitness]⟩

/-- **Shared: the witness is taken and the read is refused.** With `receive` at space `1`, taking
the witness is permitted; afterwards the read of it is refused. -/
theorem shared_witness_taken :
    LocatedPermitted space shared takeWitness ∧ L.Admits (s := start) readWitness ∧
      ¬ L.Admits (s := L.result takeWitness takeWitness_admitted) readWitness :=
  ⟨shared_formed _, readWitness_admitted,
    fun admitted => absurd admitted.firing.occurrences.kept_subset (by decide)⟩

/-- **Owned: the witness cannot be taken**, and survives every permitted firing. -/
theorem owned_witness_kept :
    ¬ (Permissions.permitted L space owned).Admits (s := start) takeWitness ∧
      ∀ {f : Fir} (admitted : L.Admits (s := start) f), LocatedPermitted space owned f →
        0 ∈ (L.result f admitted).present :=
  ⟨refused_without_receive L space owned (o := 0)
      (show 0 ∈ takeWitness.selection.taken by simp [takeWitness]) rfl,
    fun admitted formed => owned_witness_present B space payload owned admitted formed
      (by simp [start]) rfl⟩

/-! ### Tickets -/

theorem makeRow_result_equations (C : Configuration (Nat × Term signature) Nat) (k : Nat)
    (equations : C.equations = []) : ((makeRow k).result (label space payload) C).equations = [] := by
  change (makeRow k).selection.problem (label space payload) (makeRow k).rule C = []
  simp [makeRow, Selection.problem, Selection.equations, equations]

theorem makeRow_result_fresh (C : Configuration (Nat × Term signature) Nat) (n : Nat)
    (fresh : ∀ k, n < k → k ∉ C.present) :
    ∀ k, n + 1 < k → k ∉ ((makeRow (n + 1)).result (label space payload) C).present := by
  intro k bigger present
  change k ∈ fire C.present ((makeRow (n + 1)).selection.commit (T := Nat × Term signature)) at present
  rcases mem_fire.mp present with ⟨old, _⟩ | made
  · exact fresh k (by omega) old
  · simp [makeRow, Selection.commit] at made
    omega

/-- Rows `n + 1`, `n + 2`, … made one by one, each permitted by `send` at space `2`. -/
def rowsRun : (m n : Nat) → (C : Configuration (Nat × Term signature) Nat) → C.equations = [] →
    (∀ k, n < k → k ∉ C.present) → (Permissions.permitted L space shared).Run C
  | 0, _, C, _, _ => .nil C
  | m + 1, n, C, equations, fresh =>
      .cons (makeRow (n + 1))
        ⟨makeRow_admitted C (n + 1) equations (fresh (n + 1) (by omega)) (by omega),
          shared_formed _⟩
        (rowsRun m (n + 1) ((makeRow (n + 1)).result (label space payload) C)
          (makeRow_result_equations C (n + 1) equations) (makeRow_result_fresh C n fresh))

theorem madeAt_makeRow (C : Configuration (Nat × Term signature) Nat) (n : Nat) :
    madeAt (Permissions.permitted L space shared) space 2 (s := C) (makeRow (n + 1)) = 1 := by
  have atTwo : space (n + 1) = 2 := rfl
  change (fiber space 2 [n + 1].toFinset).card = 1
  simp [fiber, Finset.filter_singleton, atTwo]

theorem rowsRun_made : ∀ (m n : Nat) (C : Configuration (Nat × Term signature) Nat)
    (equations : C.equations = []) (fresh : ∀ k, n < k → k ∉ C.present),
    madeAlong (Permissions.permitted L space shared) space 2 (rowsRun m n C equations fresh) = m
  | 0, _, _, _, _ => rfl
  | m + 1, n, C, equations, fresh => by
      have rest := rowsRun_made m (n + 1) ((makeRow (n + 1)).result (label space payload) C)
        (makeRow_result_equations C (n + 1) equations) (makeRow_result_fresh C n fresh)
      change madeAt (Permissions.permitted L space shared) space 2 (makeRow (n + 1)) +
        madeAlong (Permissions.permitted L space shared) space 2
          (rowsRun m (n + 1) ((makeRow (n + 1)).result (label space payload) C)
            (makeRow_result_equations C (n + 1) equations) (makeRow_result_fresh C n fresh)) = m + 1
      rw [madeAt_makeRow C n, rest]
      omega

/-- **Rights alone do not bound rows**: for every `m`, a run permitted by `send` at space `2` makes
`m` rows there, with no ticket anywhere. -/
theorem rights_alone_unbounded (m : Nat) :
    ∃ r : (Permissions.permitted L space shared).Run start,
      madeAlong (Permissions.permitted L space shared) space 2 r = m ∧
        fiber space 3 start.present = ∅ := by
  have fresh : ∀ k, 0 < k → k ∉ start.present := by
    intro k positive present
    simp only [start, Finset.mem_singleton] at present
    omega
  exact ⟨rowsRun m 0 start rfl fresh, rowsRun_made m 0 start rfl fresh, by decide⟩

/-- **The ticketed restriction blocks it**: without tickets at space `3`, no run of ticketed firings
makes a row at space `2`. -/
theorem ticketed_blocks
    (r : (Spaces.restrict L (fun {s} f => Ticketed L space 2 3 (s := s) f)).Run start) :
    madeAlong (Spaces.restrict L (fun {s} f => Ticketed L space 2 3 (s := s) f)) space 2 r = 0 := by
  have bound := made_le_tickets L space 2 3 r
  have empty : fiber space 3 (L.present start) = ∅ := by decide
  rw [empty, Finset.card_empty] at bound
  omega

#print axioms refused_without_receive
#print axioms refused_without_peek
#print axioms refused_without_send
#print axioms commits_formed
#print axioms permitted_noninterference
#print axioms fiber_mono_without_receive
#print axioms fiber_anti_without_send
#print axioms tickets_after
#print axioms made_le_tickets
#print axioms owned_absence_preserved
#print axioms owned_witness_present
#print axioms shared_absence_spoiled
#print axioms owned_make_refused
#print axioms owned_absence_survives
#print axioms shared_witness_taken
#print axioms owned_witness_kept
#print axioms rights_alone_unbounded
#print axioms ticketed_blocks

end Controls

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Permissions
