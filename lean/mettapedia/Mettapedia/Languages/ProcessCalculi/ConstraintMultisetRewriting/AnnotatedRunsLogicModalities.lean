import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogic
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsOmega

/-!
# Modalities along runs: dynamic and tense logic of histories, and ω-runs with fairness

## Along one run

For a run `p`, reindexing `p*` is "after `p`". For one run, necessity and possibility along `p`
coincide with `p*`, since a run extends each history in exactly one way. Its two adjoints are the
past modalities of the doctrine of histories: `∃_p ⊣ p* ⊣ ∀_p`. A Hoare triple `{φ} p {ψ}` is
`φ ≤ p* ψ`, equivalently `∃_p φ ≤ ψ`: the strongest postcondition lies in `ψ`
(`single_hoare_iff`); and `p* ψ ≤ φ` is `ψ ≤ ∀_p φ` (`single_after_le_iff`).

## Along a program

A program `R` is a set of runs between each pair of classes. On families of history predicates:

* `nec R ψ` (`[R] ψ`): every run of `R` extends the history into `ψ`;
* `poss R ψ` (`⟨R⟩ ψ`): some run of `R` does;
* `post R φ`: the histories that end with a run of `R` and began in `φ` (strongest postcondition);
* `pre R φ`: the histories all of whose decompositions ending with a run of `R` began in `φ`.

Two adjunctions hold for every program (`post_le_iff`, `poss_le_iff`), and a Hoare triple over a
program is either side of the first one (`hoare_iff_le_nec`, `hoare_iff_post_le`). When the
program contains the empty runs and is closed under sequencing (`Program.Closed`), `[R]` is an
interior operator (`nec_le`, `nec_le_nec_nec`, `nec_inf`) and `⟨R⟩` a closure operator
(`le_poss`, `poss_poss_le`); the fixed points of `[R]` are the predicates every run of `R`
carries into themselves. For the program of all runs, `[R]` is the `henceforth` and `post` the `once` of
`AnnotatedRunsLogic` (`nec_allRuns`, `post_allRuns`), and the fixed points of `[R]` are the
persistent predicates of the run topos.

* positive control: `ModalityControls.reader_never_fires_in_taker_program`: along the runs that
  fire only the taker,
  "the reader has not fired" holds henceforth from the start;
* negative control: `ModalityControls.reader_can_fire`: along all runs it does not.

**Invariants, quantifying over predicates** (`hoare_iff_exists_invariant`,
`post_eq_sInf_invariants`): for a closed program a Hoare triple holds exactly when some invariant
lies between the precondition and the postcondition, and the strongest postcondition is the meet of
all invariants above the precondition. The invariants of all runs are the persistent predicates of
the run topos (`invariant_allRuns_iff`).

## Double negation: always possibly

Double negation is stable under substitution in any indexed Heyting algebra (`reindex_compl_compl`),
so it is a Lawvere–Tierney topology of the doctrine. On histories it reads "every extension can be
extended into the predicate" (`forces_compl_compl_iff`). It is not the identity: "the taker fired,
or it never can" fails at the empty history and holds always possibly
(`ModalityControls.settled_always_possible`, `ModalityControls.doubleNegation_ne_id`).

## Along ω-runs

For a transition system: `AlwaysAll`, `EventuallyAll` (every ω-run from a state), and their
fair versions `AlwaysFair`, `EventuallyFair` (every ω-run strongly fair for every task).

* **Always of a property of states does not see fairness** (`alwaysAll_iff`, `alwaysFair_iff`,
  `alwaysFair_iff_alwaysAll`): with an idle step both are invariance of the reachable states.
  For the candidate step: `candidate_alwaysFair_iff_alwaysAll`.
* **Eventually does** (`TakerProgram.eventually_fair_taken`, `TakerProgram.not_eventually_taken`):
  in the program of the taker with an idle step, along every strongly fair ω-run from the start
  the occurrence the taker consumes is eventually gone; idling forever keeps it.
* **Always of a response property does** (`TakerProgram.fair_responds`,
  `TakerProgram.idling_not_responds`): "whenever the taker is admitted it later fires" holds along
  every strongly fair ω-run and fails along idling.
* **Fairness is relative to the program** (`OpenStepControls.open_step_not_eventually_taken`): in
  the open candidate step a teller can tell `X = 1`, after which the taker is refused for ever, so a
  strongly fair ω-run need not consume the occurrence.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.CategoryTheory.PredicateDoctrine
open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)

/-! ## One run -/

section Single

universe uB vB

variable {B : Type uB} [Category.{vB} B] (root : B)

/-- **A Hoare triple along one run is the strongest postcondition below the postcondition.** -/
theorem single_hoare_iff {x y : B} (p : x ⟶ y) (φ : Set (root ⟶ x)) (ψ : Set (root ⟶ y)) :
    φ ≤ (historyDoctrine root).reindex p ψ ↔ (historyFirstOrder root).existsAlong p φ ≤ ψ :=
  ((historyFirstOrder root).exists_adj p φ ψ).symm

/-- **"After `p`" lies below `φ` exactly when `ψ` lies below necessity along `p` in the past.** -/
theorem single_after_le_iff {x y : B} (p : x ⟶ y) (φ : Set (root ⟶ x)) (ψ : Set (root ⟶ y)) :
    (historyDoctrine root).reindex p ψ ≤ φ ↔ ψ ≤ (historyFirstOrder root).forallAlong p φ :=
  (historyFirstOrder root).forall_adj p ψ φ

end Single

/-! ## Programs -/

section Programs

universe uB vB

variable {B : Type uB} [Category.{vB} B] {root : B}

/-- A program: a set of runs between each pair of stages. -/
abbrev Program (B : Type uB) [Category.{vB} B] := ∀ x y : B, Set (x ⟶ y)

/-- A predicate of the doctrine of histories at every stage. -/
abbrev Family (root : B) := ∀ y : B, Set (root ⟶ y)

/-- **A Hoare triple over a program**: every run of the program carries `φ` into `ψ`. -/
def Hoare (R : Program B) (φ ψ : Family root) : Prop :=
  ∀ ⦃x y : B⦄ (p : x ⟶ y), p ∈ R x y → φ x ≤ (historyDoctrine root).reindex p (ψ y)

/-- **Necessity along a program**: every run of the program extends the history into `ψ`. -/
def nec (R : Program B) (ψ : Family root) : Family root :=
  fun x => {h | ∀ ⦃y : B⦄ (p : x ⟶ y), p ∈ R x y → h ≫ p ∈ ψ y}

/-- **Possibility along a program**: some run of the program extends the history into `ψ`. -/
def poss (R : Program B) (ψ : Family root) : Family root :=
  fun x => {h | ∃ (y : B) (p : x ⟶ y), p ∈ R x y ∧ h ≫ p ∈ ψ y}

/-- **The strongest postcondition**: histories that end with a run of the program and began in
`φ`. -/
def post (R : Program B) (φ : Family root) : Family root :=
  fun y => {k | ∃ (x : B) (h : root ⟶ x) (p : x ⟶ y), p ∈ R x y ∧ h ∈ φ x ∧ h ≫ p = k}

/-- **Necessity in the past**: every way of ending with a run of the program began in `φ`. -/
def pre (R : Program B) (φ : Family root) : Family root :=
  fun y => {k | ∀ (x : B) (h : root ⟶ x) (p : x ⟶ y), p ∈ R x y → h ≫ p = k → h ∈ φ x}

variable (R : Program B)

theorem hoare_iff_le_nec (φ ψ : Family root) : Hoare R φ ψ ↔ φ ≤ nec R ψ :=
  ⟨fun hoare _ _ member _ p inR => hoare p inR member,
    fun below x _ p inR _ member => below x member p inR⟩

theorem post_le_iff (φ ψ : Family root) : post R φ ≤ ψ ↔ φ ≤ nec R ψ :=
  ⟨fun below x h member y p inR => below y ⟨x, h, p, inR, member, rfl⟩,
    fun below y k => by
      rintro ⟨x, h, p, inR, member, rfl⟩
      exact below x member p inR⟩

theorem hoare_iff_post_le (φ ψ : Family root) : Hoare R φ ψ ↔ post R φ ≤ ψ :=
  (hoare_iff_le_nec R φ ψ).trans (post_le_iff R φ ψ).symm

theorem poss_le_iff (φ ψ : Family root) : poss R φ ≤ ψ ↔ φ ≤ pre R ψ :=
  ⟨fun below y k member x h p inR same => below x ⟨y, p, inR, same ▸ member⟩,
    fun below x h => by
      rintro ⟨y, p, inR, member⟩
      exact below y member x h p inR rfl⟩

theorem nec_mono {ψ ψ' : Family root} (below : ψ ≤ ψ') : nec R ψ ≤ nec R ψ' :=
  fun _ _ holds _ p inR => below _ (holds p inR)

theorem nec_inf (ψ ψ' : Family root) : nec R (ψ ⊓ ψ') = nec R ψ ⊓ nec R ψ' := by
  funext x
  ext h
  exact ⟨fun holds => ⟨fun _ p inR => (holds p inR).1, fun _ p inR => (holds p inR).2⟩,
    fun holds _ p inR => ⟨holds.1 p inR, holds.2 p inR⟩⟩

/-- A program with the empty runs, closed under sequencing. -/
structure Program.Closed : Prop where
  id_mem : ∀ x : B, 𝟙 x ∈ R x x
  comp_mem : ∀ {x y z : B} {p : x ⟶ y} {q : y ⟶ z}, p ∈ R x y → q ∈ R y z → p ≫ q ∈ R x z

variable {R}

theorem nec_le (closed : Program.Closed R) (ψ : Family root) : nec R ψ ≤ ψ := fun x h holds => by
  have now := holds (𝟙 x) (closed.id_mem x)
  rwa [Category.comp_id] at now

theorem nec_le_nec_nec (closed : Program.Closed R) (ψ : Family root) :
    nec R ψ ≤ nec R (nec R ψ) := fun _ h holds _ p inR _ q inR' => by
  rw [Category.assoc]
  exact holds (p ≫ q) (closed.comp_mem inR inR')

theorem le_poss (closed : Program.Closed R) (ψ : Family root) : ψ ≤ poss R ψ := fun x h member =>
  ⟨x, 𝟙 x, closed.id_mem x, by rwa [Category.comp_id]⟩

theorem poss_poss_le (closed : Program.Closed R) (ψ : Family root) :
    poss R (poss R ψ) ≤ poss R ψ := fun _ h => by
  rintro ⟨y, p, inR, z, q, inR', member⟩
  rw [Category.assoc] at member
  exact ⟨z, p ≫ q, closed.comp_mem inR inR', member⟩

/-- **The fixed points of necessity are the families every run of the program carries into
themselves.** -/
theorem le_nec_iff_hoare (ψ : Family root) : ψ ≤ nec R ψ ↔ Hoare R ψ ψ :=
  (hoare_iff_le_nec R ψ ψ).symm

/-- **Possibility is the dual of necessity** in the Boolean doctrine of histories. -/
theorem poss_eq_compl_nec_compl (ψ : Family root) :
    poss R ψ = fun x => (nec R (fun y => (ψ y)ᶜ) x)ᶜ := by
  funext x
  ext h
  constructor
  · rintro ⟨y, p, inR, member⟩ holds
    exact holds p inR member
  · intro notAll
    by_contra none
    apply notAll
    intro y p inR member
    exact none ⟨y, p, inR, member⟩

/-- **The invariance rule, quantifying over predicates, is sound and complete for closed
programs**: a Hoare triple holds exactly when some invariant of the program lies between the
precondition and the postcondition. The weakest such invariant is `nec R ψ`. -/
theorem hoare_iff_exists_invariant (closed : Program.Closed R) (φ ψ : Family root) :
    Hoare R φ ψ ↔ ∃ I : Family root, φ ≤ I ∧ Hoare R I I ∧ I ≤ ψ := by
  constructor
  · intro hoare
    exact ⟨nec R ψ, (hoare_iff_le_nec R φ ψ).mp hoare,
      (hoare_iff_le_nec R _ _).mpr (nec_le_nec_nec closed ψ), nec_le closed ψ⟩
  · rintro ⟨I, pre, invariant, postI⟩ x y p inR h member
    exact postI y (invariant p inR (pre x member))

/-- **The strongest postcondition along a closed program is the least invariant above the
precondition**: the meet of all invariants that contain it. -/
theorem post_eq_sInf_invariants (closed : Program.Closed R) (φ : Family root) :
    post R φ = sInf {I : Family root | φ ≤ I ∧ Hoare R I I} := by
  refine le_antisymm (le_sInf ?_) (sInf_le ⟨?_, ?_⟩)
  · rintro I ⟨pre, invariant⟩
    exact (post_le_iff R φ I).mpr ((hoare_iff_le_nec R φ I).mp fun x y p inR h member =>
      invariant p inR (pre x member))
  · intro x h member
    exact ⟨x, h, 𝟙 x, closed.id_mem x, member, Category.comp_id h⟩
  · intro x y p inR k
    rintro ⟨w, h, q, inR', member, rfl⟩
    exact ⟨w, h, q ≫ p, closed.comp_mem inR' inR, member, (Category.assoc h q p).symm⟩

/-- All runs. -/
def allRuns : Program B := fun _ _ => Set.univ

theorem allRuns_closed : Program.Closed (allRuns (B := B)) :=
  ⟨fun _ => Set.mem_univ _, fun _ _ => Set.mem_univ _⟩

end Programs

/-! ## Programs of the candidate step -/

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section RunPrograms

variable {A : SubstitutionAction T S} {label : O → T} {C₀ : Configuration T O}

/-- **Necessity along all runs is henceforth.** -/
theorem nec_allRuns (φ : Family (runObject A label C₀)) (x : Runs A label) :
    nec allRuns φ x = restrict (henceforth φ) x := by
  ext h
  exact ⟨fun holds _ p => holds p (Set.mem_univ _), fun holds _ p _ => holds p⟩

/-- **The strongest postcondition along all runs is once.** -/
theorem post_allRuns (φ : Family (runObject A label C₀)) (y : Runs A label) :
    post allRuns φ y = restrict (once φ) y := by
  ext k
  exact ⟨fun ⟨x, h, p, _, member, same⟩ => ⟨x, h, p, member, same⟩,
    fun ⟨x, h, p, member, same⟩ => ⟨x, h, p, Set.mem_univ _, member, same⟩⟩

variable (A label)

/-- **The runs that fire only firings of `F`.** -/
def runsOf (F : Set (Firing T S O)) : Program (Runs A label) :=
  fun _ _ => {p | ∀ f ∈ OccurrencePath.sites p, f ∈ F}

theorem runsOf_closed (F : Set (Firing T S O)) : Program.Closed (runsOf A label F) := by
  refine ⟨fun _ _ member => (by cases member), ?_⟩
  intro _ _ _ p q inP inQ f member
  rcases (mem_sites_comp p q f).mp member with first | second
  · exact inP f first
  · exact inQ f second

/-- **The invariants of the program of all runs are the persistent predicates of the run
topos.** -/
theorem invariant_allRuns_iff {A : SubstitutionAction T S} {label : O → T} {C₀ : Configuration T O}
    (φ : Family (runObject A label C₀)) :
    Hoare allRuns φ φ ↔ ∃ P : Persistent A label C₀, ∀ y, restrict P y = φ y :=
  ⟨fun hoare => (persistent_iff φ).mpr fun _ _ p => hoare p (Set.mem_univ _),
    fun persistent _ _ p _ => (persistent_iff φ).mp persistent p⟩

end RunPrograms

/-! ## Double negation: always possibly -/

section DoubleNegation

universe uB' vB' wB'

variable {B' : Type uB'} [Category.{vB'} B']

/-- Substitution preserves negation in any indexed Heyting algebra. -/
theorem reindex_compl (D : IndexedHeyting.{uB', vB', wB'} B') {X Y : B'} (f : X ⟶ Y)
    (φ : D.Fiber Y) : D.reindex f φᶜ = (D.reindex f φ)ᶜ := by
  rw [← himp_bot, D.reindex_himp, D.reindex_bot, himp_bot]

/-- **Double negation is stable under substitution**, so with `le_compl_compl`,
`compl_compl_compl` and `compl_compl_inf_distrib` it is a Lawvere–Tierney topology of the
doctrine. -/
theorem reindex_compl_compl (D : IndexedHeyting.{uB', vB', wB'} B') {X Y : B'} (f : X ⟶ Y)
    (φ : D.Fiber Y) : D.reindex f φᶜᶜ = (D.reindex f φ)ᶜᶜ := by
  rw [reindex_compl, reindex_compl]

end DoubleNegation

section RunDoubleNegation

variable {A : SubstitutionAction T S} {label : O → T} {C₀ : Configuration T O}

/-- **Double negation on histories is "always possibly"**: every extension of the history can be
extended into the predicate. -/
theorem forces_compl_compl_iff (P : Persistent A label C₀) {x : Runs A label}
    (h : runObject A label C₀ ⟶ x) :
    h ∈ restrict Pᶜᶜ x ↔
      ∀ ⦃y : Runs A label⦄ (p : x ⟶ y), ∃ (z : Runs A label) (q : y ⟶ z),
        (h ≫ p) ≫ q ∈ restrict P z := by
  rw [forces_compl_iff]
  refine forall_congr' fun y => forall_congr' fun p => ?_
  rw [forces_compl_iff]
  push Not
  rfl

end RunDoubleNegation

/-! ## ω-runs -/

section Omega

open MeTTaCalculus.OccurrenceCommits.Liveness (LTS Run MachineClosed machineClosed_stronglyFair)

universe uSt uL uI

variable {St : Type uSt} {L : Type uL} (sys : LTS St L)

/-- **Always, along every ω-run** from `s₀`. -/
def AlwaysAll (s₀ : St) (P : St → Prop) : Prop :=
  ∀ r : Run sys, r.state 0 = s₀ → ∀ n, P (r.state n)

/-- **Eventually, along every ω-run** from `s₀`. -/
def EventuallyAll (s₀ : St) (P : St → Prop) : Prop :=
  ∀ r : Run sys, r.state 0 = s₀ → ∃ n, P (r.state n)

/-- **Always, along every strongly fair ω-run** from `s₀`. -/
def AlwaysFair {ι : Type uI} (tasks : ι → L → Prop) (s₀ : St) (P : St → Prop) : Prop :=
  ∀ r : Run sys, (∀ i, r.StronglyFair (tasks i)) → r.state 0 = s₀ → ∀ n, P (r.state n)

/-- **Eventually, along every strongly fair ω-run** from `s₀`. -/
def EventuallyFair {ι : Type uI} (tasks : ι → L → Prop) (s₀ : St) (P : St → Prop) : Prop :=
  ∀ r : Run sys, (∀ i, r.StronglyFair (tasks i)) → r.state 0 = s₀ → ∃ n, P (r.state n)

/-- **Whenever the task is admitted, it later fires.** -/
def Responds (r : Run sys) (task : L → Prop) : Prop :=
  ∀ n, sys.TaskEnabled task (r.state n) → ∃ m ≥ n, task (r.label m)

variable {sys}

/-- **Always along all ω-runs is invariance of the reachable states**, for a system that never
blocks. -/
theorem alwaysAll_iff (nb : sys.NonBlocking) (s₀ : St) (P : St → Prop) :
    AlwaysAll sys s₀ P ↔ ∀ s, sys.Reachable s₀ s → P s := by
  have closed := machineClosed_stronglyFair (sys := sys) (fun (i : Empty) => i.elim) nb s₀
  rw [← MachineClosed.invariant_iff closed P]
  exact ⟨fun holds r _ start => holds r start, fun holds r start => holds r (fun i => i.elim) start⟩

/-- **Always along strongly fair ω-runs is invariance of the reachable states**, for finitely many
tasks of a system that never blocks. -/
theorem alwaysFair_iff {ι : Type uI} [Fintype ι] [DecidableEq ι] (tasks : ι → L → Prop)
    (nb : sys.NonBlocking) (s₀ : St) (P : St → Prop) :
    AlwaysFair sys tasks s₀ P ↔ ∀ s, sys.Reachable s₀ s → P s :=
  MachineClosed.invariant_iff (machineClosed_stronglyFair tasks nb s₀) P

/-- **Always does not see fairness.** -/
theorem alwaysFair_iff_alwaysAll {ι : Type uI} [Fintype ι] [DecidableEq ι] (tasks : ι → L → Prop)
    (nb : sys.NonBlocking) (s₀ : St) (P : St → Prop) :
    AlwaysFair sys tasks s₀ P ↔ AlwaysAll sys s₀ P :=
  (alwaysFair_iff tasks nb s₀ P).trans (alwaysAll_iff nb s₀ P).symm

/-- Eventually along all ω-runs implies eventually along the fair ones. -/
theorem EventuallyAll.fair {ι : Type uI} (tasks : ι → L → Prop) {s₀ : St} {P : St → Prop}
    (all : EventuallyAll sys s₀ P) : EventuallyFair sys tasks s₀ P :=
  fun r _ start => all r start

end Omega

section Candidate

open MeTTaCalculus.OccurrenceCommits.Liveness (LTS Run)

variable (A : SubstitutionAction T S) (label : O → T)

/-- **For the candidate step, always along strongly fair ω-runs is always along all ω-runs**, both
taken with the idle step. -/
theorem candidate_alwaysFair_iff_alwaysAll {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : ι → Firing T S O → Prop) (C : Configuration T O) (P : Configuration T O → Prop) :
    AlwaysFair (candidateLTS A label).withIdle (fun i => LTS.liftTask (tasks i)) C P ↔
      AlwaysAll (candidateLTS A label).withIdle C P :=
  alwaysFair_iff_alwaysAll _ (LTS.withIdle_nonBlocking _) C P

end Candidate

/-! ## Controls -/

namespace ModalityControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start taker_valid)
open AnnotatedRuns.LogicControls (taker_then_reader_split)

/-- "The reader has not fired." -/
def readerNotFired : Family (runObject A label start) :=
  fun _ => {p | reader ∉ OccurrencePath.sites p}

/-- **Positive control: along the runs that fire only the taker, the reader never fires.** -/
theorem reader_never_fires_in_taker_program :
    𝟙 (runObject A label start) ∈ nec (runsOf A label {taker}) readerNotFired
      (runObject A label start) := by
  intro y p onlyTaker fired
  have isTaker : reader = taker :=
    onlyTaker reader ((mem_sites_comp (𝟙 (runObject A label start)) p reader).mp fired |>.elim
      (fun member => by cases member) id)
  exact AnnotationControls.taker_ne_reader isTaker.symm

/-- **Negative control: along all runs, the reader can fire.** -/
theorem reader_can_fire :
    𝟙 (runObject A label start) ∉ nec allRuns readerNotFired (runObject A label start) := by
  intro holds
  obtain ⟨m, first, second, firstSites, secondSites⟩ := taker_then_reader_split
  apply holds (first ≫ second) (Set.mem_univ _)
  refine (mem_sites_comp (𝟙 (runObject A label start)) (first ≫ second) reader).mpr (Or.inr ?_)
  refine (mem_sites_comp first second reader).mpr (Or.inr ?_)
  exact (congrArg (fun l => reader ∈ l) secondSites).mpr (List.mem_singleton_self _)

/-- **Every history can be extended to settle whether the taker fires**: double negation of
"the taker fired, or it never can" holds everywhere. -/
theorem settled_always_possible :
    (LogicControls.takerFired ⊔ LogicControls.takerFiredᶜ)ᶜᶜ = (⊤ : Persistent A label start) := by
  rw [compl_sup, inf_compl_self, compl_bot]

/-- **Double negation is not the identity on the run topos**: "the taker fired, or it never can"
fails at the empty history and holds always possibly. -/
theorem doubleNegation_ne_id :
    (LogicControls.takerFired ⊔ LogicControls.takerFiredᶜ)ᶜᶜ ≠
      (LogicControls.takerFired ⊔ LogicControls.takerFiredᶜ : Persistent A label start) := by
  rw [settled_always_possible]
  exact fun same => LogicControls.excluded_middle_fails same.symm

/-- Double negation keeps the false predicate false. -/
theorem doubleNegation_bot : (⊥ : Persistent A label start)ᶜᶜ = ⊥ := by
  rw [compl_bot, compl_top]

end ModalityControls

namespace TakerProgram

open MeTTaCalculus.OccurrenceCommits.Liveness (LTS Run)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker start taker_valid)

/-- **The program of the taker**: the candidate step restricted to the taker. -/
def system : LTS (Configuration (Term signature) Nat) Run where
  Allowed C f := f = taker ∧ f.Valid A label C
  next C f := f.result label C

/-- The task of the taker, with the idle step outside it. -/
abbrev takerTask : Option Run → Prop := LTS.liftTask (· = taker)

/-- Idling forever at the start. -/
def idling : Run system.withIdle where
  state _ := start
  label _ := none
  allowed _ := trivial
  step _ := rfl

theorem zero_at_start : 0 ∈ start.present := by decide

theorem taker_takes_zero : 0 ∉ (taker.result label start).present := by decide

/-- While the taker does not fire, the program idles and the state stays put. -/
theorem stays (r : Run system.withIdle) (n : ℕ)
    (quiet : ∀ k, n ≤ k → r.label k ≠ some taker) : ∀ k, r.state (n + k) = r.state n := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
      have step := r.step (n + k)
      have allowed := r.allowed (n + k)
      cases labelled : r.label (n + k) with
      | none =>
          rw [labelled] at step
          rw [← Nat.add_assoc, step]
          exact ih
      | some f =>
          rw [labelled] at allowed
          obtain ⟨rfl, -⟩ := allowed
          exact absurd labelled (quiet (n + k) (Nat.le_add_right n k))

/-- **Always of a response property sees fairness (positive): along every ω-run strongly fair for
the taker, whenever the taker is admitted it later fires.** -/
theorem fair_responds (r : Run system.withIdle) (fair : r.StronglyFair takerTask) :
    Responds system.withIdle r takerTask := by
  intro n enabled
  by_contra never
  have quiet : ∀ k, n ≤ k → r.label k ≠ some taker := by
    intro k le fires
    exact never ⟨k, le, by rw [fires]; rfl⟩
  have often : ∀ N, ∃ k ≥ N, system.withIdle.TaskEnabled takerTask (r.state k) := by
    intro N
    refine ⟨n + N, by omega, ?_⟩
    rw [stays r n quiet N]
    exact enabled
  obtain ⟨k, le, fires⟩ := fair often n
  cases labelled : r.label k with
  | none => rw [labelled] at fires; exact fires
  | some f =>
      rw [labelled] at fires
      exact quiet k le (by rw [labelled, fires])

/-- **Always of a response property sees fairness (negative): idling forever never responds.** -/
theorem idling_not_responds : ¬ Responds system.withIdle idling takerTask := by
  intro responds
  obtain ⟨m, -, fires⟩ := responds 0 ⟨some taker, rfl, rfl, taker_valid⟩
  exact fires

/-- **Eventually sees fairness (positive): along every strongly fair ω-run from the start, the
occurrence the taker consumes is eventually gone.** -/
theorem eventually_fair_taken :
    EventuallyFair system.withIdle (fun (_ : Unit) => takerTask) start
      (fun C => 0 ∉ C.present) := by
  intro r fair start0
  obtain ⟨m, -, fires⟩ := fair_responds r (fair ()) 0
    (by rw [start0]; exact ⟨some taker, rfl, rfl, taker_valid⟩)
  classical
  let first := Nat.find (⟨m, fires⟩ : ∃ k, takerTask (r.label k))
  have firstFires : takerTask (r.label first) := Nat.find_spec (⟨m, fires⟩ : ∃ k, takerTask (r.label k))
  have before : ∀ k, 0 ≤ k → k < first → r.label k ≠ some taker := fun k _ lt same =>
    Nat.find_min (⟨m, fires⟩ : ∃ k, takerTask (r.label k)) lt (by rw [same]; rfl)
  have atFirst : r.state first = start := by
    have unchanged : ∀ k, k ≤ first → r.state k = r.state 0 := by
      intro k
      induction k with
      | zero => exact fun _ => rfl
      | succ k ih =>
          intro le
          have step := r.step k
          have allowed := r.allowed k
          cases labelled : r.label k with
          | none =>
              rw [labelled] at step
              rw [step]
              exact ih (by omega)
          | some f =>
              rw [labelled] at allowed
              obtain ⟨rfl, -⟩ := allowed
              exact absurd labelled (before k (Nat.zero_le k) (by omega))
    rw [unchanged first le_rfl, start0]
  refine ⟨first + 1, ?_⟩
  have step := r.step first
  cases labelled : r.label first with
  | none => rw [labelled] at firstFires; exact absurd firstFires id
  | some f =>
      rw [labelled] at firstFires
      change f = taker at firstFires
      rw [step, labelled, atFirst, firstFires]
      exact taker_takes_zero

/-- **Eventually sees fairness (negative): idling forever keeps the occurrence.** -/
theorem not_eventually_taken :
    ¬ EventuallyAll system.withIdle start (fun C => 0 ∉ C.present) := by
  intro all
  obtain ⟨n, gone⟩ := all idling rfl
  exact gone zero_at_start

/-- **Always of a property of states does not see fairness** in the program of the taker. -/
theorem taker_always_fair_iff (P : Configuration (Term signature) Nat → Prop) :
    AlwaysFair system.withIdle (fun (_ : Unit) => takerTask) start P ↔
      AlwaysAll system.withIdle start P :=
  alwaysFair_iff_alwaysAll _ (LTS.withIdle_nonBlocking _) start P

end TakerProgram

namespace OpenStepControls

open MeTTaCalculus.OccurrenceCommits.Liveness (LTS Run)
open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker start taker_valid teller ones)

theorem teller_valid_start : teller.Valid A label start := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide, ⟨ones, ?_⟩, by simp [teller]⟩,
    by simp [teller]⟩
  intro equation member
  have same : equation = (.var 0, .const 1) := by
    simpa [Selection.problem, Selection.equations, start, teller] using member
  subst same
  rfl

/-- **After the teller the taker is refused**: its pattern `f(0)` needs `X = 0`, and the store
says `X = 1`. -/
theorem taker_refused_after_teller : ¬ taker.Valid A label (teller.result label start) := by
  intro valid
  obtain ⟨σ, solved⟩ := valid.firing.consistent
  have told := solved ((.var 0, .const 1) : Term signature × Term signature) (by
    simp [Selection.problem, Selection.equations, Firing.result, Selection.result, teller, start])
  have taken := solved ((ConstraintMultisetRewriting.Controls.f (.const 0), label 0) :
      Term signature × Term signature) (by
    simp [Selection.problem, Selection.equations, taker])
  change σ 0 = (Term.const 1 : Term signature) at told
  change (Term.app () (fun _ => Term.const 0) : Term signature) = Term.app () (fun _ => σ 0) at taken
  have pointwise := congrFun (eq_of_heq (Term.app.inj taken).2) ⟨0, by decide⟩
  change (Term.const 0 : Term signature) = σ 0 at pointwise
  rw [told] at pointwise
  exact absurd (Term.const.inj pointwise) (by decide)

/-- The teller, then idling for ever. -/
def tellThenIdle : Run (candidateLTS A label).withIdle :=
  Run.cons start (some teller) teller_valid_start
    { state := fun _ => teller.result label start
      label := fun _ => none
      allowed := fun _ => trivial
      step := fun _ => rfl }
    rfl

/-- Telling `X = 1` and idling is strongly fair for the taker: from then on the taker is never
admitted. -/
theorem tellThenIdle_fair : tellThenIdle.StronglyFair (LTS.liftTask (· = taker)) := by
  intro often
  exfalso
  obtain ⟨n, le, ⟨a, inTask, allowed⟩⟩ := often 1
  cases a with
  | none => exact inTask
  | some f =>
      change f = taker at inTask
      subst inTask
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      exact taker_refused_after_teller allowed

/-- **Fairness is relative to the program (negative): in the open candidate step another firing
can disable the taker for ever.** Along the strongly fair ω-run of the teller and then idling, the
occurrence the taker would consume stays. -/
theorem open_step_not_eventually_taken :
    ¬ EventuallyFair (candidateLTS A label).withIdle (fun (_ : Unit) => LTS.liftTask (· = taker))
      start (fun C => 0 ∉ C.present) := by
  intro eventually
  obtain ⟨n, gone⟩ := eventually tellThenIdle (fun _ => tellThenIdle_fair) rfl
  cases n with
  | zero => exact gone (by decide)
  | succ m =>
      change 0 ∉ (teller.result label start).present at gone
      exact gone (by decide)

end OpenStepControls

#print axioms single_hoare_iff
#print axioms single_after_le_iff
#print axioms hoare_iff_le_nec
#print axioms post_le_iff
#print axioms hoare_iff_post_le
#print axioms poss_le_iff
#print axioms nec_inf
#print axioms nec_le
#print axioms nec_le_nec_nec
#print axioms le_poss
#print axioms poss_poss_le
#print axioms le_nec_iff_hoare
#print axioms poss_eq_compl_nec_compl
#print axioms hoare_iff_exists_invariant
#print axioms post_eq_sInf_invariants
#print axioms nec_allRuns
#print axioms post_allRuns
#print axioms invariant_allRuns_iff
#print axioms runsOf_closed
#print axioms reindex_compl
#print axioms reindex_compl_compl
#print axioms forces_compl_compl_iff
#print axioms alwaysAll_iff
#print axioms alwaysFair_iff
#print axioms alwaysFair_iff_alwaysAll
#print axioms candidate_alwaysFair_iff_alwaysAll
#print axioms ModalityControls.reader_never_fires_in_taker_program
#print axioms ModalityControls.reader_can_fire
#print axioms ModalityControls.settled_always_possible
#print axioms ModalityControls.doubleNegation_ne_id
#print axioms ModalityControls.doubleNegation_bot
#print axioms TakerProgram.taker_takes_zero
#print axioms TakerProgram.fair_responds
#print axioms TakerProgram.idling_not_responds
#print axioms TakerProgram.eventually_fair_taken
#print axioms TakerProgram.not_eventually_taken
#print axioms TakerProgram.taker_always_fair_iff
#print axioms OpenStepControls.taker_refused_after_teller
#print axioms OpenStepControls.tellThenIdle_fair
#print axioms OpenStepControls.open_step_not_eventually_taken

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
