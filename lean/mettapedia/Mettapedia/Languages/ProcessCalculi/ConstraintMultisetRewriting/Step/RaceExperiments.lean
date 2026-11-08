import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSpectrum

/-!
# The experimenter: intervention between firings

A spectator sees completed runs: their traces and their answer bags (`RacePair.rung_one_blind`).
An **experimenter** also acts: between firings it adds atoms to the space, and it watches what the
system does next, including that it does nothing.

* **Interventions** (`addAtom`): adding an occurrence to the present ones, knowledge unchanged. The
  experimenter adds only at the program's **ports** (`ports`), the boundary of the open system; with
  every occurrence a port, it could also inject the atoms the program uses internally.
* **The intervened step** (`openSystem`): labelled moves of the program, and one move `add o` per
  port. **Open bisimilarity** (`OpenBisimilar`) is its bisimilarity; it implies the bisimilarity of
  the closed step (`bisimilar_of_openBisimilar`).
* **The experimenter's readout** (`Readout`): the sequences of observations an experiment can
  produce: `add o` (the experimenter added `o`), `fired ℓ` (the system fired a firing labelled
  `ℓ`), `quiet` (the system has no admitted firing).
* **Soundness** (`readout_eq_of_openBisimilar`): open-bisimilar configurations have the same
  readout.

## The triggered race pair (`Triggered`)

The race pair of `RacePair`, with every firing also taking a trigger atom of its label (the context
that enables it), which only the experimenter supplies. `P` and `Q` are both quiet, so they are
bisimilar for the closed step (`closed_bisimilar`), and every spectator readout of the closed step
agrees on them. The experiment "add the trigger of `A`; see `A` fire; add the trigger of `B`; see
nothing fire" is possible at `Q` and impossible at `P` (`experiment_at_Q`, `no_experiment_at_P`):
**the experimenter separates the pair** (`experimenter_separates`), and the pair is not open
bisimilar (`not_openBisimilar`).

Closed bisimilarity is not a congruence for interventions (`not_congruence`): the continuations
`{k}` and `{kb}` are both quiet, hence bisimilar, and adding the trigger of `C` lets only the first
fire. Open bisimilarity is closed under interventions by construction.

## What the experimenter cannot see without copying

Each readout is one linear experiment: the experimenter acts on one copy of the system and sees one
run. It sees what is refused at a point only by withholding everything else at that point, and it
cannot return to a point to try another branch. Abramsky (1987) showed that observing bisimilarity
by testing needs copying states and global testing; a readout of single experiments, as here,
observes intervention traces with quiescence (refusal-style traces of the intervened step): finer
than traces (the triggered pair), and implied by open bisimilarity (soundness). It is strictly
coarser than open bisimilarity: `RaceCopying` proves that `a.(b.c + b.d)` and `a.b.c + a.b.d`, with
triggers at the ports, have equal readouts and are not open bisimilar
(`Copying.readout_strictly_coarser`); telling them apart takes two experiments from the state
reached after `a`, that is, a copy of it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled)
open Mettapedia.GSLT.HennessyMilner (System)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-- **An intervention**: the experimenter adds an occurrence; the knowledge is unchanged. -/
def addAtom (C : Configuration T O) (o : O) : Configuration T O := ⟨C.equations, insert o C.present⟩

section Open

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)
  (ports : O → Prop)

/-- **The intervened step**: the program's labelled moves, and the experimenter's additions at
its ports. -/
def OpenMoves (C : Configuration T O) : L ⊕ O → Configuration T O → Prop
  | .inl ℓ, D => Moves A label offers C ℓ D
  | .inr o, D => ports o ∧ D = addAtom C o

/-- The intervened step as a Hennessy–Milner system. -/
def openSystem : System (gslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L ⊕ O
  act lab C D := OpenMoves A label offers ports C lab D
  act_resp_left := by
    intro lab C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  act_resp_right := by
    intro lab C D D' step same
    exact (same : D = D') ▸ step

/-- **Open bisimilarity**: bisimilarity of the intervened step. -/
def OpenBisimilar (C D : Configuration T O) : Prop := (openSystem A label offers ports).Bisimilar C D

/-- An observation of the experimenter. -/
inductive Obs (L : Type uL) (O : Type uO) where
  | add (o : O)
  | fired (ℓ : L)
  | quiet

/-- **An experiment** and the observations it produces. -/
inductive Experiment : Configuration T O → List (Obs L O) → Prop
  | nil (C : Configuration T O) : Experiment C []
  | add (C : Configuration T O) (o : O) (rest : List (Obs L O)) :
      ports o → Experiment (addAtom C o) rest → Experiment C (.add o :: rest)
  | fired (C D : Configuration T O) (ℓ : L) (rest : List (Obs L O)) :
      Moves A label offers C ℓ D → Experiment D rest → Experiment C (.fired ℓ :: rest)
  | quiet (C : Configuration T O) (rest : List (Obs L O)) :
      (∀ ℓ D, ¬ Moves A label offers C ℓ D) → Experiment C rest → Experiment C (.quiet :: rest)

/-- **The experimenter's readout**: the observation sequences experiments can produce. -/
def Readout (C : Configuration T O) : Set (List (Obs L O)) := {e | Experiment A label offers ports C e}

variable {A label offers ports}

/-- **Open bisimilarity implies bisimilarity of the closed step.** -/
theorem bisimilar_of_openBisimilar {C D : Configuration T O}
    (bisimilar : OpenBisimilar A label offers ports C D) : Bisimilar A label offers C D := by
  obtain ⟨R, ⟨forward, backward, _⟩, related⟩ := bisimilar
  refine ⟨R, ⟨?_, ?_, ?_⟩, related⟩
  · intro C D related ℓ C' moved
    exact forward related (.inl ℓ) moved
  · intro C D related ℓ D' moved
    exact backward related (.inl ℓ) moved
  · intro _ _ _ atom
    exact atom.elim

theorem experiment_transfer {R : Configuration T O → Configuration T O → Prop}
    (bisimulation : (openSystem A label offers ports).IsBisimulation R) :
    ∀ {C : Configuration T O} {e : List (Obs L O)}, Experiment A label offers ports C e →
      ∀ {D : Configuration T O}, R C D → Experiment A label offers ports D e := by
  intro C e experiment
  induction experiment with
  | nil C => exact fun _ => .nil _
  | add C o rest port _ ih =>
      intro D related
      obtain ⟨D', added, related'⟩ := bisimulation.1 related (.inr o) (show OpenMoves A label offers ports
        C (.inr o) (addAtom C o) from ⟨port, rfl⟩)
      obtain ⟨_, same⟩ : ports o ∧ D' = addAtom D o := added
      subst same
      exact .add D o rest port (ih related')
  | fired C C' ℓ rest moved _ ih =>
      intro D related
      obtain ⟨D', moved', related'⟩ := bisimulation.1 related (.inl ℓ) moved
      exact .fired D D' ℓ rest moved' (ih related')
  | quiet C rest still _ ih =>
      intro D related
      refine .quiet D rest (fun ℓ D' moved => ?_) (ih related)
      obtain ⟨C', moved', _⟩ := bisimulation.2.1 related (.inl ℓ) moved
      exact still ℓ C' moved'

/-- **The readout is sound for open bisimilarity.** -/
theorem readout_eq_of_openBisimilar {C D : Configuration T O}
    (bisimilar : OpenBisimilar A label offers ports C D) :
    Readout A label offers ports C = Readout A label offers ports D := by
  obtain ⟨R, bisimulation, related⟩ := bisimilar
  have flipped : (openSystem A label offers ports).IsBisimulation (fun x y => R y x) :=
    ⟨fun _ _ related lab _ moved => bisimulation.2.1 related lab moved,
      fun _ _ related lab _ moved => bisimulation.1 related lab moved,
      fun _ _ _ atom => atom.elim⟩
  ext e
  exact ⟨fun experiment => experiment_transfer bisimulation experiment related,
    fun experiment => experiment_transfer (D := C) flipped experiment related⟩

/-- Two configurations without admitted firings are bisimilar for the closed step. -/
theorem bisimilar_of_halted {C D : Configuration T O} (haltC : ∀ ℓ C', ¬ Moves A label offers C ℓ C')
    (haltD : ∀ ℓ D', ¬ Moves A label offers D ℓ D') : Bisimilar A label offers C D := by
  refine ⟨fun x y => (x = C ∧ y = D) ∨ (x = D ∧ y = C), ⟨?_, ?_, ?_⟩, .inl ⟨rfl, rfl⟩⟩
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ x' moved
    · exact absurd moved (haltC ℓ x')
    · exact absurd moved (haltD ℓ x')
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) ℓ y' moved
    · exact absurd moved (haltD ℓ y')
    · exact absurd moved (haltC ℓ y')
  · intro _ _ _ atom
    exact atom.elim

end Open

/-! ## The triggered race pair -/

namespace Triggered

/-- Occurrence identities: the race pair's, and one trigger per action. -/
inductive Site
  | a | p | q | k | kb | kc | ta | tb | tc
  deriving DecidableEq

/-- Action names. -/
inductive Act
  | A | B | C
  deriving DecidableEq

variable (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes `made`. -/
def firing (taken made : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], made.map (label τ)⟩, [], ⟨taken, [], made⟩⟩

/-- The race pair, each firing also taking the trigger of its action. -/
def alphabet : List (Act × Firing T S Site) :=
  [(.A, firing τ [.a, .p, .ta] [.k]), (.A, firing τ [.a, .q, .ta] [.kb]), (.A, firing τ [.a, .q, .ta] [.kc]),
    (.B, firing τ [.k, .tb] []), (.C, firing τ [.k, .tc] []), (.B, firing τ [.kb, .tb] []),
    (.C, firing τ [.kc, .tc] [])]

def offers (ℓ : Act) (f : Firing T S Site) : Prop := (ℓ, f) ∈ alphabet (S := S) τ

/-- The ports of the triggered pair: the experimenter adds triggers only. -/
def trigger (o : Site) : Prop := o = .ta ∨ o = .tb ∨ o = .tc

/-- `a.(b + c)`, waiting for triggers. -/
def P : Configuration T Site := ⟨[], {.a, .p}⟩
/-- `a.b + a.c`, waiting for triggers. -/
def Q : Configuration T Site := ⟨[], {.a, .q}⟩

theorem ground : ∀ x ∈ alphabet (S := S) τ, Ground (label τ) x.2 := by
  intro x member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

variable (A : SubstitutionAction T S)

theorem valid_iff {ℓ : Act} {f : Firing T S Site} (member : (ℓ, f) ∈ alphabet τ)
    {C : Configuration T Site} (refl : Reflexive C.equations) :
    f.Valid A (label τ) C ↔ Enabled (label τ) C.present (f.selection.commit (T := T)) :=
  (ground τ (ℓ, f) member).valid_iff A refl

theorem halted_P {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) P ℓ D := by
  rintro ⟨f, member, valid, _⟩
  rw [valid_iff τ A member reflexive_nil] at valid
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> exact absurd valid (of_decide_eq_false rfl)

theorem halted_Q {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) Q ℓ D := by
  rintro ⟨f, member, valid, _⟩
  rw [valid_iff τ A member reflexive_nil] at valid
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> exact absurd valid (of_decide_eq_false rfl)

/-- **`P` and `Q` are bisimilar for the closed step**: neither moves without a trigger. -/
theorem closed_bisimilar : Bisimilar A (label τ) (offers τ) P Q :=
  bisimilar_of_halted (fun _ _ => halted_P τ A) (fun _ _ => halted_Q τ A)

/-- The separating experiment. -/
def probe : List (Obs Act Site) := [.add .ta, .fired .A, .add .tb, .quiet]

theorem reflexive_one : Reflexive ([(τ, τ), (τ, τ), (τ, τ)] : EquationStore T) := by
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> rfl

/-- **At `Q` the probe can be observed**: the experimenter adds the trigger of `A`, the `A` that
commits to `c` fires, the experimenter adds the trigger of `B`, and nothing fires. -/
theorem experiment_at_Q : probe ∈ Readout A (label τ) (offers τ) trigger Q := by
  let f : Firing T S Site := firing τ [.a, .q, .ta] [.kc]
  have member : (Act.A, f) ∈ alphabet τ := by simp [f, alphabet]
  refine .add _ _ _ (.inl rfl) (.fired _ (f.result (label τ) (addAtom Q .ta)) _ _ ⟨f, member,
    (valid_iff τ A member reflexive_nil).mpr (of_decide_eq_true rfl), rfl⟩ (.add _ _ _ (.inr (.inl rfl)) (.quiet _ _ ?_ (.nil _))))
  rintro ℓ D ⟨g, gMember, valid, _⟩
  rw [valid_iff τ A gMember (reflexive_one τ)] at valid
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at gMember
  rcases gMember with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> exact absurd valid (of_decide_eq_false rfl)

/-- **At `P` the probe cannot be observed**: after `A`, the trigger of `B` always finds `k`. -/
theorem no_experiment_at_P : probe ∉ Readout A (label τ) (offers τ) trigger P := by
  intro experiment
  have experiment' : Experiment A (label τ) (offers τ) trigger P
      [.add .ta, .fired .A, .add .tb, .quiet] := experiment
  cases experiment' with
  | add _ _ _ _ afterAdd =>
  cases afterAdd with
  | fired _ D _ _ moved afterFire =>
  obtain ⟨f, member, valid, rfl⟩ := moved
  rw [valid_iff τ A member reflexive_nil] at valid
  have options := member
  simp [offers, alphabet] at options
  rcases options with rfl | rfl | rfl
  · cases afterFire with
    | add _ _ _ _ afterTrigger =>
    cases afterTrigger with
    | quiet _ _ still _ =>
    let g : Firing T S Site := firing τ [.k, .tb] []
    have gMember : (Act.B, g) ∈ alphabet τ := by simp [g, alphabet]
    exact still .B _ ⟨g, gMember, (valid_iff τ A gMember (reflexive_one τ)).mpr (of_decide_eq_true rfl), rfl⟩
  · exact absurd valid (of_decide_eq_false rfl)
  · exact absurd valid (of_decide_eq_false rfl)

/-- **The experimenter separates the race pair**, which the closed step identifies. -/
theorem experimenter_separates :
    Bisimilar A (label τ) (offers τ) P Q ∧
      Readout A (label τ) (offers τ) trigger P ≠ Readout A (label τ) (offers τ) trigger Q :=
  ⟨closed_bisimilar τ A, fun same => no_experiment_at_P τ A (same ▸ experiment_at_Q τ A)⟩

/-- **The triggered race pair is not open bisimilar.** -/
theorem not_openBisimilar : ¬ OpenBisimilar A (label τ) (offers τ) trigger P Q :=
  fun bisimilar => (experimenter_separates τ A).2 (readout_eq_of_openBisimilar bisimilar)

/-! ### Closed bisimilarity is not a congruence for interventions -/

/-- The continuation of `P` after `A`, waiting for a trigger. -/
def X : Configuration T Site := ⟨[], {.k}⟩
/-- The continuation of `Q` after the `A` that committed to `b`, waiting for a trigger. -/
def Y : Configuration T Site := ⟨[], {.kb}⟩

theorem halted_at {C : Configuration T Site} (refl : Reflexive C.equations)
    (none : ∀ x ∈ alphabet (S := S) τ, ¬ Enabled (label τ) C.present (x.2.selection.commit (T := T)))
    {ℓ : Act} {D : Configuration T Site} : ¬ Moves A (label τ) (offers τ) C ℓ D := by
  rintro ⟨f, member, valid, _⟩
  exact none (ℓ, f) member ((valid_iff τ A member refl).mp valid)

theorem none_enabled (C : Configuration T Site) (present : C.present = {.k} ∨ C.present = {.kb} ∨
    C.present = {.tc, .kb}) :
    ∀ x ∈ alphabet (S := S) τ, ¬ Enabled (label τ) C.present (x.2.selection.commit (T := T)) := by
  intro x member
  simp only [alphabet, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases present with same | same | same <;> rw [same] <;>
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact of_decide_eq_false rfl

/-- **Closed bisimilarity is not a congruence for adding atoms at the ports.** `X` and `Y` are both
quiet, hence bisimilar for the closed step; after the experimenter adds the trigger of `C`, `X`
fires `C` and `Y` stays quiet. -/
theorem not_congruence :
    Bisimilar A (label τ) (offers τ) X Y ∧
      ¬ Bisimilar A (label τ) (offers τ) (addAtom X .tc) (addAtom Y .tc) := by
  refine ⟨bisimilar_of_halted (fun _ _ => halted_at τ A reflexive_nil (none_enabled τ X (.inl rfl)))
    (fun _ _ => halted_at τ A reflexive_nil (none_enabled τ Y (.inr (.inl rfl)))), ?_⟩
  let g : Firing T S Site := firing τ [.k, .tc] []
  have member : (Act.C, g) ∈ alphabet τ := by simp [g, alphabet]
  refine not_bisimilar_of_sat (φ := .dia Act.C .top)
    (sat_dia.mpr ⟨_, ⟨g, member, (valid_iff τ A member reflexive_nil).mpr (of_decide_eq_true rfl), rfl⟩,
      sat_top _⟩) ?_
  intro holds
  obtain ⟨D, moved, _⟩ := sat_dia.mp holds
  exact halted_at τ A reflexive_nil (none_enabled τ (addAtom Y .tc) (.inr (.inr rfl))) moved

end Triggered

#print axioms bisimilar_of_openBisimilar
#print axioms readout_eq_of_openBisimilar
#print axioms bisimilar_of_halted
#print axioms Triggered.closed_bisimilar
#print axioms Triggered.experiment_at_Q
#print axioms Triggered.no_experiment_at_P
#print axioms Triggered.experimenter_separates
#print axioms Triggered.not_openBisimilar
#print axioms Triggered.not_congruence

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
