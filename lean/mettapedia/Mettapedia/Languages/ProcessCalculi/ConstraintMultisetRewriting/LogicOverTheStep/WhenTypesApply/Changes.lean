import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.Distinctions.ParityBoundary
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.NullsOnTheStep.AbsenceNotCompositional
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.UnificationWithLevels.ExactTransitions

/-!
# What a type must survive: firings, growth, more observers, substitution

A type is a class no admitted observer splits. Four kinds of change act on the step, and each
selects the types that survive it.

**Firings** (`Invariant`, `core`). A class survives every firing when every step from a member lands
in it. Every class has a largest such part, its **invariant core**: the members all of whose
reachable states are members (`core_subset`, `core_invariant`, `subset_core`). A class survives
every firing exactly when it is its own core (`invariant_iff_core_eq`), and **the core of a type is
a type** (`core_bisimClosed`): bisimilar states reach bisimilar states (`reaches_of_bisimilar`).
This is subject reduction read as invariance. Control: the even reaches are a type and do not
survive a firing (`evenReach_not_invariant`); the stores that can run at most `n` steps do
(`reachAtMost_invariant`).

**Growth by another party** (`StableUnderGrowth`). Another party puts its store beside ours:
`union` joins the rows and the knowledge. Observe a store through readings that a join makes true
exactly when one side does (`JoinPreserving`): on the step, which labels are present and which
equations are known (`presence`, `presence_joinPreserving`).

* **Exact theorem** (`stable_iff_positive`): a type of such a lens survives every growth exactly when
  it is **positively generated**: built from the readings by unions and intersections, with no
  complement (`PositivelyGenerated`); equivalently, when a member's true readings suffice for
  membership (`Positive`, `positive_iff_generated`). On the step: `step_stable_iff_positive`.
  The precise condition behind it (`stable_iff_positive_of_realizes`): readings that a join keeps
  true (`JoinMonotone`) and whose order growth realizes (`RealizesOrder`); a join-preserving lens is
  one (`realizes_of_joinPreserving`).
* **Controls**, each a type of a lens on the ground step that does not survive one growth:
  - absence: "no `U` is present" (`absentU_isConcept`, `absentU_not_stable`), decided at the store at
    hand by a finite search (`absentU_decidable`, `absentU_decided`);
  - an exact count: "exactly one `T`", a type of the bag lens (`exactlyOneT_isConcept`,
    `exactlyOneT_not_stable`);
  - "these are all its equations": every known equation about `A T` is `A T = T`
    (`onlyEquations_isConcept`, `onlyEquations_not_stable`).
* **Both hypotheses are needed**: a class read through identities survives growth and is not
  positively generated, because it is not a type of the lens (`identity_stable_not_positive`); and
  for the bag lens, whose readings are exact and do not respect joins
  (`storeView_not_joinPreserving`), "exactly one `T`" is positive in its readings and does not
  survive growth (`exactlyOneT_positive`).

**More observers.** Every old type stays a type under a finer lens
(`Distinctions.ObserverConcepts.concepts_subset_iff`, `isConcept_of_reindex`), and new types appear
(`Distinctions.ObserverConcepts.Controls.strict`). The least type containing an instance shrinks:
`TwoKinds.conceptOf_shrinks`.

**Substitution** (`solutionReads`, `instantiate_respects`, `instantiate_isConcept`). On the solutions
of a store at any frames, the knowledge reads a solution through its own judgements; two solutions
are indistinguishable exactly when they agree (`indist_solutionReads_iff`). A later instantiation
respects agreement, so it pulls every type back to a type. The solutions themselves survive
instantiation (`Interface.Frames.models_comp`) and form a type
(`UnificationWithLevels.models_of_agree`). Control: a raw reading at one representative is not a
type (`Distinctions.TypingConcepts.etaRow_not_isConcept`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Changes

open Set
open Mettapedia.Cybernetics.DistinctionCalculus.Exclusion
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open Distinctions.ObserverConcepts Distinctions.StepConcepts

universe u v uG uA uL uO uT uH

/-! ## Firings -/

section Firing

variable {G : GSLT.{uG}} (M : System.{uA, uL} G)

/-- A class **survives every firing** when every step from a member lands in it. -/
def Invariant (X : Set G.Term) : Prop := ∀ x ∈ X, ∀ l x', M.act l x x' → x' ∈ X

/-- Reachable by finitely many firings. -/
inductive Reaches : G.Term → G.Term → Prop
  | refl (x : G.Term) : Reaches x x
  | step {x y z : G.Term} (l : M.Label) : M.act l x y → Reaches y z → Reaches x z

/-- **The invariant core of a class**: its members all of whose reachable states are members. -/
def core (X : Set G.Term) : Set G.Term := {x | ∀ y, Reaches M x y → y ∈ X}

variable {M}

theorem core_subset (X : Set G.Term) : core M X ⊆ X := fun x all => all x (.refl x)

theorem core_invariant (X : Set G.Term) : Invariant M (core M X) :=
  fun _ all l _ step y reach => all y (.step l step reach)

theorem reaches_invariant {Y : Set G.Term} (invariant : Invariant M Y) {y z : G.Term}
    (reach : Reaches M y z) (inY : y ∈ Y) : z ∈ Y := by
  induction reach with
  | refl => exact inY
  | step l step _ ih => exact ih (invariant _ inY l _ step)

/-- **The core is the largest invariant part.** -/
theorem subset_core {X Y : Set G.Term} (invariant : Invariant M Y) (inside : Y ⊆ X) :
    Y ⊆ core M X :=
  fun _ inY _ reach => inside (reaches_invariant invariant reach inY)

/-- **A class survives every firing exactly when it is its own invariant core.** -/
theorem invariant_iff_core_eq (X : Set G.Term) : Invariant M X ↔ core M X = X := by
  constructor
  · intro invariant
    exact Subset.antisymm (core_subset X) (subset_core invariant subset_rfl)
  · intro equal
    rw [← equal]
    exact core_invariant X

/-- Bisimilar states reach bisimilar states. -/
theorem reaches_of_bisimilar {x y z : G.Term} (bisimilar : M.Bisimilar y x) (reach : Reaches M y z) :
    ∃ z', Reaches M x z' ∧ M.Bisimilar z z' := by
  induction reach generalizing x with
  | refl => exact ⟨x, .refl x, bisimilar⟩
  | step l step _ ih =>
      obtain ⟨R, bisimulation, related⟩ := bisimilar
      obtain ⟨x', step', related'⟩ := bisimulation.1 related l step
      obtain ⟨z', reach', same⟩ := ih ⟨R, bisimulation, related'⟩
      exact ⟨z', .step l step' reach', same⟩

/-- **The invariant core of a type is a type.** -/
theorem core_bisimClosed {X : Set G.Term} (closed : BisimClosed M X) : BisimClosed M (core M X) := by
  intro x all y bisimilar z reach
  obtain ⟨z', reach', same⟩ := reaches_of_bisimilar (M.bisimilar_symm bisimilar) reach
  exact closed z' (all z' reach') z (M.bisimilar_symm same)

end Firing

section FiringControl

open Distinctions.ParityBoundary NamesOnTheStep NamesOnTheStep.IssuingControls

/-- **Control: the even reaches are a type that does not survive a firing**: two copies of `T` can
run two steps, and their successor one. -/
theorem evenReach_not_invariant : ¬ Invariant countingKnowledge evenReach := by
  intro invariant
  obtain ⟨C', step⟩ := exists_succ_of_reach (C := copies 2) (m := 1) (reach_copies 2)
  obtain ⟨m, before, after⟩ := succ_reach step
  have one : reach C' = 1 := by rw [reach_copies] at before; omega
  have even : C' ∈ evenReach :=
    invariant (copies 2) (show Even (reach (copies 2)) by rw [reach_copies]; exact ⟨1, rfl⟩) () C' step
  have odd : ¬ Even (reach C') := by rw [one]; exact Nat.not_even_one
  exact odd even

/-- The stores that can run at most `n` steps. -/
def reachAtMost (n : ℕ) : Set Conf := {C | reach C ≤ n}

/-- **A type that survives every firing**: every firing uses up a copy. -/
theorem reachAtMost_invariant (n : ℕ) : Invariant countingKnowledge (reachAtMost n) := by
  intro C atMost _ C' step
  obtain ⟨m, before, after⟩ := succ_reach step
  show reach C' ≤ n
  have : reach C ≤ n := atMost
  omega

end FiringControl

/-! ## Growth -/

section Growth

variable {V : Type u} {ι : Type v}

/-- A class **survives every growth** when joining anything to a member keeps a member. -/
def StableUnderGrowth (join : V → V → V) (X : Set V) : Prop := ∀ x ∈ X, ∀ y, join x y ∈ X

/-- **Positive**: the true readings of a member suffice for membership. -/
def Positive (read : ι → V → Prop) (X : Set V) : Prop :=
  ∀ x ∈ X, ∀ y, (∀ i, read i x → read i y) → y ∈ X

/-- Readings that a join makes true exactly when one side does. -/
def JoinPreserving (join : V → V → V) (read : ι → V → Prop) : Prop :=
  ∀ i x y, read i (join x y) ↔ read i x ∨ read i y

/-- **The classes the readings generate without complement**: their true fibres, closed under
arbitrary unions and intersections. -/
inductive PositivelyGenerated (read : ι → V → Prop) : Set V → Prop
  | fibre (i : ι) : PositivelyGenerated read {x | read i x}
  | sUnion (family : Set (Set V)) :
      (∀ S ∈ family, PositivelyGenerated read S) → PositivelyGenerated read (⋃₀ family)
  | sInter (family : Set (Set V)) :
      (∀ S ∈ family, PositivelyGenerated read S) → PositivelyGenerated read (⋂₀ family)

variable {read : ι → V → Prop}

theorem positive_of_generated {X : Set V} (generated : PositivelyGenerated read X) :
    Positive read X := by
  induction generated with
  | fibre i => exact fun _ holds _ up => up i holds
  | sUnion family _ ih =>
      rintro x ⟨S, member, inS⟩ y up
      exact ⟨S, member, ih S member x inS y up⟩
  | sInter family _ ih =>
      intro x all y up S member
      exact ih S member x (all S member) y up

theorem generated_of_positive {X : Set V} (positive : Positive read X) :
    PositivelyGenerated read X := by
  have equal : X = ⋃₀ ((fun x => ⋂₀ ((fun i => {y | read i y}) '' {i | read i x})) '' X) := by
    ext y
    constructor
    · intro inX
      refine ⟨_, ⟨y, inX, rfl⟩, ?_⟩
      rintro T ⟨i, holds, rfl⟩
      exact holds
    · rintro ⟨S, ⟨x, inX, rfl⟩, inS⟩
      exact positive x inX y fun i holds => inS _ ⟨i, holds, rfl⟩
  rw [equal]
  refine PositivelyGenerated.sUnion _ ?_
  rintro S ⟨x, -, rfl⟩
  refine PositivelyGenerated.sInter _ ?_
  rintro T ⟨i, -, rfl⟩
  exact PositivelyGenerated.fibre i

/-- **Positive is generated without complement.** -/
theorem positive_iff_generated {X : Set V} : Positive read X ↔ PositivelyGenerated read X :=
  ⟨generated_of_positive, positive_of_generated⟩

/-- Readings that a join keeps true. -/
def JoinMonotone (join : V → V → V) (read : ι → V → Prop) : Prop :=
  ∀ i x y, read i x → read i (join x y)

/-- **Growth realizes the readings' order**: when every true reading of `x` is true at `y`,
something joined to `x` makes it indistinguishable from `y`. -/
def RealizesOrder (join : V → V → V) (read : ι → V → Prop) : Prop :=
  ∀ x y, (∀ i, read i x → read i y) → ∃ z, Indist read (join x z) y

/-- **The exact condition**: for readings that a join keeps true and whose order growth realizes, a
type survives every growth exactly when it is positively generated. -/
theorem stable_iff_positive_of_realizes {join : V → V → V} (monotone : JoinMonotone join read)
    (realizes : RealizesOrder join read) {X : Set V} (concept : IsConcept (Apart read) X) :
    StableUnderGrowth join X ↔ PositivelyGenerated read X := by
  rw [← positive_iff_generated]
  constructor
  · intro stable x inX y up
    obtain ⟨z, same⟩ := realizes x y up
    exact (isConcept_iff_saturated X).mp concept _ (stable x inX z) y same
  · intro positive x inX y
    exact positive x inX (join x y) fun i holds => monotone i x y holds

/-- A join-preserving lens is one: join with the target itself. -/
theorem realizes_of_joinPreserving {join : V → V → V} (preserving : JoinPreserving join read) :
    JoinMonotone join read ∧ RealizesOrder join read :=
  ⟨fun i x y holds => (preserving i x y).mpr (Or.inl holds), fun x y up => ⟨y, fun i =>
    propext ((preserving i x y).trans ⟨fun either => either.elim (up i) id, Or.inr⟩)⟩⟩

/-- **A type of a join-preserving lens survives every growth exactly when it is positively
generated.** -/
theorem stable_iff_positive {join : V → V → V} (preserving : JoinPreserving join read) {X : Set V}
    (concept : IsConcept (Apart read) X) :
    StableUnderGrowth join X ↔ PositivelyGenerated read X :=
  stable_iff_positive_of_realizes (realizes_of_joinPreserving preserving).1
    (realizes_of_joinPreserving preserving).2 concept

end Growth

/-! ## Growth on the ground step -/

section GrowthOnTheStep

open NamesOnTheStep NamesOnTheStep.IssuingControls ProgramAdequacy Distinctions.ParityBoundary
open NullsOnTheStep.Composition (union)

/-- **The presence lens**: which labels are present, and which equations are known. -/
def presence : Expr ⊕ (Expr × Expr) → Conf → Prop
  | .inl p, C => ∃ o ∈ C.present, o.1 = p
  | .inr e, C => e ∈ C.equations

theorem presence_joinPreserving : JoinPreserving union presence := by
  rintro (p | e) C D
  · show (∃ o ∈ C.present ∪ D.present, o.1 = p) ↔ (∃ o ∈ C.present, o.1 = p) ∨ ∃ o ∈ D.present, o.1 = p
    constructor
    · rintro ⟨o, member, labelled⟩
      rcases Finset.mem_union.mp member with inC | inD
      · exact Or.inl ⟨o, inC, labelled⟩
      · exact Or.inr ⟨o, inD, labelled⟩
    · rintro (⟨o, inC, labelled⟩ | ⟨o, inD, labelled⟩)
      · exact ⟨o, Finset.mem_union_left _ inC, labelled⟩
      · exact ⟨o, Finset.mem_union_right _ inD, labelled⟩
  · exact List.mem_append

/-- **On the ground step, a type of the presence lens survives every growth exactly when it is
generated from the presence readings by unions and intersections, without complement.** -/
theorem step_stable_iff_positive {X : Set Conf} (concept : IsConcept (Apart presence) X) :
    StableUnderGrowth union X ↔ PositivelyGenerated presence X :=
  stable_iff_positive presence_joinPreserving concept

/-- `T` is present. -/
def presentT : Set Conf := {C | presence (.inl factT) C}

/-- **A type that survives every growth**: `T` is present. -/
theorem presentT_stable : StableUnderGrowth union presentT :=
  fun C inside D => (presence_joinPreserving (.inl factT) C D).mpr (Or.inl inside)

theorem presentT_isConcept : IsConcept (Apart presence) presentT :=
  isConcept_preimage (read := presence) (.inl factT) {p | p}

/-- A store holding one `U`. -/
def withU : Conf := ⟨[], {(factU, 0)}⟩

/-- **Absence**: no `U` is present. -/
def absentU : Set Conf := {C | ¬ presence (.inl factU) C}

theorem absentU_isConcept : IsConcept (Apart presence) absentU :=
  (isConcept_iff_saturated _).mpr fun _ outside _ same inside =>
    outside ((Iff.of_eq (same (.inl factU))).mpr inside)

/-- **Absence is decided at the store at hand**: a finite search of its present occurrences. -/
instance absentU_decidable : DecidablePred (· ∈ absentU) := fun C =>
  inferInstanceAs (Decidable (¬ ∃ o ∈ C.present, o.1 = factU))

theorem absentU_decided : emptyStore ∈ absentU ∧ withU ∉ absentU := by
  constructor <;> decide

/-- **Control: absence does not survive growth.** -/
theorem absentU_not_stable : ¬ StableUnderGrowth union absentU := by
  intro stable
  have empty : emptyStore ∈ absentU := by
    rintro ⟨o, member, _⟩
    simp [emptyStore] at member
  exact stable emptyStore empty withU
    ⟨(factU, 0), Finset.mem_union_right _ (Finset.mem_singleton_self _), rfl⟩

/-- **An exact count**: exactly one `T`. -/
def exactlyOneT : Set Conf := {C | (bag C).count factT = 1}

/-- Exactly one `T` is a type of the bag lens. -/
theorem exactlyOneT_isConcept : IsConcept (Apart storeView) exactlyOneT := by
  refine (isConcept_iff_saturated _).mpr fun C inside D same => ?_
  have sameBag : bag D = bag C := (Iff.of_eq (same (.inl (bag C)))).mp rfl
  show (bag D).count factT = 1
  rw [sameBag]
  exact inside

/-- One more `T`, with a new identity. -/
def oneMoreT : Conf := ⟨[], {(factT, 1)}⟩

/-- **Control: an exact count does not survive growth.** -/
theorem exactlyOneT_not_stable : ¬ StableUnderGrowth union exactlyOneT := by
  intro stable
  have one : copies 1 ∈ exactlyOneT := by
    show (bag (copies 1)).count factT = 1
    rw [(copies_chain 1).1, Multiset.count_replicate_self]
  have joined := stable (copies 1) one oneMoreT
  have presentTwo : (union (copies 1) oneMoreT).present = (copies 2).present := by decide
  have two : (bag (union (copies 1) oneMoreT)).count factT = 2 := by
    show ((union (copies 1) oneMoreT).present.val.map Prod.fst).count factT = 2
    rw [presentTwo]
    show (bag (copies 2)).count factT = 2
    rw [(copies_chain 2).1, Multiset.count_replicate_self]
  have : (bag (union (copies 1) oneMoreT)).count factT = 1 := joined
  omega

/-- **"These are all its equations"**: every known equation about `t` is in the list. -/
def onlyEquations (t : Expr) (E : List (Expr × Expr)) : Set Conf :=
  {C | ∀ e ∈ C.equations, e.1 = t → e ∈ E}

theorem onlyEquations_isConcept (t : Expr) (E : List (Expr × Expr)) :
    IsConcept (Apart presence) (onlyEquations t E) := by
  refine (isConcept_iff_saturated _).mpr fun C inside D same e member about => ?_
  exact inside e ((Iff.of_eq (same (.inr e))).mpr member) about

/-- **Control: "these are all its equations" does not survive growth**: the empty store knows no
equation about `A T` other than `A T = T`; beside a store that knows `A T = U`, it does. -/
theorem onlyEquations_not_stable :
    ¬ StableUnderGrowth union (onlyEquations (factA factT) [(factA factT, factT)]) := by
  intro stable
  have empty : emptyStore ∈ onlyEquations (factA factT) [(factA factT, factT)] :=
    fun e member => absurd member List.not_mem_nil
  have bad := stable emptyStore empty ⟨[(factA factT, factU)], ∅⟩ (factA factT, factU)
    (by simp [union, emptyStore]) rfl
  exact absurd bad (by decide)

/-- **Control: the lens hypothesis is needed.** Holding the occurrence with identity `0` survives
every growth and is not positively generated: no presence reading sees identities. -/
theorem identity_stable_not_positive :
    StableUnderGrowth union {C : Conf | (factT, 0) ∈ C.present} ∧
      ¬ PositivelyGenerated presence {C : Conf | (factT, 0) ∈ C.present} := by
  refine ⟨fun C inside D => Finset.mem_union_left _ inside, fun generated => ?_⟩
  have inside : copies 1 ∈ {C : Conf | (factT, 0) ∈ C.present} := by
    show (factT, 0) ∈ (copies 1).present
    decide
  have same : ∀ i, presence i (copies 1) → presence i oneMoreT := by
    rintro (p | e) holds
    · obtain ⟨o, member, rfl⟩ := holds
      have : o = (factT, 0) := by
        have : o ∈ ({(factT, 0)} : Finset Occ) := by
          have presentOne : (copies 1).present = {(factT, 0)} := by decide
          rw [← presentOne]
          exact member
        exact Finset.mem_singleton.mp this
      subst this
      exact ⟨(factT, 1), Finset.mem_singleton_self _, rfl⟩
    · exact absurd holds List.not_mem_nil
  have moved := positive_of_generated generated _ inside oneMoreT same
  exact absurd moved (by decide)

/-- **The bag lens does not respect joins**: two stores of one `T` each, side by side, hold two. -/
theorem storeView_not_joinPreserving : ¬ JoinPreserving union storeView := by
  intro preserving
  have joined := (preserving (.inl (Multiset.replicate 1 factT)) (copies 1) oneMoreT).mpr
    (Or.inl (copies_chain 1).1)
  have presentTwo : (union (copies 1) oneMoreT).present = (copies 2).present := by decide
  have cards := congrArg Multiset.card (show (union (copies 1) oneMoreT).present.val.map Prod.fst =
    Multiset.replicate 1 factT from joined)
  rw [presentTwo, show (copies 2).present.val.map Prod.fst = Multiset.replicate 2 factT from
    (copies_chain 2).1] at cards
  simp at cards

/-- **Control: join-preservation is needed.** Exactly one `T` is positive in the exact readings of the
bag lens, a type of it, and does not survive growth. -/
theorem exactlyOneT_positive : Positive storeView exactlyOneT := by
  intro C inside D up
  have sameBag : bag D = bag C := up (.inl (bag C)) rfl
  show (bag D).count factT = 1
  rw [sameBag]
  exact inside

end GrowthOnTheStep

/-! ## Substitution -/

section Substitution

open Interface UnificationWithLevels

variable {Obj : Type uO} {Tm : Obj → Type uT} {Hom : Obj → Obj → Type uH} (X : Frames Tm Hom)

/-- **The knowledge's readings of a solution** `a ⟶ b`: whether a term of `a`, read through it,
equals a term of `b`. -/
def solutionReads (a b : Obj) : Tm a × Tm b → Hom a b → Prop :=
  fun p f => X.E (X.act f p.1) p.2

/-- **Indistinguishable to the knowledge is agreement.** -/
theorem indist_solutionReads_iff {a b : Obj} (f g : Hom a b) :
    Indist (solutionReads X a b) f g ↔ Agree X f g := by
  constructor
  · intro same t
    have here : X.E (X.act g t) (X.act g t) := (X.equivalence b).refl _
    exact (Iff.of_eq (same (t, X.act g t))).mpr here
  · intro agree p
    apply propext
    constructor
    · intro equal
      exact (X.equivalence b).trans ((X.equivalence b).symm (agree p.1)) equal
    · intro equal
      exact (X.equivalence b).trans (agree p.1) equal

/-- **Instantiating the unknowns respects the knowledge**: a later substitution sends agreeing
solutions to agreeing solutions. -/
theorem instantiate_respects {a b c : Obj} (h : Hom b c) :
    Respects (solutionReads X a b) (solutionReads X a c) (fun f => X.comp h f) :=
  fun f g same => (indist_solutionReads_iff X _ _).mpr
    (Agree.comp_left ((indist_solutionReads_iff X f g).mp same) h)

/-- **Every type survives instantiation**: a type of the knowledge at the later frame pulls back to a
type. -/
theorem instantiate_isConcept {a b c : Obj} (h : Hom b c) {S : Set (Hom a c)}
    (concept : IsConcept (Apart (solutionReads X a c)) S) :
    IsConcept (Apart (solutionReads X a b)) ((fun f => X.comp h f) ⁻¹' S) :=
  (pullback_isConcept_iff _ _ _).mpr (instantiate_respects X h) S concept

end Substitution

#print axioms core_invariant
#print axioms subset_core
#print axioms invariant_iff_core_eq
#print axioms core_bisimClosed
#print axioms evenReach_not_invariant
#print axioms reachAtMost_invariant
#print axioms positive_iff_generated
#print axioms stable_iff_positive_of_realizes
#print axioms realizes_of_joinPreserving
#print axioms stable_iff_positive
#print axioms step_stable_iff_positive
#print axioms absentU_decided
#print axioms presentT_stable
#print axioms absentU_not_stable
#print axioms exactlyOneT_isConcept
#print axioms exactlyOneT_not_stable
#print axioms onlyEquations_not_stable
#print axioms identity_stable_not_positive
#print axioms storeView_not_joinPreserving
#print axioms exactlyOneT_positive
#print axioms indist_solutionReads_iff
#print axioms instantiate_isConcept

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.WhenTypesApply.Changes
