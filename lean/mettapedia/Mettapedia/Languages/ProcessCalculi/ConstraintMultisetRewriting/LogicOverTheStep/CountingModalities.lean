import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.ProgramAdequacy

/-!
# Counting firings: graded modalities over the step's span

OSLF's possibility reads a span through its existential image: some edge leaves the state into
the predicate. Over the step's firing span (`StepSpan.firingSpan`) the edges are the admitted
firings themselves, so they can be counted.

* `countingDiamond S n φ x`: at least `n` distinct edges leave `x` into `φ`. With `n = 1` it is
  OSLF's possibility (`countingDiamond_one`); it is antitone in `n` (`countingDiamond_anti`).
  Over the firing span, the edges at a state are its admitted firings: events, with their rule
  and selected occurrences, not their successor states.

## Graded logic and counting bisimulation

`GFormula` has atoms, conjunction, negation and `atLeast n`. A **counting bisimulation** relates
states with the same observations and, for every predicate saturated by it, the same counts
(`IsCountingBisimulation`).

* `gsat_iff_of_counting`: counting bisimulations preserve every graded formula.
* **`graded_adequacy`**: when every state has finitely many edges (`EdgeFinite`), graded logical
  equivalence is counting bisimilarity.

## Counts along morphisms of spans

Possibility crosses a morphism of spans whose source square is a weak pullback
(`ModalComparison.SpanMap.diamond_eq`). Counts need more: a locally injective morphism carries
them forward (`map_counting_le`); with the weak pullback it is a local isomorphism of spans, which
carries them exactly (`map_counting_iff`) and so carries every graded formula
(`gsat_along_map`). The map from firings to successors (`StepSpan.toSucc`) is a weak pullback and
not locally injective: two readings of two copies of `T` reach one successor
(`successors_collapse_events`, `toSucc_not_locallyInjective`).

## At the level of finite programs

Distinct fresh identities make distinct firings, so a making rule has infinitely many firings,
all renamings of one another (`ProgramAdequacy`). The **event step** (`eventStep`) keeps one firing
per event: per rule, taken and read occurrences, with the canonical fresh choice and no predicate
queries. Under a finite program it has finitely many firings at every store
(`eventStep_edgeFinite`), so graded adequacy holds there (`event_graded_adequacy`).

## At the level of the real step

On the real step under a rule set (`ProgramAdequacy.program`) the counting modality counts
**events**: distinct rules with their taken and read occurrences, each with some admitted firing
into the predicate (`eventDiamond`). Every firing of an event is renamed, fixing the store, onto the
canonical one (`canonical_event`), so for predicates that renaming cannot change, the real step and
the event step have the same events (`program_events_iff`), and counting events of the real step is
counting firings of the event step (`program_events_counted`). Event counts are invariant under
renaming (`eventDiamond_rename_iff`), so graded formulas read over the real step (`eventSat`) are
read over the event step (`eventSat_iff_gsat`), and **graded adequacy holds on the real step under
every finite program** (`program_graded_adequacy`).

Control: at the empty store, the program that makes `T` has at least `n` firings for every `n`, one
per fresh identity (`making_firings_unbounded`), and exactly one event (`making_one_event`).

## Control: two copies against one

On the ground step under the program that reads `T`, the store with two copies of `T` and the
store with one are bisimilar for the plain modalities (`plain_bisimilar`), with the plain diamond
true at both, while `atLeast 2` holds at two copies only (`two_copies_counted`,
`one_copy_counted_once`).
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.CountingModalities

open Interface
open Mettapedia.OSLF.Framework.DerivedModalities
open FragmentsOfTheStep.TransitionMaps
open Mettapedia.GSLT Mettapedia.GSLT.HennessyMilner
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open StepSpan ProgramAdequacy

universe uX uE uA uT uS uO uY uE'

/-! ## Counting over a span -/

section Span

variable {X : Type uX} (S : ReductionSpan.{uX, uE} X)

/-- **At least `n` distinct edges from a state into a predicate.** -/
def countingDiamond (n : ℕ) (φ : X → Prop) (x : X) : Prop :=
  ∃ edges : Finset S.Edge, edges.card = n ∧ ∀ e ∈ edges, S.source e = x ∧ φ (S.target e)

theorem countingDiamond_zero (φ : X → Prop) (x : X) : countingDiamond S 0 φ x :=
  ⟨∅, rfl, by simp⟩

/-- **Counting one edge is OSLF's possibility.** -/
theorem countingDiamond_one (φ : X → Prop) : countingDiamond S 1 φ = derivedDiamond S φ := by
  funext x
  apply propext
  constructor
  · rintro ⟨edges, card, inside⟩
    obtain ⟨e, member⟩ := Finset.card_pos.mp (by omega : 0 < edges.card)
    obtain ⟨source, holds⟩ := inside e member
    exact ⟨e, source, holds⟩
  · rintro ⟨e, source, holds⟩
    refine ⟨{e}, Finset.card_singleton e, fun e' member => ?_⟩
    rw [Finset.mem_singleton.mp member]
    exact ⟨source, holds⟩

theorem countingDiamond_anti {m n : ℕ} (le : m ≤ n) {φ : X → Prop} {x : X}
    (holds : countingDiamond S n φ x) : countingDiamond S m φ x := by
  obtain ⟨edges, card, inside⟩ := holds
  obtain ⟨smaller, sub, card'⟩ := Finset.exists_subset_card_eq (s := edges) (by omega : m ≤ edges.card)
  exact ⟨smaller, card', fun e member => inside e (sub member)⟩

/-- Counts depend only on the predicate along the edges leaving the state. -/
theorem countingDiamond_congr {φ ψ : X → Prop} {x : X}
    (agree : ∀ e, S.source e = x → (φ (S.target e) ↔ ψ (S.target e))) (n : ℕ) :
    countingDiamond S n φ x ↔ countingDiamond S n ψ x := by
  constructor
  · rintro ⟨edges, card, inside⟩
    exact ⟨edges, card, fun e member =>
      ⟨(inside e member).1, (agree e (inside e member).1).mp (inside e member).2⟩⟩
  · rintro ⟨edges, card, inside⟩
    exact ⟨edges, card, fun e member =>
      ⟨(inside e member).1, (agree e (inside e member).1).mpr (inside e member).2⟩⟩

/-! ## Graded logic -/

/-- **Graded formulas**: atoms, conjunction, negation, and "at least `n` edges into". -/
inductive GFormula (Atom : Type uA) : Type uA where
  | top
  | atom (a : Atom)
  | conj (l r : GFormula Atom)
  | neg (inner : GFormula Atom)
  | atLeast (n : ℕ) (inner : GFormula Atom)

variable {Atom : Type uA} (observes : Atom → X → Prop)

/-- Satisfaction. -/
def gsat : GFormula Atom → X → Prop
  | .top, _ => True
  | .atom a, x => observes a x
  | .conj l r, x => gsat l x ∧ gsat r x
  | .neg inner, x => ¬ gsat inner x
  | .atLeast n inner, x => countingDiamond S n (gsat inner) x

/-- A predicate that cannot tell related states apart. -/
def Saturated (R : X → X → Prop) (U : X → Prop) : Prop := ∀ y z, R y z → (U y ↔ U z)

/-- **A counting bisimulation**: related states have the same observations and the same counts
into every saturated predicate. -/
def IsCountingBisimulation (R : X → X → Prop) : Prop :=
  (∀ x y, R x y → ∀ a, observes a x ↔ observes a y) ∧
    ∀ x y, R x y → ∀ U, Saturated R U → ∀ n, countingDiamond S n U x ↔ countingDiamond S n U y

def CountingBisimilar (x y : X) : Prop := ∃ R, IsCountingBisimulation S observes R ∧ R x y

/-- **Counting bisimulations preserve every graded formula.** -/
theorem gsat_iff_of_counting {R : X → X → Prop} (bisimulation : IsCountingBisimulation S observes R) :
    ∀ (φ : GFormula Atom) {x y : X}, R x y → (gsat S observes φ x ↔ gsat S observes φ y)
  | .top, _, _, _ => Iff.rfl
  | .atom a, _, _, related => bisimulation.1 _ _ related a
  | .conj l r, _, _, related =>
      and_congr (gsat_iff_of_counting bisimulation l related)
        (gsat_iff_of_counting bisimulation r related)
  | .neg inner, _, _, related => not_congr (gsat_iff_of_counting bisimulation inner related)
  | .atLeast n inner, _, _, related =>
      bisimulation.2 _ _ related _ (fun _ _ r => gsat_iff_of_counting bisimulation inner r) n

/-- Graded logical equivalence. -/
def GEquivalent (x y : X) : Prop := ∀ φ : GFormula Atom, gsat S observes φ x ↔ gsat S observes φ y

/-- Finitely many edges leave every state. -/
def EdgeFinite : Prop := ∀ x, {e : S.Edge | S.source e = x}.Finite

/-- Finite conjunction. -/
def conjList : List (GFormula Atom) → GFormula Atom
  | [] => .top
  | φ :: rest => .conj φ (conjList rest)

/-- Finite disjunction. -/
def disjList (formulas : List (GFormula Atom)) : GFormula Atom := .neg (conjList (formulas.map .neg))

theorem gsat_conjList (x : X) :
    ∀ formulas : List (GFormula Atom), gsat S observes (conjList formulas) x ↔
      ∀ φ ∈ formulas, gsat S observes φ x
  | [] => by simp [conjList, gsat]
  | φ :: rest => by simp [conjList, gsat, gsat_conjList x rest]

theorem gsat_disjList (x : X) (formulas : List (GFormula Atom)) :
    gsat S observes (disjList formulas) x ↔ ∃ φ ∈ formulas, gsat S observes φ x := by
  simp only [disjList, gsat, gsat_conjList, List.mem_map]
  constructor
  · intro notAll
    by_contra none
    exact notAll fun ψ ⟨φ, member, same⟩ => same ▸ fun holds => none ⟨φ, member, holds⟩
  · rintro ⟨φ, member, holds⟩ all
    exact all (.neg φ) ⟨φ, member, rfl⟩ holds

theorem exists_separating {x y : X} (inequivalent : ¬ GEquivalent S observes x y) :
    ∃ φ : GFormula Atom, gsat S observes φ x ∧ ¬ gsat S observes φ y := by
  obtain ⟨φ, disagree⟩ := not_forall.mp inequivalent
  by_cases holds : gsat S observes φ x
  · exact ⟨φ, holds, fun other => disagree ⟨fun _ => other, fun _ => holds⟩⟩
  · exact ⟨.neg φ, holds, fun notThere =>
      disagree ⟨fun here => absurd here holds, fun there => absurd there notThere⟩⟩

/-- **The counting step of adequacy**: between equivalent states, counts into a saturated
predicate are carried, through one formula that defines the predicate on the finitely many
targets. -/
theorem counting_of_gequivalent (finite : EdgeFinite S) {x y : X}
    (equivalent : GEquivalent S observes x y) {U : X → Prop}
    (saturated : Saturated (GEquivalent S observes) U) (n : ℕ)
    (holds : countingDiamond S n U x) : countingDiamond S n U y := by
  classical
  let targets : Finset X := ((finite x).toFinset ∪ (finite y).toFinset).image S.target
  have reach : ∀ e, S.source e = x ∨ S.source e = y → S.target e ∈ targets := by
    intro e from_
    refine Finset.mem_image.mpr ⟨e, ?_, rfl⟩
    rcases from_ with atX | atY
    · exact Finset.mem_union_left _ ((finite x).mem_toFinset.mpr atX)
    · exact Finset.mem_union_right _ ((finite y).mem_toFinset.mpr atY)
  have separate : ∀ t t' : X, ∃ δ : GFormula Atom,
      U t → ¬ U t' → gsat S observes δ t ∧ ¬ gsat S observes δ t' := by
    intro t t'
    by_cases split : U t ∧ ¬ U t'
    · have inequivalent : ¬ GEquivalent S observes t t' :=
        fun same => split.2 ((saturated t t' same).mp split.1)
      obtain ⟨δ, yes, no⟩ := exists_separating S observes inequivalent
      exact ⟨δ, fun _ _ => ⟨yes, no⟩⟩
    · exact ⟨.top, fun inside outside => absurd ⟨inside, outside⟩ split⟩
  choose δ separates using separate
  let inside := (targets.filter U).toList
  let outside := (targets.filter fun t => ¬ U t).toList
  let ψ : GFormula Atom := disjList (inside.map fun t => conjList (outside.map fun t' => δ t t'))
  have agree : ∀ t ∈ targets, (U t ↔ gsat S observes ψ t) := by
    intro t member
    rw [gsat_disjList]
    constructor
    · intro tU
      refine ⟨_, List.mem_map.mpr ⟨t, Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨member, tU⟩),
        rfl⟩, ?_⟩
      rw [gsat_conjList]
      intro φ inList
      obtain ⟨t', t'In, rfl⟩ := List.mem_map.mp inList
      exact (separates t t' tU (Finset.mem_filter.mp (Finset.mem_toList.mp t'In)).2).1
    · rintro ⟨φ, inList, there⟩
      obtain ⟨t₀, t₀In, rfl⟩ := List.mem_map.mp inList
      rw [gsat_conjList] at there
      by_contra notU
      have t₀U : U t₀ := (Finset.mem_filter.mp (Finset.mem_toList.mp t₀In)).2
      have tOut : t ∈ outside := Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨member, notU⟩)
      exact (separates t₀ t t₀U notU).2 (there _ (List.mem_map.mpr ⟨t, tOut, rfl⟩))
  have atX := (countingDiamond_congr S (fun e source => agree _ (reach e (Or.inl source))) n).mp holds
  have atY := (equivalent (.atLeast n ψ)).mp atX
  exact (countingDiamond_congr S (fun e source => agree _ (reach e (Or.inr source))) n).mpr atY

theorem gequivalent_isCounting (finite : EdgeFinite S) :
    IsCountingBisimulation S observes (GEquivalent S observes) := by
  refine ⟨fun x y equivalent a => equivalent (.atom a), fun x y equivalent U saturated n => ?_⟩
  exact ⟨counting_of_gequivalent S observes finite equivalent saturated n,
    counting_of_gequivalent S observes finite (fun φ => (equivalent φ).symm) saturated n⟩

/-- **Graded adequacy**: on an edge-finite span, graded logical equivalence is counting
bisimilarity. -/
theorem graded_adequacy (finite : EdgeFinite S) (x y : X) :
    GEquivalent S observes x y ↔ CountingBisimilar S observes x y := by
  constructor
  · intro equivalent
    exact ⟨GEquivalent S observes, gequivalent_isCounting S observes finite, equivalent⟩
  · rintro ⟨R, bisimulation, related⟩ φ
    exact gsat_iff_of_counting S observes bisimulation φ related

end Span

/-! ## Counts along morphisms of spans -/

section Maps

open ModalComparison

variable {X : Type uX} {Y : Type uY} {SX : ReductionSpan.{uX, uE} X} {SY : ReductionSpan.{uY, uE'} Y}
  {h : X → Y}

/-- A morphism of spans is **locally injective** when edges with one source and one image are
equal. -/
def LocallyInjective (m : SpanMap SX SY h) : Prop :=
  ∀ e₁ e₂, SX.source e₁ = SX.source e₂ → m.edge e₁ = m.edge e₂ → e₁ = e₂

/-- **Counts are carried forward along locally injective morphisms of spans.** -/
theorem map_counting_le (m : SpanMap SX SY h) (injective : LocallyInjective m) (n : ℕ)
    (φ : Y → Prop) (x : X) :
    countingDiamond SX n (pb h φ) x → countingDiamond SY n φ (h x) := by
  classical
  rintro ⟨edges, card, inside⟩
  have injOn : Set.InjOn m.edge edges := fun e₁ in₁ e₂ in₂ same =>
    injective e₁ e₂ ((inside e₁ in₁).1.trans (inside e₂ in₂).1.symm) same
  refine ⟨edges.image m.edge, by rw [Finset.card_image_of_injOn injOn, card], ?_⟩
  intro e' member
  obtain ⟨e, inE, rfl⟩ := Finset.mem_image.mp member
  obtain ⟨source, holds⟩ := inside e inE
  refine ⟨(m.source e).trans (congrArg h source), ?_⟩
  show φ (SY.target (m.edge e))
  rw [m.target e]
  exact holds

/-- **Counts are equal along local isomorphisms of spans**: locally injective morphisms whose
source square is a weak pullback. -/
theorem map_counting_iff (m : SpanMap SX SY h) (injective : LocallyInjective m)
    (weak : WeakPullback SX.source SY.source h m.edge) (n : ℕ) (φ : Y → Prop) (x : X) :
    countingDiamond SY n φ (h x) ↔ countingDiamond SX n (pb h φ) x := by
  classical
  refine ⟨fun counted => ?_, map_counting_le m injective n φ x⟩
  obtain ⟨edges, card, inside⟩ := counted
  choose lift source mapped using
    fun (e' : SY.Edge) (member : e' ∈ edges) => weak x e' (inside e' member).1
  let g : edges → SX.Edge := fun e' => lift e'.1 e'.2
  have gInjective : Function.Injective g := by
    intro a b same
    have images : m.edge (lift a.1 a.2) = m.edge (lift b.1 b.2) := congrArg m.edge same
    rw [mapped a.1 a.2, mapped b.1 b.2] at images
    exact Subtype.ext images
  refine ⟨edges.attach.image g,
    by rw [Finset.card_image_of_injective _ gInjective, Finset.card_attach, card], ?_⟩
  intro e member
  obtain ⟨e', _, rfl⟩ := Finset.mem_image.mp member
  refine ⟨source e'.1 e'.2, ?_⟩
  show φ (h (SX.target (lift e'.1 e'.2)))
  rw [← m.target, mapped e'.1 e'.2]
  exact (inside e'.1 e'.2).2

/-- **Local isomorphisms of spans carry every graded formula**, when they carry the observations. -/
theorem gsat_along_map {Atom : Type uA} (observesX : Atom → X → Prop) (observesY : Atom → Y → Prop)
    (m : SpanMap SX SY h) (injective : LocallyInjective m)
    (weak : WeakPullback SX.source SY.source h m.edge)
    (observed : ∀ a x, observesX a x ↔ observesY a (h x)) :
    ∀ (ψ : GFormula Atom) (x : X), gsat SX observesX ψ x ↔ gsat SY observesY ψ (h x)
  | .top, _ => Iff.rfl
  | .atom a, x => observed a x
  | .conj l r, x => and_congr (gsat_along_map observesX observesY m injective weak observed l x)
      (gsat_along_map observesX observesY m injective weak observed r x)
  | .neg inner, x => not_congr (gsat_along_map observesX observesY m injective weak observed inner x)
  | .atLeast n inner, x =>
      (countingDiamond_congr SX (φ := gsat SX observesX inner) (ψ := pb h (gsat SY observesY inner))
        (fun e _ => gsat_along_map observesX observesY m injective weak observed inner (SX.target e))
          n).trans
        (map_counting_iff m injective weak n (gsat SY observesY inner) x).symm

end Maps

/-! ## The event step: one firing per event -/

section Events

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]
  (A : SubstitutionAction T S) (label : O → T)

/-- **The event step under a rule set**: one firing per event, with the canonical fresh choice and
no predicate queries. -/
def eventStep (supply : Supply label) (R : Set (RuleInstance T)) :
    Interface.Step (Frames.ofSubstitution A) O (Configuration T O) (fun _ => AnnotatedRuns.Firing T S O) :=
  Interface.Step.ofEffect (AnnotatedRuns.firstOrder A label).toStep.effectCore
    fun {C} f _ => f.Valid A label C ∧ f.rule ∈ R ∧ f.queries = [] ∧
      f.selection.made = freshFor label supply C.present f.rule.produce

/-- **Finitely many events at every store, under a finite program.** -/
theorem eventStep_edgeFinite (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite) :
    EdgeFinite (firingSpan (eventStep A label supply R)) := by
  intro C
  let key : (firingSpan (eventStep A label supply R)).Edge → RuleInstance T × List O × List O :=
    fun e => (e.2.1.rule, e.2.1.selection.taken, e.2.1.selection.read)
  let takes : Set (List O) := ⋃ rule ∈ R, listsOver C.present rule.take.length
  let reads : Set (List O) := ⋃ rule ∈ R, listsOver C.present rule.read.length
  have bounded : (R ×ˢ (takes ×ˢ reads)).Finite :=
    finite.prod ((finite.biUnion fun _ _ => listsOver_finite _ _).prod
      (finite.biUnion fun _ _ => listsOver_finite _ _))
  refine Set.Finite.of_finite_image (f := key) (bounded.subset ?_) ?_
  · rintro _ ⟨⟨C', f, ⟨_, valid, member, _, _⟩⟩, source, rfl⟩
    have atC : C' = C := source
    subst atC
    refine ⟨member, Set.mem_biUnion member ⟨valid.firing.take_length.symm, fun o inside =>
      valid.firing.occurrences.taken_subset (List.mem_toFinset.mpr inside)⟩,
      Set.mem_biUnion member ⟨valid.firing.read_length.symm, fun o inside =>
      valid.firing.occurrences.kept_subset (List.mem_toFinset.mpr inside)⟩⟩
  · rintro ⟨C₁, ⟨rule₁, queries₁, ⟨taken₁, read₁, made₁⟩⟩, ⟨_, _, _, noQueries₁, canonical₁⟩⟩ source₁
      ⟨C₂, ⟨rule₂, queries₂, ⟨taken₂, read₂, made₂⟩⟩, ⟨_, _, _, noQueries₂, canonical₂⟩⟩ source₂ same
    have at₁ : C₁ = C := source₁
    have at₂ : C₂ = C := source₂
    subst at₁
    subst at₂
    simp only [key, Prod.mk.injEq] at same
    obtain ⟨rfl, rfl, rfl⟩ := same
    have queries : queries₁ = queries₂ := noQueries₁.trans noQueries₂.symm
    have made : made₁ = made₂ := canonical₁.trans canonical₂.symm
    subst queries
    subst made
    rfl

/-- **Graded adequacy for events under every finite program.** -/
theorem event_graded_adequacy (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite)
    {Atom : Type uA} (observes : Atom → Configuration T O → Prop) (C D : Configuration T O) :
    GEquivalent (firingSpan (eventStep A label supply R)) observes C D ↔
      CountingBisimilar (firingSpan (eventStep A label supply R)) observes C D :=
  graded_adequacy _ observes (eventStep_edgeFinite A label supply finite) C D

/-- The canonical fresh choice for no labels is empty. -/
theorem freshFor_nil (supply : Supply label) (used : Finset O) : freshFor label supply used [] = [] :=
  List.map_eq_nil_iff.mp (freshFor_spec label supply used []).2.2

/-! ## Events of the real step -/

/-- **At least `n` events into `φ`**: `n` distinct rules with taken and read occurrences, each with
an admitted firing into `φ`. Firings of one event differ only in their fresh identities and
predicate queries. -/
def eventDiamond (P : Interface.Step (Frames.ofSubstitution A) O (Configuration T O)
      (fun _ => AnnotatedRuns.Firing T S O)) (n : ℕ) (φ : Configuration T O → Prop)
    (C : Configuration T O) : Prop :=
  ∃ events : Finset (RuleInstance T × List O × List O), events.card = n ∧
    ∀ k ∈ events, ∃ (f : AnnotatedRuns.Firing T S O) (admitted : P.Admits (s := C) f),
      (f.rule, f.selection.taken, f.selection.read) = k ∧ φ (P.result f admitted)

/-- **The canonical firing of an event**: a valid selection is renamed, fixing the store, onto the
canonical fresh choice; that selection is valid, and its result is the renamed result. -/
theorem canonical_event (supply : Supply label) {rule : RuleInstance T} {taken read made : List O}
    {C : Configuration T O} (valid : (⟨taken, read, made⟩ : Selection O).Valid A label rule C) :
    ∃ π : Equiv.Perm O, Keeps label π ∧
      (⟨taken, read, freshFor label supply C.present rule.produce⟩ : Selection O).Valid A label rule C ∧
      (⟨taken, read, freshFor label supply C.present rule.produce⟩ : Selection O).result label rule C =
        renameConf π ((⟨taken, read, made⟩ : Selection O).result label rule C) := by
  obtain ⟨canonicalNodup, canonicalFresh, canonicalLabels⟩ :=
    freshFor_spec label supply C.present rule.produce
  have madeFresh : ∀ o ∈ made, o ∉ C.present := by
    intro o member present
    exact Finset.disjoint_left.mp valid.occurrences.fresh (List.mem_toFinset.mpr member) present
  obtain ⟨π, keeps, fix, mapped⟩ := exists_renaming label made _ valid.output_distinct canonicalNodup
    (valid.outputs.trans canonicalLabels.symm) C.present madeFresh canonicalFresh
  have takenInside : ∀ o ∈ taken, o ∈ C.present := fun o member =>
    valid.occurrences.taken_subset (List.mem_toFinset.mpr member)
  have readInside : ∀ o ∈ read, o ∈ C.present := fun o member =>
    valid.occurrences.kept_subset (List.mem_toFinset.mpr member)
  have selection : renameSel π ⟨taken, read, made⟩ =
      (⟨taken, read, freshFor label supply C.present rule.produce⟩ : Selection O) := by
    simp only [renameSel, map_fix fix takenInside, map_fix fix readInside, mapped]
  have store : renameConf π C = C := renameConf_fix fix
  refine ⟨π, keeps, ?_, ?_⟩
  · have renamed := valid_rename A label keeps valid
    rw [selection, store] at renamed
    exact renamed
  · rw [← selection, ← result_rename label keeps, store]

/-- **The real step and the event step have the same events**, into predicates that renaming of
identities cannot change. -/
theorem program_events_iff (supply : Supply label) (R : Set (RuleInstance T)) (n : ℕ)
    {φ : Configuration T O → Prop}
    (invariant : ∀ (π : Equiv.Perm O) (D : Configuration T O), Keeps label π →
      (φ (renameConf π D) ↔ φ D))
    (C : Configuration T O) :
    eventDiamond A (program A label R) n φ C ↔ eventDiamond A (eventStep A label supply R) n φ C := by
  constructor
  · rintro ⟨events, card, witnesses⟩
    refine ⟨events, card, fun k member => ?_⟩
    obtain ⟨⟨rule, queries, ⟨taken, read, made⟩⟩, ⟨_, valid, inR⟩, key, holds⟩ := witnesses k member
    obtain ⟨π, keeps, canonicalValid, canonicalResult⟩ := canonical_event A label supply valid.firing
    let f₀ : AnnotatedRuns.Firing T S O :=
      ⟨rule, [], ⟨taken, read, freshFor label supply C.present rule.produce⟩⟩
    have f₀Valid : f₀.Valid A label C :=
      (PredicateQueryAdmission.valid_empty_iff A label rule C _).mpr canonicalValid
    refine ⟨f₀, ⟨(AnnotatedRuns.firstOrder A label).toStep.prepares f₀Valid, f₀Valid, inR, rfl, rfl⟩,
      key, ?_⟩
    show φ ((⟨taken, read, freshFor label supply C.present rule.produce⟩ : Selection O).result label rule C)
    rw [canonicalResult, invariant π _ keeps]
    exact holds
  · rintro ⟨events, card, witnesses⟩
    refine ⟨events, card, fun k member => ?_⟩
    obtain ⟨f, ⟨prepared, valid, inR, _, _⟩, key, holds⟩ := witnesses k member
    exact ⟨f, ⟨prepared, valid, inR⟩, key, holds⟩

/-- **On the event step, counting events is counting firings.** -/
theorem eventStep_events_iff (supply : Supply label) (R : Set (RuleInstance T)) (n : ℕ)
    (φ : Configuration T O → Prop) (C : Configuration T O) :
    eventDiamond A (eventStep A label supply R) n φ C ↔
      countingDiamond (firingSpan (eventStep A label supply R)) n φ C := by
  classical
  constructor
  · rintro ⟨events, card, witnesses⟩
    choose firing admitted key holds using witnesses
    let edge : events → (firingSpan (eventStep A label supply R)).Edge :=
      fun k => ⟨C, ⟨firing k.1 k.2, admitted k.1 k.2⟩⟩
    have injective : Function.Injective edge := by
      intro k₁ k₂ same
      have keys : ((firing k₁.1 k₁.2).rule, (firing k₁.1 k₁.2).selection.taken,
          (firing k₁.1 k₁.2).selection.read) =
          ((firing k₂.1 k₂.2).rule, (firing k₂.1 k₂.2).selection.taken,
            (firing k₂.1 k₂.2).selection.read) :=
        congrArg (fun e : (firingSpan (eventStep A label supply R)).Edge =>
          (e.2.1.rule, e.2.1.selection.taken, e.2.1.selection.read)) same
      exact Subtype.ext ((key k₁.1 k₁.2).symm.trans (keys.trans (key k₂.1 k₂.2)))
    refine ⟨events.attach.image edge, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ injective, Finset.card_attach, card]
    · intro e member
      obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp member
      exact ⟨rfl, holds k.1 k.2⟩
  · rintro ⟨edges, card, inside⟩
    let key : (firingSpan (eventStep A label supply R)).Edge → RuleInstance T × List O × List O :=
      fun e => (e.2.1.rule, e.2.1.selection.taken, e.2.1.selection.read)
    have injOn : Set.InjOn key edges := by
      rintro ⟨C₁, ⟨rule₁, queries₁, ⟨taken₁, read₁, made₁⟩⟩, ⟨_, _, _, noQueries₁, canonical₁⟩⟩ member₁
        ⟨C₂, ⟨rule₂, queries₂, ⟨taken₂, read₂, made₂⟩⟩, ⟨_, _, _, noQueries₂, canonical₂⟩⟩ member₂ same
      have at₁ : C₁ = C := (inside _ member₁).1
      have at₂ : C₂ = C := (inside _ member₂).1
      subst at₁
      subst at₂
      simp only [key, Prod.mk.injEq] at same
      obtain ⟨rfl, rfl, rfl⟩ := same
      have queries : queries₁ = queries₂ := noQueries₁.trans noQueries₂.symm
      have made : made₁ = made₂ := canonical₁.trans canonical₂.symm
      subst queries
      subst made
      rfl
    refine ⟨edges.image key, ?_, ?_⟩
    · rw [Finset.card_image_of_injOn injOn, card]
    · intro k member
      obtain ⟨⟨C', f, admitted⟩, edgeIn, rfl⟩ := Finset.mem_image.mp member
      obtain ⟨source, holds⟩ := inside _ edgeIn
      have atC : C' = C := source
      subst atC
      exact ⟨f, admitted, rfl, holds⟩

/-- **Counting events of the real step is counting firings of the event step**, into predicates
that renaming of identities cannot change. -/
theorem program_events_counted (supply : Supply label) (R : Set (RuleInstance T)) (n : ℕ)
    {φ : Configuration T O → Prop}
    (invariant : ∀ (π : Equiv.Perm O) (D : Configuration T O), Keeps label π →
      (φ (renameConf π D) ↔ φ D))
    (C : Configuration T O) :
    eventDiamond A (program A label R) n φ C ↔
      countingDiamond (firingSpan (eventStep A label supply R)) n φ C :=
  (program_events_iff A label supply R n invariant C).trans (eventStep_events_iff A label supply R n φ C)

/-- **Renaming identities carries events**, with their counts. -/
theorem eventDiamond_rename (R : Set (RuleInstance T)) (n : ℕ) {φ : Configuration T O → Prop}
    (invariant : ∀ (π : Equiv.Perm O) (D : Configuration T O), Keeps label π →
      (φ (renameConf π D) ↔ φ D))
    {π : Equiv.Perm O} (keeps : Keeps label π) (C : Configuration T O) :
    eventDiamond A (program A label R) n φ C → eventDiamond A (program A label R) n φ (renameConf π C) := by
  classical
  rintro ⟨events, card, witnesses⟩
  let move : RuleInstance T × List O × List O → RuleInstance T × List O × List O :=
    fun k => (k.1, k.2.1.map π, k.2.2.map π)
  have injective : Function.Injective move := by
    rintro ⟨r₁, t₁, d₁⟩ ⟨r₂, t₂, d₂⟩ same
    simp only [move, Prod.mk.injEq] at same
    obtain ⟨rfl, taken, read⟩ := same
    obtain rfl := List.map_injective_iff.mpr π.injective taken
    obtain rfl := List.map_injective_iff.mpr π.injective read
    rfl
  refine ⟨events.image move, by rw [Finset.card_image_of_injective _ injective, card], ?_⟩
  intro k member
  obtain ⟨k₀, inEvents, rfl⟩ := Finset.mem_image.mp member
  obtain ⟨⟨rule, queries, sel⟩, ⟨_, valid, inR⟩, key, holds⟩ := witnesses k₀ inEvents
  let f : AnnotatedRuns.Firing T S O := ⟨rule, [], renameSel π sel⟩
  have fValid : f.Valid A label (renameConf π C) :=
    (PredicateQueryAdmission.valid_empty_iff A label rule _ _).mpr (valid_rename A label keeps valid.firing)
  refine ⟨f, ⟨(AnnotatedRuns.firstOrder A label).toStep.prepares fValid, fValid, inR⟩, ?_, ?_⟩
  · rw [← key]
    rfl
  · show φ ((renameSel π sel).result label rule (renameConf π C))
    rw [result_rename label keeps, invariant π _ keeps]
    exact holds

theorem eventDiamond_rename_iff (R : Set (RuleInstance T)) (n : ℕ) {φ : Configuration T O → Prop}
    (invariant : ∀ (π : Equiv.Perm O) (D : Configuration T O), Keeps label π →
      (φ (renameConf π D) ↔ φ D))
    {π : Equiv.Perm O} (keeps : Keeps label π) (C : Configuration T O) :
    eventDiamond A (program A label R) n φ (renameConf π C) ↔ eventDiamond A (program A label R) n φ C := by
  constructor
  · intro holds
    have back := eventDiamond_rename A label R n invariant (keeps_symm label keeps) _ holds
    rwa [renameConf_symm] at back
  · exact eventDiamond_rename A label R n invariant keeps C

/-- **Graded formulas read over the real step**, counting events. -/
def eventSat (R : Set (RuleInstance T)) {Atom : Type uA} (observes : Atom → Configuration T O → Prop) :
    GFormula Atom → Configuration T O → Prop
  | .top, _ => True
  | .atom a, C => observes a C
  | .conj l r, C => eventSat R observes l C ∧ eventSat R observes r C
  | .neg inner, C => ¬ eventSat R observes inner C
  | .atLeast n inner, C => eventDiamond A (program A label R) n (eventSat R observes inner) C

/-- Graded formulas cannot tell renamed stores apart, when the observations cannot. -/
theorem eventSat_rename (R : Set (RuleInstance T)) {Atom : Type uA}
    (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C)) :
    ∀ (φ : GFormula Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (eventSat A label R observes φ (renameConf π C) ↔ eventSat A label R observes φ C)
  | .top, _, _, _ => Iff.rfl
  | .atom a, π, C, keeps => invariant a π C keeps
  | .conj l r, π, C, keeps => and_congr (eventSat_rename R observes invariant l π C keeps)
      (eventSat_rename R observes invariant r π C keeps)
  | .neg inner, π, C, keeps => not_congr (eventSat_rename R observes invariant inner π C keeps)
  | .atLeast n inner, _, C, keeps =>
      eventDiamond_rename_iff A label R n
        (fun π' D keeps' => eventSat_rename R observes invariant inner π' D keeps') keeps C

/-- **Reading graded formulas over the real step, counting events, is reading them over the event
step**, for observations that renaming cannot change. -/
theorem eventSat_iff_gsat (supply : Supply label) (R : Set (RuleInstance T)) {Atom : Type uA}
    (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C)) :
    ∀ (φ : GFormula Atom) (C : Configuration T O),
      eventSat A label R observes φ C ↔ gsat (firingSpan (eventStep A label supply R)) observes φ C
  | .top, _ => Iff.rfl
  | .atom _, _ => Iff.rfl
  | .conj l r, C => and_congr (eventSat_iff_gsat supply R observes invariant l C)
      (eventSat_iff_gsat supply R observes invariant r C)
  | .neg inner, C => not_congr (eventSat_iff_gsat supply R observes invariant inner C)
  | .atLeast n inner, C =>
      (program_events_counted A label supply R n
        (fun π D keeps => eventSat_rename A label R observes invariant inner π D keeps) C).trans
        (countingDiamond_congr _ (fun _ _ => eventSat_iff_gsat supply R observes invariant inner _) n)

/-- **Graded adequacy on the real step, counting events, under every finite program**: graded
formulas read over the real step's firings, counted up to their events, tell stores apart exactly
as counting bisimilarity of the event step does. -/
theorem program_graded_adequacy (supply : Supply label) {R : Set (RuleInstance T)} (finite : R.Finite)
    {Atom : Type uA} (observes : Atom → Configuration T O → Prop)
    (invariant : ∀ (a : Atom) (π : Equiv.Perm O) (C : Configuration T O), Keeps label π →
      (observes a (renameConf π C) ↔ observes a C)) (C D : Configuration T O) :
    (∀ φ : GFormula Atom, eventSat A label R observes φ C ↔ eventSat A label R observes φ D) ↔
      CountingBisimilar (firingSpan (eventStep A label supply R)) observes C D := by
  rw [← event_graded_adequacy A label supply finite observes C D]
  have reads := eventSat_iff_gsat A label supply R observes invariant
  exact ⟨fun same φ => (reads φ C).symm.trans ((same φ).trans (reads φ D)),
    fun same φ => (reads φ C).trans ((same φ).trans (reads φ D).symm)⟩

end Events

/-! ## Control: two copies against one -/

section Control

open NamesOnTheStep NamesOnTheStep.IssuingControls

/-- The program that reads `T`. -/
def readsT : RuleInstance Expr := ⟨[], [factT], [], [], []⟩

abbrev readStep := eventStep ground Prod.fst occSupply {readsT}

/-- One copy of `T`, and two. -/
def oneCopy (knowledge : EquationStore Expr) : Conf := ⟨knowledge, {(factT, 0)}⟩
def twoCopies (knowledge : EquationStore Expr) : Conf := ⟨knowledge, {(factT, 0), (factT, 1)}⟩

/-- Reading the copy `k`. -/
def readingAt (k : ℕ) (C : Conf) : Fir :=
  ⟨readsT, [], ⟨[], [(factT, k)], freshFor Prod.fst occSupply C.present readsT.produce⟩⟩

theorem ground_consistent_iff (store : EquationStore Expr) :
    ground.Consistent store ↔ ∀ e ∈ store, e.1 = e.2 :=
  ⟨fun ⟨_, solved⟩ e member => solved e member, fun all => ⟨(), all⟩⟩

/-- A reading learns `T = T`. -/
theorem reading_problem (k : ℕ) (C : Conf) :
    (readingAt k C).selection.problem Prod.fst readsT C = C.equations ++ [(factT, factT)] := by
  simp [Selection.problem, Selection.equations, readingAt, readsT]

/-- **The reading of a present copy is an event**, wherever the knowledge is consistent. -/
theorem reading_admitted {C : Conf} {k : ℕ} (present : (factT, k) ∈ C.present)
    (consistent : ∀ e ∈ C.equations, e.1 = e.2) :
    readStep.Admits (s := C) (readingAt k C) := by
  have made : (readingAt k C).selection.made = [] := freshFor_nil Prod.fst occSupply C.present
  have valid : (readingAt k C).selection.Valid ground Prod.fst readsT C := by
    refine ⟨List.nodup_nil, made ▸ List.nodup_nil, rfl, rfl, by rw [made]; rfl, ?_, ?_, ?_⟩
    · refine ⟨by simp [readingAt, Selection.commit], ?_, by simp [readingAt, Selection.commit], ?_,
        fun _ member => by simp [Selection.commit] at member⟩
      · simpa [readingAt, Selection.commit] using present
      · show Disjoint (readingAt k C).selection.made.toFinset C.present
        rw [made]
        simp
    · rw [reading_problem]
      refine (ground_consistent_iff _).mpr fun e member => ?_
      rcases List.mem_append.mp member with inC | single
      · exact consistent e inC
      · rw [List.mem_singleton.mp single]
    · intro check member
      simp [readsT] at member
  exact ⟨(AnnotatedRuns.firstOrder ground Prod.fst).toStep.prepares
      ((PredicateQueryAdmission.valid_empty_iff ground Prod.fst readsT C _).mpr valid),
    (PredicateQueryAdmission.valid_empty_iff ground Prod.fst readsT C _).mpr valid, rfl, rfl, rfl⟩

/-- Every event of the reading program is a reading of a present copy. -/
theorem event_is_reading {C : Conf} {f : Fir} (admitted : readStep.Admits (s := C) f) :
    ∃ k, (factT, k) ∈ C.present ∧ f = readingAt k C := by
  obtain ⟨_, valid, member, noQueries, canonical⟩ := admitted
  have isReads : f.rule = readsT := member
  obtain ⟨rule, queries, ⟨taken, read, made⟩⟩ := f
  simp only at isReads noQueries canonical
  subst isReads
  subst noQueries
  have takenNil : taken = [] := List.length_eq_zero_iff.mp valid.firing.take_length.symm
  subst takenNil
  obtain ⟨o, rfl⟩ : ∃ o, read = [o] := List.length_eq_one_iff.mp valid.firing.read_length.symm
  have inside : o ∈ C.present :=
    valid.firing.occurrences.kept_subset (by simp [Selection.commit])
  have consistent := valid.firing.consistent
  obtain ⟨_, solved⟩ := consistent
  have labelled : (factT, o.1) ∈ (⟨[], [o], made⟩ : Selection Occ).problem Prod.fst readsT C := by
    simp [Selection.problem, Selection.equations, readsT]
  have equal : factT = o.1 := solved _ labelled
  refine ⟨o.2, ?_, ?_⟩
  · have same : o = (factT, o.2) := Prod.ext equal.symm rfl
    rw [← same]
    exact inside
  · have same : o = (factT, o.2) := Prod.ext equal.symm rfl
    rw [same]
    simp only [readingAt, canonical]

/-- **The result of a reading**: the knowledge learns `T = T`, the store is unchanged. -/
theorem reading_result {C : Conf} {k : ℕ} (admitted : readStep.Admits (s := C) (readingAt k C)) :
    readStep.result (readingAt k C) admitted = ⟨C.equations ++ [(factT, factT)], C.present⟩ := by
  have made : (readingAt k C).selection.made = [] := freshFor_nil Prod.fst occSupply C.present
  have taken : (readingAt k C).selection.taken = [] := rfl
  show (readingAt k C).selection.result Prod.fst readsT C = _
  simp only [Selection.result, reading_problem, fire, Selection.commit, made, taken,
    List.toFinset_nil, Finset.sdiff_empty, Finset.union_empty]

/-- **Two copies give two events.** -/
theorem two_copies_counted (knowledge : EquationStore Expr) (consistent : ∀ e ∈ knowledge, e.1 = e.2) :
    countingDiamond (firingSpan readStep) 2 (fun _ => True) (twoCopies knowledge) := by
  classical
  have first := reading_admitted (C := twoCopies knowledge) (k := 0) (by simp [twoCopies]) consistent
  have second := reading_admitted (C := twoCopies knowledge) (k := 1) (by simp [twoCopies]) consistent
  let e₀ : (firingSpan readStep).Edge := ⟨twoCopies knowledge, readingAt 0 (twoCopies knowledge), first⟩
  let e₁ : (firingSpan readStep).Edge := ⟨twoCopies knowledge, readingAt 1 (twoCopies knowledge), second⟩
  have distinct : e₀ ≠ e₁ := by
    intro same
    have firings := congrArg (fun e : (firingSpan readStep).Edge => e.2.1.selection.read) same
    simp [e₀, e₁, readingAt] at firings
  refine ⟨{e₀, e₁}, Finset.card_pair distinct, ?_⟩
  intro e member
  rcases Finset.mem_insert.mp member with same | other
  · rw [same]
    exact ⟨rfl, trivial⟩
  · rw [Finset.mem_singleton.mp other]
    exact ⟨rfl, trivial⟩

/-- **One copy gives one event.** -/
theorem one_copy_counted_once (knowledge : EquationStore Expr) :
    ¬ countingDiamond (firingSpan readStep) 2 (fun _ => True) (oneCopy knowledge) := by
  rintro ⟨edges, card, inside⟩
  have atMostOne : edges.card ≤ 1 := by
    rw [Finset.card_le_one]
    rintro ⟨C₁, f₁, a₁⟩ member₁ ⟨C₂, f₂, a₂⟩ member₂
    have at₁ : C₁ = oneCopy knowledge := (inside _ member₁).1
    have at₂ : C₂ = oneCopy knowledge := (inside _ member₂).1
    subst at₁
    subst at₂
    obtain ⟨k₁, present₁, rfl⟩ := event_is_reading a₁
    obtain ⟨k₂, present₂, rfl⟩ := event_is_reading a₂
    have zero₁ : k₁ = 0 := by simpa [oneCopy] using present₁
    have zero₂ : k₂ = 0 := by simpa [oneCopy] using present₂
    subst zero₁
    subst zero₂
    rfl
  omega

/-- The plain diamond holds at both. -/
theorem plain_diamond_both (knowledge : EquationStore Expr) (consistent : ∀ e ∈ knowledge, e.1 = e.2) :
    derivedDiamond (firingSpan readStep) (fun _ => True) (oneCopy knowledge) ∧
      derivedDiamond (firingSpan readStep) (fun _ => True) (twoCopies knowledge) := by
  rw [← countingDiamond_one]
  exact ⟨countingDiamond_anti _ (le_refl 1)
      ⟨{⟨_, _, reading_admitted (C := oneCopy knowledge) (k := 0) (by simp [oneCopy]) consistent⟩},
        rfl, fun e member => by rw [Finset.mem_singleton.mp member]; exact ⟨rfl, trivial⟩⟩,
    countingDiamond_anti _ (by norm_num) (two_copies_counted knowledge consistent)⟩

/-- Successors of the reading program from a store of copies of `T`. -/
theorem read_succ_iff {C C' : Conf} (copies : ∃ k, (factT, k) ∈ C.present) :
    Succ readStep C C' ↔ (∀ e ∈ C.equations, e.1 = e.2) ∧ C' = ⟨C.equations ++ [(factT, factT)], C.present⟩ := by
  constructor
  · rintro ⟨f, admitted, rfl⟩
    obtain ⟨k, _, rfl⟩ := event_is_reading admitted
    refine ⟨?_, reading_result admitted⟩
    obtain ⟨_, solved⟩ := admitted.2.1.firing.consistent
    intro e member
    exact solved e (by simp [Selection.problem, member])
  · rintro ⟨consistent, rfl⟩
    obtain ⟨k, present⟩ := copies
    exact ⟨_, reading_admitted present consistent, reading_result _⟩

/-- **Plain bisimilarity**: observing the knowledge, one copy and two copies are bisimilar. -/
theorem plain_bisimilar (knowledge : EquationStore Expr) :
    (stepSystem readStep fun (K : EquationStore Expr) (C : Conf) => C.equations = K).Bisimilar
      (oneCopy knowledge) (twoCopies knowledge) := by
  let Z : Conf → Conf → Prop := fun C D =>
    C.equations = D.equations ∧ C.present = (oneCopy []).present ∧ D.present = (twoCopies []).present
  refine ⟨Z, ⟨?_, ?_, ?_⟩, rfl, rfl, rfl⟩
  · rintro C D ⟨sameKnowledge, oneC, twoD⟩ _ C' step
    have hasC : ∃ k, (factT, k) ∈ C.present := ⟨0, by rw [oneC]; simp [oneCopy]⟩
    have hasD : ∃ k, (factT, k) ∈ D.present := ⟨0, by rw [twoD]; simp [twoCopies]⟩
    obtain ⟨consistent, rfl⟩ := (read_succ_iff hasC).mp step
    refine ⟨_, (read_succ_iff hasD).mpr ⟨sameKnowledge ▸ consistent, rfl⟩, ?_⟩
    exact ⟨by simp [sameKnowledge], oneC, twoD⟩
  · rintro C D ⟨sameKnowledge, oneC, twoD⟩ _ D' step
    have hasC : ∃ k, (factT, k) ∈ C.present := ⟨0, by rw [oneC]; simp [oneCopy]⟩
    have hasD : ∃ k, (factT, k) ∈ D.present := ⟨0, by rw [twoD]; simp [twoCopies]⟩
    obtain ⟨consistent, rfl⟩ := (read_succ_iff hasD).mp step
    refine ⟨_, (read_succ_iff hasC).mpr ⟨sameKnowledge.symm ▸ consistent, rfl⟩, ?_⟩
    exact ⟨by simp [sameKnowledge], oneC, twoD⟩
  · rintro C D ⟨sameKnowledge, _, _⟩ K
    show C.equations = K ↔ D.equations = K
    rw [sameKnowledge]

/-- **Control: counts tell apart what the plain modalities do not.** -/
theorem counting_separates :
    (stepSystem readStep fun (K : EquationStore Expr) (C : Conf) => C.equations = K).Bisimilar
        (oneCopy []) (twoCopies []) ∧
      (stepSystem readStep fun (K : EquationStore Expr) (C : Conf) => C.equations = K).LogicallyEquivalent
        (oneCopy []) (twoCopies []) ∧
      countingDiamond (firingSpan readStep) 2 (fun _ => True) (twoCopies []) ∧
      ¬ countingDiamond (firingSpan readStep) 2 (fun _ => True) (oneCopy []) :=
  ⟨plain_bisimilar [], System.logicallyEquivalent_of_bisimilar _ (plain_bisimilar []),
    two_copies_counted [] (by simp), one_copy_counted_once []⟩

/-- **Events, not successor states**: at two copies of `T` the reading program has two firings,
and both reach one successor, so counting over the successor relation sees one. -/
theorem successors_collapse_events :
    countingDiamond (firingSpan readStep) 2 (fun _ => True) (twoCopies []) ∧
      ¬ countingDiamond (FragmentsOfTheStep.TransitionMaps.span (Succ readStep)) 2 (fun _ => True)
        (twoCopies []) := by
  refine ⟨two_copies_counted [] (by simp), ?_⟩
  rintro ⟨edges, card, inside⟩
  have unique : ∀ e ∈ edges,
      e.val = (twoCopies [], (⟨[] ++ [(factT, factT)], (twoCopies []).present⟩ : Conf)) := by
    rintro ⟨⟨x, y⟩, step⟩ member
    have source : x = twoCopies [] := (inside _ member).1
    subst source
    have reached : y = ⟨(twoCopies []).equations ++ [(factT, factT)], (twoCopies []).present⟩ :=
      ((read_succ_iff ⟨0, by simp [twoCopies]⟩).mp step).2
    show ((twoCopies [], y) : Conf × Conf) = (twoCopies [], (⟨[] ++ [(factT, factT)], (twoCopies []).present⟩ : Conf))
    rw [reached]
    rfl
  have atMostOne : edges.card ≤ 1 :=
    Finset.card_le_one.mpr fun a inA b inB => Subtype.ext ((unique a inA).trans (unique b inB).symm)
  omega

/-- **Control: possibility crosses from firings to successors, counts do not.** The map from the
reading program's firings to its successor relation lifts every successor
(`StepSpan.toSucc_source_weakPullback`), and is not locally injective: two readings reach one
successor. -/
theorem toSucc_not_locallyInjective : ¬ LocallyInjective (toSucc readStep) := by
  intro injective
  exact successors_collapse_events.2
    (map_counting_le (toSucc readStep) injective 2 (fun _ => True) (twoCopies [])
      successors_collapse_events.1)

/-! ### Control: firings of the real step are not events -/

/-- The program that makes `T` from nothing. -/
def makingT : RuleInstance Expr := ⟨[], [], [], [], [factT]⟩

/-- The empty store. -/
def emptyConf : Conf := ⟨[], ∅⟩

/-- Making `T` with the identity `(T, i)` is admitted at the empty store, for every `i`. -/
theorem making_admitted (i : ℕ) :
    (program ground Prod.fst {makingT}).Admits (s := emptyConf)
      (⟨makingT, [], ⟨[], [], [(factT, i)]⟩⟩ : Fir) := by
  have valid : (⟨[], [], [(factT, i)]⟩ : Selection Occ).Valid ground Prod.fst makingT emptyConf := by
    refine ⟨List.nodup_nil, List.nodup_singleton _, rfl, rfl, rfl, ⟨?_, ?_, ?_, ?_, ?_⟩, ⟨(), ?_⟩, ?_⟩
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit]
    · simp [Selection.commit, emptyConf]
    · intro _ inQueries
      simp [Selection.commit] at inQueries
    · intro e inProblem
      simp [Selection.problem, Selection.equations, makingT, emptyConf] at inProblem
    · intro check inChecks
      simp [makingT] at inChecks
  have fValid := (PredicateQueryAdmission.valid_empty_iff ground Prod.fst makingT emptyConf _).mpr valid
  exact ⟨(AnnotatedRuns.firstOrder ground Prod.fst).toStep.prepares fValid, fValid, rfl⟩

/-- **Firings of the real step are unbounded**: at the empty store, the making program has at least
`n` firings for every `n`, one per fresh identity. -/
theorem making_firings_unbounded (n : ℕ) :
    countingDiamond (firingSpan (program ground Prod.fst {makingT})) n (fun _ => True) emptyConf := by
  classical
  let edge : ℕ → (firingSpan (program ground Prod.fst {makingT})).Edge := fun i =>
    ⟨emptyConf, ⟨⟨makingT, [], ⟨[], [], [(factT, i)]⟩⟩, making_admitted i⟩⟩
  have injective : Function.Injective edge := by
    intro i j same
    have made : ([(factT, i)] : List Occ) = [(factT, j)] :=
      congrArg (fun e : (firingSpan (program ground Prod.fst {makingT})).Edge => e.2.1.selection.made) same
    simpa using made
  refine ⟨(Finset.range n).image edge, by rw [Finset.card_image_of_injective _ injective,
    Finset.card_range], ?_⟩
  intro e member
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp member
  exact ⟨rfl, trivial⟩

/-- **The making program has one event at the empty store.** -/
theorem making_one_event :
    eventDiamond ground (program ground Prod.fst {makingT}) 1 (fun _ => True) emptyConf ∧
      ¬ eventDiamond ground (program ground Prod.fst {makingT}) 2 (fun _ => True) emptyConf := by
  constructor
  · refine ⟨{(makingT, [], [])}, rfl, fun k member => ?_⟩
    rw [Finset.mem_singleton.mp member]
    exact ⟨⟨makingT, [], ⟨[], [], [(factT, 0)]⟩⟩, making_admitted 0, rfl, trivial⟩
  · rintro ⟨events, card, witnesses⟩
    have single : events ⊆ {(makingT, [], [])} := by
      intro k member
      obtain ⟨⟨rule, queries, ⟨taken, read, made⟩⟩, ⟨_, valid, inR⟩, key, _⟩ := witnesses k member
      have isMaking : rule = makingT := inR
      subst isMaking
      have takenNil : taken = [] := List.length_eq_zero_iff.mp valid.firing.take_length.symm
      have readNil : read = [] := List.length_eq_zero_iff.mp valid.firing.read_length.symm
      subst takenNil
      subst readNil
      rw [Finset.mem_singleton, ← key]
    have bound := Finset.card_le_card single
    rw [card, Finset.card_singleton] at bound
    omega

end Control

#print axioms countingDiamond_one
#print axioms countingDiamond_anti
#print axioms gsat_iff_of_counting
#print axioms counting_of_gequivalent
#print axioms gequivalent_isCounting
#print axioms graded_adequacy
#print axioms eventStep_edgeFinite
#print axioms event_graded_adequacy
#print axioms canonical_event
#print axioms program_events_iff
#print axioms eventStep_events_iff
#print axioms program_events_counted
#print axioms eventDiamond_rename
#print axioms eventDiamond_rename_iff
#print axioms eventSat_rename
#print axioms eventSat_iff_gsat
#print axioms program_graded_adequacy
#print axioms reading_admitted
#print axioms event_is_reading
#print axioms reading_result
#print axioms two_copies_counted
#print axioms one_copy_counted_once
#print axioms plain_diamond_both
#print axioms read_succ_iff
#print axioms plain_bisimilar
#print axioms counting_separates
#print axioms successors_collapse_events
#print axioms map_counting_le
#print axioms map_counting_iff
#print axioms gsat_along_map
#print axioms toSucc_not_locallyInjective
#print axioms making_admitted
#print axioms making_firings_unbounded
#print axioms making_one_event

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.LogicOverTheStep.CountingModalities
