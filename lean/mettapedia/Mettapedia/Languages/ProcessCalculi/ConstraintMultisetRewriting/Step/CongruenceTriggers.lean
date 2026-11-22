import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.CongruenceOpen

/-!
# Minimal trigger sets: a context-labelled step for triggered programs

The experimenter of `RaceExperiments` adds atoms at the ports. A **minimal trigger set** for a
move is the set of port atoms that the move needs and the configuration lacks, and no other.

## Atoms a firing does not use

A firing **uses** what it takes and what it reads (`uses`). For a firing without predicate queries
and checks, atoms it does not use and does not make change neither its admission
(`valid_frame`) nor its result, which carries them along (`result_frame`).

## The minimal step

Under the label `(ℓ, M)` a configuration moves when `M` is a set of ports, absent from it, used by
a firing offered under `ℓ`, and the configuration with `M` added admits that firing
(`MinimalMoves`). The label is then exactly what the firing uses and the configuration lacks
(`minimal_eq`), and it is contained in every context that admits the firing (`minimal_least`).

## Triggered programs

A program is **triggered** (`TriggeredProgram`) when every label `ℓ` has a trigger `trigger ℓ` at the
ports, and every firing offered under `ℓ` takes its trigger, touches no other port, and has no
predicate query and no check. The triggered race pair is one (`Triggered.program`). Every minimal
trigger set of a triggered program is empty or the label's trigger.

* **The minimal step's bisimilarity is open bisimilarity** (`TriggeredProgram.minimalBisimilar_iff`).
* **It is a congruence for contexts of port atoms** (`TriggeredProgram.tensor_ports`), with or
  without disjointness.

## Controls

* **Without the trigger hypothesis the two bisimilarities differ** (`Spare.open_not_minimal`): with
  a firing that takes the ports `s` and `t` and one that takes `s` alone, the empty configuration and
  `{t}` are open bisimilar, and only the first moves under the trigger set `{s, t}`; no trigger map
  makes that program triggered (`Spare.not_triggered`).
* **A disjoint context outside the ports breaks the congruence**
  (`Triggered.nonport_not_congruence`): `{p}` and `{q}` are open bisimilar, hence minimally
  bisimilar, for the triggered race pair, and beside the atom `a`, disjoint from both and not a
  port, they become the race pair, which is not.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing)
open MeTTaCalculus.OccurrenceCommits (Enabled fire)
open Mettapedia.GSLT.HennessyMilner (System)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}

/-! ## Atoms a firing does not use -/

section Frame

/-- **The occurrences a firing uses**: what it takes and what it reads. -/
def uses (f : Firing T S O) : Finset O := f.selection.taken.toFinset ∪ f.selection.read.toFinset

variable {A : SubstitutionAction T S} {label : O → T}

/-- **An admitted firing finds what it uses.** -/
theorem uses_subset {f : Firing T S O} {C : Configuration T O} (valid : f.Valid A label C) :
    uses f ⊆ C.present :=
  Finset.union_subset valid.firing.occurrences.taken_subset valid.firing.occurrences.kept_subset

/-- **Atoms a firing neither uses nor makes do not change its admission**, for a firing without
predicate queries and checks. -/
theorem valid_frame {f : Firing T S O} (noQueries : f.queries = []) (noChecks : f.rule.checks = [])
    (K : EquationStore T) {X Y : Finset O} (sub : X ⊆ Y)
    (unused : ∀ o ∈ Y, o ∉ X → o ∉ uses f ∧ o ∉ f.selection.made.toFinset) :
    f.Valid A label ⟨K, Y⟩ ↔ f.Valid A label ⟨K, X⟩ := by
  have enabled : Enabled label Y (f.selection.commit (T := T)) ↔
      Enabled label X (f.selection.commit (T := T)) := by
    constructor
    · rintro ⟨taken, kept, apart, fresh, queries⟩
      refine ⟨fun o member => ?_, fun o member => ?_, apart,
        Finset.disjoint_of_subset_right sub fresh, fun read member => by simp [Selection.commit] at member⟩
      · by_contra outside
        exact (unused o (taken member) outside).1 (Finset.mem_union_left _ member)
      · by_contra outside
        exact (unused o (kept member) outside).1 (Finset.mem_union_right _ member)
    · rintro ⟨taken, kept, apart, fresh, queries⟩
      refine ⟨taken.trans sub, kept.trans sub, apart, Finset.disjoint_left.mpr fun {o} made inY => ?_,
        fun read member => by simp [Selection.commit] at member⟩
      by_cases inX : o ∈ X
      · exact Finset.disjoint_left.mp fresh made inX
      · exact (unused o inY inX).2 made
  constructor
  · rintro ⟨⟨takeDistinct, madeDistinct, takeLength, readLength, outputs, occurrences, consistent, -⟩,
      -⟩
    exact ⟨⟨takeDistinct, madeDistinct, takeLength, readLength, outputs, enabled.mp occurrences,
      consistent, fun check member => by rw [noChecks] at member; simp at member⟩,
      fun query member => by rw [noQueries] at member; simp at member⟩
  · rintro ⟨⟨takeDistinct, madeDistinct, takeLength, readLength, outputs, occurrences, consistent, -⟩,
      -⟩
    exact ⟨⟨takeDistinct, madeDistinct, takeLength, readLength, outputs, enabled.mpr occurrences,
      consistent, fun check member => by rw [noChecks] at member; simp at member⟩,
      fun query member => by rw [noQueries] at member; simp at member⟩

/-- **A firing carries the atoms beside it along**: adding `N ⊇ M` instead of `M` adds to the result
what `N` holds and the firing does not take. -/
theorem result_frame (f : Firing T S O) (K : EquationStore T) (X : Finset O) {M N : Finset O}
    (sub : M ⊆ N) :
    f.result label ⟨K, X ∪ N⟩ = addAll (f.result label ⟨K, X ∪ M⟩) (N \ f.selection.taken.toFinset) := by
  have present : fire (X ∪ N) (f.selection.commit (T := T)) =
      fire (X ∪ M) (f.selection.commit (T := T)) ∪ (N \ f.selection.taken.toFinset) := by
    ext o
    simp only [MeTTaCalculus.OccurrenceCommits.mem_fire, Finset.mem_union, Finset.mem_sdiff,
      Selection.commit]
    constructor
    · rintro (⟨inX | inN, notTaken⟩ | made)
      · exact Or.inl (Or.inl ⟨Or.inl inX, notTaken⟩)
      · exact Or.inr ⟨inN, notTaken⟩
      · exact Or.inl (Or.inr made)
    · rintro ((⟨inX | inM, notTaken⟩ | made) | ⟨inN, notTaken⟩)
      · exact Or.inl ⟨Or.inl inX, notTaken⟩
      · exact Or.inl ⟨Or.inr (sub inM), notTaken⟩
      · exact Or.inr made
      · exact Or.inl ⟨Or.inr inN, notTaken⟩
  show (⟨f.selection.problem label f.rule ⟨K, X ∪ N⟩, fire (X ∪ N) (f.selection.commit (T := T))⟩ :
      Configuration T O) =
    ⟨f.selection.problem label f.rule ⟨K, X ∪ M⟩,
      fire (X ∪ M) (f.selection.commit (T := T)) ∪ (N \ f.selection.taken.toFinset)⟩
  rw [present]
  rfl

end Frame

/-! ## The minimal step -/

section Minimal

variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)
  (ports : O → Prop)

/-- **A move under a minimal trigger set**: under `(ℓ, M)`, with `M` a set of ports absent from the
configuration and used by a firing offered under `ℓ`, the configuration with `M` added fires that
firing. -/
def MinimalMoves (C : Configuration T O) (lab : L × Finset O) (D : Configuration T O) : Prop :=
  ∃ f, offers lab.1 f ∧ (∀ o ∈ lab.2, ports o) ∧ Disjoint lab.2 C.present ∧ lab.2 ⊆ uses f ∧
    f.Valid A label (addAll C lab.2) ∧ D = f.result label (addAll C lab.2)

/-- The minimal step as a Hennessy–Milner system. -/
def minimalSystem : System (gslt A label offers) where
  Atom := PEmpty.{1}
  observes atom _ := atom.elim
  observes_resp atom := atom.elim
  Label := L × Finset O
  act lab C D := MinimalMoves A label offers ports C lab D
  act_resp_left := by
    intro lab C C' D same step
    exact ⟨D, (same : C = C') ▸ step, rfl⟩
  act_resp_right := by
    intro lab C D D' step same
    exact (same : D = D') ▸ step

/-- **Bisimilarity of the minimal step.** -/
def MinimalBisimilar (C D : Configuration T O) : Prop :=
  (minimalSystem A label offers ports).Bisimilar C D

/-- **A triggered program**: every label has a trigger at the ports, and every firing offered under
it takes the trigger, touches no other port, and has no predicate query and no check. -/
structure TriggeredProgram (trigger : L → O) : Prop where
  port : ∀ ℓ, ports (trigger ℓ)
  takes : ∀ ℓ f, offers ℓ f → trigger ℓ ∈ f.selection.taken
  only : ∀ ℓ f, offers ℓ f → ∀ o, ports o → o ∈ uses f ∨ o ∈ f.selection.made.toFinset →
    o = trigger ℓ
  queries : ∀ ℓ f, offers ℓ f → f.queries = []
  checks : ∀ ℓ f, offers ℓ f → f.rule.checks = []

variable {A label offers ports}

theorem MinimalBisimilar.step {C D : Configuration T O} (h : MinimalBisimilar A label offers ports C D)
    {lab : L × Finset O} {C' : Configuration T O} (moved : MinimalMoves A label offers ports C lab C') :
    ∃ D', MinimalMoves A label offers ports D lab D' ∧ MinimalBisimilar A label offers ports C' D' := by
  obtain ⟨R, bisimulation, related⟩ := h
  obtain ⟨D', moved', related'⟩ := bisimulation.1 related lab moved
  exact ⟨D', moved', R, bisimulation, related'⟩

theorem MinimalBisimilar.symm {C D : Configuration T O} (h : MinimalBisimilar A label offers ports C D) :
    MinimalBisimilar A label offers ports D C :=
  (minimalSystem A label offers ports).bisimilar_symm h

/-- **The trigger set is what the firing uses and the configuration lacks.** -/
theorem minimal_eq {C : Configuration T O} {M : Finset O} {f : Firing T S O}
    (apart : Disjoint M C.present) (used : M ⊆ uses f) (valid : f.Valid A label (addAll C M)) :
    M = uses f \ C.present := by
  ext o
  constructor
  · intro inM
    exact Finset.mem_sdiff.mpr ⟨used inM, Finset.disjoint_left.mp apart inM⟩
  · intro member
    obtain ⟨inUses, notC⟩ := Finset.mem_sdiff.mp member
    rcases Finset.mem_union.mp (uses_subset valid inUses) with inC | inM
    · exact absurd inC notC
    · exact inM

/-- **The trigger set is contained in every context that admits the firing.** -/
theorem minimal_least {C : Configuration T O} {M N : Finset O} {f : Firing T S O}
    (apart : Disjoint M C.present) (used : M ⊆ uses f) (validN : f.Valid A label (addAll C N)) :
    M ⊆ N := by
  intro o inM
  rcases Finset.mem_union.mp (uses_subset validN (used inM)) with inC | inN
  · exact absurd inC (Finset.disjoint_left.mp apart inM)
  · exact inN

variable {trigger : L → O}

/-- At an admitted firing of a triggered program, the label's trigger is present. -/
theorem TriggeredProgram.present (program : TriggeredProgram offers ports trigger) {ℓ : L}
    {f : Firing T S O} (offered : offers ℓ f) {C : Configuration T O} (valid : f.Valid A label C) :
    trigger ℓ ∈ C.present :=
  uses_subset valid (Finset.mem_union_left _ (List.mem_toFinset.mpr (program.takes ℓ f offered)))

theorem TriggeredProgram.mem_uses (program : TriggeredProgram offers ports trigger) {ℓ : L}
    {f : Firing T S O} (offered : offers ℓ f) : trigger ℓ ∈ uses f :=
  Finset.mem_union_left _ (List.mem_toFinset.mpr (program.takes ℓ f offered))

/-- **A trigger set of a triggered program holds at most the label's trigger.** -/
theorem TriggeredProgram.eq_trigger (program : TriggeredProgram offers ports trigger) {ℓ : L}
    {f : Firing T S O} (offered : offers ℓ f) {M : Finset O} (portsM : ∀ o ∈ M, ports o)
    (used : M ⊆ uses f) : ∀ o ∈ M, o = trigger ℓ :=
  fun o inM => program.only ℓ f offered o (portsM o inM) (Or.inl (used inM))

/-- Of a set of ports, an offered firing takes at most its trigger. -/
theorem TriggeredProgram.sdiff_taken (program : TriggeredProgram offers ports trigger) {ℓ : L}
    {f : Firing T S O} (offered : offers ℓ f) {N : Finset O} (portsN : ∀ o ∈ N, ports o) :
    N \ f.selection.taken.toFinset = N.erase (trigger ℓ) := by
  ext o
  rw [Finset.mem_sdiff, Finset.mem_erase, List.mem_toFinset]
  constructor
  · rintro ⟨inN, notTaken⟩
    refine ⟨fun same => notTaken ?_, inN⟩
    rw [same]
    exact program.takes ℓ f offered
  · rintro ⟨notTrigger, inN⟩
    exact ⟨inN, fun taken => notTrigger (program.only ℓ f offered o (portsN o inN)
      (Or.inl (Finset.mem_union_left _ (List.mem_toFinset.mpr taken))))⟩

/-- **Open bisimilarity answers a minimal move.** -/
theorem TriggeredProgram.open_step (program : TriggeredProgram offers ports trigger)
    {X Y : Configuration T O} (related : OpenBisimilar A label offers ports X Y) {ℓ : L}
    {M : Finset O} {f : Firing T S O} (offered : offers ℓ f) (portsM : ∀ o ∈ M, ports o)
    (apart : Disjoint M X.present) (used : M ⊆ uses f) (valid : f.Valid A label (addAll X M)) :
    ∃ Y', MinimalMoves A label offers ports Y (ℓ, M) Y' ∧
      OpenBisimilar A label offers ports (f.result label (addAll X M)) Y' := by
  have onlyTrigger := program.eq_trigger offered portsM used
  obtain ⟨Y', ⟨g, offeredG, validG, rfl⟩, related'⟩ :=
    (related.add_ports M portsM).step (lab := .inl ℓ) ⟨f, offered, valid, rfl⟩
  have apartY : Disjoint M Y.present := by
    refine Finset.disjoint_left.mpr fun {o} inM inY => ?_
    have isTrigger := onlyTrigger o inM
    have unchanged : addAll Y M = Y := by
      show (⟨Y.equations, Y.present ∪ M⟩ : Configuration T O) = Y
      rw [Finset.union_eq_left.mpr fun x member => by rw [onlyTrigger x member, ← isTrigger]; exact inY]
    rw [unchanged] at validG
    have flipped : OpenBisimilar A label offers ports Y X :=
      (openSystem A label offers ports).bisimilar_symm related
    obtain ⟨X', ⟨h, offeredH, validH, -⟩, -⟩ := flipped.step (lab := .inl ℓ) ⟨g, offeredG, validG, rfl⟩
    refine Finset.disjoint_left.mp apart inM ?_
    rw [isTrigger]
    exact program.present offeredH validH
  refine ⟨g.result label (addAll Y M), ⟨g, offeredG, portsM, apartY, fun o inM => ?_, validG, rfl⟩,
    related'⟩
  rw [onlyTrigger o inM]
  exact program.mem_uses offeredG

/-- **Minimal bisimilarity answers a move beside port atoms.** A move of `C` beside the ports `N` is a
minimal move of `C` with the ports beside it; its answer at `D` is admitted beside `N` too, and both
results keep the ports of `N` other than the trigger. -/
theorem TriggeredProgram.closed_step (program : TriggeredProgram offers ports trigger)
    {C D : Configuration T O} (related : MinimalBisimilar A label offers ports C D) {N : Finset O}
    (portsN : ∀ o ∈ N, ports o) {ℓ : L} {f : Firing T S O} (offered : offers ℓ f)
    (valid : f.Valid A label (addAll C N)) :
    ∃ g, offers ℓ g ∧ g.Valid A label (addAll D N) ∧
      ∃ C' D', MinimalBisimilar A label offers ports C' D' ∧
        f.result label (addAll C N) = addAll C' (N.erase (trigger ℓ)) ∧
        g.result label (addAll D N) = addAll D' (N.erase (trigger ℓ)) := by
  have usesSub : uses f ⊆ C.present ∪ N := uses_subset valid
  have sub : uses f \ C.present ⊆ N := fun o member => by
    obtain ⟨inUses, notC⟩ := Finset.mem_sdiff.mp member
    rcases Finset.mem_union.mp (usesSub inUses) with inC | inN
    · exact absurd inC notC
    · exact inN
  have validM : f.Valid A label (addAll C (uses f \ C.present)) := by
    refine (valid_frame (program.queries ℓ f offered) (program.checks ℓ f offered) C.equations
      (Finset.union_subset_union (Finset.Subset.refl _) sub)
      fun o inY notX => ⟨fun inUses => ?_, fun made => ?_⟩).mp valid
    · refine notX (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨inUses, fun inC => ?_⟩))
      exact notX (Finset.mem_union_left _ inC)
    · exact Finset.disjoint_left.mp valid.firing.occurrences.fresh made inY
  obtain ⟨D'', ⟨g, offeredG, -, -, -, validG, rfl⟩, related'⟩ :=
    related.step (lab := (ℓ, uses f \ C.present)) ⟨f, offered, fun o member => portsN o (sub member),
      Finset.sdiff_disjoint, Finset.sdiff_subset, validM, rfl⟩
  have usesG : uses g ⊆ D.present ∪ (uses f \ C.present) := uses_subset validG
  have validGN : g.Valid A label (addAll D N) := by
    refine (valid_frame (program.queries ℓ g offeredG) (program.checks ℓ g offeredG) D.equations
      (Finset.union_subset_union (Finset.Subset.refl _) sub)
      fun o inY notX => ⟨fun inUses => notX (usesG inUses), fun made => ?_⟩).mpr validG
    have inN : o ∈ N := by
      rcases Finset.mem_union.mp inY with inD | inN
      · exact absurd (Finset.mem_union_left _ inD) notX
      · exact inN
    have isTrigger := program.only ℓ g offeredG o (portsN o inN) (Or.inr made)
    refine notX ?_
    rw [isTrigger]
    exact usesG (program.mem_uses offeredG)
  refine ⟨g, offeredG, validGN, _, _, related', ?_, ?_⟩
  · rw [← program.sdiff_taken offered portsN]
    exact result_frame f C.equations C.present sub
  · rw [← program.sdiff_taken offeredG portsN]
    exact result_frame g D.equations D.present sub

/-- **For a triggered program, the minimal step's bisimilarity is open bisimilarity.** -/
theorem TriggeredProgram.minimalBisimilar_iff (program : TriggeredProgram offers ports trigger)
    {C D : Configuration T O} :
    MinimalBisimilar A label offers ports C D ↔ OpenBisimilar A label offers ports C D := by
  constructor
  · intro h
    refine ⟨fun X Y => ∃ C₀ D₀ N, MinimalBisimilar A label offers ports C₀ D₀ ∧ (∀ o ∈ N, ports o) ∧
        X = addAll C₀ N ∧ Y = addAll D₀ N, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
      C, D, ∅, h, fun o member => absurd member (Finset.notMem_empty o), (addAll_empty C).symm,
      (addAll_empty D).symm⟩
    · rintro X Y ⟨C₀, D₀, N, related, portsN, rfl, rfl⟩ (ℓ | o) X' moved
      · obtain ⟨f, offered, valid, rfl⟩ := moved
        obtain ⟨g, offeredG, validG, C', D', related', left, right⟩ :=
          program.closed_step related portsN offered valid
        exact ⟨g.result label (addAll D₀ N), ⟨g, offeredG, validG, rfl⟩, C', D', _, related',
          fun x member => portsN x (Finset.mem_of_mem_erase member), left, right⟩
      · obtain ⟨port, rfl⟩ := moved
        refine ⟨addAtom (addAll D₀ N) o, ⟨port, rfl⟩, C₀, D₀, insert o N, related,
          fun x member => ?_, (addAll_insert C₀ o N).symm, (addAll_insert D₀ o N).symm⟩
        rcases Finset.mem_insert.mp member with same | inN
        · rw [same]
          exact port
        · exact portsN x inN
    · rintro X Y ⟨C₀, D₀, N, related, portsN, rfl, rfl⟩ (ℓ | o) Y' moved
      · obtain ⟨g, offered, valid, rfl⟩ := moved
        obtain ⟨f, offeredF, validF, D', C', related', right, left⟩ :=
          program.closed_step related.symm portsN offered valid
        exact ⟨f.result label (addAll C₀ N), ⟨f, offeredF, validF, rfl⟩, C', D', _, related'.symm,
          fun x member => portsN x (Finset.mem_of_mem_erase member), left, right⟩
      · obtain ⟨port, rfl⟩ := moved
        refine ⟨addAtom (addAll C₀ N) o, ⟨port, rfl⟩, C₀, D₀, insert o N, related,
          fun x member => ?_, (addAll_insert C₀ o N).symm, (addAll_insert D₀ o N).symm⟩
        rcases Finset.mem_insert.mp member with same | inN
        · rw [same]
          exact port
        · exact portsN x inN
  · intro h
    refine ⟨OpenBisimilar A label offers ports, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, h⟩
    · rintro X Y related ⟨ℓ, M⟩ X' ⟨f, offered, portsM, apart, used, valid, rfl⟩
      exact program.open_step related offered portsM apart used valid
    · rintro X Y related ⟨ℓ, M⟩ Y' ⟨g, offered, portsM, apart, used, valid, rfl⟩
      obtain ⟨X', moved, related'⟩ := program.open_step
        ((openSystem A label offers ports).bisimilar_symm related) offered portsM apart used valid
      exact ⟨X', moved, (openSystem A label offers ports).bisimilar_symm related'⟩

/-- **For a triggered program, minimal bisimilarity is a congruence for contexts of port atoms.** -/
theorem TriggeredProgram.tensor_ports (program : TriggeredProgram offers ports trigger)
    {C D : Configuration T O} (h : MinimalBisimilar A label offers ports C D) (N : Finset O)
    (portsN : ∀ o ∈ N, ports o) :
    MinimalBisimilar A label offers ports (AnnotatedRuns.tensor C ⟨[], N⟩)
      (AnnotatedRuns.tensor D ⟨[], N⟩) :=
  program.minimalBisimilar_iff.mpr ((program.minimalBisimilar_iff.mp h).tensor_ports N portsN)

end Minimal

/-! ## Controls -/

/-! ### The triggered race pair -/

namespace Triggered

variable (τ : T)

/-- The trigger of each action. -/
def triggerOf : Act → Site
  | .A => .ta
  | .B => .tb
  | .C => .tc

/-- **The triggered race pair is a triggered program.** -/
theorem program : TriggeredProgram (offers (S := S) τ) trigger triggerOf where
  port ℓ := by cases ℓ <;> simp [trigger, triggerOf]
  takes ℓ f member := by
    simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> simp [firing, triggerOf]
  only ℓ f member o port used := by
    simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    simp only [trigger] at port
    rcases port with rfl | rfl | rfl <;>
      rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ <;> simp [uses, firing, triggerOf] at used ⊢
  queries ℓ f member := by
    simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> rfl
  checks ℓ f member := by
    simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
    rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ <;> rfl

variable (A : SubstitutionAction T S)

/-- **The minimal step separates the triggered race pair.** -/
theorem not_minimalBisimilar : ¬ MinimalBisimilar A (label τ) (offers τ) trigger P Q := fun h =>
  not_openBisimilar τ A ((program τ).minimalBisimilar_iff.mp h)

/-- Configurations of `p` or `q` with triggers and no knowledge never move. -/
theorem stuck {C : Configuration T Site} (empty : C.equations = [])
    (inside : ∀ o ∈ C.present, o = .p ∨ o = .q ∨ trigger o) {ℓ : Act} {D : Configuration T Site} :
    ¬ Moves A (label τ) (offers τ) C ℓ D := by
  rintro ⟨f, member, valid, -⟩
  have refl : Race.Reflexive C.equations := by
    rw [empty]
    exact reflexive_nil
  rw [valid_iff τ A member refl] at valid
  have found : ∀ o, o ∈ (f.selection.commit (T := T)).taken → o = .p ∨ o = .q ∨ trigger o :=
    fun o taken => inside o (valid.taken_subset taken)
  simp only [offers, alphabet, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false] at member
  rcases member with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ <;> simp [firing, Selection.commit, trigger] at found

/-- **`{p}` and `{q}` are open bisimilar with the triggers as ports**: neither ever moves. -/
theorem stuck_openBisimilar :
    OpenBisimilar A (label τ) (offers τ) trigger ⟨[], {.p}⟩ ⟨[], {.q}⟩ := by
  refine ⟨fun X Y => X.equations = [] ∧ Y.equations = [] ∧ ∃ N : Finset Site, (∀ o ∈ N, trigger o) ∧
      X.present = insert .p N ∧ Y.present = insert .q N, ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
    rfl, rfl, ∅, fun o member => absurd member (Finset.notMem_empty o), rfl, rfl⟩
  · rintro X Y ⟨emptyX, emptyY, N, triggers, presentX, presentY⟩ (ℓ | o) X' moved
    · refine absurd moved (stuck τ A emptyX fun o member => ?_)
      rw [presentX] at member
      rcases Finset.mem_insert.mp member with rfl | inN
      · exact .inl rfl
      · exact .inr (.inr (triggers o inN))
    · obtain ⟨port, rfl⟩ := moved
      refine ⟨addAtom Y o, ⟨port, rfl⟩, emptyX, emptyY, insert o N, fun x member => ?_, ?_, ?_⟩
      · rcases Finset.mem_insert.mp member with rfl | inN
        · exact port
        · exact triggers x inN
      · show insert o X.present = insert .p (insert o N)
        rw [presentX, Finset.insert_comm]
      · show insert o Y.present = insert .q (insert o N)
        rw [presentY, Finset.insert_comm]
  · rintro X Y ⟨emptyX, emptyY, N, triggers, presentX, presentY⟩ (ℓ | o) Y' moved
    · refine absurd moved (stuck τ A emptyY fun o member => ?_)
      rw [presentY] at member
      rcases Finset.mem_insert.mp member with rfl | inN
      · exact .inr (.inl rfl)
      · exact .inr (.inr (triggers o inN))
    · obtain ⟨port, rfl⟩ := moved
      refine ⟨addAtom X o, ⟨port, rfl⟩, emptyX, emptyY, insert o N, fun x member => ?_, ?_, ?_⟩
      · rcases Finset.mem_insert.mp member with rfl | inN
        · exact port
        · exact triggers x inN
      · show insert o X.present = insert .p (insert o N)
        rw [presentX, Finset.insert_comm]
      · show insert o Y.present = insert .q (insert o N)
        rw [presentY, Finset.insert_comm]

/-- **A disjoint context outside the ports breaks the congruence.** `{p}` and `{q}` are minimally
bisimilar; the atom `a` is disjoint from both and is not a port; beside it they are the race pair,
which is not minimally bisimilar. -/
theorem nonport_not_congruence :
    MinimalBisimilar A (label τ) (offers τ) trigger ⟨[], {.p}⟩ ⟨[], {.q}⟩ ∧
      Disjoint ({.p} : Finset Site) {.a} ∧ Disjoint ({.q} : Finset Site) {.a} ∧ ¬ trigger .a ∧
      ¬ MinimalBisimilar A (label τ) (offers τ) trigger
        (AnnotatedRuns.tensor ⟨[], {.p}⟩ ⟨[], {.a}⟩) (AnnotatedRuns.tensor ⟨[], {.q}⟩ ⟨[], {.a}⟩) := by
  refine ⟨(program τ).minimalBisimilar_iff.mpr (stuck_openBisimilar τ A), by decide, by decide,
    by simp [trigger], fun h => ?_⟩
  have composedP : AnnotatedRuns.tensor (⟨[], {.p}⟩ : Configuration T Site) ⟨[], {.a}⟩ = P := by
    show (⟨[] ++ [], {.p} ∪ {.a}⟩ : Configuration T Site) = ⟨[], {.a, .p}⟩
    rw [List.append_nil, show ({.p} ∪ {.a} : Finset Site) = {.a, .p} by decide]
  have composedQ : AnnotatedRuns.tensor (⟨[], {.q}⟩ : Configuration T Site) ⟨[], {.a}⟩ = Q := by
    show (⟨[] ++ [], {.q} ∪ {.a}⟩ : Configuration T Site) = ⟨[], {.a, .q}⟩
    rw [List.append_nil, show ({.q} ∪ {.a} : Finset Site) = {.a, .q} by decide]
  rw [composedP, composedQ] at h
  exact not_minimalBisimilar τ A h

end Triggered

/-! ### Two ports in one firing -/

namespace Spare

/-- Two occurrences, both ports. -/
inductive Site
  | s | t
  deriving DecidableEq

variable (τ : T)

/-- Every occurrence carries `τ`. -/
def label : Site → T := fun _ => τ

/-- The ground firing that takes `taken` and makes nothing. -/
def firing (taken : List Site) : Firing T S Site :=
  ⟨⟨taken.map (label τ), [], [], [], []⟩, [], ⟨taken, [], []⟩⟩

/-- One label; one firing takes `s` and `t`, the other `s` alone. -/
def offers (_ : Unit) (f : Firing T S Site) : Prop := f = firing τ [.s, .t] ∨ f = firing τ [.s]

/-- Every occurrence is a port. -/
def ports (_ : Site) : Prop := True

theorem ground {f : Firing T S Site} (offered : offers τ () f) : Ground (label τ) f := by
  rcases offered with rfl | rfl
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [firing], List.nodup_nil⟩
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp [firing], List.nodup_nil⟩

variable (A : SubstitutionAction T S)

/-- **The program is not triggered**: its first firing uses two ports. -/
theorem not_triggered (trigger : Unit → Site) : ¬ TriggeredProgram (offers (S := S) τ) ports trigger := by
  intro program
  have used : ∀ o : Site, o = trigger () := fun o =>
    program.only () (firing τ [.s, .t]) (.inl rfl) o trivial (.inl (by cases o <;> simp [uses, firing]))
  exact absurd ((used .s).trans (used .t).symm) (by decide)

theorem fire_s {f : Firing T S Site} (offered : offers τ () f) (P : Finset Site) :
    Site.s ∉ fire P (f.selection.commit (T := T)) := by
  rcases offered with rfl | rfl <;>
    simp [MeTTaCalculus.OccurrenceCommits.mem_fire, firing, Selection.commit]

theorem valid_s {P : Configuration T Site} (refl : Race.Reflexive P.equations) (inside : Site.s ∈ P.present) :
    (firing (S := S) τ [.s]).Valid A (label τ) P := by
  rw [(ground τ (.inr rfl)).valid_iff A refl]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [firing, Selection.commit, inside]

theorem s_of_valid {f : Firing T S Site} (offered : offers τ () f) {P : Configuration T Site}
    (valid : f.Valid A (label τ) P) : Site.s ∈ P.present := by
  refine uses_subset valid ?_
  rcases offered with rfl | rfl <;> simp [uses, firing]

/-- One direction of the open bisimulation that compares the presence of `s` only. -/
theorem spare_step {X Y : Configuration T Site} (reflX : Race.Reflexive X.equations)
    (reflY : Race.Reflexive Y.equations) (same : Site.s ∈ X.present ↔ Site.s ∈ Y.present)
    (lab : Unit ⊕ Site) {X' : Configuration T Site}
    (moved : OpenMoves A (label τ) (offers τ) ports X lab X') :
    ∃ Y', OpenMoves A (label τ) (offers τ) ports Y lab Y' ∧ Race.Reflexive X'.equations ∧
      Race.Reflexive Y'.equations ∧ (Site.s ∈ X'.present ↔ Site.s ∈ Y'.present) := by
  rcases lab with ℓ | o
  · obtain ⟨f, offered, valid, rfl⟩ := moved
    have inY := same.mp (s_of_valid τ A offered valid)
    refine ⟨(firing τ [.s]).result (label τ) Y, ⟨firing τ [.s], .inr rfl, valid_s τ A reflY inY, rfl⟩,
      (ground τ offered).reflexive_result reflX, (ground τ (.inr rfl)).reflexive_result reflY, ?_⟩
    exact iff_of_false (fire_s τ offered X.present) (fire_s τ (.inr rfl) Y.present)
  · obtain ⟨port, rfl⟩ := moved
    refine ⟨addAtom Y o, ⟨port, rfl⟩, reflX, reflY, ?_⟩
    show Site.s ∈ insert o X.present ↔ Site.s ∈ insert o Y.present
    rw [Finset.mem_insert, Finset.mem_insert]
    exact or_congr Iff.rfl same

/-- **Open bisimilarity is not minimal bisimilarity without the trigger hypothesis.** The empty
configuration and `{t}` are open bisimilar; the first moves under the trigger set `{s, t}`, and the
second has no move under it. -/
theorem open_not_minimal :
    OpenBisimilar A (label τ) (offers τ) ports ⟨[], ∅⟩ ⟨[], {.t}⟩ ∧
      ¬ MinimalBisimilar A (label τ) (offers τ) ports ⟨[], ∅⟩ ⟨[], {.t}⟩ := by
  refine ⟨⟨fun X Y => Race.Reflexive X.equations ∧ Race.Reflexive Y.equations ∧
      (Site.s ∈ X.present ↔ Site.s ∈ Y.present), ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩,
    reflexive_nil, reflexive_nil, by simp⟩, ?_⟩
  · rintro X Y ⟨reflX, reflY, same⟩ lab X' moved
    obtain ⟨Y', moved', reflX', reflY', same'⟩ := spare_step τ A reflX reflY same lab moved
    exact ⟨Y', moved', reflX', reflY', same'⟩
  · rintro X Y ⟨reflX, reflY, same⟩ lab Y' moved
    obtain ⟨X', moved', reflY', reflX', same'⟩ := spare_step τ A reflY reflX same.symm lab moved
    exact ⟨X', moved', reflX', reflY', same'.symm⟩
  · intro h
    have moves : MinimalMoves A (label τ) (offers τ) ports ⟨[], ∅⟩ ((), {.s, .t})
        ((firing (S := S) τ [.s, .t]).result (label τ) (addAll ⟨[], ∅⟩ {.s, .t})) := by
      refine ⟨firing τ [.s, .t], .inl rfl, fun _ _ => trivial, by simp, by simp [uses, firing], ?_, rfl⟩
      rw [(ground τ (.inl rfl)).valid_iff A reflexive_nil]
      exact of_decide_eq_true rfl
    obtain ⟨D', ⟨-, -, -, apart, -⟩, -⟩ := h.step moves
    exact absurd apart (by simp)

end Spare

#print axioms uses_subset
#print axioms valid_frame
#print axioms result_frame
#print axioms MinimalBisimilar.step
#print axioms MinimalBisimilar.symm
#print axioms minimal_eq
#print axioms minimal_least
#print axioms TriggeredProgram.present
#print axioms TriggeredProgram.eq_trigger
#print axioms TriggeredProgram.sdiff_taken
#print axioms TriggeredProgram.open_step
#print axioms TriggeredProgram.closed_step
#print axioms TriggeredProgram.minimalBisimilar_iff
#print axioms TriggeredProgram.tensor_ports
#print axioms Triggered.program
#print axioms Triggered.not_minimalBisimilar
#print axioms Triggered.stuck
#print axioms Triggered.stuck_openBisimilar
#print axioms Triggered.nonport_not_congruence
#print axioms Spare.ground
#print axioms Spare.not_triggered
#print axioms Spare.open_not_minimal

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
