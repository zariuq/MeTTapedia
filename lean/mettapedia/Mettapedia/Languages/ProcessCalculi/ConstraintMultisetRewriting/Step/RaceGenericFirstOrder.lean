import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceGeneric
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceReadouts

/-!
# The first-order races layer is the one-frame instance of the generic one

The first-order step is the one-frame instance of the interface (`AnnotatedRuns.firstOrder`), with
the transport that identifies configurations with the same solutions and occurrences
(`AnnotatedRuns.firstOrderTransport`). A first-order program is read over the interface by offering
the same firings at every configuration (`lift`).

## The definitions coincide

* **Moves and bisimilarity** (`moves_lift_iff`, `bisimilar_lift_iff`): exactly those of
  `RaceSpectrum`.
* **Steps** (`stepMoves_lift_of_race`, `race_of_stepMoves_lift`, `stepBisimilar_lift_iff`): every step
  of `RaceSteps` (a word of pairwise statically independent firings) is a step of the generic layer,
  whose independence is the interface's semantic diamond; conversely, when the program offers only
  static firings (no checks, query regions that do not depend on the solution) every generic step is
  one of `RaceSteps`, through `AnnotatedRuns.firstOrder_independent_iff_static`. On such programs the
  two step bisimilarities coincide.
* **Histories** (`hpBisimilar_lift_iff`): with the independence of events read off the static
  independence of their firings (`indepOf`), the generic causal past is the past of `RaceSteps`
  (`past_forget`), and the two history-preserving bisimilarities coincide, for every program.

## What the lift gives the first-order layer

* **Configurations with the same solutions and occurrences are step bisimilar** (for static programs)
  **and history-preserving bisimilar** (for every program): `stepBisimilar_of_sameUpTo`,
  `hpBisimilar_of_sameUpTo`.
* **Renaming.** The renaming transport (`AnnotatedRuns.renamingTransport`) keeps the labels of an
  equivariant program (`invariant_of_equivariant`), its independence is the one-frame one
  (`independent_renaming_iff`), so renaming-related configurations of an equivariant program are
  bisimilar (`bisimilar_of_renamingIso`) and, for static programs, step bisimilar
  (`stepBisimilar_of_renamingIso`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic

open AnnotatedRuns (Firing StaticIndependent firstOrder firstOrderTransport follow Executable
  RenamingIso renamingTransport)
open GuardFreeProcessOrders (SameUpTo)
open Mettapedia.GSLT.HennessyMilner (Formula)

universe uT uS uO uL

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O] {L : Type uL}
variable (A : SubstitutionAction T S) (label : O → T) (offers : L → Firing T S O → Prop)

/-- **A first-order program read over the interface**: the same firings at every configuration. -/
def lift : L → (C : Configuration T O) → Firing T S O → Prop := fun ℓ _ f => offers ℓ f

variable {A label offers}

/-! ## Moves -/

theorem moves_lift_iff {C D : Configuration T O} {ℓ : L} :
    Moves (firstOrder A label).toStep (lift offers) C ℓ D ↔ Race.Moves A label offers C ℓ D :=
  ⟨fun ⟨f, admitted, offered, result⟩ => ⟨f, offered, admitted, result⟩,
    fun ⟨f, offered, valid, result⟩ => ⟨f, valid, offered, result⟩⟩

/-- **Bisimilarity of the lift is bisimilarity of `RaceSpectrum`.** -/
theorem bisimilar_lift_iff {C D : Configuration T O} :
    Bisimilar (firstOrder A label).toStep (lift offers) C D ↔ Race.Bisimilar A label offers C D := by
  constructor
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨fun a b rel ℓ a' moved => ?_, fun a b rel ℓ b' moved => ?_,
      fun _ _ _ atom => atom.elim⟩, related⟩
    · obtain ⟨b'', moved', rel'⟩ := forward rel ℓ (moves_lift_iff.mpr moved)
      exact ⟨b'', moves_lift_iff.mp moved', rel'⟩
    · obtain ⟨a'', moved', rel'⟩ := backward rel ℓ (moves_lift_iff.mpr moved)
      exact ⟨a'', moves_lift_iff.mp moved', rel'⟩
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨fun a b rel ℓ a' moved => ?_, fun a b rel ℓ b' moved => ?_,
      fun _ _ _ atom => atom.elim⟩, related⟩
    · obtain ⟨b'', moved', rel'⟩ := forward rel ℓ (moves_lift_iff.mp moved)
      exact ⟨b'', moves_lift_iff.mpr moved', rel'⟩
    · obtain ⟨a'', moved', rel'⟩ := backward rel ℓ (moves_lift_iff.mp moved)
      exact ⟨a'', moves_lift_iff.mpr moved', rel'⟩

/-- **Satisfaction in the lift is satisfaction in `RaceSpectrum`.** -/
theorem sat_lift_iff : ∀ (φ : Formula PEmpty.{1} L) (C : Configuration T O),
    Sat (firstOrder A label).toStep (lift offers) φ C ↔ Race.Sat A label offers φ C
  | .top, _ => Iff.rfl
  | .atom atom, _ => atom.elim
  | .conj φ ψ, C => and_congr (sat_lift_iff φ C) (sat_lift_iff ψ C)
  | .neg φ, C => not_congr (sat_lift_iff φ C)
  | .dia _ φ, _ =>
      ⟨fun ⟨D, moved, holds⟩ => ⟨D, moves_lift_iff.mp moved, (sat_lift_iff φ D).mp holds⟩,
        fun ⟨D, moved, holds⟩ => ⟨D, moves_lift_iff.mpr moved, (sat_lift_iff φ D).mpr holds⟩⟩

/-! ## Steps -/

variable (A label) in
/-- **A pairwise statically independent executable word is a concurrent word.** -/
theorem concurrent_of_pairwise : ∀ (w : List (Firing T S O)) {C : Configuration T O},
    w.Pairwise (StaticIndependent label) → Executable A label C w →
      Concurrent (firstOrder A label).toStep (firstOrderTransport A label) C w (follow label C w)
  | [], C, _, _ => .nil C
  | f :: rest, C, pairwise, executable => by
      have later := concurrent_of_pairwise rest (List.pairwise_cons.mp pairwise).2 executable.2
      refine Concurrent.cons (P := (firstOrder A label).toStep) (T := firstOrderTransport A label) f rest
        executable.1 ?_ ?_
      · intro g member
        classical
        have permuted := (step_order_irrelevant A label pairwise
          ((List.perm_cons_erase member).cons f) executable).1
        have gAfter : g.Valid A label (f.result label C) := permuted.2.1
        obtain ⟨gValid, fAfter, -⟩ := AnnotatedRuns.swap_valid A label
          ((List.pairwise_cons.mp pairwise).1 g member) executable.1 gAfter
        exact (AnnotatedRuns.firstOrder_independent_iff A label).mpr
          ⟨executable.1, gValid, gAfter, fAfter⟩
      · have residuals : rest.map ((firstOrderTransport A label).residual f executable.1) = rest :=
          List.map_id' rest
        rw [residuals]
        exact later

variable (A label) in
/-- **A concurrent word of static firings is pairwise statically independent and fires.** -/
theorem fires_of_concurrent : ∀ {C : Configuration T O} {w : List (Firing T S O)} {D : Configuration T O},
    Concurrent (firstOrder A label).toStep (firstOrderTransport A label) C w D → (∀ f ∈ w, f.Static) →
      w.Pairwise (StaticIndependent label) ∧ Fires A label C w ∧ D = follow label C w
  | C, [], D, concurrent, _ => by
      obtain rfl := concurrent_nil_iff.mp concurrent
      exact ⟨List.Pairwise.nil, trivial, rfl⟩
  | C, f :: rest, D, concurrent, static => by
      obtain ⟨admitted, independent, later⟩ := concurrent_cons_iff.mp concurrent
      have residuals : rest.map ((firstOrderTransport A label).residual f admitted) = rest :=
        List.map_id' rest
      rw [residuals] at later
      obtain ⟨pairwise, fires, rfl⟩ :=
        fires_of_concurrent later fun g member => static g (List.mem_cons_of_mem _ member)
      refine ⟨List.pairwise_cons.mpr ⟨fun g member => ?_, pairwise⟩, ⟨admitted, fires⟩, rfl⟩
      obtain ⟨-, -, gAfter, -⟩ := (AnnotatedRuns.firstOrder_independent_iff A label).mp
        (independent g member)
      exact (AnnotatedRuns.firstOrder_independent_iff_static A label (static f (List.mem_cons_self ..))
        (static g (List.mem_cons_of_mem _ member)) admitted gAfter).mp (independent g member)

/-- **Every step of `RaceSteps` is a step of the lift.** -/
theorem stepMoves_lift_of_race {C D : Configuration T O} {M : Multiset L}
    (stepped : Race.StepMoves A label offers C M D) :
    StepMoves (firstOrder A label).toStep (firstOrderTransport A label) (lift offers) C M D := by
  obtain ⟨w, nonempty, offered, pairwise, executable, rfl, rfl⟩ := stepped
  exact ⟨w, nonempty, offered, concurrent_of_pairwise A label _ pairwise executable, rfl⟩

/-- **For static programs every step of the lift is a step of `RaceSteps`.** -/
theorem race_of_stepMoves_lift (static : ∀ ℓ f, offers ℓ f → f.Static) {C D : Configuration T O}
    {M : Multiset L}
    (stepped : StepMoves (firstOrder A label).toStep (firstOrderTransport A label) (lift offers) C M D) :
    Race.StepMoves A label offers C M D := by
  obtain ⟨w, nonempty, offered, concurrent, rfl⟩ := stepped
  obtain ⟨pairwise, fires, rfl⟩ := fires_of_concurrent A label concurrent fun f member => by
    obtain ⟨x, inW, rfl⟩ := List.mem_map.mp member
    exact static x.1 x.2 (offered x inW)
  exact ⟨w, nonempty, offered, pairwise,
    executable_of_fires A label (by simpa using nonempty) fires, rfl, rfl⟩

/-- **For static programs, step bisimilarity of the lift is step bisimilarity of `RaceSteps`.** -/
theorem stepBisimilar_lift_iff (static : ∀ ℓ f, offers ℓ f → f.Static) {C D : Configuration T O} :
    StepBisimilar (firstOrder A label).toStep (firstOrderTransport A label) (lift offers) C D ↔
      Race.StepBisimilar A label offers C D := by
  constructor
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨fun a b rel M a' moved => ?_, fun a b rel M b' moved => ?_,
      fun _ _ _ atom => atom.elim⟩, related⟩
    · obtain ⟨b'', moved', rel'⟩ := forward rel M (stepMoves_lift_of_race moved)
      exact ⟨b'', race_of_stepMoves_lift static moved', rel'⟩
    · obtain ⟨a'', moved', rel'⟩ := backward rel M (stepMoves_lift_of_race moved)
      exact ⟨a'', race_of_stepMoves_lift static moved', rel'⟩
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨R, ⟨fun a b rel M a' moved => ?_, fun a b rel M b' moved => ?_,
      fun _ _ _ atom => atom.elim⟩, related⟩
    · obtain ⟨b'', moved', rel'⟩ := forward rel M (race_of_stepMoves_lift static moved)
      exact ⟨b'', stepMoves_lift_of_race moved', rel'⟩
    · obtain ⟨a'', moved', rel'⟩ := backward rel M (race_of_stepMoves_lift static moved)
      exact ⟨a'', stepMoves_lift_of_race moved', rel'⟩

/-! ## Histories -/

variable (label) in
/-- **The independence of first-order events**: the static independence of their firings. -/
def indepOf (a b : Event (Configuration T O) (fun _ => Firing T S O)) : Prop :=
  StaticIndependent label a.2 b.2

/-- The history of `RaceSteps` underlying a generic history: the firings with their pasts. -/
def forget (h : History (Configuration T O) (fun _ => Firing T S O)) : Race.History T S O :=
  h.map fun a => (a.1.2, a.2)

theorem directPast_forget (h : History (Configuration T O) (fun _ => Firing T S O))
    (C : Configuration T O) (f : Firing T S O) :
    directPast (indepOf label) h ⟨C, f⟩ = Race.directPast label (forget h) f := by
  ext i
  rw [mem_directPast, Race.mem_directPast]
  simp only [forget, List.length_map, List.getElem?_map]
  constructor
  · rintro ⟨lt, x, get, dependent⟩
    exact ⟨lt, (x.1.2, x.2), by rw [get]; rfl, dependent⟩
  · rintro ⟨lt, e, get, dependent⟩
    rcases h' : h[i]? with _ | x
    · rw [h'] at get
      cases get
    · rw [h'] at get
      cases get
      exact ⟨lt, x, rfl, dependent⟩

/-- **The generic causal past is the past of `RaceSteps`.** -/
theorem past_forget (h : History (Configuration T O) (fun _ => Firing T S O)) (C : Configuration T O)
    (f : Firing T S O) : past (indepOf label) h ⟨C, f⟩ = Race.past label (forget h) f := by
  unfold past Race.past
  rw [directPast_forget]
  congr 1
  refine Finset.biUnion_congr rfl fun i _ => ?_
  simp only [forget, List.getElem?_map]
  rcases h[i]? with _ | x <;> rfl

/-- The configuration with its forgotten history. -/
def image (x : Configuration T O × History (Configuration T O) (fun _ => Firing T S O)) :
    Configuration T O × Race.History T S O :=
  (x.1, forget x.2)

theorem hmoves_toRace {x y : Configuration T O × History (Configuration T O) (fun _ => Firing T S O)}
    {lab : L × Finset ℕ} (moved : HMoves (indepOf label) (firstOrder A label).toStep (lift offers) x lab y) :
    Race.HMoves A label offers (image x) lab (image y) := by
  obtain ⟨f, admitted, offered, labelled, rfl⟩ := moved
  refine ⟨f, offered, admitted, labelled.trans (past_forget x.2 x.1 f), ?_⟩
  exact Prod.ext rfl (by simp [image, forget])

theorem hmoves_ofRace {x : Configuration T O × History (Configuration T O) (fun _ => Firing T S O)}
    {lab : L × Finset ℕ} {u : Configuration T O × Race.History T S O}
    (moved : Race.HMoves A label offers (image x) lab u) :
    ∃ y, HMoves (indepOf label) (firstOrder A label).toStep (lift offers) x lab y ∧ u = image y := by
  obtain ⟨f, offered, valid, labelled, rfl⟩ := moved
  refine ⟨(f.result label x.1, x.2 ++ [(⟨x.1, f⟩, lab.2)]),
    ⟨f, valid, offered, labelled.trans (past_forget x.2 x.1 f).symm, rfl⟩, ?_⟩
  exact Prod.ext rfl (by simp [image, forget])

/-- **History-preserving bisimilarity of the lift is that of `RaceSteps`**, for every program. -/
theorem hpBisimilar_lift_iff {C D : Configuration T O} :
    HPBisimilar (indepOf label) (firstOrder A label).toStep (lift offers) C D ↔
      Race.HPBisimilar A label offers C D := by
  constructor
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨fun u v => ∃ x y, R x y ∧ u = image x ∧ v = image y, ⟨?_, ?_,
      fun _ _ _ atom => atom.elim⟩, ⟨(C, []), (D, []), related, rfl, rfl⟩⟩
    · rintro u v ⟨x, y, rel, rfl, rfl⟩ lab u' moved
      obtain ⟨x', movedX, rfl⟩ := hmoves_ofRace moved
      obtain ⟨y', movedY, rel'⟩ := forward rel lab movedX
      exact ⟨image y', hmoves_toRace movedY, x', y', rel', rfl, rfl⟩
    · rintro u v ⟨x, y, rel, rfl, rfl⟩ lab v' moved
      obtain ⟨y', movedY, rfl⟩ := hmoves_ofRace moved
      obtain ⟨x', movedX, rel'⟩ := backward rel lab movedY
      exact ⟨image x', hmoves_toRace movedX, x', y', rel', rfl, rfl⟩
  · rintro ⟨R, ⟨forward, backward, _⟩, related⟩
    refine ⟨fun x y => R (image x) (image y), ⟨?_, ?_, fun _ _ _ atom => atom.elim⟩, related⟩
    · rintro x y rel lab x' movedX
      obtain ⟨v, movedV, rel'⟩ := forward rel lab (hmoves_toRace movedX)
      obtain ⟨y', movedY, rfl⟩ := hmoves_ofRace movedV
      exact ⟨y', movedY, rel'⟩
    · rintro x y rel lab y' movedY
      obtain ⟨u, movedU, rel'⟩ := backward rel lab (hmoves_toRace movedY)
      obtain ⟨x', movedX, rfl⟩ := hmoves_ofRace movedU
      exact ⟨x', movedX, rel'⟩

/-! ## What the lift gives the first-order layer -/

theorem invariant_firstOrder : Invariant (firstOrder A label).toStep (lift offers) (firstOrderTransport A label) :=
  fun _ _ _ _ _ offered => offered

theorem strict_firstOrder {C : Configuration T O} {f f' : Firing T S O} :
    (firstOrderTransport A label).Alike (s := C) f f' ↔ f = f' := Iff.rfl

theorem indepInvariant_firstOrder :
    IndepInvariant (indepOf label) (firstOrderTransport A label) := by
  rintro ⟨_, a⟩ ⟨_, a'⟩ ⟨_, b⟩ ⟨_, b'⟩ ⟨_, sameA⟩ ⟨_, sameB⟩
  change a = a' at sameA
  change b = b' at sameB
  subst sameA
  subst sameB
  exact Iff.rfl

/-- **Configurations with the same solutions and occurrences are step bisimilar**, for static
programs. -/
theorem stepBisimilar_of_sameUpTo (static : ∀ ℓ f, offers ℓ f → f.Static) {C D : Configuration T O}
    (same : SameUpTo A C D) : Race.StepBisimilar A label offers C D :=
  (stepBisimilar_lift_iff static).mp
    (stepBisimilar_of_same strict_firstOrder invariant_firstOrder ⟨⟨same⟩⟩)

/-- **Configurations with the same solutions and occurrences are history-preserving bisimilar**, for
every program. -/
theorem hpBisimilar_of_sameUpTo {C D : Configuration T O} (same : SameUpTo A C D) :
    Race.HPBisimilar A label offers C D :=
  hpBisimilar_lift_iff.mp
    (hpBisimilar_of_same invariant_firstOrder indepInvariant_firstOrder (T := firstOrderTransport A label)
      ⟨⟨same⟩⟩)

/-- **An equivariant program keeps its labels along the renaming transport.** -/
theorem invariant_of_equivariant (equivariant : Race.Equivariant label offers) :
    Invariant (firstOrder A label).toStep (lift offers) (renamingTransport A label) :=
  fun _ _ i ℓ f offered => equivariant i.rename i.keeps ℓ f offered

/-- **Renaming-related configurations of an equivariant program are bisimilar.** -/
theorem bisimilar_of_renamingIso (equivariant : Race.Equivariant label offers)
    {C D : Configuration T O} (i : RenamingIso A label C D) : Race.Bisimilar A label offers C D :=
  bisimilar_lift_iff.mp (bisimilar_of_same (renamingTransport A label)
    (invariant_of_equivariant equivariant) ⟨i⟩)

variable (A label) in
/-- **The renaming transport has the one-frame independence.** -/
theorem independent_renaming_iff {C : Configuration T O} {f g : Firing T S O} :
    (renamingTransport A label).Independent C f g ↔ (firstOrderTransport A label).Independent C f g := by
  rw [AnnotatedRuns.firstOrder_independent_iff]
  constructor
  · rintro ⟨first, second, afterFirst, afterSecond, -⟩
    exact ⟨first, second, afterFirst, afterSecond⟩
  · rintro ⟨first, second, afterFirst, afterSecond⟩
    obtain ⟨_, _, _, _, ⟨same⟩⟩ := (AnnotatedRuns.firstOrder_independent_iff A label).mpr
      ⟨first, second, afterFirst, afterSecond⟩
    exact ⟨first, second, afterFirst, afterSecond, ⟨RenamingIso.ofSame same.down⟩⟩

theorem concurrent_of_renaming : ∀ {C D : Configuration T O} {w : List (Firing T S O)},
    Concurrent (firstOrder A label).toStep (renamingTransport A label) C w D →
      Concurrent (firstOrder A label).toStep (firstOrderTransport A label) C w D
  | _, _, [], concurrent => by
      obtain rfl := concurrent_nil_iff.mp concurrent
      exact .nil _
  | _, _, f :: rest, concurrent => by
      obtain ⟨admitted, independent, later⟩ := concurrent_cons_iff.mp concurrent
      have residuals : rest.map ((renamingTransport A label).residual f admitted) = rest := List.map_id' rest
      have residuals' : rest.map ((firstOrderTransport A label).residual f admitted) = rest := List.map_id' rest
      rw [residuals] at later
      refine concurrent_cons_iff.mpr ⟨admitted,
        fun g member => (independent_renaming_iff A label).mp (independent g member), ?_⟩
      rw [residuals']
      exact concurrent_of_renaming later

theorem renaming_of_concurrent : ∀ {C D : Configuration T O} {w : List (Firing T S O)},
    Concurrent (firstOrder A label).toStep (firstOrderTransport A label) C w D →
      Concurrent (firstOrder A label).toStep (renamingTransport A label) C w D
  | _, _, [], concurrent => by
      obtain rfl := concurrent_nil_iff.mp concurrent
      exact .nil _
  | _, _, f :: rest, concurrent => by
      obtain ⟨admitted, independent, later⟩ := concurrent_cons_iff.mp concurrent
      have residuals : rest.map ((firstOrderTransport A label).residual f admitted) = rest := List.map_id' rest
      have residuals' : rest.map ((renamingTransport A label).residual f admitted) = rest := List.map_id' rest
      rw [residuals] at later
      refine concurrent_cons_iff.mpr ⟨admitted,
        fun g member => (independent_renaming_iff A label).mpr (independent g member), ?_⟩
      rw [residuals']
      exact renaming_of_concurrent later

/-- **Renaming-related configurations of an equivariant static program are step bisimilar.** -/
theorem stepBisimilar_of_renamingIso (equivariant : Race.Equivariant label offers)
    (static : ∀ ℓ f, offers ℓ f → f.Static) {C D : Configuration T O} (i : RenamingIso A label C D) :
    Race.StepBisimilar A label offers C D := by
  obtain ⟨R, ⟨forward, backward, _⟩, related⟩ :=
    stepBisimilar_of_same (T := renamingTransport A label) (offers := lift offers) Iff.rfl
      (invariant_of_equivariant equivariant) ⟨i⟩
  have toFirst : ∀ {a b : Configuration T O} {M : Multiset L},
      StepMoves (firstOrder A label).toStep (renamingTransport A label) (lift offers) a M b →
        Race.StepMoves A label offers a M b := fun ⟨w, nonempty, offered, concurrent, labels⟩ =>
    race_of_stepMoves_lift static ⟨w, nonempty, offered, concurrent_of_renaming concurrent, labels⟩
  have ofFirst : ∀ {a b : Configuration T O} {M : Multiset L}, Race.StepMoves A label offers a M b →
      StepMoves (firstOrder A label).toStep (renamingTransport A label) (lift offers) a M b := fun moved => by
    obtain ⟨w, nonempty, offered, concurrent, labels⟩ := stepMoves_lift_of_race moved
    exact ⟨w, nonempty, offered, renaming_of_concurrent concurrent, labels⟩
  refine ⟨R, ⟨fun a b rel M a' moved => ?_, fun a b rel M b' moved => ?_,
    fun _ _ _ atom => atom.elim⟩, related⟩
  · obtain ⟨b'', moved', rel'⟩ := forward rel M (ofFirst moved)
    exact ⟨b'', toFirst moved', rel'⟩
  · obtain ⟨a'', moved', rel'⟩ := backward rel M (ofFirst moved)
    exact ⟨a'', toFirst moved', rel'⟩

#print axioms moves_lift_iff
#print axioms bisimilar_lift_iff
#print axioms sat_lift_iff
#print axioms concurrent_of_pairwise
#print axioms fires_of_concurrent
#print axioms stepMoves_lift_of_race
#print axioms race_of_stepMoves_lift
#print axioms stepBisimilar_lift_iff
#print axioms past_forget
#print axioms hpBisimilar_lift_iff
#print axioms stepBisimilar_of_sameUpTo
#print axioms hpBisimilar_of_sameUpTo
#print axioms bisimilar_of_renamingIso
#print axioms independent_renaming_iff
#print axioms stepBisimilar_of_renamingIso

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race.Generic
