import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRunsLogicModalities

/-!
# State predicates over stored patterns, and their invariance along programs

A configuration stores terms: each present occurrence holds its label. A predicate on states can
quantify over the stored patterns, with the property of patterns itself a variable.

* `Stored label P C`: every stored pattern of `C` satisfies `P`. It respects `SameUpTo`
  (`stored_congr`), so it is a predicate on classes (`StoredAt`).
* `Produces P f`: the firing produces only patterns satisfying `P`.
* **Invariance, uniformly in the property of patterns** (`stored_result`, `storedAt_path`,
  `stored_hoare`): for every `P`, every run of the firings that produce only `P`-patterns carries
  "every stored pattern satisfies `P`" into itself. Read on histories through their end
  (`atEnd`), this is a Hoare triple of the dynamic logic of `AnnotatedRunsLogicModalities` over
  the program `runsOf {f | Produces P f}`, and with `hoare_iff_exists_invariant` it is the
  invariance rule instantiated at a predicate variable.
* **Henceforth is always along ω-runs** (`henceforth_iff_alwaysAll`, `henceforth_iff_alwaysFair`):
  for a predicate of states, necessity along all runs at the empty history is always along every
  ω-run of the candidate step with an idle step, and along every strongly fair one.

Controls, with "no stored `9`":

* positive: `StoredControls.taker_reader_keep_noNine`: the runs of the taker and the reader from
  the start keep it;
* negative: `StoredControls.maker_breaks_noNine`: the run of the maker of `9` from the empty
  configuration does not.
-/

set_option autoImplicit false

open CategoryTheory

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns

open Mettapedia.GSLT.Causality.OccurrenceHistory (OccurrencePath)
open GuardFreeProcessOrders (SameUpTo)

universe uT uS uO
variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

section Stored

variable (A : SubstitutionAction T S) (label : O → T)

/-- **Every stored pattern satisfies `P`.** -/
def Stored (P : T → Prop) (C : Configuration T O) : Prop := ∀ o ∈ C.present, P (label o)

omit [DecidableEq O] in
theorem stored_congr (P : T → Prop) {C D : Configuration T O} (same : SameUpTo A C D) :
    Stored label P C ↔ Stored label P D := by
  unfold Stored
  rw [same.2]

/-- Every stored pattern of a class satisfies `P`. -/
def StoredAt (P : T → Prop) : ConfigurationClass A O → Prop :=
  Quotient.lift (Stored label P) fun _ _ same => propext (stored_congr A label P same)

/-- The firing produces only patterns satisfying `P`. -/
def Produces (P : T → Prop) (f : Firing T S O) : Prop := ∀ t ∈ f.rule.produce, P t

/-- **A firing that produces only `P`-patterns keeps every stored pattern in `P`.** -/
theorem stored_result {P : T → Prop} {f : Firing T S O} {C : Configuration T O}
    (valid : f.Valid A label C) (produces : Produces P f) (stored : Stored label P C) :
    Stored label P (f.result label C) := by
  intro o member
  change o ∈ (C.present \ f.selection.taken.toFinset) ∪ f.selection.made.toFinset at member
  rcases Finset.mem_union.mp member with kept | made
  · exact stored o (Finset.mem_sdiff.mp kept).1
  · apply produces
    rw [← valid.firing.outputs]
    exact List.mem_map_of_mem (List.mem_toFinset.mp made)

/-- **Along a run of firings that produce only `P`-patterns, every stored pattern stays in
`P`.** -/
theorem storedAt_path (P : T → Prop) {x y : (theory A label).Term}
    (p : OccurrencePath (presentation A label) x y) :
    (∀ f ∈ OccurrencePath.sites p, Produces P f) → StoredAt A label P x → StoredAt A label P y := by
  induction p with
  | refl => exact fun _ stored => stored
  | cons o rest ih =>
      intro produces stored
      obtain ⟨f, ⟨⟨fValid, fTarget⟩⟩⟩ := o
      subst fTarget
      apply ih fun g member => produces g (List.mem_cons_of_mem _ member)
      have step : ∀ c : ConfigurationClass A O, f.ValidAt A label c → StoredAt A label P c →
          StoredAt A label P (f.resultClass A label c) := by
        intro c
        refine Quotient.inductionOn c ?_
        intro C valid storedC
        exact stored_result A label valid (produces f List.mem_cons_self) storedC
      exact step _ fValid stored

/-- A state predicate read on histories: it asks only where the history ends. -/
def atEnd (C₀ : Configuration T O) (Q : ConfigurationClass A O → Prop) :
    Family (runObject A label C₀) :=
  fun y => {_h | Q y}

/-- **Higher-order invariance of stored patterns**: for every property `P` of patterns, the runs of
the firings that produce only `P`-patterns carry "every stored pattern satisfies `P`" into
itself. -/
theorem stored_hoare (C₀ : Configuration T O) (P : T → Prop) :
    Hoare (runsOf A label {f | Produces P f}) (atEnd A label C₀ (StoredAt A label P))
      (atEnd A label C₀ (StoredAt A label P)) :=
  fun _ _ p inR _ stored => storedAt_path A label P p inR stored

/-- **Henceforth at the empty history is always along every ω-run**, for predicates of states: a
class predicate holds after every run from `C₀` exactly when it holds at every state of every
ω-run of the candidate step with an idle step from `C₀`. -/
theorem henceforth_iff_alwaysAll (C₀ : Configuration T O) (consistent : A.Consistent C₀.equations)
    (Q : ConfigurationClass A O → Prop) :
    𝟙 (runObject A label C₀) ∈ nec allRuns (atEnd A label C₀ Q) (runObject A label C₀) ↔
      AlwaysAll (candidateLTS A label).withIdle C₀ (fun C => Q (classOf A label C)) := by
  rw [alwaysAll_iff (MeTTaCalculus.OccurrenceCommits.Liveness.LTS.withIdle_nonBlocking _)]
  constructor
  · intro holds s reachable
    obtain ⟨w, exec⟩ :=
      (MeTTaCalculus.OccurrenceCommits.Liveness.LTS.withIdle_reachable_iff _ C₀ s).mp reachable
    obtain ⟨runs, rfl⟩ := (exec_iff A label C₀ w s consistent).mp exec
    obtain ⟨p, -⟩ := exists_path A label C₀ w runs _ rfl
    exact holds (𝟙 _ ≫ p) (Set.mem_univ _)
  · intro holds y p _
    have ends := target_eq A label (𝟙 (runObject A label C₀) ≫ p) C₀ rfl
    have runs := executable_of_path A label (𝟙 (runObject A label C₀) ≫ p) C₀ rfl consistent
    have reached := holds _ ((MeTTaCalculus.OccurrenceCommits.Liveness.LTS.withIdle_reachable_iff _
      C₀ _).mpr ⟨_, (exec_iff A label C₀ _ _ consistent).mpr ⟨runs, rfl⟩⟩)
    exact (congrArg Q ends).mpr reached

/-- **And along every strongly fair ω-run**, for finitely many tasks. -/
theorem henceforth_iff_alwaysFair {ι : Type*} [Fintype ι] [DecidableEq ι]
    (tasks : ι → Firing T S O → Prop) (C₀ : Configuration T O)
    (consistent : A.Consistent C₀.equations) (Q : ConfigurationClass A O → Prop) :
    𝟙 (runObject A label C₀) ∈ nec allRuns (atEnd A label C₀ Q) (runObject A label C₀) ↔
      AlwaysFair (candidateLTS A label).withIdle
        (fun i => MeTTaCalculus.OccurrenceCommits.Liveness.LTS.liftTask (tasks i)) C₀
        (fun C => Q (classOf A label C)) :=
  (henceforth_iff_alwaysAll A label C₀ consistent Q).trans
    (candidate_alwaysFair_iff_alwaysAll A label tasks C₀ _).symm

/-- A smaller program keeps every Hoare triple. -/
theorem Hoare.mono {B : Type*} [Category B] {root : B} {R R' : Program B} {φ ψ : Family root}
    (hoare : Hoare R' φ ψ) (smaller : ∀ x y, R x y ⊆ R' x y) : Hoare R φ ψ :=
  fun _ _ p inR => hoare p (smaller _ _ inR)

end Stored

/-! ## Controls -/

namespace StoredControls

open Mettapedia.Logic.LP
open ConstraintMultisetRewriting.Controls (signature A)
open AnnotatedRuns.Controls (label Run taker reader start maker empty)

/-- "Not the pattern `9`." -/
def noNine (t : Term signature) : Prop := t ≠ .const 9

theorem taker_produces : Produces noNine taker := by
  intro t member
  simp only [taker, List.mem_singleton] at member
  subst member
  intro same
  cases same

theorem reader_produces : Produces noNine reader := by
  intro t member
  simp only [reader, List.mem_singleton] at member
  subst member
  intro same
  cases same

theorem start_noNine : StoredAt A label noNine (classOf A label start) := by
  intro o member
  change o ∈ ({0, 1} : Finset Nat) at member
  rcases Finset.mem_insert.mp member with rfl | inOne
  · intro same
    cases same
  · rw [Finset.mem_singleton.mp inOne]
    intro same
    cases same

/-- **Positive control: the runs of the taker and the reader keep "no stored `9`".** -/
theorem taker_reader_keep_noNine :
    Hoare (runsOf A label {taker, reader}) (atEnd A label start (StoredAt A label noNine))
      (atEnd A label start (StoredAt A label noNine)) := by
  refine (stored_hoare A label start noNine).mono fun _ _ p inR f member => ?_
  rcases inR f member with isTaker | isReader
  · rw [isTaker]
    exact taker_produces
  · rw [Set.mem_singleton_iff.mp isReader]
    exact reader_produces

theorem maker_valid_empty : maker.Valid A label empty := by
  refine ⟨⟨by decide, by decide, rfl, rfl, rfl, by decide,
    ⟨Subst.id signature, by simp [Selection.problem, Selection.equations, empty, maker]⟩,
    by simp [maker]⟩, by simp [maker]⟩

/-- **Negative control: the run of the maker of `9` breaks "no stored `9`".** -/
theorem maker_breaks_noNine :
    ¬ Hoare (runsOf A label {maker}) (atEnd A label empty (StoredAt A label noNine))
      (atEnd A label empty (StoredAt A label noNine)) := by
  intro hoare
  obtain ⟨p, pSites⟩ := exists_path A label empty [maker]
    ⟨maker_valid_empty, maker_valid_empty.firing.consistent⟩ _ rfl
  have onlyMaker : p ∈ runsOf A label {maker} _ _ := fun f member =>
    (congrArg (fun l => f ∈ l) pSites).mp member |> List.mem_singleton.mp
  have before : 𝟙 (runObject A label empty) ∈ atEnd A label empty (StoredAt A label noNine)
      (runObject A label empty) := fun o member => absurd member (Finset.notMem_empty o)
  have after := hoare p onlyMaker before
  have nine : (9 : Nat) ∈ (maker.result label empty).present := by decide
  exact after 9 nine rfl

end StoredControls

#print axioms stored_congr
#print axioms stored_result
#print axioms storedAt_path
#print axioms stored_hoare
#print axioms henceforth_iff_alwaysAll
#print axioms henceforth_iff_alwaysFair
#print axioms Hoare.mono
#print axioms StoredControls.taker_produces
#print axioms StoredControls.reader_produces
#print axioms StoredControls.start_noNine
#print axioms StoredControls.taker_reader_keep_noNine
#print axioms StoredControls.maker_valid_empty
#print axioms StoredControls.maker_breaks_noNine

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.AnnotatedRuns
