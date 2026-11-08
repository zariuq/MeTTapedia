import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RaceSteps
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.RacePair
import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Step.ObserverChoices

/-!
# Resolving a race with a record

A commit operator (`first`, `once`) resolves a race among firings. What can such an operator be?

* **No deterministic equivariant commit** (`no_deterministic_equivariant_commit`): a commit that is a
  function of what the observer recorded, and commutes with every renaming of occurrences, picks
  neither of two competing firings that an automorphism of the record exchanges. This is
  `AnnotatedRuns.no_equivariant_selection` lifted from occurrences to firings. It excludes
  deterministic equivariant commits only: a commit with extra state or an asymmetry may select, and a
  randomized commit may be equivariant as a distribution while each of its outcomes breaks the
  symmetry.
* **The record-carrying commit** (`CommitsWithRecord`) is a contract, not a consequence of the
  theorem above: the commit is a relation between a record and its outcomes, each outcome a winning
  firing together with the record extended by the occurrences the winner took, which is what the
  escape `AnnotatedRuns.choiceEscape` records for a firing without predicate queries
  (`choiceEscape_records`). The relation is equivariant (`commitsWithRecord_equivariant`): renaming the
  record renames its outcomes. Each outcome breaks the symmetry: a renaming that moves a taken
  occurrence is not an automorphism of the extended record (`commitsWithRecord_breaks_symmetry`).

## Where the choice is visible

* **When the choice was made is invisible in the answer bag and visible in the causal identity**
  (`commit_timing`): the race pair commits at its first firing in `Q` and at its second in `P`;
  their answer bags agree at every budget, and they are not history-preserving bisimilar.
* **Which branch was chosen is invisible in the answer bag** (`Twins.bag_symmetric`): for two firings
  racing for one gate, each with its own occurrence of two indiscernible ones, the collected bag is
  invariant under the exchange of those occurrences.
  The history of each run names its winner (`Twins.history_names_winner`) and its extended record
  is not fixed by the exchange (`Twins.record_breaks_symmetry`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race

open AnnotatedRuns (Firing renameConfiguration)
open Observation (Record)
open MeTTaCalculus.OccurrenceCommits (Enabled)

universe uT uS uO

variable {T : Type uT} {S : Type uS} {O : Type uO} [DecidableEq O]

/-! ## Deterministic commits -/

omit [DecidableEq O] in
/-- **No deterministic equivariant commit.** A commit that chooses a firing as a function of the
record and commutes with renaming chooses neither of two distinct firings that an automorphism of
the record exchanges. -/
theorem no_deterministic_equivariant_commit (commit : Record O → Firing T S O)
    (equivariant : ∀ (π : O ≃ O) (r : Record O), commit (Record.rename π r) = (commit r).rename π)
    {r : Record O} {π : O ≃ O} (aut : π ∈ Record.automorphisms r) {f g : Firing T S O}
    (apart : f ≠ g) (exchanges : f.rename π = g ∧ g.rename π = f) : commit r ≠ f ∧ commit r ≠ g := by
  have fixed : (commit r).rename π = commit r := by
    rw [← equivariant]
    exact congrArg commit aut
  refine ⟨fun picked => apart ?_, fun picked => apart ?_⟩
  · rw [picked, exchanges.1] at fixed
    exact fixed.symm
  · rw [picked, exchanges.2] at fixed
    exact fixed

/-! ## The record-carrying commit -/

/-- **The record-carrying commit**: an outcome is a winning competitor together with the record
extended by the occurrences it took. -/
def CommitsWithRecord (competitors : List (Firing T S O)) (r : Record O)
    (out : Firing T S O × Record O) : Prop :=
  out.1 ∈ competitors ∧ out.2 = r ++ Record.references out.1.selection.taken

/-- The record a commit adds is the escape's record of the winner, for firings without predicate
queries. -/
theorem choiceEscape_records (A : SubstitutionAction T S) (label : O → T) {C : Configuration T O}
    {f : Firing T S O} (noQueries : f.queries = []) :
    (AnnotatedRuns.choiceEscape A label).records (s := C) f = Record.references f.selection.taken := by
  show Observation.querySightings f.queries ++ _ = _
  rw [noQueries]
  rfl

omit [DecidableEq O] in
/-- **The record-carrying commit is equivariant**: when the competitors are closed under a renaming,
renaming the record renames every outcome. -/
theorem commitsWithRecord_equivariant {competitors : List (Firing T S O)} {π : O ≃ O}
    (closed : ∀ f ∈ competitors, f.rename π ∈ competitors) {r : Record O}
    {out : Firing T S O × Record O} (commits : CommitsWithRecord competitors r out) :
    CommitsWithRecord competitors (Record.rename π r) (out.1.rename π, Record.rename π out.2) := by
  obtain ⟨member, record⟩ := commits
  refine ⟨closed _ member, ?_⟩
  rw [record, Record.rename_append]
  show _ = _ ++ Record.references (out.1.selection.taken.map π)
  rw [Observation.Record.references_rename]

omit [DecidableEq O] in
/-- **Each outcome breaks the symmetry**: a renaming that moves an occurrence the winner took is not
an automorphism of the extended record. -/
theorem commitsWithRecord_breaks_symmetry {competitors : List (Firing T S O)} {r : Record O}
    {out : Firing T S O × Record O} (commits : CommitsWithRecord competitors r out) {π : O ≃ O}
    {o : O} (taken : o ∈ out.1.selection.taken) (moved : π o ≠ o) :
    π ∉ Record.automorphisms out.2 := by
  intro aut
  have carried : Record.rename π out.2 = out.2 := aut
  rw [commits.2, Record.rename_append_eq_iff] at carried
  exact moved ((Record.references_rename_eq_iff.mp carried.2) o taken)

/-! ## When the choice was made -/

/-- **The timing of a commit is invisible in the answer bag and visible in the causal identity.**
In the race pair, `Q` commits at its first firing and `P` at its second; their answer bags agree at
every budget, and they are not history-preserving bisimilar. -/
theorem commit_timing (t : Pair.Tags T) (A : SubstitutionAction T S) (apart : t.b ≠ t.c) :
    (∀ n, Search.Outcome.collect ((Pair.search t A).approx n (.inr Pair.P)) =
      Search.Outcome.collect ((Pair.search t A).approx n (.inr Pair.Q))) ∧
      ¬ HPBisimilar A (Pair.label t) (Pair.offers t) Pair.P Pair.Q :=
  ⟨Pair.collect_P_eq_collect_Q t A,
    fun hp => Pair.not_bisimilar_P_Q t A apart (bisimilar_of_hpBisimilar hp)⟩

/-! ## Which branch was chosen -/

namespace Twins

/-- Two indiscernible occurrences and the gate both competitors take. -/
inductive Site
  | x | y | g
  deriving DecidableEq

variable (τ : T)

/-- Both carry `τ`. -/
def label : Site → T := fun _ => τ

/-- Take one occurrence and the gate. -/
def take (o : Site) : Firing T S Site := ⟨⟨[τ, τ], [], [], [], []⟩, [], ⟨[o, .g], [], []⟩⟩

/-- The two competitors. -/
def competitors : List (Firing T S Site) := [take τ .x, take τ .y]

/-- The exchange of the two occurrences. -/
def exchange : Site ≃ Site := Equiv.swap .x .y

def C : Configuration T Site := ⟨[], {.x, .y, .g}⟩
/-- After `x` won. -/
def Cx : Configuration T Site := ⟨[(τ, τ), (τ, τ)], {.y}⟩
/-- After `y` won. -/
def Cy : Configuration T Site := ⟨[(τ, τ), (τ, τ)], {.x}⟩

theorem config_eq {D E : Configuration T Site} (equations : D.equations = E.equations)
    (present : D.present = E.present) : D = E := by
  cases D
  cases E
  cases equations
  cases present
  rfl

theorem ground : ∀ f ∈ competitors (S := S) τ, Ground (label τ) f := by
  intro f member
  simp only [competitors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, of_decide_eq_true rfl, of_decide_eq_true rfl⟩

theorem exchange_take (o : Site) : (take (S := S) τ o).rename exchange = take τ (exchange o) := rfl

/-- **The two competitors are exchanged.** -/
theorem competitors_exchanged :
    (take (S := S) τ .x).rename exchange = take τ .y ∧ (take (S := S) τ .y).rename exchange = take τ .x :=
  ⟨rfl, rfl⟩

theorem take_ne : take (S := S) τ .x ≠ take τ .y := by
  intro same
  have := congrArg (fun f : Firing T S Site => f.selection.taken) same
  simp [take] at this

theorem result_x : (take (S := S) τ .x).result (label τ) C = Cx τ := config_eq rfl (of_decide_eq_true rfl)
theorem result_y : (take (S := S) τ .y).result (label τ) C = Cy τ := config_eq rfl (of_decide_eq_true rfl)

theorem reflexive_two : Reflexive ([(τ, τ), (τ, τ)] : EquationStore T) := by
  intro e member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> rfl

variable (A : SubstitutionAction T S)

/-- The search of the race. -/
noncomputable abbrev search := (alternatives A (label τ) (competitors τ)).space

theorem next_C : ((alternatives A (label τ) (competitors τ)).next C).map (fun g => g.1.1) =
    [take τ .x, take τ .y] := by
  rw [next_map_of_ground (ground τ) reflexive_nil]
  rfl

theorem next_Cx : ((alternatives A (label τ) (competitors τ)).next (Cx τ)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ) (reflexive_two τ)]
  rfl

theorem next_Cy : ((alternatives A (label τ) (competitors τ)).next (Cy τ)).map (fun g => g.1.1) = [] := by
  rw [next_map_of_ground (ground τ) (reflexive_two τ)]
  rfl

/-- **The answer bag holds both branches, once each.** -/
theorem bag : Search.Outcome.collect ((search τ A).approx 2 (.inr C)) =
    Search.Outcome.pure ({Cx τ, Cy τ} : Multiset (Configuration T Site)) := by
  rw [Search.Space.approx_succ, unfold_of_cons (next_C τ A)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, result_x, result_y,
    Search.Space.approx_succ, unfold_of_nil (next_Cx τ A), unfold_of_nil (next_Cy τ A),
    Search.Space.approx_inl]
  rfl

theorem rename_Cx : renameConfiguration exchange (Cx τ) = Cy τ := config_eq rfl (of_decide_eq_true rfl)
theorem rename_Cy : renameConfiguration exchange (Cy τ) = Cx τ := config_eq rfl (of_decide_eq_true rfl)

/-- **Which branch was chosen is invisible in the answer bag**: the bag is invariant under the
exchange of the competitors. -/
theorem bag_symmetric :
    (Search.Outcome.collect ((search τ A).approx 2 (.inr C))).map
        (Multiset.map (renameConfiguration exchange)) =
      Search.Outcome.collect ((search τ A).approx 2 (.inr C)) := by
  rw [bag, Search.Outcome.map_pure]
  congr 1
  show Multiset.map _ (Cx τ ::ₘ {Cy τ}) = Cx τ ::ₘ {Cy τ}
  rw [Multiset.map_cons, Multiset.map_singleton, rename_Cx, rename_Cy]
  exact Multiset.cons_swap _ _ _
/-- **The history of each run names its winner**: the history moves out of `C` record the firing
that took the race. -/
theorem history_names_winner {ℓ : Unit} {P : Finset ℕ} {y : Configuration T Site × History T S Site}
    (moved : HMoves A (label τ) (fun _ f => f ∈ competitors τ) (C, []) (ℓ, P) y) :
    (y = (Cx τ, [(take τ .x, P)]) ∨ y = (Cy τ, [(take τ .y, P)])) := by
  obtain ⟨f, member, _, _, rfl⟩ := moved
  simp only [competitors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact .inl (by rw [result_x]; rfl)
  · exact .inr (by rw [result_y]; rfl)

/-- **The extended record of each outcome breaks the symmetry** that made the race undecidable for
a deterministic equivariant commit. -/
theorem record_breaks_symmetry (r : Record Site) {out : Firing T S Site × Record Site}
    (commits : CommitsWithRecord (competitors τ) r out) : exchange ∉ Record.automorphisms out.2 := by
  have member := commits.1
  simp only [competitors, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with same | same
  · exact commitsWithRecord_breaks_symmetry commits (o := .x) (by rw [same]; simp [take]) (by decide)
  · exact commitsWithRecord_breaks_symmetry commits (o := .y) (by rw [same]; simp [take]) (by decide)

/-- **No deterministic equivariant commit resolves the twins**: at a record that sighted both, a
deterministic equivariant commit picks neither competitor. -/
theorem twins_no_commit (commit : Record Site → Firing T S Site)
    (equivariant : ∀ (π : Site ≃ Site) (r : Record Site), commit (Record.rename π r) = (commit r).rename π) :
    commit [Observation.Record.sighting {.x, .y}] ≠ take τ .x ∧
      commit [Observation.Record.sighting {.x, .y}] ≠ take τ .y := by
  refine no_deterministic_equivariant_commit commit equivariant ?_ (take_ne τ) (competitors_exchanged τ)
  show Record.rename exchange [Observation.Record.sighting {.x, .y}] = [Observation.Record.sighting {.x, .y}]
  simp only [Record.rename, List.map_cons, List.map_nil, Observation.Record.renameEntry_sighting]
  congr 2
  decide

end Twins

#print axioms no_deterministic_equivariant_commit
#print axioms choiceEscape_records
#print axioms commitsWithRecord_equivariant
#print axioms commitsWithRecord_breaks_symmetry
#print axioms commit_timing
#print axioms Twins.bag
#print axioms Twins.bag_symmetric
#print axioms Twins.history_names_winner
#print axioms Twins.record_breaks_symmetry
#print axioms Twins.twins_no_commit

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.Race
