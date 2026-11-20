import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Correctness

/-!
# T1 for executions

The reading runs under the set-store disciplines of `RuleSyntax` (`SetStoreSyntax.DisciplinedStep`).
Through `SetStoreSyntax.discipline_terminal_eq_closure`, every disciplined terminal run from
`{(demand C₀)} ∪ Rel` ends with exactly the rows the semantics describes
(`terminal_run_eq_semanticRows`, `terminal_run_rows`).

So that this is not vacuous: when finitely many calls are demanded, each with finitely many values,
the closure is finite (`closure_finite`) and a terminal run exists for every discipline
(`exists_terminal_run`, through `SetStoreSyntax.discipline_exists_terminal` with the closure as the
finite closed carrier). Conversely a terminal run forces that finiteness
(`finite_of_terminal_run`): the hypothesis is exactly what termination needs.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open OneFrame (Terms)
open SetStoreSyntax (consequence GroundRows Discipline DisciplinedStep TerminalWith Determinate
  discipline_terminal_eq_closure discipline_exists_terminal)

universe u

/-- Lists of bounded length over a finite set form a finite set. -/
theorem lists_finite {T : Type*} {A : Set T} (finite : A.Finite) :
    ∀ N : ℕ, {ts : List T | ts.length ≤ N ∧ ∀ t ∈ ts, t ∈ A}.Finite
  | 0 => by
    apply (Set.finite_singleton ([] : List T)).subset
    rintro ts ⟨length, -⟩
    exact List.eq_nil_of_length_eq_zero (Nat.le_zero.mp length)
  | N + 1 => by
    apply ((Set.finite_singleton ([] : List T)).union
      (finite.biUnion fun a _ => (lists_finite finite N).image (List.cons a))).subset
    rintro ts ⟨length, inside⟩
    cases ts with
    | nil => exact Or.inl rfl
    | cons t rest =>
      refine Or.inr (Set.mem_biUnion (inside t List.mem_cons_self) ⟨rest, ⟨?_, ?_⟩, rfl⟩)
      · simpa using length
      · exact fun x member => inside x (List.mem_cons_of_mem _ member)

/-! ## Finiteness -/

section Finiteness

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L]
  {M : L → ModuleRule (readingSignature σ L)} {Rel : Finset (Atom (readingSignature σ L))}
  {C₀ : Term (readingSignature σ L)}

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
/-- **Finitely many demanded calls with finitely many values each give finitely many rows**: the
stages hold demanded calls and targets that are values of demanded calls or rows of `Rel`. -/
theorem semanticRows_finite [Finite L] (demands : {C | Demanded M ↑Rel C₀ C}.Finite)
    (values : ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite) :
    (semanticRows M Rel C₀).Finite := by
  have allValues : (⋃ C ∈ {C | Demanded M ↑Rel C₀ C}, {w | Derives M ↑Rel C w}).Finite :=
    demands.biUnion fun C inside => values C inside
  have stored : ((⋃ C ∈ {C | Demanded M ↑Rel C₀ C}, {w | Derives M ↑Rel C w}) ∪
      atomRow '' (Rel : Set (Atom (readingSignature σ L)))).Finite :=
    allValues.union (Rel.finite_toSet.image _)
  have superset : (demandRow '' {C | Demanded M ↑Rel C₀ C} ∪
      (⋃ C ∈ {C | Demanded M ↑Rel C₀ C}, valueRow C '' {w | Derives M ↑Rel C w}) ∪
      (⋃ l : L, (fun x : Term (readingSignature σ L) × List (Term (readingSignature σ L)) =>
          stagePattern l x.1 x.2) ''
        ({C | Demanded M ↑Rel C₀ C} ×ˢ {ts | ts.length ≤ (M l).premises.length ∧
          ∀ t ∈ ts, t ∈ (⋃ C ∈ {C | Demanded M ↑Rel C₀ C}, {w | Derives M ↑Rel C w}) ∪
            atomRow '' (Rel : Set (Atom (readingSignature σ L)))})) ∪
      atomRow '' (Rel : Set (Atom (readingSignature σ L)))).Finite :=
    (((demands.image _).union (demands.biUnion fun C inside => (values C inside).image _)).union
      (Set.finite_iUnion fun l => (demands.prod (lists_finite stored _)).image _)).union
      (Rel.finite_toSet.image _)
  apply superset.subset
  rintro row (⟨C, rfl, demanded⟩ | ⟨C, w, rfl, demanded, derives⟩ |
    ⟨l, θ, pre, post, split, rfl, demanded, holds⟩ | ⟨a, member, rfl⟩)
  · exact Or.inl (Or.inl (Or.inl ⟨C, demanded, rfl⟩))
  · exact Or.inl (Or.inl (Or.inr (Set.mem_biUnion demanded ⟨w, derives, rfl⟩)))
  · refine Or.inl (Or.inr (Set.mem_iUnion.mpr ⟨l, ⟨(θ.applyTerm (M l).lhs, (targets pre).map θ.applyTerm),
      ⟨demanded, ?_, ?_⟩, (apply_stagePattern θ l (M l).lhs (targets pre)).symm⟩⟩))
    · simp [targets_length, split]
    · intro t inside
      obtain ⟨target, inTargets, rfl⟩ := List.mem_map.mp inside
      obtain ⟨p, member, rfl⟩ := List.mem_map.mp inTargets
      obtain ⟨before, after, rfl⟩ := List.append_of_mem member
      cases p with
      | call source target =>
        have asked : Demanded M ↑Rel C₀ (θ.applyTerm source) :=
          .call (pre := before) (post := after ++ post) (source := source) (target := target) demanded
            (by rw [split]; simp) fun q inside => holds q (List.mem_append_left _ inside)
        exact Or.inl (Set.mem_biUnion asked (holds _ member))
      | query atom =>
        exact Or.inr ⟨θ.applyAtom atom, holds _ member, (apply_atomRow θ atom).symm⟩
  · exact Or.inr ⟨a, Finset.mem_coe.mpr member, rfl⟩

/-- **The closure is finite** when finitely many calls are demanded, each with finitely many values. -/
theorem closure_finite [Finite L] (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround)
    (relGround : ∀ a ∈ Rel, a.isGround) (demands : {C | Demanded M ↑Rel C₀ C}.Finite)
    (values : ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite) :
    (SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel)).Finite := by
  rw [closure_eq_semanticRows rr ground relGround]
  exact semanticRows_finite demands values

/-- The finite closure is a closed carrier. -/
theorem closure_toFinset_closed [Finite L] (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround)
    (relGround : ∀ a ∈ Rel, a.isGround) (demands : {C | Demanded M ↑Rel C₀ C}.Finite)
    (values : ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite) :
    SetStoreClosure.Closed (consequence (P := reading M))
      (closure_finite rr ground relGround demands values).toFinset := by
  intro m enabled x made
  rw [Set.Finite.mem_toFinset]
  exact SetStoreClosure.closure_closed _ _ m
    ⟨fun y inside => (Set.Finite.mem_toFinset _).mp (enabled inside), made⟩

/-- **A terminal run of the reading's ground instances exists** (`SetStoreClosure.exists_terminal`
with the finite closure as carrier), and it ends with exactly the described rows. -/
theorem exists_terminal_instance_run [Finite L] (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround)
    (relGround : ∀ a ∈ Rel, a.isGround) (demands : {C | Demanded M ↑Rel C₀ C}.Finite)
    (values : ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite) :
    ∃ rows, Relation.ReflTransGen (SetStoreClosure.Step (consequence (P := reading M))) (seed C₀ Rel) rows ∧
      SetStoreClosure.Terminal (consequence (P := reading M)) rows ∧
      (rows : Set (Term (readingSignature σ L))) = semanticRows M Rel C₀ := by
  obtain ⟨rows, run, terminal⟩ := SetStoreClosure.exists_terminal (consequence (P := reading M))
    (closure_finite rr ground relGround demands values).toFinset
    (closure_toFinset_closed rr ground relGround demands values) (seed C₀ Rel)
    (fun x inside => (Set.Finite.mem_toFinset _).mpr (SetStoreClosure.seed_subset_closure _ _ inside))
  exact ⟨rows, run, terminal, (SetStoreClosure.terminal_eq_closure _ _ run terminal).trans
    (closure_eq_semanticRows rr ground relGround)⟩

end Finiteness

/-! ## Every terminal run

The set-store disciplines of `RuleSyntax` are stated for signatures in `Type`. -/

section Runs

variable {σ : LPSignature.{0, 0, 0, 0}} {L : Type} [Fintype L]
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L]
  {M : L → ModuleRule (readingSignature σ L)} {Rel : Finset (Atom (readingSignature σ L))}
  {C₀ : Term (readingSignature σ L)}

variable (M) in
/-- The reading's rules as a list. -/
noncomputable def readingRules : List (Rule (Terms (Term (readingSignature σ L)))) :=
  (readingList M Finset.univ.toList).map Prod.snd

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
theorem readingRules_covers : ∀ rule ∈ reading M, rule ∈ readingRules M :=
  fun _ inside => mem_list_of_mem_reading (fun l => Finset.mem_toList.mpr (Finset.mem_univ l)) inside

/-- **T1, every run.** Every disciplined terminal run of the reading from `{(demand C₀)} ∪ Rel` ends
with exactly the rows the semantics describes. -/
theorem terminal_run_eq_semanticRows (slots : σ.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
    {after : Finset (Term (readingSignature σ L))}
    (run : Relation.ReflTransGen (DisciplinedStep discipline timing (reading M)) (seed C₀ Rel) after)
    (terminal : TerminalWith discipline timing (reading M) after)
    (uniquePolicy : discipline = .unique → Determinate (P := reading M) after) :
    (after : Set (Term (readingSignature σ L))) = semanticRows M Rel C₀ :=
  (discipline_terminal_eq_closure (signature := readingSignature σ L) (P := reading M) slots discipline timing
    (reading_propagates rr) (readingRules M)
    readingRules_covers (seed_ground ground relGround) run terminal uniquePolicy).trans
    (closure_eq_semanticRows rr ground relGround)

/-- **T1, every run, demands and values.** A disciplined terminal run holds `(demand C)` exactly for
the demanded calls and `(value C w)` exactly for their values. -/
theorem terminal_run_rows (slots : σ.vars ≃ ℕ) (discipline : Discipline) (timing : SetStore.AskTiming)
    (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
    {after : Finset (Term (readingSignature σ L))}
    (run : Relation.ReflTransGen (DisciplinedStep discipline timing (reading M)) (seed C₀ Rel) after)
    (terminal : TerminalWith discipline timing (reading M) after)
    (uniquePolicy : discipline = .unique → Determinate (P := reading M) after) :
    (∀ C, demandRow C ∈ after ↔ Demanded M ↑Rel C₀ C) ∧
      ∀ C w, valueRow C w ∈ after ↔ Demanded M ↑Rel C₀ C ∧ Derives M ↑Rel C w := by
  have equal := terminal_run_eq_semanticRows slots discipline timing rr ground relGround run terminal
    uniquePolicy
  refine ⟨fun C => ?_, fun C w => ?_⟩
  · rw [← Finset.mem_coe, equal]
    exact demandRow_mem_semanticRows
  · rw [← Finset.mem_coe, equal]
    exact valueRow_mem_semanticRows

/-- **A terminal run forces finiteness**: its rows are finitely many, so are the demanded calls and
each one's values. -/
theorem finite_of_terminal_run (slots : σ.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
    {after : Finset (Term (readingSignature σ L))}
    (run : Relation.ReflTransGen (DisciplinedStep discipline timing (reading M)) (seed C₀ Rel) after)
    (terminal : TerminalWith discipline timing (reading M) after)
    (uniquePolicy : discipline = .unique → Determinate (P := reading M) after) :
    {C | Demanded M ↑Rel C₀ C}.Finite ∧ ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite := by
  obtain ⟨demands, values⟩ := terminal_run_rows slots discipline timing rr ground relGround run terminal
    uniquePolicy
  refine ⟨?_, fun C _ => ?_⟩
  · apply (after.finite_toSet.preimage (f := demandRow) fun _ _ _ _ same => demandRow_inj same).subset
    exact fun C demanded => (demands C).mpr demanded
  · apply (after.finite_toSet.preimage (f := valueRow C) fun _ _ _ _ same => (valueRow_inj same).2).subset
    intro w derives
    exact (values C w).mpr ⟨by assumption, derives⟩

/-- **A terminal run exists** for every discipline when finitely many calls are demanded, each with
finitely many values. -/
theorem exists_terminal_run (discipline : Discipline) (timing : SetStore.AskTiming)
    (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
    (demands : {C | Demanded M ↑Rel C₀ C}.Finite)
    (values : ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite) :
    ∃ after, Relation.ReflTransGen (DisciplinedStep discipline timing (reading M)) (seed C₀ Rel) after ∧
      TerminalWith discipline timing (reading M) after := by
  exact discipline_exists_terminal discipline timing (reading_propagates rr)
    (closure_finite rr ground relGround demands values).toFinset (seed C₀ Rel)
    (closure_toFinset_closed rr ground relGround demands values)
    (fun x inside => (Set.Finite.mem_toFinset _).mpr (SetStoreClosure.seed_subset_closure _ _ inside))
    (seed_ground ground relGround)

/-- **T1 with existence.** For finitely many demanded calls with finitely many values each, a terminal
run exists, and it holds exactly the demanded calls and their values. -/
theorem exists_terminal_run_rows (slots : σ.vars ≃ ℕ) (discipline : Discipline)
    (timing : SetStore.AskTiming) (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
    (demands : {C | Demanded M ↑Rel C₀ C}.Finite)
    (values : ∀ C, Demanded M ↑Rel C₀ C → {w | Derives M ↑Rel C w}.Finite)
    (uniquePolicy : discipline = .unique → ∀ rows,
      Relation.ReflTransGen (DisciplinedStep discipline timing (reading M)) (seed C₀ Rel) rows →
        Determinate (P := reading M) rows) :
    ∃ after, Relation.ReflTransGen (DisciplinedStep discipline timing (reading M)) (seed C₀ Rel) after ∧
      TerminalWith discipline timing (reading M) after ∧
      (∀ C, demandRow C ∈ after ↔ Demanded M ↑Rel C₀ C) ∧
      ∀ C w, valueRow C w ∈ after ↔ Demanded M ↑Rel C₀ C ∧ Derives M ↑Rel C w := by
  obtain ⟨after, run, terminal⟩ := exists_terminal_run discipline timing rr ground relGround demands values
  exact ⟨after, run, terminal, terminal_run_rows slots discipline timing rr ground relGround run terminal
    fun unique => uniquePolicy unique after run⟩

end Runs

#print axioms lists_finite
#print axioms semanticRows_finite
#print axioms closure_finite
#print axioms closure_toFinset_closed
#print axioms exists_terminal_instance_run
#print axioms terminal_run_eq_semanticRows
#print axioms terminal_run_rows
#print axioms finite_of_terminal_run
#print axioms exists_terminal_run
#print axioms exists_terminal_run_rows

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
