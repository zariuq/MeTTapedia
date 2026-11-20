import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Reading

/-!
# T1: the reading's closure holds exactly the demanded calls and their values

For a module `M`, relation rows `Rel` and a ground call `C₀`, the reading runs from the seed
`{(demand C₀)} ∪ Rel` (`seed`). Its least closure under the ground instances of its rules
(`SetStoreClosure.closure (consequence (P := reading M))`) is described by the semantics alone
(`semanticRows`):

* `(demand C)` exactly for the calls `Demanded` from `C₀` (`demandRow_mem_closure_iff`);
* `(value C w)` exactly when `C` is demanded and `Derives C w` (`valueRow_mem_closure_iff`);
* `(l/i C t1 .. ti)` exactly when `C` is demanded and, under one substitution matching `l`'s left
  side to `C`, premises `1 .. i` hold and store `t1 .. ti` (`stageRow_mem_closure_iff`);
* a relation row exactly for the rows of `Rel` (`atomRow_mem_closure_iff`); nothing else
  (`closure_eq_semanticRows`).

The hypotheses: every module rule is range-restricted, `C₀` is ground, and so are `Rel`'s rows.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom Subst)
open OneFrame (Terms)
open SetStoreSyntax (varsIn mem_variables Propagates GroundMatch GroundRows consequence instance_ground
  apply_eq_of_agree agree_of_apply_eq)
open Mettapedia.GSLT.OpenEnded.ChaoticIteration (isLeast_target)

universe u

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L]

/-- Atoms are compared by their symbol and their arguments. -/
instance atomDecidableEq {ρ : LPSignature} [DecidableEq ρ.relationSymbols] [DecidableEq (Term ρ)] :
    DecidableEq (Atom ρ) := fun first second =>
  decidable_of_iff
    ((⟨first.symbol, first.args⟩ : Σ r : ρ.relationSymbols, Fin (ρ.relationArity r) → Term ρ) =
      ⟨second.symbol, second.args⟩)
    (by
      cases first
      cases second
      simp only [Sigma.mk.injEq, Atom.mk.injEq])

/-! ## The seed, and ground closures -/

/-- The seed of a run: the call asked, and the relation's rows. -/
def seed (C₀ : Term (readingSignature σ L)) (Rel : Finset (Atom (readingSignature σ L))) :
    Finset (Term (readingSignature σ L)) :=
  insert (demandRow C₀) (Rel.image atomRow)

theorem seed_ground {C₀ : Term (readingSignature σ L)} {Rel : Finset (Atom (readingSignature σ L))}
    (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround) : GroundRows (seed C₀ Rel) := by
  intro t inside
  rcases Finset.mem_insert.mp inside with rfl | inside
  · exact demandRow_ground ground
  · obtain ⟨a, member, rfl⟩ := Finset.mem_image.mp inside
    exact relGround a member

/-- From a ground seed, every row of the closure of a program is ground. -/
theorem closure_ground {ρ : LPSignature} [DecidableEq ρ.vars] [DecidableEq ρ.constants]
    [DecidableEq ρ.functionSymbols] (P : Program (Terms (Term ρ))) {start : Finset (Term ρ)}
    (ground : GroundRows start) :
    ∀ t ∈ SetStoreClosure.closure (consequence (P := P)) start, t.isGround := by
  have least := (isLeast_target (fun m => SetStoreClosure.action (consequence (P := P) m))
    (start : Set (Term ρ))).2
  refine least ⟨fun t inside => ground t inside, fun m t made => ?_⟩
  exact instance_ground m t made.2

/-! ## The rows the semantics describes -/

variable {M : L → ModuleRule (readingSignature σ L)} {Rel : Finset (Atom (readingSignature σ L))}
  {C₀ : Term (readingSignature σ L)}

variable (M Rel C₀) in
/-- **The rows the semantics describes**: the demanded calls, their values, the stages of rules
matched at a demanded call whose first premises hold, and the relation's rows. -/
def semanticRows : Set (Term (readingSignature σ L)) :=
  {row | (∃ C, row = demandRow C ∧ Demanded M ↑Rel C₀ C) ∨
    (∃ C w, row = valueRow C w ∧ Demanded M ↑Rel C₀ C ∧ Derives M ↑Rel C w) ∨
    (∃ l θ pre post, (M l).premises = pre ++ post ∧
      row = θ.applyTerm (stagePattern l (M l).lhs (targets pre)) ∧
      Demanded M ↑Rel C₀ (θ.applyTerm (M l).lhs) ∧ ∀ p ∈ pre, Holds M ↑Rel θ p) ∨
    (∃ a ∈ Rel, row = atomRow a)}

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
theorem demandRow_mem_semanticRows {C : Term (readingSignature σ L)} :
    demandRow C ∈ semanticRows M Rel C₀ ↔ Demanded M ↑Rel C₀ C := by
  constructor
  · rintro (⟨C', same, demanded⟩ | ⟨C', w, same, _⟩ | ⟨l, θ, pre, post, _, same, demanded, _⟩ | ⟨a, _, same⟩)
    · exact demandRow_inj same ▸ demanded
    · exact absurd same (demandRow_ne_valueRow _ _ _)
    · by_cases empty : pre = []
      · subst empty
        rw [stagePattern_nil] at same
        exact demandRow_inj same ▸ demanded
      · rw [apply_stagePattern_cons θ l _ empty] at same
        exact absurd same (demandRow_ne_stageRow _ _ _ _)
    · exact absurd same (demandRow_ne_atomRow _ _)
  · exact fun demanded => Or.inl ⟨C, rfl, demanded⟩

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
theorem valueRow_mem_semanticRows {C w : Term (readingSignature σ L)} :
    valueRow C w ∈ semanticRows M Rel C₀ ↔ Demanded M ↑Rel C₀ C ∧ Derives M ↑Rel C w := by
  constructor
  · rintro (⟨C', same, _⟩ | ⟨C', w', same, demanded, derives⟩ | ⟨l, θ, pre, post, _, same, _, _⟩ |
      ⟨a, _, same⟩)
    · exact absurd same.symm (demandRow_ne_valueRow _ _ _)
    · obtain ⟨rfl, rfl⟩ := valueRow_inj same
      exact ⟨demanded, derives⟩
    · by_cases empty : pre = []
      · subst empty
        rw [stagePattern_nil] at same
        exact absurd same.symm (demandRow_ne_valueRow _ _ _)
      · rw [apply_stagePattern_cons θ l _ empty] at same
        exact absurd same (valueRow_ne_stageRow _ _ _ _ _)
    · exact absurd same (valueRow_ne_atomRow _ _ _)
  · exact fun ⟨demanded, derives⟩ => Or.inr (Or.inl ⟨C, w, rfl, demanded, derives⟩)

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
theorem atomRow_mem_semanticRows {a : Atom (readingSignature σ L)} :
    atomRow a ∈ semanticRows M Rel C₀ ↔ a ∈ Rel := by
  constructor
  · rintro (⟨C, same, _⟩ | ⟨C, w, same, _⟩ | ⟨l, θ, pre, post, _, same, _, _⟩ | ⟨a', member, same⟩)
    · exact absurd same.symm (demandRow_ne_atomRow _ _)
    · exact absurd same.symm (valueRow_ne_atomRow _ _ _)
    · by_cases empty : pre = []
      · subst empty
        rw [stagePattern_nil] at same
        exact absurd same.symm (demandRow_ne_atomRow _ _)
      · rw [apply_stagePattern_cons θ l _ empty] at same
        exact absurd same.symm (stageRow_ne_atomRow _ _ _ _)
    · exact atomRow_inj same ▸ member
  · exact fun member => Or.inr (Or.inr (Or.inr ⟨a, member, rfl⟩))

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
theorem stageRow_mem_semanticRows {l : L} {C : Term (readingSignature σ L)}
    {ts : List (Term (readingSignature σ L))} :
    stageRow l C ts ∈ semanticRows M Rel C₀ ↔ ts ≠ [] ∧ ∃ θ pre post, (M l).premises = pre ++ post ∧
      C = θ.applyTerm (M l).lhs ∧ ts = (targets pre).map θ.applyTerm ∧ Demanded M ↑Rel C₀ C ∧
      ∀ p ∈ pre, Holds M ↑Rel θ p := by
  constructor
  · rintro (⟨C', same, _⟩ | ⟨C', w, same, _⟩ | ⟨l', θ, pre, post, split, same, demanded, holds⟩ |
      ⟨a, _, same⟩)
    · exact absurd same.symm (demandRow_ne_stageRow _ _ _ _)
    · exact absurd same.symm (valueRow_ne_stageRow _ _ _ _ _)
    · by_cases empty : pre = []
      · subst empty
        rw [stagePattern_nil] at same
        exact absurd same.symm (demandRow_ne_stageRow _ _ _ _)
      · rw [apply_stagePattern_cons θ l' _ empty] at same
        obtain ⟨rfl, rfl, rfl⟩ := stageRow_inj same
        refine ⟨?_, θ, pre, post, split, rfl, rfl, demanded, holds⟩
        simpa [targets] using empty
    · exact absurd same (stageRow_ne_atomRow _ _ _ _)
  · rintro ⟨nonempty, θ, pre, post, split, rfl, rfl, demanded, holds⟩
    have preNonempty : pre ≠ [] := by
      rintro rfl
      exact nonempty rfl
    refine Or.inr (Or.inr (Or.inl ⟨l, θ, pre, post, split, ?_, demanded, holds⟩))
    rw [apply_stagePattern_cons θ l _ preNonempty]

/-! ## Agreement on bound variables -/

omit [DecidableEq σ.constants] [DecidableEq σ.functionSymbols] [DecidableEq σ.relationSymbols]
  [DecidableEq L] in
/-- **A stage that the semantics describes gives the stage's facts under the matching substitution.**
The substitution that matches a stage pattern to a described row agrees, on the variables bound at
that stage, with the one the description names; so the left side's call is demanded and the
premises before the stage hold under it. -/
theorem stage_facts (rr : ∀ l, RangeRestricted (M l)) {l : L} {pre post : List (Premise (readingSignature σ L))}
    (split : (M l).premises = pre ++ post) (θ' : Subst (readingSignature σ L))
    (described : θ'.applyTerm (stagePattern l (M l).lhs (targets pre)) ∈ semanticRows M Rel C₀) :
    Demanded M ↑Rel C₀ (θ'.applyTerm (M l).lhs) ∧ ∀ p ∈ pre, Holds M ↑Rel θ' p := by
  by_cases empty : pre = []
  · subst empty
    rw [stagePattern_nil] at described
    exact ⟨demandRow_mem_semanticRows.mp described, fun p member => absurd member List.not_mem_nil⟩
  · rw [apply_stagePattern_cons θ' l _ empty] at described
    obtain ⟨_, θ, pre', post', split', sameLhs, sameTargets, demanded, holds⟩ :=
      stageRow_mem_semanticRows.mp described
    have lengths : pre.length = pre'.length := by
      have := congrArg List.length sameTargets
      simpa [targets_length] using this
    obtain ⟨rfl, -⟩ := List.append_inj (split.symm.trans split') lengths
    have agree : ∀ v ∈ (M l).bound pre, θ v = θ' v := by
      intro v inside
      rcases Finset.mem_union.mp inside with inLhs | inBinds
      · exact (agree_of_apply_eq θ' θ (M l).lhs sameLhs v inLhs).symm
      · rw [← varsIn_targets] at inBinds
        exact (agree_of_map_eq θ' θ (targets pre) sameTargets v inBinds).symm
    exact ⟨sameLhs ▸ demanded, holds_transfer (rr l) split agree holds⟩

/-! ## The closure is inside the described rows -/

theorem seed_subset_semanticRows : (seed C₀ Rel : Set (Term (readingSignature σ L))) ⊆ semanticRows M Rel C₀ := by
  intro t inside
  rcases Finset.mem_insert.mp inside with rfl | inside
  · exact demandRow_mem_semanticRows.mpr .seed
  · obtain ⟨a, member, rfl⟩ := Finset.mem_image.mp inside
    exact atomRow_mem_semanticRows.mpr member

omit [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L] in
theorem holds_of_row {θ : Subst (readingSignature σ L)} {p : Premise (readingSignature σ L)}
    (described : θ.applyTerm p.row ∈ semanticRows M Rel C₀) : Holds M ↑Rel θ p := by
  cases p with
  | call source target =>
    rw [Premise.row, apply_valueRow] at described
    exact (valueRow_mem_semanticRows.mp described).2
  | query atom =>
    rw [Premise.row, apply_atomRow] at described
    exact Finset.mem_coe.mpr (atomRow_mem_semanticRows.mp described)

/-- **The described rows are closed under every ground instance of the reading.** -/
theorem semanticRows_closed (rr : ∀ l, RangeRestricted (M l)) (m : GroundMatch (reading M)) :
    SetStoreClosure.action (consequence m) (semanticRows M Rel C₀) ⊆ semanticRows M Rel C₀ := by
  rintro v ⟨readsIn, made⟩
  have reads : ∀ r ∈ m.rule.body.read, m.assignment.applyTerm r ∈ semanticRows M Rel C₀ :=
    fun r inside => readsIn (List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, inside, rfl⟩))
  obtain ⟨x, makes, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
  obtain ⟨l, ⟨pre, source, target, post, split, isRule⟩ | ⟨pre, p, post, split, isRule⟩ | isRule⟩ :=
    mem_reading_iff.mp m.member
  · rw [isRule] at reads makes
    obtain rfl := List.mem_singleton.mp makes
    obtain ⟨asked, holds⟩ := stage_facts rr split m.assignment (reads _ List.mem_cons_self)
    rw [apply_demandRow]
    exact demandRow_mem_semanticRows.mpr (.call asked split holds)
  · rw [isRule] at reads makes
    obtain rfl := List.mem_singleton.mp makes
    obtain ⟨asked, holds⟩ := stage_facts rr split m.assignment (reads _ List.mem_cons_self)
    have here := holds_of_row (reads _ (List.mem_cons_of_mem _ List.mem_cons_self))
    refine Or.inr (Or.inr (Or.inl ⟨l, m.assignment, pre ++ [p], post, by simp [split], ?_, asked, ?_⟩))
    · simp [targets]
    · intro q member
      rcases List.mem_append.mp member with before | now
      · exact holds q before
      · obtain rfl := List.mem_singleton.mp now
        exact here
  · rw [isRule] at reads makes
    obtain rfl := List.mem_singleton.mp makes
    obtain ⟨asked, holds⟩ := stage_facts rr (post := []) (List.append_nil _).symm m.assignment
      (reads _ List.mem_cons_self)
    rw [apply_valueRow]
    exact valueRow_mem_semanticRows.mpr ⟨asked, derives_iff.mpr ⟨l, m.assignment, rfl, rfl, holds⟩⟩

theorem closure_subset_semanticRows (rr : ∀ l, RangeRestricted (M l)) :
    SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) ⊆ semanticRows M Rel C₀ :=
  (isLeast_target (fun m => SetStoreClosure.action (consequence (P := reading M) m))
    (seed C₀ Rel : Set (Term (readingSignature σ L)))).2
      ⟨seed_subset_semanticRows, fun m => semanticRows_closed rr m⟩

/-! ## The described rows are reached -/

section Reached

variable (rr : ∀ l, RangeRestricted (M l)) (ground : GroundRows (seed C₀ Rel))
include rr ground

/-- A rule of the reading fires inside the closure. -/
theorem fire {rule : Rule (Terms (Term (readingSignature σ L)))} (member : rule ∈ reading M)
    (θ : Subst (readingSignature σ L))
    (reads : ∀ r ∈ rule.body.read,
      θ.applyTerm r ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel)) :
    ∀ x ∈ rule.body.produce,
      θ.applyTerm x ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) := by
  let m : GroundMatch (reading M) :=
    { rule := rule
      member := member
      propagates := reading_propagates rr rule member
      assignment := θ
      groundReads := fun r inside => closure_ground (reading M) ground _ (reads r inside)
      checked := fun left right inside => by
        rw [checks_of_mem_reading member] at inside
        cases inside }
  intro x made
  apply SetStoreClosure.closure_closed _ _ m
  refine ⟨fun y inside => ?_, List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, made, rfl⟩)⟩
  obtain ⟨r, inRead, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp inside)
  exact reads r inRead

/-- The stage of a rule matched at an asked call is reached once its premises are reached: a call
premise's value whenever its call is asked, a query by a row of `Rel`. -/
theorem stage_reached {l : L} {θ : Subst (readingSignature σ L)}
    (asked : demandRow (θ.applyTerm (M l).lhs) ∈
      SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel)) :
    ∀ (pre post : List (Premise (readingSignature σ L))), (M l).premises = pre ++ post →
      (∀ source target, Premise.call source target ∈ pre →
        demandRow (θ.applyTerm source) ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) →
        valueRow (θ.applyTerm source) (θ.applyTerm target) ∈
          SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel)) →
      (∀ atom, Premise.query atom ∈ pre → θ.applyAtom atom ∈ Rel) →
      θ.applyTerm (stagePattern l (M l).lhs (targets pre)) ∈
        SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) := by
  intro pre
  induction pre using List.reverseRecOn with
  | nil =>
    intro post _ _ _
    rw [stagePattern_nil]
    exact asked
  | append_singleton pre p ih =>
    intro post split calls queries
    have split' : (M l).premises = pre ++ p :: post := by simp [split]
    have before := ih (p :: post) split' (fun s t member => calls s t (List.mem_append_left _ member))
      (fun a member => queries a (List.mem_append_left _ member))
    have row : θ.applyTerm p.row ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) := by
      cases p with
      | call source target =>
        have demand := fire rr ground (askRule_mem_reading l split') θ
          (fun r inside => by
            obtain rfl := List.mem_singleton.mp inside
            exact before) _ List.mem_cons_self
        rw [apply_demandRow] at demand
        rw [Premise.row, apply_valueRow]
        exact calls source target (List.mem_append_right _ List.mem_cons_self) demand
      | query atom =>
        rw [Premise.row, apply_atomRow]
        apply SetStoreClosure.seed_subset_closure
        exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _
          (queries atom (List.mem_append_right _ List.mem_cons_self)))
    have made := fire rr ground (stepRule_mem_reading l split') θ
      (fun r inside => by
        rcases List.mem_cons.mp inside with rfl | inside
        · exact before
        · obtain rfl := List.mem_singleton.mp inside
          exact row) _ List.mem_cons_self
    simpa [targets_append, targets] using made

/-- **A derivation of an asked call reaches its value row.** -/
theorem value_reached {C w : Term (readingSignature σ L)} (derives : Derives M ↑Rel C w) :
    demandRow C ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) →
      valueRow C w ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) := by
  induction derives with
  | rule l θ calls queries ih =>
    intro asked
    have stage := stage_reached rr ground asked (M l).premises [] (List.append_nil _).symm
      (fun s t member demand => ih s t member demand)
      (fun a member => Finset.mem_coe.mp (queries a member))
    have made := fire rr ground (finalRule_mem_reading l) θ
      (fun r inside => by
        obtain rfl := List.mem_singleton.mp inside
        exact stage) _ List.mem_cons_self
    rwa [apply_valueRow] at made

/-- **A demanded call is asked.** -/
theorem demand_reached {C : Term (readingSignature σ L)} (demanded : Demanded M ↑Rel C₀ C) :
    demandRow C ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) := by
  induction demanded with
  | seed => exact SetStoreClosure.seed_subset_closure _ _ (Finset.mem_insert_self _ _)
  | @call l θ pre post source target _ split holds ih =>
    have stage := stage_reached rr ground ih pre (Premise.call source target :: post) split
      (fun s t member demand => value_reached rr ground (holds _ member) demand)
      (fun a member => Finset.mem_coe.mp (holds _ member))
    have made := fire rr ground (askRule_mem_reading l split) θ
      (fun r inside => by
        obtain rfl := List.mem_singleton.mp inside
        exact stage) _ List.mem_cons_self
    rwa [apply_demandRow] at made

theorem semanticRows_subset_closure :
    semanticRows M Rel C₀ ⊆ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) := by
  rintro row (⟨C, rfl, demanded⟩ | ⟨C, w, rfl, demanded, derives⟩ |
    ⟨l, θ, pre, post, split, rfl, demanded, holds⟩ | ⟨a, member, rfl⟩)
  · exact demand_reached rr ground demanded
  · exact value_reached rr ground derives (demand_reached rr ground demanded)
  · exact stage_reached rr ground (demand_reached rr ground demanded) pre post split
      (fun s t member demand => value_reached rr ground (holds _ member) demand)
      (fun a member => Finset.mem_coe.mp (holds _ member))
  · exact SetStoreClosure.seed_subset_closure _ _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ member))

end Reached

/-! ## T1 -/

section Theorems

variable (rr : ∀ l, RangeRestricted (M l)) (ground : C₀.isGround) (relGround : ∀ a ∈ Rel, a.isGround)
include rr ground relGround

/-- **T1, the closure.** The reading's least closure from `{(demand C₀)} ∪ Rel` is exactly the set of
rows the semantics describes. -/
theorem closure_eq_semanticRows :
    SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) = semanticRows M Rel C₀ :=
  Set.Subset.antisymm (closure_subset_semanticRows rr)
    (semanticRows_subset_closure rr (seed_ground ground relGround))

/-- **T1, demands.** `(demand C)` is in the closure exactly when `C` is demanded from `C₀`. -/
theorem demandRow_mem_closure_iff (C : Term (readingSignature σ L)) :
    demandRow C ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) ↔
      Demanded M ↑Rel C₀ C := by
  rw [closure_eq_semanticRows rr ground relGround]
  exact demandRow_mem_semanticRows

/-- **T1, values.** `(value C w)` is in the closure exactly when `C` is demanded and has the value `w`. -/
theorem valueRow_mem_closure_iff (C w : Term (readingSignature σ L)) :
    valueRow C w ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) ↔
      Demanded M ↑Rel C₀ C ∧ Derives M ↑Rel C w := by
  rw [closure_eq_semanticRows rr ground relGround]
  exact valueRow_mem_semanticRows

/-- **T1, stages** (the induction invariant): `(l/i C t1 .. ti)` is in the closure exactly when
`i ≥ 1`, `C` is demanded, and under one substitution matching `l`'s left side to `C`, `l`'s first
`i` premises hold and store `t1 .. ti`. -/
theorem stageRow_mem_closure_iff (l : L) (C : Term (readingSignature σ L)) (ts : List (Term (readingSignature σ L))) :
    stageRow l C ts ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) ↔
      ts ≠ [] ∧ ∃ θ pre post, (M l).premises = pre ++ post ∧ C = θ.applyTerm (M l).lhs ∧
        ts = (targets pre).map θ.applyTerm ∧ Demanded M ↑Rel C₀ C ∧ ∀ p ∈ pre, Holds M ↑Rel θ p := by
  rw [closure_eq_semanticRows rr ground relGround]
  exact stageRow_mem_semanticRows

/-- **T1, relation rows**: the closure holds exactly the given rows of the relation. -/
theorem atomRow_mem_closure_iff (a : Atom (readingSignature σ L)) :
    atomRow a ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel) ↔ a ∈ Rel := by
  rw [closure_eq_semanticRows rr ground relGround]
  exact atomRow_mem_semanticRows

/-- Every row of the closure is a demand, a value, a stage of a rule, or a relation's row. -/
theorem closure_row_cases {row : Term (readingSignature σ L)}
    (inside : row ∈ SetStoreClosure.closure (consequence (P := reading M)) (seed C₀ Rel)) :
    (∃ C, row = demandRow C) ∨ (∃ C w, row = valueRow C w) ∨ (∃ l C ts, row = stageRow l C ts) ∨
      ∃ a ∈ Rel, row = atomRow a := by
  rw [closure_eq_semanticRows rr ground relGround] at inside
  rcases inside with ⟨C, rfl, _⟩ | ⟨C, w, rfl, _⟩ | ⟨l, θ, pre, post, _, rfl, _, _⟩ | described
  · exact Or.inl ⟨C, rfl⟩
  · exact Or.inr (Or.inl ⟨C, w, rfl⟩)
  · by_cases empty : pre = []
    · subst empty
      rw [stagePattern_nil]
      exact Or.inl ⟨_, rfl⟩
    · rw [apply_stagePattern_cons θ l _ empty]
      exact Or.inr (Or.inr (Or.inl ⟨l, _, _, rfl⟩))
  · exact Or.inr (Or.inr (Or.inr described))

end Theorems

#print axioms closure_ground
#print axioms stage_facts
#print axioms semanticRows_closed
#print axioms closure_subset_semanticRows
#print axioms stage_reached
#print axioms value_reached
#print axioms demand_reached
#print axioms semanticRows_subset_closure
#print axioms closure_eq_semanticRows
#print axioms demandRow_mem_closure_iff
#print axioms valueRow_mem_closure_iff
#print axioms stageRow_mem_closure_iff
#print axioms atomRow_mem_closure_iff
#print axioms closure_row_cases

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
