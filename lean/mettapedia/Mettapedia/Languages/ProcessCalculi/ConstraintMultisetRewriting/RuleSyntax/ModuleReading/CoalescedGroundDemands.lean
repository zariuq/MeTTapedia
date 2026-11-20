import Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading.Correctness

/-!
# Coalescing ground demands without forgetting the call

A general demand can be implemented here by supplying a finite cover
of its ground instances as seeds of one positive module reading. One
run can share derived values across calls. Its completed rows are
exactly the union of the rows of the per-seed runs.

The nontrivial direction is closure of the union: a stage started by
one seed can use a value found by another seed, but that value is a
valid premise of the same concrete call. The selected call's tag is
therefore retained. This is a fixed-relation, ground-cover profile;
it does not assert correctness of symbolic open-call tabling.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading

open Mettapedia.Logic.LP (LPSignature Term Atom)
open SetStoreSyntax (GroundMatch consequence)
open Mettapedia.GSLT.OpenEnded.ChaoticIteration (isLeast_target)

universe u

variable {σ : LPSignature.{u, u, u, u}} {L : Type u}
  [DecidableEq σ.vars] [DecidableEq σ.constants] [DecidableEq σ.functionSymbols]
  [DecidableEq σ.relationSymbols] [DecidableEq L]

variable {M : L → ModuleRule (readingSignature σ L)}
  {Rel : Finset (Atom (readingSignature σ L))}

variable (M Rel)

def coalescedSeed (roots : Finset (Term (readingSignature σ L))) : Finset (Term (readingSignature σ L)) :=
  roots.biUnion (fun root => seed root Rel)

def coalescedRows (roots : Finset (Term (readingSignature σ L))) : Set (Term (readingSignature σ L)) :=
  SetStoreClosure.closure (consequence (P := reading M)) (coalescedSeed Rel roots)

/-- The auxiliary semantics retains each row's source demand, not an
unlabelled value pooled from unrelated calls. -/
def unionSemantics (roots : Finset (Term (readingSignature σ L))) : Set (Term (readingSignature σ L)) :=
  {row | ∃ root ∈ roots, row ∈ semanticRows M Rel root}

variable {M Rel}

private theorem unionSemantics_closed (roots : Finset (Term (readingSignature σ L)))
    (rr : ∀ l, RangeRestricted (M l)) (m : GroundMatch (reading M)) :
    SetStoreClosure.action (consequence m) (unionSemantics M Rel roots) ⊆
      unionSemantics M Rel roots := by
  rintro v ⟨readsIn, made⟩
  have reads : ∀ r ∈ m.rule.body.read, m.assignment.applyTerm r ∈ unionSemantics M Rel roots :=
    fun r member => readsIn (List.mem_toFinset.mpr (List.mem_map.mpr ⟨r, member, rfl⟩))
  obtain ⟨x, makes, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp made)
  obtain ⟨l, ⟨pre, source, target, post, split, isRule⟩ | ⟨pre, p, post, split, isRule⟩ | isRule⟩ :=
    mem_reading_iff.mp m.member
  · rw [isRule] at reads makes
    obtain rfl := List.mem_singleton.mp makes
    obtain ⟨root, active, stage⟩ := reads _ List.mem_cons_self
    obtain ⟨asked, holds⟩ := stage_facts rr split m.assignment stage
    rw [apply_demandRow]
    exact ⟨root, active, demandRow_mem_semanticRows.mpr (.call asked split holds)⟩
  · rw [isRule] at reads makes
    obtain rfl := List.mem_singleton.mp makes
    obtain ⟨root, active, stage⟩ := reads _ List.mem_cons_self
    obtain ⟨asked, holds⟩ := stage_facts rr split m.assignment stage
    obtain ⟨_, _, fromSomeRoot⟩ := reads _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have here := holds_of_row fromSomeRoot
    refine ⟨root, active, Or.inr (Or.inr (Or.inl
      ⟨l, m.assignment, pre ++ [p], post, by simp [split], ?_, asked, ?_⟩))⟩
    · simp [targets]
    · intro q member
      rcases List.mem_append.mp member with earlier | now
      · exact holds q earlier
      · obtain rfl := List.mem_singleton.mp now
        exact here
  · rw [isRule] at reads makes
    obtain rfl := List.mem_singleton.mp makes
    obtain ⟨root, active, stage⟩ := reads _ List.mem_cons_self
    obtain ⟨asked, holds⟩ := stage_facts rr (post := []) (List.append_nil _).symm m.assignment stage
    rw [apply_valueRow]
    exact ⟨root, active, valueRow_mem_semanticRows.mpr
      ⟨asked, derives_iff.mpr ⟨l, m.assignment, rfl, rfl, holds⟩⟩⟩

theorem coalescedRows_eq_union (roots : Finset (Term (readingSignature σ L)))
    (rr : ∀ l, RangeRestricted (M l)) (rootsGround : ∀ root ∈ roots, root.isGround)
    (relGround : ∀ atom ∈ Rel, atom.isGround) :
    coalescedRows M Rel roots = unionSemantics M Rel roots := by
  have least := (isLeast_target (fun m : GroundMatch (reading M) => SetStoreClosure.action (consequence m))
    (coalescedSeed Rel roots : Set (Term (readingSignature σ L)))).2
  refine Set.Subset.antisymm (least ⟨?_, fun m => unionSemantics_closed roots rr m⟩) ?_
  · intro row inside
    obtain ⟨root, active, fromSeed⟩ := Finset.mem_biUnion.mp inside
    exact ⟨root, active, seed_subset_semanticRows fromSeed⟩
  · rintro row ⟨root, active, semantic⟩
    rw [← closure_eq_semanticRows rr (rootsGround root active) relGround] at semantic
    have fromRoot := (isLeast_target (fun m : GroundMatch (reading M) => SetStoreClosure.action (consequence m))
      (seed root Rel : Set (Term (readingSignature σ L)))).2
    apply fromRoot ⟨?_, SetStoreClosure.closure_closed _ _⟩ semantic
    intro kept member
    exact SetStoreClosure.seed_subset_closure _ _
      (Finset.mem_biUnion.mpr ⟨root, active, member⟩)

/-- Tag-filtered retrieval from a covered general demand preserves
exactly the answers of the individual variant run. No two seeds have
to derive their answers in the same order. -/
theorem coalesced_value_iff_variant (roots : Finset (Term (readingSignature σ L)))
    (rr : ∀ l, RangeRestricted (M l)) (rootsGround : ∀ root ∈ roots, root.isGround)
    (relGround : ∀ atom ∈ Rel, atom.isGround)
    {client : Term (readingSignature σ L)} (covers : client ∈ roots)
    (value : Term (readingSignature σ L)) :
    valueRow client value ∈ coalescedRows M Rel roots ↔
      valueRow client value ∈ SetStoreClosure.closure
        (consequence (P := reading M)) (seed client Rel) := by
  rw [coalescedRows_eq_union roots rr rootsGround relGround,
    valueRow_mem_closure_iff rr (rootsGround client covers) relGround]
  constructor
  · rintro ⟨_, _, semantic⟩
    exact ⟨.seed, (valueRow_mem_semanticRows.mp semantic).2⟩
  · rintro ⟨_, derives⟩
    exact ⟨client, covers, valueRow_mem_semanticRows.mpr ⟨.seed, derives⟩⟩

/-- A value from another covered call is not a valid answer just because
it occurs in the pooled result. This control does not depend on which
language-specific condition distinguishes the two ground calls. -/
theorem forgetting_call_can_add_answer (roots : Finset (Term (readingSignature σ L)))
    (rr : ∀ l, RangeRestricted (M l)) (rootsGround : ∀ root ∈ roots, root.isGround)
    (relGround : ∀ atom ∈ Rel, atom.isGround)
    {client other value : Term (readingSignature σ L)} (covers : client ∈ roots) (hasOther : other ∈ roots)
    (produces : Derives M ↑Rel other value) (refuses : ¬ Derives M ↑Rel client value) :
    (∃ tag, valueRow tag value ∈ coalescedRows M Rel roots) ∧
      valueRow client value ∉ coalescedRows M Rel roots := by
  constructor
  · rw [coalescedRows_eq_union roots rr rootsGround relGround]
    exact ⟨other, other, hasOther, valueRow_mem_semanticRows.mpr ⟨.seed, produces⟩⟩
  · intro batched
    have individual := (coalesced_value_iff_variant roots rr rootsGround relGround covers value).mp batched
    exact refuses ((valueRow_mem_closure_iff rr (rootsGround client covers) relGround _ _).mp individual).2

#print axioms coalescedRows_eq_union
#print axioms coalesced_value_iff_variant
#print axioms forgetting_call_can_add_answer

end Mettapedia.Languages.ProcessCalculi.ConstraintMultisetRewriting.RuleSyntax.ModuleReading
