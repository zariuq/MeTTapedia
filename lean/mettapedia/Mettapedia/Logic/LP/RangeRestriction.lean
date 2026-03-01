import Mettapedia.Logic.LP.Semantics

/-!
# Range Restriction and Unit Program LP Soundness

LP soundness (LHM → derivability) fails for arbitrary programs because a clause may
have LP variables in its head that do not appear in any body atom.  Such variables
can be instantiated to *arbitrary* ground terms, making the LHM contain atoms that
are not witnessed by any specific rule instantiation.

**Range-restricted clause**: every variable in the head appears in at least one body atom.
**Unit clause**: body is empty.

For *unit programs* (all clauses have empty body, no EDB facts) the LHM has a clean
characterization:

  `a ∈ leastHerbrandModel kb  ↔  ∃ c ∈ kb.prog, ∃ g : Grounding, g.groundAtom c.head = a`

This is because `T_P kb I = T_P kb ∅` for all interpretations `I` (the body-emptiness
makes T_P independent of I), so `T_P kb ∅` is already a fixpoint and hence equals the LHM.

## Contents

- `Clause.isUnit` — body is empty
- `KnowledgeBase.isUnit` — all clauses are unit, EDB is empty
- `T_P_LP_const_of_unit` — T_P is independent of interpretation for unit KBs
- `lhm_eq_T_P_empty_of_unit` — LHM = T_P(∅) for unit KBs
- `lhm_unit_mem_iff` — membership characterization (main theorem)
- `lhm_unit_mem_witness` / `lhm_unit_mem_of_clause` — consequence corollaries

Additionally:

- `Clause.isRangeRestricted` — every head variable appears in some body atom
- `KnowledgeBase.isRangeRestricted` — all clauses are range-restricted
- `unit_clause_rangeRestricted_iff_head_ground` — unit + range-restricted ↔ ground head

The general LP soundness theorem for range-restricted KBs (LHM ⊆ SLD-derivable) is
deferred: it requires a full SLD completeness argument in the other direction, which
depends on `SLD.lean` having an induction-compatible proof strategy.

## References

- Lloyd, *Foundations of Logic Programming*, §2.3 (range restriction)
- van Emden & Kowalski, 1976 (T_P fixpoint semantics)
-/

namespace Mettapedia.Logic.LP

/-! ## Unit Clauses and Unit KBs -/

/-- A clause is a *unit clause* if its body is empty. -/
def Clause.isUnit {σ : LPSignature} (c : Clause σ) : Prop :=
  c.body = []

/-- A knowledge base is a *unit KB* if:
    - the EDB is empty (`db = ∅`), and
    - every clause in `prog` is a unit clause. -/
def KnowledgeBase.isUnit {σ : LPSignature} (kb : KnowledgeBase σ) : Prop :=
  kb.db = ∅ ∧ ∀ c ∈ kb.prog, c.isUnit

/-! ## Range Restriction -/

/-- A clause is *range-restricted* if every variable in the head appears in at least
    one body atom.

    For unit clauses (body = []) this holds vacuously only when the head has no
    free variables.  Programs with variables in unit-clause heads are NOT
    range-restricted, which is why `lp_sound` fails for compiled MeTTaIL KBs. -/
def Clause.isRangeRestricted {σ : LPSignature} [DecidableEq σ.vars]
    (c : Clause σ) : Prop :=
  ∀ v : σ.vars, v ∈ c.head.freeVars → ∃ b ∈ c.body, v ∈ b.freeVars

/-- A knowledge base is *range-restricted* if every clause in the program is. -/
def KnowledgeBase.isRangeRestricted {σ : LPSignature} [DecidableEq σ.vars]
    (kb : KnowledgeBase σ) : Prop :=
  ∀ c ∈ kb.prog, c.isRangeRestricted

/-- A unit clause with a non-variable head is NOT range-restricted in general:
    any LP variable in the head is not covered by the empty body.

    Conversely, a unit clause IS range-restricted iff the head has no free variables. -/
theorem unit_clause_rangeRestricted_iff_head_ground {σ : LPSignature} [DecidableEq σ.vars]
    (c : Clause σ) (hu : c.isUnit) :
    c.isRangeRestricted ↔ c.head.freeVars = ∅ := by
  simp only [Clause.isRangeRestricted, Clause.isUnit] at *
  constructor
  · intro h
    ext v
    constructor
    · intro hv
      obtain ⟨b, hb, _⟩ := h v hv
      rw [hu] at hb; exact absurd hb List.not_mem_nil
    · intro hv; cases hv
  · intro h v hv
    simp [h] at hv

/-! ## T_P is constant for unit KBs -/

/-- For a unit KB, `T_P_LP kb` is independent of the interpretation:
    `T_P_LP kb I = T_P_LP kb J` for any interpretations `I` and `J`.

    Proof: T_P includes EDB (= ∅) plus grounded clause heads with satisfied bodies.
    Since all bodies are empty, the body condition is vacuously satisfied regardless
    of I, so the IDB part does not depend on I. -/
theorem T_P_LP_const_of_unit {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) (I J : Interpretation σ) :
    T_P_LP kb I = T_P_LP kb J := by
  obtain ⟨hdb, hprog⟩ := hunit
  ext a
  simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq]
  constructor <;> {
    rintro (ha | ⟨c, g, hc, hhead, hbody⟩)
    · simp_all
    · right
      refine ⟨c, g, hc, hhead, ?_⟩
      intro b hb
      have hunit_c := hprog c hc
      simp only [Clause.isUnit] at hunit_c
      simp [hunit_c] at hb
  }

/-- For a unit KB, `T_P_LP kb (T_P_LP kb ∅) ⊆ T_P_LP kb ∅`. -/
theorem T_P_unit_empty_prefixpoint {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) :
    T_P_LP kb (T_P_LP kb ∅) ⊆ T_P_LP kb ∅ :=
  (T_P_LP_const_of_unit kb hunit (T_P_LP kb ∅) ∅).le

/-- For a unit KB, `T_P_LP kb ∅ ⊆ leastHerbrandModel kb`. -/
theorem T_P_unit_empty_le_lhm {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) :
    T_P_LP kb ∅ ⊆ leastHerbrandModel kb := by
  obtain ⟨hdb, hprog⟩ := hunit
  intro a ha
  simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq] at ha
  rcases ha with ha | ⟨c, g, hc, hhead, _⟩
  · simp [hdb] at ha
  · exact hhead ▸ leastHerbrandModel_clause kb c hc g (fun b hb => by
      have hunit_c := hprog c hc
      simp only [Clause.isUnit] at hunit_c
      rw [hunit_c] at hb; cases hb)

/-- For a unit KB, `leastHerbrandModel kb ⊆ T_P_LP kb ∅`. -/
theorem lhm_le_T_P_unit_empty {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) :
    leastHerbrandModel kb ⊆ T_P_LP kb ∅ :=
  leastHerbrandModel_least kb (T_P_LP kb ∅) (T_P_unit_empty_prefixpoint kb hunit)

/-- For a unit KB, the least Herbrand model equals `T_P_LP kb ∅`. -/
theorem lhm_eq_T_P_empty_of_unit {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) :
    leastHerbrandModel kb = T_P_LP kb ∅ :=
  Set.Subset.antisymm (lhm_le_T_P_unit_empty kb hunit) (T_P_unit_empty_le_lhm kb hunit)

/-! ## Membership Characterization for Unit KBs -/

/-- **Main characterization**: for a unit KB, `a ∈ leastHerbrandModel kb` if and only if
    there exists a clause `c ∈ kb.prog` and a grounding `g` such that
    `g.groundAtom c.head = a`.

    This is the fundamental soundness theorem for unit programs: every element of
    the LHM is directly witnessed by a single clause instantiation.

    Note: for non-unit programs (with function-free body atoms), the LHM may contain
    atoms not directly witnessed by a single clause head (they may require chaining
    through body atoms), which is why this characterization only holds for unit KBs. -/
theorem lhm_unit_mem_iff {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) (a : GroundAtom σ) :
    a ∈ leastHerbrandModel kb ↔
    ∃ c ∈ kb.prog, ∃ g : Grounding σ, g.groundAtom c.head = a := by
  obtain ⟨hdb, hprog⟩ := hunit
  constructor
  · intro h
    rw [lhm_eq_T_P_empty_of_unit kb ⟨hdb, hprog⟩] at h
    simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq] at h
    rcases h with h | ⟨c, g, hc, hhead, _⟩
    · simp [hdb] at h
    · exact ⟨c, hc, g, hhead⟩
  · rintro ⟨c, hc, g, rfl⟩
    exact leastHerbrandModel_clause kb c hc g (fun b hb => by
      have hunit_c := hprog c hc
      simp only [Clause.isUnit] at hunit_c
      simp [hunit_c] at hb)

/-- Corollary: membership in the LHM has the form `g.groundAtom c.head` for unit KBs. -/
theorem lhm_unit_mem_witness {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) (a : GroundAtom σ)
    (h : a ∈ leastHerbrandModel kb) :
    ∃ c ∈ kb.prog, ∃ g : Grounding σ, g.groundAtom c.head = a :=
  (lhm_unit_mem_iff kb hunit a).mp h

/-- Converse: a grounded clause head is in the LHM for a unit KB. -/
theorem lhm_unit_mem_of_clause {σ : LPSignature} (kb : KnowledgeBase σ)
    (hunit : kb.isUnit) (c : Clause σ) (hc : c ∈ kb.prog) (g : Grounding σ) :
    g.groundAtom c.head ∈ leastHerbrandModel kb :=
  (lhm_unit_mem_iff kb hunit _).mpr ⟨c, hc, g, rfl⟩

end Mettapedia.Logic.LP
