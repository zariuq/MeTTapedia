import Mettapedia.Logic.Datalog.Semantics
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.List.FinRange

/-!
# Datalog Evaluation: Soundness and Finiteness

This file provides the evaluation layer on top of the semantics:

- `HerbrandBase` — the finite set of all constructible ground atoms (when types are `Fintype`).
- `mem_HerbrandBase` — every ground atom lies in the Herbrand base.
- `leastModel_finite` — `leastModel kb` is a finite set when types are `Fintype`.
- `leastModel_le_T_P_iter_sup` — the least model equals the sup of all iterates.
- `leastModel_eq_iter_sup` — characterization via iteration.

## API notes (Lean 4.27)

- `List.not_mem_nil` and `List.mem_cons_self` have ALL arguments implicit; use without
  explicit application (the Prop IS the statement, not a function).
- `List.map_get_finRange` is the non-deprecated name for the finRange-get round-trip lemma.
-/

namespace Mettapedia.Logic.Datalog

/-! ## Section 1: Herbrand Base -/

/-- The Herbrand base: all ground atoms constructible from `τ.constants` and
    `τ.relationSymbols`.  Well-defined when both are `Fintype` with `DecidableEq`. -/
noncomputable def HerbrandBase {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols] :
    Finset (GroundAtom τ) :=
  Fintype.elems.biUnion (fun (r : τ.relationSymbols) =>
    (Fintype.piFinset (fun (_ : Fin (τ.relationArity r)) =>
        (Fintype.elems : Finset τ.constants))).image
      (fun f => { symbol     := r
                  atom_terms := (List.finRange (τ.relationArity r)).map f
                  term_length := by simp }))

/-- Helper: `List.map (fun i : Fin n => l.get (h ▸ i)) (List.finRange n) = l`
    for any proof `h : l.length = n`. -/
private lemma map_get_cast {α : Type*} (l : List α) (n : ℕ) (h : l.length = n) :
    List.map (fun (i : Fin n) => l.get (h ▸ i)) (List.finRange n) = l := by
  have : List.map (fun (i : Fin n) => l.get (h ▸ i)) (List.finRange n) =
         List.map l.get (List.finRange l.length) := by subst h; rfl
  rw [this]
  exact List.map_get_finRange l

/-- Every ground atom lies in the Herbrand base. -/
theorem mem_HerbrandBase {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (ga : GroundAtom τ) : ga ∈ (HerbrandBase : Finset (GroundAtom τ)) := by
  simp only [HerbrandBase, Finset.mem_biUnion, Finset.mem_image,
             Fintype.mem_piFinset, Fintype.complete]
  -- After simp, all membership conditions reduce to True.
  refine ⟨ga.symbol, trivial, ?_⟩
  refine ⟨fun i => ga.atom_terms.get (ga.term_length ▸ i), fun _ => trivial, ?_⟩
  -- Prove equality of GroundAtoms by extensionality
  apply GroundAtom.ext <;> [rfl; exact map_get_cast ga.atom_terms _ ga.term_length]

/-! ## Section 2: Finiteness of the Least Model -/

/-- When constants and relation symbols are `Fintype`, `leastModel kb` is finite.

    Proof: the Herbrand base is a pre-fixpoint (every T_P step stays in it), so by
    `leastModel_least`, `leastModel ⊆ HerbrandBase`, which is a finite set. -/
theorem leastModel_finite {τ : Signature}
    [Fintype τ.constants] [DecidableEq τ.constants]
    [Fintype τ.relationSymbols] [DecidableEq τ.relationSymbols]
    (kb : KnowledgeBase τ) : (leastModel kb).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet HerbrandBase)
  apply leastModel_least
  rw [T_P_le_iff]
  exact ⟨fun a _ => Finset.mem_coe.mpr (mem_HerbrandBase a),
         fun _ _ _ _ => Finset.mem_coe.mpr (mem_HerbrandBase _)⟩

/-! ## Section 3: Iteration Completeness -/

/-- Helper: given finitely many witnesses for `∃ n, P b n` over a list `atoms`,
    find a single `n_max` that works uniformly for all. -/
private lemma exists_uniform_bound {τ : Signature} (kb : KnowledgeBase τ)
    (atoms : List (Atom τ)) (g : Grounding τ)
    (h : ∀ b ∈ atoms, ∃ n, g.applyAtom b ∈ T_P_iter kb n) :
    ∃ n, ∀ b ∈ atoms, g.applyAtom b ∈ T_P_iter kb n := by
  induction atoms with
  | nil => exact ⟨0, fun b hb => absurd hb List.not_mem_nil⟩
  | cons hd tl ih =>
    obtain ⟨n1, hn1⟩ := h hd List.mem_cons_self
    obtain ⟨n2, hn2⟩ := ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))
    exact ⟨max n1 n2, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact T_P_iter_mono kb n1 _ (Nat.le_max_left _ _) hn1
      · exact T_P_iter_mono kb n2 _ (Nat.le_max_right _ _) (hn2 b hb)⟩

/-- leastModel is contained in the union of all T_P iterates.

    Proof: the union ⋃ n, T_P_iter kb n is itself a pre-fixpoint: applying T_P to
    an element in the union gives an element in the next step. -/
theorem leastModel_le_T_P_iter_sup {τ : Signature} (kb : KnowledgeBase τ) :
    leastModel kb ⊆ ⋃ n, T_P_iter kb n := by
  apply leastModel_least
  intro a ha
  simp only [T_P, Set.mem_union, Finset.mem_coe, Set.mem_setOf_eq] at ha
  rcases ha with ha | ⟨r, g, hr, hhead, hbody⟩
  · -- EDB fact: in step 0
    exact Set.mem_iUnion.mpr ⟨0, by simp [T_P_iter, Finset.mem_coe.mpr ha]⟩
  · -- Derived: body atoms are in the union; by finiteness of the list, all fit in one step
    have hbody' : ∀ b ∈ r.body, ∃ n, g.applyAtom b ∈ T_P_iter kb n :=
      fun b hb => Set.mem_iUnion.mp (hbody b hb)
    obtain ⟨n_max, hn_max⟩ := exists_uniform_bound kb r.body g hbody'
    rw [← hhead]
    exact Set.mem_iUnion.mpr ⟨n_max + 1,
      Set.mem_union_right _ ⟨r, g, hr, rfl, hn_max⟩⟩

/-- The union of all iterates is contained in leastModel (soundness). -/
theorem T_P_iter_sup_le_leastModel {τ : Signature} (kb : KnowledgeBase τ) :
    ⋃ n, T_P_iter kb n ⊆ leastModel kb :=
  Set.iUnion_subset (T_P_iter_le_leastModel kb)

/-- The least model equals the supremum (union) of all T_P iterates. -/
theorem leastModel_eq_iter_sup {τ : Signature} (kb : KnowledgeBase τ) :
    leastModel kb = ⋃ n, T_P_iter kb n :=
  Set.Subset.antisymm
    (leastModel_le_T_P_iter_sup kb)
    (T_P_iter_sup_le_leastModel kb)

end Mettapedia.Logic.Datalog
