import Mettapedia.Logic.LP.Semantics
import Mettapedia.Logic.LP.FunctionFree
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic

/-!
# Function-Free LP Evaluation: Soundness and Finiteness

Port of `Mettapedia.Logic.Datalog.Evaluation` onto LP types.

- `HerbrandBase` — finite set of all ground atoms (function-free + `Fintype`)
- `mem_HerbrandBase` — every ground atom lies in the Herbrand base
- `leastHerbrandModel_finite` — the least model is a finite set
- `leastHerbrandModel_eq_iter_sup` — the least model = ⋃ n, T_P_LP_iter kb n

The iteration completeness theorems (Section 2) work for ALL LP signatures,
not just function-free ones.

## References

- Lloyd, *Foundations of Logic Programming*, Ch. 2
- van Emden & Kowalski, 1976
-/

namespace Mettapedia.Logic.LP

variable {σ : LPSignature}

/-! ## Section 1: Herbrand Base (function-free) -/

/-- The Herbrand base: all ground atoms constructible from finite constant and
    relation symbol types.  Requires function-free for `Fintype (GroundTerm σ)`. -/
noncomputable def HerbrandBase [IsEmpty σ.functionSymbols]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols] :
    Finset (GroundAtom σ) :=
  Fintype.elems.biUnion (fun (r : σ.relationSymbols) =>
    (Fintype.piFinset (fun (_ : Fin (σ.relationArity r)) =>
        (Fintype.elems : Finset (GroundTerm σ)))).image
      (fun f => ⟨r, f⟩))

/-- Every ground atom lies in the Herbrand base. -/
theorem mem_HerbrandBase [IsEmpty σ.functionSymbols]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (ga : GroundAtom σ) : ga ∈ (HerbrandBase : Finset (GroundAtom σ)) := by
  unfold HerbrandBase
  rw [Finset.mem_biUnion]
  refine ⟨ga.symbol, Fintype.complete _, ?_⟩
  rw [Finset.mem_image]
  exact ⟨ga.args, Fintype.mem_piFinset.mpr (fun _ => Fintype.complete _), rfl⟩

/-- When constants and relation symbols are `Fintype`, the least Herbrand model is finite. -/
theorem leastHerbrandModel_finite [IsEmpty σ.functionSymbols]
    [Fintype σ.constants] [DecidableEq σ.constants]
    [Fintype σ.relationSymbols] [DecidableEq σ.relationSymbols]
    (kb : KnowledgeBase σ) : (leastHerbrandModel kb).Finite := by
  apply Set.Finite.subset (Finset.finite_toSet HerbrandBase)
  apply leastHerbrandModel_least
  rw [T_P_LP_le_iff]
  exact ⟨fun a _ => Finset.mem_coe.mpr (mem_HerbrandBase a),
         fun _ _ _ _ => Finset.mem_coe.mpr (mem_HerbrandBase _)⟩

/-! ## Section 2: Iteration Completeness (all signatures) -/

/-- Helper: given finitely many witnesses for `∃ n, P b n` over a list `atoms`,
    find a single `n_max` that works uniformly for all. -/
private lemma exists_uniform_bound (kb : KnowledgeBase σ)
    (atoms : List (Atom σ)) (g : Grounding σ)
    (h : ∀ b ∈ atoms, ∃ n, g.groundAtom b ∈ T_P_LP_iter kb n) :
    ∃ n, ∀ b ∈ atoms, g.groundAtom b ∈ T_P_LP_iter kb n := by
  induction atoms with
  | nil => exact ⟨0, fun _ hb => absurd hb List.not_mem_nil⟩
  | cons hd tl ih =>
    obtain ⟨n1, hn1⟩ := h hd List.mem_cons_self
    obtain ⟨n2, hn2⟩ := ih (fun b hb => h b (List.mem_cons.mpr (Or.inr hb)))
    exact ⟨max n1 n2, fun b hb => by
      rcases List.mem_cons.mp hb with rfl | hb
      · exact T_P_LP_iter_mono kb n1 _ (Nat.le_max_left _ _) hn1
      · exact T_P_LP_iter_mono kb n2 _ (Nat.le_max_right _ _) (hn2 b hb)⟩

/-- The least Herbrand model is contained in the union of all T_P iterates. -/
theorem leastHerbrandModel_le_T_P_LP_iter_sup (kb : KnowledgeBase σ) :
    leastHerbrandModel kb ⊆ ⋃ n, T_P_LP_iter kb n := by
  apply leastHerbrandModel_least
  intro a ha
  simp only [T_P_LP, Set.mem_union, Set.mem_setOf_eq] at ha
  rcases ha with ha | ⟨c, g, hc, hhead, hbody⟩
  · exact Set.mem_iUnion.mpr ⟨0, ha⟩
  · have hbody' : ∀ b ∈ c.body, ∃ n, g.groundAtom b ∈ T_P_LP_iter kb n :=
      fun b hb => Set.mem_iUnion.mp (hbody b hb)
    obtain ⟨n_max, hn_max⟩ := exists_uniform_bound kb c.body g hbody'
    rw [← hhead]
    exact Set.mem_iUnion.mpr ⟨n_max + 1,
      Set.mem_union_right _ ⟨c, g, hc, rfl, hn_max⟩⟩

/-- The union of all iterates is contained in the least Herbrand model. -/
theorem T_P_LP_iter_sup_le_leastHerbrandModel (kb : KnowledgeBase σ) :
    ⋃ n, T_P_LP_iter kb n ⊆ leastHerbrandModel kb :=
  Set.iUnion_subset (T_P_LP_iter_le_leastHerbrandModel kb)

/-- The least Herbrand model equals the supremum (union) of all T_P iterates. -/
theorem leastHerbrandModel_eq_iter_sup (kb : KnowledgeBase σ) :
    leastHerbrandModel kb = ⋃ n, T_P_LP_iter kb n :=
  Set.Subset.antisymm
    (leastHerbrandModel_le_T_P_LP_iter_sup kb)
    (T_P_LP_iter_sup_le_leastHerbrandModel kb)

end Mettapedia.Logic.LP
