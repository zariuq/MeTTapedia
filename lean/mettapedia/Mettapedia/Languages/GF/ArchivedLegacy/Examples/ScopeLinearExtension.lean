import Mettapedia.Languages.GF.Examples.ScopeAmbiguity
import Mettapedia.Languages.GF.VisibleLayer
import Mettapedia.Languages.GF.VisibleLayerGFInstance

/-!
# Scope Ambiguity Completeness via Linear Extensions

Two-quantifier completeness theorem for the EMLA witness:

- reachable V2 scope orders from `emla_state2` are exactly the linear
  extensions of the (dependency-free) two-handle partial order;
- concretely, exactly `["q1", "q2"]` and `["q2", "q1"]`.
-/

namespace Mettapedia.Languages.GF.Examples.ScopeLinearExtension

open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.VisibleLayerGFInstance
open Mettapedia.Languages.GF.Examples.ScopeAmbiguity
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- A finite dependency edge between quantifier handles: `fst` must precede `snd`. -/
abbrev ScopeDepEdge := String × String

/-- Finite scope-dependency DAG data (node list + edge list). -/
structure ScopeDependencyDAG where
  handles : List String
  deps : List ScopeDepEdge
  handles_nodup : handles.Nodup

/-- An edge is respected by an order when the source appears strictly before target. -/
def edgeRespected (ord : List String) (e : ScopeDepEdge) : Prop :=
  ord.idxOf e.1 < ord.idxOf e.2

/-- `ord` is a linear extension of a finite dependency DAG:
same handle multiset (`Perm`) and all edges respected. -/
def dagLinearExtension (dag : ScopeDependencyDAG) (ord : List String) : Prop :=
  ord.Perm dag.handles ∧
  ∀ e ∈ dag.deps, edgeRespected ord e

/-- Generic soundness+completeness wrapper for any finite DAG reachability relation. -/
theorem dag_reachability_complete
    {dag : ScopeDependencyDAG} {Reach : List String → Prop}
    (hSound : ∀ ord, Reach ord → dagLinearExtension dag ord)
    (hComplete : ∀ ord, dagLinearExtension dag ord → Reach ord)
    (ord : List String) :
    Reach ord ↔ dagLinearExtension dag ord := by
  constructor
  · exact hSound ord
  · exact hComplete ord

/-- Quantifier handles present in `emla_state2` are exactly `q1` or `q2`. -/
theorem emla_state2_quant_handle_iff
    (q : String) :
    (∃ d r, StoreAtom.quant q d r ∈ emla_state2.store) ↔
      q = "q1" ∨ q = "q2" := by
  constructor
  · intro hq
    rcases hq with ⟨d, r, hmem⟩
    have hcases :
        StoreAtom.quant q d r = StoreAtom.quant "q1" emla_det1 emla_restr1
        ∨ StoreAtom.quant q d r = StoreAtom.quant "q2" emla_det2 emla_restr2 := by
      have hmem' :
          StoreAtom.quant q d r ∈ ({StoreAtom.quant "q1" emla_det1 emla_restr1} : Multiset StoreAtom)
          ∨ StoreAtom.quant q d r ∈ ({StoreAtom.quant "q2" emla_det2 emla_restr2} : Multiset StoreAtom) := by
        simpa [emla_state2] using (Multiset.mem_add.mp hmem)
      rcases hmem' with h1 | h2
      · exact Or.inl (Multiset.mem_singleton.mp h1)
      · exact Or.inr (Multiset.mem_singleton.mp h2)
    rcases hcases with h1 | h2
    · injection h1 with hqeq _ _
      exact Or.inl hqeq
    · injection h2 with hqeq _ _
      exact Or.inr hqeq
  · intro hq
    rcases hq with rfl | rfl
    · exact ⟨emla_det1, emla_restr1, by
        change StoreAtom.quant "q1" emla_det1 emla_restr1 ∈
          ({StoreAtom.quant "q1" emla_det1 emla_restr1} +
            {StoreAtom.quant "q2" emla_det2 emla_restr2} : Multiset StoreAtom)
        exact Multiset.mem_add.mpr
          (Or.inl (Multiset.mem_singleton_self (StoreAtom.quant "q1" emla_det1 emla_restr1)))⟩
    · exact ⟨emla_det2, emla_restr2, by
        change StoreAtom.quant "q2" emla_det2 emla_restr2 ∈
          ({StoreAtom.quant "q1" emla_det1 emla_restr1} +
            {StoreAtom.quant "q2" emla_det2 emla_restr2} : Multiset StoreAtom)
        exact Multiset.mem_add.mpr
          (Or.inr (Multiset.mem_singleton_self (StoreAtom.quant "q2" emla_det2 emla_restr2)))⟩

/-- Linear extensions for the EMLA two-quantifier partial order. -/
def emlaLinearExtension (ord : List String) : Prop :=
  ord = ["q1", "q2"] ∨ ord = ["q2", "q1"]

/-- Reachable scope order from `emla_state2` via one V2 scope-choice step. -/
def emlaReachableScopeOrder (ord : List String) : Prop :=
  (ord = ["q1", "q2"] ∧
    VisibleStep gfVisibleCfg emla_state2
      ⟨emla_state2.term, emla_state2.store + {StoreAtom.scope "q1" "q2"}⟩) ∨
  (ord = ["q2", "q1"] ∧
    VisibleStep gfVisibleCfg emla_state2
      ⟨emla_state2.term, emla_state2.store + {StoreAtom.scope "q2" "q1"}⟩)

/-- Any reachable EMLA V2 order is a linear extension. -/
theorem emla_reachable_implies_linearExtension
    {ord : List String} :
    emlaReachableScopeOrder ord → emlaLinearExtension ord := by
  intro hreach
  rcases hreach with ⟨h12, _⟩ | ⟨h21, _⟩
  · exact Or.inl h12
  · exact Or.inr h21

/-- Every linear extension is reachable from `emla_state2` by V2 choice. -/
theorem emla_linearExtension_implies_reachable
    {ord : List String} :
    emlaLinearExtension ord → emlaReachableScopeOrder ord := by
  intro hlin
  rcases emla_scope_nondet with ⟨hsurf, hinv⟩
  rcases hlin with h12 | h21
  · exact Or.inl ⟨h12, hsurf⟩
  · exact Or.inr ⟨h21, hinv⟩

/-- Scope ambiguity completeness (two-quantifier EMLA fragment):
reachable scope orders are exactly the linear extensions. -/
theorem emla_scope_completeness_linearExtensions
    (ord : List String) :
    emlaReachableScopeOrder ord ↔ emlaLinearExtension ord := by
  constructor
  · exact emla_reachable_implies_linearExtension
  · exact emla_linearExtension_implies_reachable

/-! ## Finite-DAG Generalization and EMLA Instantiation -/

/-- EMLA dependency DAG instance: two handles and no dependency edges. -/
def emlaDAG : ScopeDependencyDAG where
  handles := ["q1", "q2"]
  deps := []
  handles_nodup := by simp

private theorem perm_q1q2_eq_or_swap
    {ord : List String} (hperm : ord.Perm ["q1", "q2"]) :
    ord = ["q1", "q2"] ∨ ord = ["q2", "q1"] := by
  have hlen : ord.length = 2 := by simpa using hperm.length_eq
  cases ord with
  | nil =>
      simp at hlen
  | cons x xs =>
      cases xs with
      | nil =>
          simp at hlen
      | cons y ys =>
          cases ys with
          | nil =>
              have hx : x = "q1" ∨ x = "q2" := by
                have : x ∈ ["q1", "q2"] := hperm.subset (by simp)
                simpa using this
              have hy : y = "q1" ∨ y = "q2" := by
                have : y ∈ ["q1", "q2"] := hperm.subset (by simp)
                simpa using this
              have hnodup : List.Nodup [x, y] := by
                exact (hperm.nodup_iff).2 (by simp)
              rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
              · exfalso
                simp at hnodup
              · exact Or.inl rfl
              · exact Or.inr rfl
              · exfalso
                simp at hnodup
          | cons z zs =>
              simp at hlen

/-- EMLA two-handle linear-extension predicate is exactly the finite-DAG one
for `emlaDAG`. -/
theorem emlaLinearExtension_iff_dagLinearExtension
    (ord : List String) :
    emlaLinearExtension ord ↔ dagLinearExtension emlaDAG ord := by
  constructor
  · intro h
    rcases h with h12 | h21
    · subst h12
      refine ⟨List.Perm.refl _, ?_⟩
      · intro e he
        simp [emlaDAG] at he
    · subst h21
      refine ⟨?_, ?_⟩
      · simpa using (List.Perm.swap "q1" "q2" [])
      · intro e he
        simp [emlaDAG] at he
  · intro h
    exact perm_q1q2_eq_or_swap h.1

/-- EMLA completeness stated against the generic finite-DAG linear-extension notion. -/
theorem emla_scope_completeness_dag
    (ord : List String) :
    emlaReachableScopeOrder ord ↔ dagLinearExtension emlaDAG ord := by
  constructor
  · intro h
    exact (emlaLinearExtension_iff_dagLinearExtension ord).mp
      ((emla_scope_completeness_linearExtensions ord).mp h)
  · intro h
    exact (emla_scope_completeness_linearExtensions ord).mpr
      ((emlaLinearExtension_iff_dagLinearExtension ord).mpr h)

end Mettapedia.Languages.GF.Examples.ScopeLinearExtension
