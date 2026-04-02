import Mettapedia.Languages.GF.HandCrafted.English.InterfaceRefinement
import Mettapedia.Languages.GF.WorldModelVisibleBridge

/-!
# GF Infrapolitics-Style Theorem Bundle

This file packages stack-native theorem families suggested by the current
GF/visible-store/WM semantics:

- coarse-vs-fine interface strictness (`13`, with a `10`-style separation
  analogue);
- store-mediated semantic coordination / stigmergy (`12`);
- concrete LF-visible / PF-hidden distinction witnesses.

Conceptual note:
- These are formal theorems in the existing GF/WM stack, not imported social
  theory. The comments only mark the analogies motivating the bundle.
-/

namespace Mettapedia.Languages.GF.HandCrafted.English.Infrapolitics

open Mettapedia.Languages.GF
open Mettapedia.Languages.GF.HandCrafted.Abstract
open Mettapedia.Languages.GF.HandCrafted.English.InterfaceRefinement
open Mettapedia.Languages.GF.HandCrafted.English.InterfaceContrast
open Mettapedia.Languages.GF.HandCrafted.English.Linearization
open Mettapedia.Languages.GF.VisibleLayer
open Mettapedia.Languages.GF.WorldModelSemantics
open Mettapedia.Languages.GF.WorldModelVisibleBridge
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.QuantifiedFormula2
open Mettapedia.Logic.EvidenceQuantale

/-- Store-mediated semantic coordination:
if two agents share the same term and the same bind/ref footprint
(under the standard functional/unique invariants), then they compute the same
meaning for every formula. -/
theorem stigmergic_coordination_via_shared_store
    {cfg : VisibleCfg} {π : WorldModelSemantics.TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2)
    (s₁ s₂ : GrammarState)
    (hterm : s₁.term = s₂.term)
    (hfb₁ : functionalBind s₁.store) (hur₁ : uniqueRef s₁.store)
    (hfb₂ : functionalBind s₂.store) (hur₂ : uniqueRef s₂.store)
    (hbind : ∀ pr r, StoreAtom.bind pr r ∈ s₁.store ↔ StoreAtom.bind pr r ∈ s₂.store)
    (href : ∀ r pos, StoreAtom.ref r pos ∈ s₁.store ↔ StoreAtom.ref r pos ∈ s₂.store) :
    ∀ φ : QFormula2, gsemE2Full cfg π I Dom φ s₁ = gsemE2Full cfg π I Dom φ s₂ := by
  intro φ
  exact
    gsemE2Full_invariant_equiv
      (cfg := cfg) (π := π) I Dom φ
      s₁ s₂ hterm hfb₁ hur₁ hfb₂ hur₂ hbind href

/-- Independent public-store updates commute semantically. -/
theorem stigmergic_commutation_of_independent_updates
    {cfg : VisibleCfg} {π : TemporalPolicy}
    (I : QEvidenceAtomSem) (Dom : Domain2) (φ : QFormula2)
    (s : GrammarState) (a1 a2 : StoreAtom) :
    let s12a := ⟨s.term, s.store + {a1} + {a2}⟩
    let s12b := ⟨s.term, s.store + {a2} + {a1}⟩
    gsemE2Full cfg π I Dom φ s12a = gsemE2Full cfg π I Dom φ s12b :=
  gsemE2Full_commute_independent (cfg := cfg) (π := π) I Dom φ s a1 a2

/-- Fine LF+PF consequence always refines coarse LF-only consequence. -/
theorem lfpf_consequence_refines_lf_globally :
    ∀ t1 t2 : AbstractNode, LFPFConsequence t1 t2 → LFOnlyConsequence t1 t2 := by
  intro t1 t2 h
  exact lfpf_consequence_refines_lf h

/-- The converse fails globally: LF-only consequence is genuinely coarser
than LF+PF consequence. -/
theorem lf_only_does_not_force_lfpf_globally :
    ¬ (∀ t1 t2 : AbstractNode, LFOnlyConsequence t1 t2 → LFPFConsequence t1 t2) := by
  intro hBack
  have hlf :
      LFOnlyConsequence activeClause passiveClause := by
    simpa [LFOnlyConsequence] using active_reduces_to_passive
  have hpfneq :
      linearizeTree {} activeClause .Nom .Sg ≠
        linearizeTree {} passiveClause .Nom .Sg :=
    active_pf_string_ne_passive_pf_string
  have hnot :
      ¬ LFPFConsequence activeClause passiveClause :=
    lf_only_with_pf_distinct_not_lfpf
      (t1 := activeClause) (t2 := passiveClause) hlf hpfneq
  exact hnot (hBack activeClause passiveClause hlf)

/-- Concrete coarse/fine separation witness:
the coarse LF interface recognizes the active/passive relation, while the fine
LF+PF interface refuses to collapse it. -/
theorem coarse_lf_sees_relation_fine_lfpf_preserves_distinction :
    ∃ t1 t2 : AbstractNode,
      LFOnlyConsequence t1 t2 ∧ ¬ LFPFConsequence t1 t2 := by
  exact
    ⟨activeClause, passiveClause,
      (by simpa [LFOnlyConsequence] using active_reduces_to_passive),
      (lf_only_with_pf_distinct_not_lfpf
        (t1 := activeClause) (t2 := passiveClause)
        (by simpa [LFOnlyConsequence] using active_reduces_to_passive)
        active_pf_string_ne_passive_pf_string)⟩

/-- Concrete separation witness restated directly at the PF-string level. -/
theorem coarse_relation_with_fine_surface_separation :
    ∃ t1 t2 : AbstractNode,
      LFOnlyConsequence t1 t2 ∧
      linearizeTree {} t1 .Nom .Sg ≠ linearizeTree {} t2 .Nom .Sg := by
  exact
    ⟨activeClause, passiveClause,
      (by simpa [LFOnlyConsequence] using active_reduces_to_passive),
      active_pf_string_ne_passive_pf_string⟩

end Mettapedia.Languages.GF.HandCrafted.English.Infrapolitics
