import Foundation.Modal.Kripke.Basic
import Foundation.Modal.Neighborhood.Basic
import Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodEmbedding
import Mettapedia.Logic.PLNWorldModelKripkeCompleteness
import Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness

/-!
# Canonical Kripke-to-Neighborhood WM Representation

This module builds a canonical frame/model translation from Kripke semantics to
neighborhood semantics, proves satisfaction preservation, and exports
Kripke-to-neighborhood WM consequence corollaries without requiring an explicit
user-supplied embedding argument.
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodCanonical

open LO
open LO.Modal
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelKripke
open Mettapedia.Logic.PLNWorldModelNeighborhood
open Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodEmbedding

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelKripke.ModalQuery
abbrev PointedKripke := Mettapedia.Logic.PLNWorldModelKripke.PointedKripke
abbrev PointedNeighborhood := Mettapedia.Logic.PLNWorldModelNeighborhood.PointedNeighborhood

/-- Canonical Kripke-to-neighborhood frame translation:
`w` supports `X` iff every Kripke successor of `w` is in `X`. -/
def kripkeFrameToNeighborhood (F : Kripke.Frame) : Neighborhood.Frame where
  World := F.World
  world_nonempty := F.world_nonempty
  𝒩 w := {X : Set F.World | {v : F.World | F.Rel w v} ⊆ X}

/-- Canonical Kripke-to-neighborhood model translation with induced valuation. -/
def kripkeModelToNeighborhood (M : Kripke.Model) : Neighborhood.Model where
  toFrame := kripkeFrameToNeighborhood M.toFrame
  Val a := {w : M.World | M w a}

@[simp] theorem kripkeModelToNeighborhood_toFrame (M : Kripke.Model) :
    (kripkeModelToNeighborhood M).toFrame = kripkeFrameToNeighborhood M.toFrame := rfl

@[simp] theorem kripkeModelToNeighborhood_val (M : Kripke.Model) (a : ℕ) :
    (kripkeModelToNeighborhood M).Val a = {w : M.World | M w a} := rfl

/-- Satisfaction preservation under the canonical Kripke-to-neighborhood translation. -/
theorem satisfies_iff_kripke_toNeighborhood (M : Kripke.Model) :
    ∀ (x : M.World) (φ : ModalQuery),
      Formula.Neighborhood.Satisfies (kripkeModelToNeighborhood M) x φ ↔
      Formula.Kripke.Satisfies M x φ := by
  intro x φ
  induction φ generalizing x with
  | atom a =>
      change x ∈ {w : M.World | M w a} ↔ M x a
      simp
  | falsum =>
      change (x ∈ (kripkeModelToNeighborhood M).truthset Formula.falsum) ↔ False
      simp [LO.Modal.Neighborhood.Model.truthset]
  | imp φ ψ ihφ ihψ =>
      have hImpN :
          Formula.Neighborhood.Satisfies (kripkeModelToNeighborhood M) x (φ ➝ ψ) ↔
            (Formula.Neighborhood.Satisfies (kripkeModelToNeighborhood M) x φ →
              Formula.Neighborhood.Satisfies (kripkeModelToNeighborhood M) x ψ) :=
        Formula.Neighborhood.Satisfies.def_imp
          (M := kripkeModelToNeighborhood M) (x := x) (φ := φ) (ψ := ψ)
      have hImpK :
          Formula.Kripke.Satisfies M x (φ ➝ ψ) ↔
            (Formula.Kripke.Satisfies M x φ → Formula.Kripke.Satisfies M x ψ) :=
        Formula.Kripke.Satisfies.imp_def
          (M := M) (x := x) (φ := φ) (ψ := ψ)
      constructor
      · intro hx
        refine hImpK.mpr ?_
        intro hφK
        have hφN : Formula.Neighborhood.Satisfies (kripkeModelToNeighborhood M) x φ :=
          (ihφ x).2 hφK
        have hψN : Formula.Neighborhood.Satisfies (kripkeModelToNeighborhood M) x ψ :=
          (hImpN.mp hx) hφN
        exact (ihψ x).1 hψN
      · intro hx
        refine hImpN.mpr ?_
        intro hφN
        have hφK : Formula.Kripke.Satisfies M x φ := (ihφ x).1 hφN
        have hψK : Formula.Kripke.Satisfies M x ψ := (hImpK.mp hx) hφK
        exact (ihψ x).2 hψK
  | box φ ih =>
      constructor
      · intro hx
        have hN :
            (kripkeModelToNeighborhood M) φ ∈ (kripkeModelToNeighborhood M).𝒩 x :=
          (Formula.Neighborhood.Satisfies.def_box
            (M := kripkeModelToNeighborhood M) (x := x) (φ := φ)).1 hx
        have hsubset :
            {y : M.World | M.toFrame.Rel x y} ⊆ (kripkeModelToNeighborhood M) φ := by
          simpa [kripkeModelToNeighborhood, kripkeFrameToNeighborhood] using hN
        exact (Formula.Kripke.Satisfies.box_def).2 (by
          intro y hxy
          have hy : y ∈ (kripkeModelToNeighborhood M) φ := hsubset (by simpa using hxy)
          exact (ih y).1 hy)
      · intro hx
        have hsubset :
            {y : M.World | M.toFrame.Rel x y} ⊆ (kripkeModelToNeighborhood M) φ := by
          intro y hy
          have hySat : Formula.Kripke.Satisfies M y φ :=
            (Formula.Kripke.Satisfies.box_def).1 hx y (by simpa using hy)
          exact (ih y).2 hySat
        have hN :
            (kripkeModelToNeighborhood M) φ ∈ (kripkeModelToNeighborhood M).𝒩 x := by
          change {y : M.World | M.toFrame.Rel x y} ⊆ (kripkeModelToNeighborhood M) φ
          exact hsubset
        exact (Formula.Neighborhood.Satisfies.def_box
          (M := kripkeModelToNeighborhood M) (x := x) (φ := φ)).2 hN

/-- Canonical pointed-state translation induced by model translation. -/
def pointedKripkeToNeighborhood (pk : PointedKripke) : PointedNeighborhood where
  model := kripkeModelToNeighborhood pk.model
  world := pk.world

/-- Pointed satisfaction preservation under canonical translation. -/
theorem pointed_satisfies_iff (pk : PointedKripke) (φ : ModalQuery) :
    (pointedKripkeToNeighborhood pk).satisfies φ ↔ pk.satisfies φ := by
  simpa [Mettapedia.Logic.PLNWorldModelNeighborhood.PointedNeighborhood.satisfies,
    Mettapedia.Logic.PLNWorldModelKripke.PointedKripke.satisfies,
    pointedKripkeToNeighborhood] using
    (satisfies_iff_kripke_toNeighborhood pk.model pk.world φ)

/-- Class-level canonical Kripke-to-neighborhood representation API. -/
class CanonicalKripkeNeighborhoodEmbedding where
  pointMap : PointedKripke → PointedNeighborhood
  sat_iff : ∀ pk : PointedKripke, ∀ φ : ModalQuery,
    (pointMap pk).satisfies φ ↔ pk.satisfies φ

/-- Canonical instance from the standard frame/model translation. -/
instance : CanonicalKripkeNeighborhoodEmbedding where
  pointMap := pointedKripkeToNeighborhood
  sat_iff := pointed_satisfies_iff

/-- Convert class-level canonical representation to the generic embedding structure. -/
def canonicalEmbedding [CanonicalKripkeNeighborhoodEmbedding] :
    KripkeToNeighborhoodEmbedding where
  toNeighborhood := CanonicalKripkeNeighborhoodEmbedding.pointMap
  sat_iff := CanonicalKripkeNeighborhoodEmbedding.sat_iff

/-- Canonical query-strength transport corollary. -/
theorem queryStrength_mapState_eq_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    (Wk : Multiset PointedKripke) (φ : ModalQuery) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) φ =
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ :=
  queryStrength_mapState_eq (E := canonicalEmbedding) (Wk := Wk) (φ := φ)

/-- Canonical singleton consequence alignment corollary. -/
theorem singletonStrengthLEOn_canonical_iff_kripke
    [CanonicalKripkeNeighborhoodEmbedding]
    (φ ψ : ModalQuery) :
    (∀ pk : PointedKripke,
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({CanonicalKripkeNeighborhoodEmbedding.pointMap pk} : Multiset PointedNeighborhood) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({CanonicalKripkeNeighborhoodEmbedding.pointMap pk} : Multiset PointedNeighborhood) ψ)
      ↔ Mettapedia.Logic.PLNWorldModelKripke.singletonStrengthLE φ ψ :=
  singletonStrengthLEOnEmbedding_iff_kripke (E := canonicalEmbedding) (φ := φ) (ψ := ψ)

/-- Canonical mapped-neighborhood multiset consequence from Kripke proof-theoretic implication. -/
theorem mapState_strength_le_of_provable_imp_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ Wk, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) ψ :=
  mapState_strength_le_of_provable_imp
    (S := S) (𝓢 := 𝓢) (C := C)
    (E := canonicalEmbedding) (Wk := Wk)
    (φ := φ) (ψ := ψ) hW hprov

/-- Canonical governance-facing mapped consequence from the Kripke implication bridge. -/
theorem mapState_governance_ob_pe_strength_le_of_provable_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (Wk : Multiset PointedKripke) (φ : ModalQuery)
    (hW : ∀ pk ∈ Wk, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .obligatory φ) ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .permitted φ) :=
  mapState_governance_ob_pe_strength_le_of_provable
    (S := S) (𝓢 := 𝓢) (C := C)
    (E := canonicalEmbedding) (Wk := Wk)
    (φ := φ) hW hprov

/-- Direct parallel closure under canonical embedding:
the same implication premise yields both Kripke and mapped-neighborhood WM inequalities. -/
theorem parallel_strength_le_of_provable_imp_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ Wk, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    (WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk ψ) ∧
    (WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) ψ) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Logic.PLNWorldModelKripkeCompleteness.multiset_strength_le_of_provable_imp
        (S := S) (𝓢 := 𝓢) (C := C)
        (W := Wk) (φ := φ) (ψ := ψ) hW hprov
  · exact
      mapState_strength_le_of_provable_imp_canonical
        (S := S) (𝓢 := 𝓢) (C := C)
        (Wk := Wk) (φ := φ) (ψ := ψ) hW hprov

/-- Governance-facing parallel closure under canonical embedding:
the same `□φ ➝ ◇φ` premise yields both Kripke and mapped-neighborhood WM inequalities. -/
theorem parallel_governance_ob_pe_strength_le_of_provable_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (Wk : Multiset PointedKripke) (φ : ModalQuery)
    (hW : ∀ pk ∈ Wk, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    (WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk (□φ) ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk (◇φ)) ∧
    (WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .obligatory φ) ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .permitted φ)) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Logic.PLNWorldModelKripkeCompleteness.multiset_ob_pe_strength_le_of_provable
        (S := S) (𝓢 := 𝓢) (C := C)
        (W := Wk) (φ := φ) hW hprov
  · exact
      mapState_governance_ob_pe_strength_le_of_provable_canonical
        (S := S) (𝓢 := 𝓢) (C := C)
        (Wk := Wk) (φ := φ) hW hprov

/-- Concrete parallel wrapper (`KT` / `EMT`) under canonical embedding:
the same implication shape yields a Kripke-side inequality on `Wk` and a
mapped-neighborhood inequality on `mapState canonicalEmbedding Wk`. -/
theorem parallel_strength_le_of_provable_imp_KT_EMT_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hWKT : ∀ pk ∈ Wk, pk.model.toFrame ∈ Kripke.FrameClass.KT)
    (hWEMT : ∀ pn ∈ mapState canonicalEmbedding Wk, pn.model.toFrame ∈ Neighborhood.FrameClass.EMT)
    (hprovKT : Modal.KT ⊢ (φ ➝ ψ))
    (hprovEMT : Modal.EMT ⊢ (φ ➝ ψ)) :
    (WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk ψ) ∧
    (WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) ψ) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Logic.PLNWorldModelKripkeCompleteness.multiset_strength_le_of_provable_imp_KT
        (W := Wk) (φ := φ) (ψ := ψ) hWKT hprovKT
  · exact
      Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness.multiset_strength_le_of_provable_imp_EMT
        (W := mapState canonicalEmbedding Wk) (φ := φ) (ψ := ψ) hWEMT hprovEMT

/-- Concrete parallel wrapper (`KD` / `ED`) under canonical embedding:
the same implication shape yields a Kripke-side inequality on `Wk` and a
mapped-neighborhood inequality on `mapState canonicalEmbedding Wk`. -/
theorem parallel_strength_le_of_provable_imp_KD_ED_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hWKD : ∀ pk ∈ Wk, pk.model.toFrame ∈ Kripke.FrameClass.KD)
    (hWED : ∀ pn ∈ mapState canonicalEmbedding Wk, pn.model.toFrame ∈ Neighborhood.FrameClass.ED)
    (hprovKD : Modal.KD ⊢ (φ ➝ ψ))
    (hprovED : Modal.ED ⊢ (φ ➝ ψ)) :
    (WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk ψ) ∧
    (WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) φ ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) ψ) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Logic.PLNWorldModelKripkeCompleteness.multiset_strength_le_of_provable_imp_KD
        (W := Wk) (φ := φ) (ψ := ψ) hWKD hprovKD
  · exact
      Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness.multiset_strength_le_of_provable_imp_ED
        (W := mapState canonicalEmbedding Wk) (φ := φ) (ψ := ψ) hWED hprovED

/-- Governance-shaped concrete parallel wrapper (`KT` / `EMT`):
`□φ ⪯ φ` on Kripke states and mapped-neighborhood states. -/
theorem parallel_governance_rexist_strength_le_KT_EMT_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    (Wk : Multiset PointedKripke) (φ : ModalQuery)
    (hWKT : ∀ pk ∈ Wk, pk.model.toFrame ∈ Kripke.FrameClass.KT)
    (hWEMT : ∀ pn ∈ mapState canonicalEmbedding Wk, pn.model.toFrame ∈ Neighborhood.FrameClass.EMT)
    (hprovKT : Modal.KT ⊢ (□φ ➝ φ))
    (hprovEMT : Modal.EMT ⊢ (□φ ➝ φ)) :
    (WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk (□φ) ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ) ∧
    (WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .rexist φ) ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) φ) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Logic.PLNWorldModelKripkeCompleteness.multiset_rexist_strength_le_of_provable_KT
        (W := Wk) (φ := φ) hWKT hprovKT
  · simpa [governanceModalityToModalQuery] using
      (Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness.multiset_strength_le_of_provable_imp_EMT
        (W := mapState canonicalEmbedding Wk) (φ := □φ) (ψ := φ) hWEMT hprovEMT)

/-- Governance-shaped concrete parallel wrapper (`KD` / `ED`):
`□φ ⪯ ◇φ` on Kripke states and mapped-neighborhood states. -/
theorem parallel_governance_ob_pe_strength_le_KD_ED_canonical
    [CanonicalKripkeNeighborhoodEmbedding]
    (Wk : Multiset PointedKripke) (φ : ModalQuery)
    (hWKD : ∀ pk ∈ Wk, pk.model.toFrame ∈ Kripke.FrameClass.KD)
    (hWED : ∀ pn ∈ mapState canonicalEmbedding Wk, pn.model.toFrame ∈ Neighborhood.FrameClass.ED)
    (hprovKD : Modal.KD ⊢ (□φ ➝ ◇φ))
    (hprovED : Modal.ED ⊢ (□φ ➝ ◇φ)) :
    (WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk (□φ) ≤
      WorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk (◇φ)) ∧
    (WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .obligatory φ) ≤
      WorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState canonicalEmbedding Wk) (governanceModalityToModalQuery .permitted φ)) := by
  refine ⟨?_, ?_⟩
  · exact
      Mettapedia.Logic.PLNWorldModelKripkeCompleteness.multiset_ob_pe_strength_le_of_provable_KD
        (W := Wk) (φ := φ) hWKD hprovKD
  · simpa [governanceModalityToModalQuery] using
      (Mettapedia.Logic.PLNWorldModelNeighborhoodCompleteness.multiset_strength_le_of_provable_imp_ED
        (W := mapState canonicalEmbedding Wk) (φ := □φ) (ψ := ◇φ) hWED hprovED)

end Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodCanonical
