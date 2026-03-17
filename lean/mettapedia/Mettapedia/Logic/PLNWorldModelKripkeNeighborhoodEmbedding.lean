import Mettapedia.Logic.PLNWorldModelKripke
import Mettapedia.Logic.PLNWorldModelNeighborhood
import Mettapedia.Logic.PLNWorldModelKripkeCompleteness
import Mettapedia.Logic.GovernanceReasoning.Core

/-!
# Kripke-to-Neighborhood WM Embedding

This module provides a semantic embedding interface from pointed Kripke states
into pointed neighborhood states, then transports singleton/multiset WM query
strength consequences across that embedding.

It also exposes a governance-facing consequence theorem obtained from the
Kripke proof-theoretic bridge (`provable implication -> multiset WM inequality`)
and transported through the embedding.
-/

namespace Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodEmbedding

open LO
open LO.Modal
open Mettapedia.Logic.GovernanceReasoning.Core
open Mettapedia.Logic.PLNWorldModel
open Mettapedia.Logic.PLNWorldModelKripke
open Mettapedia.Logic.PLNWorldModelNeighborhood
open Mettapedia.Logic.PLNWorldModelKripkeCompleteness

abbrev ModalQuery := Mettapedia.Logic.PLNWorldModelKripke.ModalQuery
abbrev PointedKripke := Mettapedia.Logic.PLNWorldModelKripke.PointedKripke
abbrev PointedNeighborhood := Mettapedia.Logic.PLNWorldModelNeighborhood.PointedNeighborhood

/-- Semantic embedding from pointed Kripke states to pointed neighborhood states.
It is extensional at the modal-satisfaction level. -/
structure KripkeToNeighborhoodEmbedding where
  toNeighborhood : PointedKripke → PointedNeighborhood
  sat_iff : ∀ pk : PointedKripke, ∀ φ : ModalQuery,
    (toNeighborhood pk).satisfies φ ↔ pk.satisfies φ

/-- State-level map induced by the embedding. -/
def mapState (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) : Multiset PointedNeighborhood :=
  Wk.map E.toNeighborhood

/-- BinaryEvidence equality under Kripke-to-neighborhood embedding map. -/
theorem evidence_mapState_eq
    (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) (φ : ModalQuery) :
    neighborhoodEvidence (mapState E Wk) φ = kripkeEvidence Wk φ := by
  classical
  letI : DecidablePred (fun pn : PointedNeighborhood => pn.satisfies φ) := Classical.decPred _
  letI : DecidablePred (fun pk : PointedKripke => pk.satisfies φ) := Classical.decPred _
  letI : DecidablePred (fun pk : PointedKripke => (E.toNeighborhood pk).satisfies φ) := Classical.decPred _
  letI : DecidablePred (fun pk : PointedKripke => ¬ (E.toNeighborhood pk).satisfies φ) := by
    intro pk
    infer_instance
  have hpred :
      (fun pk : PointedKripke => (E.toNeighborhood pk).satisfies φ) =
        (fun pk : PointedKripke => pk.satisfies φ) := by
    funext pk
    exact propext (E.sat_iff pk φ)
  have hpredNeg :
      (fun pk : PointedKripke => ¬ (E.toNeighborhood pk).satisfies φ) =
        (fun pk : PointedKripke => ¬ pk.satisfies φ) := by
    funext pk
    exact propext (not_congr (E.sat_iff pk φ))
  have hpos :
      Multiset.countP (fun pn : PointedNeighborhood => pn.satisfies φ) (mapState E Wk) =
        Multiset.countP (fun pk : PointedKripke => pk.satisfies φ) Wk := by
    calc
      Multiset.countP (fun pn : PointedNeighborhood => pn.satisfies φ) (mapState E Wk)
          = Multiset.card (Wk.filter fun pk : PointedKripke => (E.toNeighborhood pk).satisfies φ) := by
            simpa [mapState] using
              (Multiset.countP_map (f := E.toNeighborhood) (s := Wk)
                (p := fun pn : PointedNeighborhood => pn.satisfies φ))
      _ = Multiset.card (Wk.filter fun pk : PointedKripke => pk.satisfies φ) := by
            simp [hpred]
      _ = Multiset.countP (fun pk : PointedKripke => pk.satisfies φ) Wk := by
            rw [Multiset.countP_eq_card_filter]
  have hneg :
      Multiset.countP (fun pn : PointedNeighborhood => ¬ pn.satisfies φ) (mapState E Wk) =
        Multiset.countP (fun pk : PointedKripke => ¬ pk.satisfies φ) Wk := by
    calc
      Multiset.countP (fun pn : PointedNeighborhood => ¬ pn.satisfies φ) (mapState E Wk)
          = Multiset.card (Wk.filter fun pk : PointedKripke => ¬ (E.toNeighborhood pk).satisfies φ) := by
            simpa [mapState] using
              (Multiset.countP_map (f := E.toNeighborhood) (s := Wk)
                (p := fun pn : PointedNeighborhood => ¬ pn.satisfies φ))
      _ = Multiset.card (Wk.filter fun pk : PointedKripke => ¬ pk.satisfies φ) := by
            simp [hpredNeg]
      _ = Multiset.countP (fun pk : PointedKripke => ¬ pk.satisfies φ) Wk := by
            rw [Multiset.countP_eq_card_filter]
  ext
  · simpa [neighborhoodEvidence, kripkeEvidence] using hpos
  · simpa [neighborhoodEvidence, kripkeEvidence] using hneg

/-- Query-strength equality under Kripke-to-neighborhood embedding map. -/
theorem queryStrength_mapState_eq
    (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) (φ : ModalQuery) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) φ =
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ := by
  change (BinaryWorldModel.evidence (mapState E Wk) φ).toStrength =
      (BinaryWorldModel.evidence Wk φ).toStrength
  exact congrArg (fun e => e.toStrength)
    (evidence_mapState_eq (E := E) (Wk := Wk) (φ := φ))

/-- Singleton-strength transport (image-restricted neighborhood side) iff Kripke singleton-strength. -/
theorem singletonStrengthLEOnEmbedding_iff_kripke
    (E : KripkeToNeighborhoodEmbedding) (φ ψ : ModalQuery) :
    (∀ pk : PointedKripke,
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({E.toNeighborhood pk} : Multiset PointedNeighborhood) φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        ({E.toNeighborhood pk} : Multiset PointedNeighborhood) ψ)
      ↔ Mettapedia.Logic.PLNWorldModelKripke.singletonStrengthLE φ ψ := by
  constructor
  · intro h pk
    have hpkN :
        BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            (mapState E ({pk} : Multiset PointedKripke)) φ ≤
          BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            (mapState E ({pk} : Multiset PointedKripke)) ψ := by
      simpa [mapState] using h pk
    simpa [queryStrength_mapState_eq (E := E) (Wk := ({pk} : Multiset PointedKripke))
      (φ := φ),
      queryStrength_mapState_eq (E := E) (Wk := ({pk} : Multiset PointedKripke))
      (φ := ψ)] using hpkN
  · intro h pk
    have hpkK :
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
            ({pk} : Multiset PointedKripke) φ ≤
          BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
            ({pk} : Multiset PointedKripke) ψ := h pk
    have hpkN :
        BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            (mapState E ({pk} : Multiset PointedKripke)) φ ≤
          BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
            (mapState E ({pk} : Multiset PointedKripke)) ψ := by
      simpa [queryStrength_mapState_eq (E := E) (Wk := ({pk} : Multiset PointedKripke))
        (φ := φ),
        queryStrength_mapState_eq (E := E) (Wk := ({pk} : Multiset PointedKripke))
        (φ := ψ)] using hpkK
    simpa [mapState] using hpkN

/-- Multiset inequality transport from Kripke WM to mapped neighborhood WM states. -/
theorem mapState_strength_le_of_kripke
    (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hK :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          Wk φ ≤
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          Wk ψ) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) ψ := by
  simpa [queryStrength_mapState_eq (E := E) (Wk := Wk) (φ := φ),
    queryStrength_mapState_eq (E := E) (Wk := Wk) (φ := ψ)] using hK

/-- Parallel WM consequence corollary: Kripke inequality implies mapped-neighborhood inequality. -/
theorem kripke_neighborhood_parallel_of_kripke
    (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hK :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          Wk φ ≤
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          Wk ψ) :
    (BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
        Wk ψ) ∧
    (BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) ψ) := by
  exact ⟨hK, mapState_strength_le_of_kripke (E := E) (Wk := Wk) (φ := φ) (ψ := ψ) hK⟩

/-- Mapped-neighborhood consequence from Kripke proof-theoretic implication bridge. -/
theorem mapState_strength_le_of_provable_imp
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) (φ ψ : ModalQuery)
    (hW : ∀ pk ∈ Wk, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (φ ➝ ψ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) φ ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) ψ := by
  have hK :
      BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          Wk φ ≤
        BinaryWorldModel.queryStrength (State := Multiset PointedKripke) (Query := ModalQuery)
          Wk ψ :=
    multiset_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C) (W := Wk) (φ := φ) (ψ := ψ) hW hprov
  exact mapState_strength_le_of_kripke (E := E) (Wk := Wk) (φ := φ) (ψ := ψ) hK

/-- Governance-facing modal-collapse map used with the Kripke proof-theoretic bridge. -/
def governanceModalityToModalQuery (m : DeonticModality) (φ : ModalQuery) : ModalQuery :=
  match m with
  | .rexist => □φ
  | .obligatory => □φ
  | .permitted => ◇φ
  | .forbidden => □(∼φ)
  | .optional => (◇φ ⋏ ◇(∼φ))

@[simp] theorem governanceModalityToModalQuery_obligatory (φ : ModalQuery) :
    governanceModalityToModalQuery .obligatory φ = □φ := rfl

@[simp] theorem governanceModalityToModalQuery_permitted (φ : ModalQuery) :
    governanceModalityToModalQuery .permitted φ = ◇φ := rfl

/-- Governance-facing theorem:
if `□φ ➝ ◇φ` is provable in a Kripke-sound system over frame class `C`,
then the mapped neighborhood WM state satisfies the corresponding
obligation/permission consequence inequality. -/
theorem mapState_governance_ob_pe_strength_le_of_provable
    {S : Type*} [Entailment S ModalQuery]
    {𝓢 : S}
    {C : Kripke.FrameClass}
    [Sound 𝓢 C]
    (E : KripkeToNeighborhoodEmbedding)
    (Wk : Multiset PointedKripke) (φ : ModalQuery)
    (hW : ∀ pk ∈ Wk, pk.model.toFrame ∈ C)
    (hprov : 𝓢 ⊢ (□φ ➝ ◇φ)) :
    BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) (governanceModalityToModalQuery .obligatory φ) ≤
      BinaryWorldModel.queryStrength (State := Multiset PointedNeighborhood) (Query := ModalQuery)
        (mapState E Wk) (governanceModalityToModalQuery .permitted φ) := by
  simpa [governanceModalityToModalQuery] using
    (mapState_strength_le_of_provable_imp
      (S := S) (𝓢 := 𝓢) (C := C)
      (E := E) (Wk := Wk)
      (φ := □φ) (ψ := ◇φ) hW hprov)

end Mettapedia.Logic.PLNWorldModelKripkeNeighborhoodEmbedding
