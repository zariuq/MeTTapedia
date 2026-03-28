import Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment
import Mathlib.Data.Finset.Dedup

/-!
# P vs NP crux: the current rho present-moment surface already realizes arbitrary finite slices

The current Meredith route wants a small per-instance observable surface.
Before talking about compression, it is worth checking the exact surface
already present in the rho `presentMoment` / `surfaceChannels` layer.

This file builds a simple finite probe family:

* state `i` is a single output on channel `i`;
* environment `S` is a flat bag of input guards on the channels in `S`.

On this slice, the current surface is exact:

* channel `i` is in `surfaceChannels(state i, env S)` iff `i ∈ S`;
* the concrete external-present-moment pair
  `(par (env S) hole, channel i)` is present iff `i ∈ S`.

So even before the HML layer, the exact current per-instance observable surface
already realizes arbitrary finite membership patterns.  Any same-route rescue
therefore still needs a real compression theorem; it does not get one for free
from the current Meredith present-moment machinery.
-/

namespace Mettapedia.Computability.PNP

open Mettapedia.Languages.ProcessCalculi.RhoCalculus
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Context
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Reduction
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.PresentMoment
open Mettapedia.OSLF.MeTTaIL.Syntax

/-- Probe channel `i`. -/
def shardChan (i : Nat) : Pattern := .bvar i

/-- A fixed inert payload. -/
def shardPayload : Pattern := .apply "PZero" []

/-- A fixed inert input body. -/
def shardBody : Pattern := .bvar 0

/-- Single-output probe state on channel `i`. -/
def shardOutput (i : Nat) : Pattern :=
  .apply "POutput" [shardChan i, shardPayload]

/-- Single-input probe guard on channel `i`. -/
def shardInput (i : Nat) : Pattern :=
  .apply "PInput" [shardChan i, .lambda none shardBody]

/-- The flat list of input guards selected by `s`. -/
def shardEnvList (s : List Nat) : List Pattern :=
  s.map shardInput

/-- The flat environment bag selected by `s`. -/
def shardEnv (s : List Nat) : Pattern :=
  .collection .hashBag (shardEnvList s) none

/-- The distinguished external-present-moment pair for state `i` against `s`. -/
def shardExternalPair (s : List Nat) (i : Nat) : EvalContext × Pattern :=
  ⟨.par (shardEnv s) .hole, shardChan i⟩

theorem shardChan_injective : Function.Injective shardChan := by
  intro i j h
  simpa [shardChan] using h

theorem shardInput_injective : Function.Injective shardInput := by
  intro i j h
  simpa [shardInput, shardChan] using h

@[simp] theorem freeNames_shardOutput (i : Nat) :
    freeNames (shardOutput i) = {shardChan i} := by
  simp [shardOutput, freeNames]

@[simp] theorem freeNames_shardInput (i : Nat) :
    freeNames (shardInput i) = {shardChan i} := by
  simp [shardInput, freeNames]

theorem shardInput_mem_shardEnvList_iff {s : List Nat} {i : Nat} :
    shardInput i ∈ shardEnvList s ↔ i ∈ s := by
  unfold shardEnvList
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨j, hj, hij⟩ := h
    simpa [shardInput_injective hij] using hj
  · intro hi
    exact List.mem_map.mpr ⟨i, hi, rfl⟩

theorem shardChan_mem_freeNames_shardEnv_iff {s : List Nat} {i : Nat} :
    shardChan i ∈ freeNames (shardEnv s) ↔ i ∈ s := by
  unfold shardEnv shardEnvList
  simp [freeNames, Mettapedia.Lists.SetFold.Set.mem_foldl_union, shardInput, shardChan]

theorem canInteract_shardFill_iff {s : List Nat} {i : Nat} :
    canInteract
      (.collection .hashBag
        (parComponents (shardEnv s) ++ parComponents (shardOutput i)) none)
      (shardChan i) ↔ i ∈ s := by
  unfold canInteract shardEnv shardEnvList parComponents
  constructor
  · rintro ⟨⟨body, hInput⟩, ⟨q, _hOutput⟩⟩
    rw [List.mem_append] at hInput
    rcases hInput with hInput | hInput
    · have hInput' : ∃ j ∈ s, shardInput j = .apply "PInput" [shardChan i, .lambda none body] := by
        simpa [parComponents, shardEnv, shardEnvList] using hInput
      rcases hInput' with ⟨j, hj, hjEq⟩
      have hji : j = i := by
        have hji_body : j = i ∧ shardBody = body := by
          simpa [shardInput, shardChan] using hjEq
        exact hji_body.1
      exact hji ▸ hj
    · simp [shardOutput] at hInput
  · intro hi
    refine ⟨⟨shardBody, ?_⟩, ⟨shardPayload, ?_⟩⟩
    · rw [List.mem_append]
      exact Or.inl ((shardInput_mem_shardEnvList_iff).2 hi)
    · rw [List.mem_append]
      simp [shardOutput]

theorem shardChan_mem_surfaceChannels_iff {s : List Nat} {i : Nat} :
    shardChan i ∈ surfaceChannels (shardOutput i) (shardEnv s) ↔ i ∈ s := by
  unfold surfaceChannels
  constructor
  · intro h
    rcases h with ⟨_, hcan⟩
    have hfill := (canInteract_perm List.perm_append_comm (shardChan i)).1 hcan
    exact (canInteract_shardFill_iff (s := s) (i := i)).1 hfill
  · intro hi
    refine ⟨?_, ?_⟩
    · exact ⟨by simp [freeNames_shardOutput], (shardChan_mem_freeNames_shardEnv_iff).2 hi⟩
    · have hfill := (canInteract_shardFill_iff (s := s) (i := i)).2 hi
      exact (canInteract_perm List.perm_append_comm (shardChan i)).2 hfill

theorem mem_surfaceChannels_shard_iff {s : List Nat} {i : Nat} {x : Pattern} :
    x ∈ surfaceChannels (shardOutput i) (shardEnv s) ↔ x = shardChan i ∧ i ∈ s := by
  constructor
  · intro h
    have hx : x = shardChan i := by
      have hxOut : x ∈ freeNames (shardOutput i) := h.1.1
      simpa [freeNames_shardOutput] using hxOut
    subst x
    exact ⟨rfl, (shardChan_mem_surfaceChannels_iff (s := s) (i := i)).1 h⟩
  · rintro ⟨rfl, hi⟩
    exact (shardChan_mem_surfaceChannels_iff (s := s) (i := i)).2 hi

theorem shardExternalPair_mem_presentMomentExt_iff {s : List Nat} {i : Nat} :
    shardExternalPair s i ∈ presentMomentExt (shardOutput i) (shardEnv s) ↔ i ∈ s := by
  constructor
  · intro h
    unfold shardExternalPair at h
    unfold presentMomentExt at h
    rcases h with ⟨x, hxSurf, K, hK, hpair, q, _hq⟩
    have hx : x = shardChan i := by
      simpa [hK] using (congrArg Prod.snd hpair).symm
    subst hx
    exact (shardChan_mem_surfaceChannels_iff (s := s) (i := i)).1 hxSurf
  · intro hi
    have hSurf : shardChan i ∈ surfaceChannels (shardOutput i) (shardEnv s) :=
      (shardChan_mem_surfaceChannels_iff (s := s) (i := i)).2 hi
    have hCan :
        canInteract
          (.collection .hashBag
            (parComponents (shardEnv s) ++ parComponents (shardOutput i)) none)
          (shardChan i) :=
      (canInteract_shardFill_iff (s := s) (i := i)).2 hi
    obtain ⟨q, hRedFlat⟩ := reduces_of_canInteract hCan
    have hRedFilled :
        Nonempty (Reduces
          (fillEvalContext (.par (shardEnv s) .hole) (shardOutput i))
          q) := by
      rcases hRedFlat with ⟨hRedFlat⟩
      have hsc :
          StructuralCongruence
            (.collection .hashBag [shardEnv s, shardOutput i] none)
            (.collection .hashBag
              (parComponents (shardEnv s) ++ parComponents (shardOutput i)) none) :=
        par_sc_flatten (shardEnv s) (shardOutput i)
      exact ⟨Reduces.equiv hsc hRedFlat (StructuralCongruence.refl _)⟩
    refine ⟨shardChan i, hSurf, .par (shardEnv s) .hole, rfl, rfl, q, ?_⟩
    exact ⟨LabeledTransition.from_reduction (by
      simpa [fillEvalContext] using hRedFilled)⟩

/-- Finite-set version of `shardEnv`, used for exact finite signature slices. -/
noncomputable def shardFinEnv {n : Nat} (S : Finset (Fin n)) : Pattern :=
  shardEnv (S.toList.map Fin.val)

theorem mem_shardFinEnvList_iff {n : Nat} {S : Finset (Fin n)} {i : Fin n} :
    i.1 ∈ S.toList.map Fin.val ↔ i ∈ S := by
  constructor
  · intro h
    rw [List.mem_map] at h
    obtain ⟨j, hj, hjEq⟩ := h
    have hji : j = i := Fin.ext hjEq
    simpa [hji] using (Finset.mem_toList.mp hj)
  · intro hi
    rw [List.mem_map]
    exact ⟨i, Finset.mem_toList.mpr hi, rfl⟩

theorem shardChan_mem_surfaceChannels_finset_iff {n : Nat}
    {S : Finset (Fin n)} {i : Fin n} :
    shardChan i.1 ∈ surfaceChannels (shardOutput i.1) (shardFinEnv S) ↔ i ∈ S := by
  unfold shardFinEnv
  rw [shardChan_mem_surfaceChannels_iff]
  exact mem_shardFinEnvList_iff

theorem shardExternalPair_mem_presentMomentExt_finset_iff {n : Nat}
    {S : Finset (Fin n)} {i : Fin n} :
    shardExternalPair (S.toList.map Fin.val) i.1 ∈
      presentMomentExt (shardOutput i.1) (shardFinEnv S) ↔ i ∈ S := by
  unfold shardFinEnv
  rw [shardExternalPair_mem_presentMomentExt_iff]
  exact mem_shardFinEnvList_iff

/-- The exact present-moment surface signature realized by the finite probe set `S`. -/
noncomputable def shardSurfaceSignature {n : Nat} (S : Finset (Fin n)) : Fin n → Prop :=
  fun i => shardChan i.1 ∈ surfaceChannels (shardOutput i.1) (shardFinEnv S)

theorem shardSurfaceSignature_iff_mem {n : Nat}
    {S : Finset (Fin n)} {i : Fin n} :
    shardSurfaceSignature S i ↔ i ∈ S :=
  shardChan_mem_surfaceChannels_finset_iff

theorem shardSurfaceSignature_injective {n : Nat} :
    Function.Injective (shardSurfaceSignature (n := n)) := by
  intro S T hST
  apply Finset.ext
  intro i
  have hi : shardSurfaceSignature S i ↔ shardSurfaceSignature T i := by
    simpa using congrArg (fun f : Fin n → Prop => f i) hST
  exact (shardSurfaceSignature_iff_mem (S := S) (i := i)).symm.trans
    (hi.trans (shardSurfaceSignature_iff_mem (S := T) (i := i)))

end Mettapedia.Computability.PNP
