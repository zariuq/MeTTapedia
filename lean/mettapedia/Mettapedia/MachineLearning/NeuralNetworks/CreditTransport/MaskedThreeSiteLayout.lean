import Mettapedia.MachineLearning.NeuralNetworks.CreditTransport.DeepErrorCoordinateAcceleration

/-!
# Canonical masked layout for three error sites

The neural implementation stores three equal-shaped error tensors, selects the
active coordinates of each tensor in flattened storage order, and concatenates
the three selected blocks in site order.  This file makes that layout an exact
finite-dimensional construction.

The first equivalence splits every stored coordinate into the active and
inactive subspaces.  The second ranks active coordinates in their inherited
storage order and then flattens the product in site-major order.  Both maps are
linear isometries, so padding removal and flat packing preserve the Euclidean
norm exactly.  A different site order remains an isometry but is not the same
layout; the final fixture records that distinction.
-/

namespace Mettapedia.MachineLearning.NeuralNetworks.CreditTransport

namespace MaskedThreeSiteLayout

open DeepErrorCoordinateAcceleration

noncomputable section

/-- Stored coordinates selected by a declared mask. -/
abbrev ActiveCoord {n : ℕ} (mask : Fin n → Prop) :=
  {coordinate : Fin n // mask coordinate}

/-- Stored coordinates rejected by a declared mask. -/
abbrev InactiveCoord {n : ℕ} (mask : Fin n → Prop) :=
  {coordinate : Fin n // ¬ mask coordinate}

/-- The three equal-shaped tensors before padding coordinates are removed. -/
abbrev RawThreeSiteError (n : ℕ) :=
  EuclideanSpace ℝ (Fin 3 × Fin n)

/-- Split a three-site storage index into its active or inactive branch.
The site coordinate is retained on both branches. -/
def splitIndexEquiv {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    (Fin 3 × Fin n) ≃
      (Fin 3 × ActiveCoord mask) ⊕ (Fin 3 × InactiveCoord mask) :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) (Equiv.sumCompl mask).symm).trans
    (Equiv.prodSumDistrib (Fin 3) (ActiveCoord mask) (InactiveCoord mask))

/-- Reindex the three stored tensors as an exact active/inactive Euclidean
split.  No coordinate is discarded by this map. -/
def splitStoredErrors {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    RawThreeSiteError n ≃ₗᵢ[ℝ]
      ThreeSiteStoredError (ActiveCoord mask) (InactiveCoord mask) :=
  (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (splitIndexEquiv mask)).trans
    (PiLp.sumPiLpEquivProdLpPiLp 2
      (fun _ : (Fin 3 × ActiveCoord mask) ⊕
          (Fin 3 × InactiveCoord mask) => ℝ))

/-- The canonical increasing rank of an active coordinate. -/
def activeRankOrderIso {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    ActiveCoord mask ≃o Fin (Fintype.card (ActiveCoord mask)) :=
  (Fintype.orderIsoFinOfCardEq (ActiveCoord mask) rfl).symm

/-- The underlying equivalence of the canonical increasing rank. -/
def activeRankEquiv {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    ActiveCoord mask ≃ Fin (Fintype.card (ActiveCoord mask)) :=
  (activeRankOrderIso mask).toEquiv

/-- Site-major flattening: the active rank varies fastest, then the site.
Thus the flat index is `rank + activeCount * site`. -/
def siteMajorIndexEquiv {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    (Fin 3 × ActiveCoord mask) ≃
      Fin (3 * Fintype.card (ActiveCoord mask)) :=
  (Equiv.prodCongr (Equiv.refl (Fin 3)) (activeRankEquiv mask)).trans
    finProdFinEquiv

/-- Pack the three active site blocks into one site-major Euclidean vector. -/
def packActiveSiteMajor {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    ThreeSiteActiveError (ActiveCoord mask) ≃ₗᵢ[ℝ]
      EuclideanSpace ℝ (Fin (3 * Fintype.card (ActiveCoord mask))) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (siteMajorIndexEquiv mask)

@[simp] theorem splitStoredErrors_norm
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (stored : RawThreeSiteError n) :
    ‖splitStoredErrors mask stored‖ = ‖stored‖ :=
  (splitStoredErrors mask).norm_map stored

@[simp] theorem packActiveSiteMajor_norm
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (active : ThreeSiteActiveError (ActiveCoord mask)) :
    ‖packActiveSiteMajor mask active‖ = ‖active‖ :=
  (packActiveSiteMajor mask).norm_map active

theorem splitStoredErrors_active_apply
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (stored : RawThreeSiteError n) (site : Fin 3)
    (coordinate : ActiveCoord mask) :
    (splitStoredErrors mask stored).fst (site, coordinate) =
      stored (site, coordinate.1) := by
  rfl

theorem splitStoredErrors_inactive_apply
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (stored : RawThreeSiteError n) (site : Fin 3)
    (coordinate : InactiveCoord mask) :
    (splitStoredErrors mask stored).snd (site, coordinate) =
      stored (site, coordinate.1) := by
  rfl

/-- Reconstructing an active-only tensor preserves every selected coordinate. -/
theorem reconstruct_active_apply
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (active : ThreeSiteActiveError (ActiveCoord mask))
    (site : Fin 3) (coordinate : ActiveCoord mask) :
    (splitStoredErrors mask).symm
        (storeActive (InactiveCoord := InactiveCoord mask) active)
        (site, coordinate.1) = active (site, coordinate) := by
  calc
    (splitStoredErrors mask).symm
          (storeActive (InactiveCoord := InactiveCoord mask) active)
          (site, coordinate.1) =
        (splitStoredErrors mask
          ((splitStoredErrors mask).symm
            (storeActive (InactiveCoord := InactiveCoord mask) active))).fst
          (site, coordinate) :=
      (splitStoredErrors_active_apply mask _ site coordinate).symm
    _ = (storeActive (InactiveCoord := InactiveCoord mask) active).fst
          (site, coordinate) := by
      rw [(splitStoredErrors mask).apply_symm_apply]
    _ = active (site, coordinate) := rfl

/-- Reconstructing an active-only tensor writes zero to every padding
coordinate. -/
theorem reconstruct_inactive_apply
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (active : ThreeSiteActiveError (ActiveCoord mask))
    (site : Fin 3) (coordinate : InactiveCoord mask) :
    (splitStoredErrors mask).symm
        (storeActive (InactiveCoord := InactiveCoord mask) active)
        (site, coordinate.1) = 0 := by
  calc
    (splitStoredErrors mask).symm
          (storeActive (InactiveCoord := InactiveCoord mask) active)
          (site, coordinate.1) =
        (splitStoredErrors mask
          ((splitStoredErrors mask).symm
            (storeActive (InactiveCoord := InactiveCoord mask) active))).snd
          (site, coordinate) :=
      (splitStoredErrors_inactive_apply mask _ site coordinate).symm
    _ = (storeActive (InactiveCoord := InactiveCoord mask) active).snd
          (site, coordinate) := by
      rw [(splitStoredErrors mask).apply_symm_apply]
    _ = 0 := rfl

/-- Flat packing and unpacking are inverse operations. -/
@[simp] theorem unpack_pack_active
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (active : ThreeSiteActiveError (ActiveCoord mask)) :
    (packActiveSiteMajor mask).symm (packActiveSiteMajor mask active) = active :=
  (packActiveSiteMajor mask).symm_apply_apply active

/-- Flat unpacking and packing are inverse operations. -/
@[simp] theorem pack_unpack_active
    {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask]
    (flat : EuclideanSpace ℝ
      (Fin (3 * Fintype.card (ActiveCoord mask)))) :
    packActiveSiteMajor mask ((packActiveSiteMajor mask).symm flat) = flat :=
  (packActiveSiteMajor mask).apply_symm_apply flat

/-! ## Exact layout fixtures -/

/-- A small row mask with active flattened storage coordinates `0`, `2`, and
`4`. -/
def alternatingMask (coordinate : Fin 6) : Prop :=
  coordinate.1 % 2 = 0

instance alternatingMaskDecidable : DecidablePred alternatingMask :=
  fun coordinate => inferInstanceAs (Decidable (coordinate.1 % 2 = 0))

theorem alternatingMask_active_card :
    Fintype.card (ActiveCoord alternatingMask) = 3 := by
  decide

def activeZero : ActiveCoord alternatingMask := ⟨0, by decide⟩
def activeTwo : ActiveCoord alternatingMask := ⟨2, by decide⟩
def activeFour : ActiveCoord alternatingMask := ⟨4, by decide⟩

/-- The active-coordinate ranking follows flattened storage order. -/
theorem alternatingMask_active_ranks :
    (activeRankEquiv alternatingMask activeZero).1 = 0 ∧
    (activeRankEquiv alternatingMask activeTwo).1 = 1 ∧
    (activeRankEquiv alternatingMask activeFour).1 = 2 := by
  have hzeroTwo : activeZero < activeTwo := by decide
  have htwoFour : activeTwo < activeFour := by decide
  have hrankZeroTwo :=
    (activeRankOrderIso alternatingMask).lt_iff_lt.mpr hzeroTwo
  have hrankTwoFour :=
    (activeRankOrderIso alternatingMask).lt_iff_lt.mpr htwoFour
  have hzeroBound := (activeRankEquiv alternatingMask activeZero).isLt
  have htwoBound := (activeRankEquiv alternatingMask activeTwo).isLt
  have hfourBound := (activeRankEquiv alternatingMask activeFour).isLt
  have hcard := alternatingMask_active_card
  change (activeRankEquiv alternatingMask activeZero).1 <
      (activeRankEquiv alternatingMask activeTwo).1 at hrankZeroTwo
  change (activeRankEquiv alternatingMask activeTwo).1 <
      (activeRankEquiv alternatingMask activeFour).1 at hrankTwoFour
  omega

/-- Site-major concatenation places the second active coordinate of site one
at flat offset `3 + 1 = 4`. -/
theorem alternatingMask_siteMajor_index :
    (siteMajorIndexEquiv alternatingMask (1, activeTwo)).1 = 4 := by
  have hrank := alternatingMask_active_ranks
  have hcard := alternatingMask_active_card
  change (activeRankEquiv alternatingMask activeTwo).1 +
      Fintype.card (ActiveCoord alternatingMask) = 4
  omega

/-- A wrong site permutation is still a bijective norm-preserving layout, but
it is observably not the registered site-major layout. -/
def swappedSiteIndexEquiv {n : ℕ} (mask : Fin n → Prop) [DecidablePred mask] :
    (Fin 3 × ActiveCoord mask) ≃
      Fin (3 * Fintype.card (ActiveCoord mask)) :=
  (Equiv.prodCongr (Equiv.swap (0 : Fin 3) 1) (activeRankEquiv mask)).trans
    finProdFinEquiv

theorem swappedSite_layout_differs :
    siteMajorIndexEquiv alternatingMask (0, activeZero) ≠
      swappedSiteIndexEquiv alternatingMask (0, activeZero) := by
  intro hequal
  have hrank := alternatingMask_active_ranks
  have hcard := alternatingMask_active_card
  have hvalue := congrArg Fin.val hequal
  change (activeRankEquiv alternatingMask activeZero).1 =
      (activeRankEquiv alternatingMask activeZero).1 +
        Fintype.card (ActiveCoord alternatingMask) at hvalue
  omega

#print axioms splitStoredErrors_norm
#print axioms reconstruct_active_apply
#print axioms reconstruct_inactive_apply
#print axioms packActiveSiteMajor_norm
#print axioms alternatingMask_siteMajor_index
#print axioms swappedSite_layout_differs

end

end MaskedThreeSiteLayout

end Mettapedia.MachineLearning.NeuralNetworks.CreditTransport
