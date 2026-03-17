import Mettapedia.Logic.EvidenceQuantale

/-!
# Identity BinaryEvidence Layer

This module adds a guarded identity-evidence layer on top of the canonical
`BinaryEvidence` carrier.

The layer is intentionally conservative:
- identity transport is guarded by assurance and contradiction thresholds,
- path composition uses quantale tensor (`*`),
- independent identity paths revise additively (`+`),
- competing identities remain as guarded alternatives (no forced merge).
-/

namespace Mettapedia.Logic.IdentityEvidence

open Mettapedia.Logic.EvidenceQuantale
open scoped ENNReal

/-- Identity evidence relation: evidence that two entities are identical. -/
abbrev IdEvidence (Entity : Type*) := Entity → Entity → BinaryEvidence

/-- Guard thresholds for identity-based transport. -/
structure TransportThresholds where
  assuranceMin : ℝ≥0∞
  contradictionMax : ℝ≥0∞

/-- Assurance score used by transport guards. -/
noncomputable def assurance (e : BinaryEvidence) : ℝ≥0∞ :=
  BinaryEvidence.toStrength e

/-- Contradiction mass: normalized negative evidence ratio `n⁻/(n⁺+n⁻)`. -/
noncomputable def contradictionMass (e : BinaryEvidence) : ℝ≥0∞ :=
  if e.total = 0 then 0 else e.neg / e.total

/-- Guard predicate for identity transport. -/
noncomputable def transportGuard (τ : TransportThresholds) (e : BinaryEvidence) : Prop :=
  τ.assuranceMin ≤ assurance e ∧ contradictionMass e ≤ τ.contradictionMax

/-- Boolean guard for executable routing. -/
noncomputable def transportGuardB (τ : TransportThresholds) (e : BinaryEvidence) : Bool :=
  by
    classical
    exact decide (transportGuard τ e)

theorem transportGuardB_eq_true_iff (τ : TransportThresholds) (e : BinaryEvidence) :
    transportGuardB τ e = true ↔ transportGuard τ e := by
  classical
  simp [transportGuardB]

/-- Transport payload evidence across identity iff guard passes. -/
noncomputable def transportAcrossIdentity
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    (src dst : Entity)
    (payload : BinaryEvidence) : BinaryEvidence :=
  if transportGuardB τ (idEv src dst) then payload * idEv src dst else payload

/-- Optional transport gate (`enabled = false` gives conservative no-op). -/
noncomputable def transportAcrossIdentityIf
    {Entity : Type*}
    (enabled : Bool)
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    (src dst : Entity)
    (payload : BinaryEvidence) : BinaryEvidence :=
  if enabled then transportAcrossIdentity idEv τ src dst payload else payload

theorem transportAcrossIdentityIf_disabled
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    (src dst : Entity)
    (payload : BinaryEvidence) :
    transportAcrossIdentityIf false idEv τ src dst payload = payload := by
  simp [transportAcrossIdentityIf]

theorem transportAcrossIdentityIf_enabled
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    (src dst : Entity)
    (payload : BinaryEvidence) :
    transportAcrossIdentityIf true idEv τ src dst payload =
      transportAcrossIdentity idEv τ src dst payload := by
  simp [transportAcrossIdentityIf]

/-- Identity-path composition via quantale tensor. -/
noncomputable def pathEvidence
    {Entity : Type*}
    (idEv : IdEvidence Entity) : List Entity → BinaryEvidence
  | [] => BinaryEvidence.one
  | [_] => BinaryEvidence.one
  | src :: dst :: rest => idEv src dst * pathEvidence idEv (dst :: rest)

@[simp] theorem pathEvidence_nil
    {Entity : Type*}
    (idEv : IdEvidence Entity) :
    pathEvidence idEv [] = BinaryEvidence.one := rfl

@[simp] theorem pathEvidence_singleton
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (x : Entity) :
    pathEvidence idEv [x] = BinaryEvidence.one := rfl

theorem pathEvidence_pair
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (x y : Entity) :
    pathEvidence idEv [x, y] = idEv x y := by
  simp [pathEvidence, BinaryEvidence.tensor_one]

theorem pathEvidence_triple
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (x y z : Entity) :
    pathEvidence idEv [x, y, z] = idEv x y * idEv y z := by
  simp [pathEvidence, BinaryEvidence.tensor_one]

/-- Optional path transport (disabled mode is conservative no-op). -/
noncomputable def transportAlongPathIf
    {Entity : Type*}
    (enabled : Bool)
    (idEv : IdEvidence Entity)
    (path : List Entity)
    (payload : BinaryEvidence) : BinaryEvidence :=
  if enabled then payload * pathEvidence idEv path else payload

theorem transportAlongPathIf_disabled
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (path : List Entity)
    (payload : BinaryEvidence) :
    transportAlongPathIf false idEv path payload = payload := by
  simp [transportAlongPathIf]

/-- Additive revision of independent identity-path evidence. -/
noncomputable def reviseIdentityEvidence (e₁ e₂ : BinaryEvidence) : BinaryEvidence :=
  e₁ + e₂

@[simp] theorem reviseIdentityEvidence_pos (e₁ e₂ : BinaryEvidence) :
    (reviseIdentityEvidence e₁ e₂).pos = e₁.pos + e₂.pos := by
  simp [reviseIdentityEvidence, BinaryEvidence.hplus_def]

@[simp] theorem reviseIdentityEvidence_neg (e₁ e₂ : BinaryEvidence) :
    (reviseIdentityEvidence e₁ e₂).neg = e₁.neg + e₂.neg := by
  simp [reviseIdentityEvidence, BinaryEvidence.hplus_def]

/-- Guarded identity alternatives from a candidate list. -/
noncomputable def guardedAlternatives
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    (src : Entity)
    (candidates : List Entity) : List Entity :=
  candidates.filter (fun dst => transportGuardB τ (idEv src dst))

theorem mem_guardedAlternatives_iff
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    (src dst : Entity)
    (candidates : List Entity) :
    dst ∈ guardedAlternatives idEv τ src candidates
      ↔ dst ∈ candidates ∧ transportGuard τ (idEv src dst) := by
  simp [guardedAlternatives, transportGuardB_eq_true_iff]

theorem competing_identities_preserved
    {Entity : Type*}
    (idEv : IdEvidence Entity)
    (τ : TransportThresholds)
    {src y z : Entity}
    {candidates : List Entity}
    (hneq : y ≠ z)
    (hy : y ∈ candidates)
    (hz : z ∈ candidates)
    (hgy : transportGuard τ (idEv src y))
    (hgz : transportGuard τ (idEv src z)) :
    y ∈ guardedAlternatives idEv τ src candidates ∧
      z ∈ guardedAlternatives idEv τ src candidates ∧
      y ≠ z := by
  constructor
  · exact (mem_guardedAlternatives_iff idEv τ src y candidates).2 ⟨hy, hgy⟩
  constructor
  · exact (mem_guardedAlternatives_iff idEv τ src z candidates).2 ⟨hz, hgz⟩
  · exact hneq

/-- Canary identity evidence map with one strong and one weak edge. -/
def canaryIdEvidence : IdEvidence String := fun src dst =>
  if src = "alice" ∧ dst = "ally" then ⟨3, 2⟩
  else if src = "ally" ∧ dst = "alicia" then ⟨4, 1⟩
  else if src = "alice" ∧ dst = "alicia" then ⟨1, 3⟩
  else BinaryEvidence.one

/-- Loose thresholds: transport guard always passes. -/
def canaryLooseThresholds : TransportThresholds :=
  { assuranceMin := 0
    contradictionMax := ⊤ }

/-- Strict thresholds: assurance requirement is intentionally impossible. -/
def canaryStrictThresholds : TransportThresholds :=
  { assuranceMin := 2
    contradictionMax := ⊤ }

def canaryPayload : BinaryEvidence := ⟨5, 1⟩

theorem canary_loose_guard_true (e : BinaryEvidence) :
    transportGuard canaryLooseThresholds e := by
  constructor
  · simp [canaryLooseThresholds, assurance]
  · simp [canaryLooseThresholds]

theorem canary_strict_guard_false (e : BinaryEvidence) :
    ¬ transportGuard canaryStrictThresholds e := by
  intro h
  have hStrengthLeOne : assurance e ≤ 1 := by
    simpa [assurance] using BinaryEvidence.toStrength_le_one e
  have hTwoLeOne : (2 : ℝ≥0∞) ≤ 1 := le_trans h.1 hStrengthLeOne
  norm_num at hTwoLeOne

/-- Enabled transport canary: with loose thresholds, guard passes and transport fires. -/
theorem transport_enabled_canary_guard_pass :
    transportAcrossIdentityIf true canaryIdEvidence canaryLooseThresholds
      "alice" "ally" canaryPayload = ⟨15, 2⟩ := by
  have hguard : transportGuard canaryLooseThresholds ((⟨3, 2⟩ : BinaryEvidence)) :=
    canary_loose_guard_true _
  have hguardB : transportGuardB canaryLooseThresholds ((⟨3, 2⟩ : BinaryEvidence)) = true :=
    (transportGuardB_eq_true_iff _ _).2 hguard
  calc
    transportAcrossIdentityIf true canaryIdEvidence canaryLooseThresholds
      "alice" "ally" canaryPayload
        = canaryPayload * (⟨3, 2⟩ : BinaryEvidence) := by
            simp [transportAcrossIdentityIf, transportAcrossIdentity, hguardB,
              canaryIdEvidence, canaryPayload]
    _ = ⟨15, 2⟩ := by
      ext <;> norm_num [BinaryEvidence.tensor_def, canaryPayload]

/-- Enabled transport canary: with strict thresholds, guard fails and payload is unchanged. -/
theorem transport_enabled_canary_guard_fail :
    transportAcrossIdentityIf true canaryIdEvidence canaryStrictThresholds
      "alice" "ally" canaryPayload = canaryPayload := by
  have hnot : ¬ transportGuard canaryStrictThresholds (canaryIdEvidence "alice" "ally") :=
    canary_strict_guard_false _
  have hguardBFalse :
      transportGuardB canaryStrictThresholds (canaryIdEvidence "alice" "ally") = false := by
    by_cases hB : transportGuardB canaryStrictThresholds (canaryIdEvidence "alice" "ally") = true
    · exact False.elim (hnot ((transportGuardB_eq_true_iff _ _).1 hB))
    · exact Bool.eq_false_iff.mpr hB
  simp [transportAcrossIdentityIf, transportAcrossIdentity, hguardBFalse]

/-- Enabled path-transport canary: path evidence composes with tensor. -/
theorem transport_enabled_path_canary :
    transportAlongPathIf true canaryIdEvidence ["alice", "ally", "alicia"] canaryPayload =
      canaryPayload * (canaryIdEvidence "alice" "ally" * canaryIdEvidence "ally" "alicia") := by
  simp [transportAlongPathIf, pathEvidence, canaryIdEvidence, BinaryEvidence.tensor_one]

/-- Competing guarded identities remain distinct alternatives (no forced merge). -/
theorem competing_identities_retained_canary :
    "ally" ∈ guardedAlternatives canaryIdEvidence canaryLooseThresholds "alice"
      ["ally", "alicia"] ∧
      "alicia" ∈ guardedAlternatives canaryIdEvidence canaryLooseThresholds "alice"
      ["ally", "alicia"] ∧
      "ally" ≠ "alicia" := by
  refine competing_identities_preserved canaryIdEvidence canaryLooseThresholds
    (src := "alice") (y := "ally") (z := "alicia")
    (candidates := ["ally", "alicia"]) ?hneq ?hy ?hz ?hgy ?hgz
  · decide
  · simp
  · simp
  · exact canary_loose_guard_true _
  · exact canary_loose_guard_true _

end Mettapedia.Logic.IdentityEvidence
