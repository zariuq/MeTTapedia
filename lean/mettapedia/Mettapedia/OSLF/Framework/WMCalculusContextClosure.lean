import Mettapedia.OSLF.Framework.WMCalculusLanguageDef

/-!
# WM Calculus — Context Closure via Congruence Rules

WM patterns use `.apply` (not `.collection`), so the `congElem` constructor of
`DeclReducesWithPremises` never fires on WM terms.  To get reduction inside
subterms (e.g. reducing `W` inside `Extract(W, q)`), we add explicit congruence
`RewriteRule`s with `Premise.congruence` premises.

Each WM constructor with n argument positions gets one congruence rule per
position.  The `Premise.congruence src tgt` checks `rewriteWithContextNoPremises`
to verify that `src` can step to `tgt`.

## Architecture

- `wmCongruenceRules` — the list of all congruence rules
- `wmExtVertexLanguageDefWithCong` — extends the raw LanguageDef with congruence rules
- `wmFullVertexLanguageDefWithCong` — same for full vertex
- Subset theorems: raw rules ⊆ cong-extended rules

## References

- `Engine.lean` — `Premise.congruence`, `premiseStepWithEnv`
- `DeclReducesWithPremises.lean` — `congElem` (only for `.collection`)
- `WMCalculusLanguageDef.lean` — pattern vocabulary, raw rules
-/

namespace Mettapedia.OSLF.Framework.WMCalculusContextClosure

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.TypeSynthesis
open Mettapedia.OSLF.Framework.WMCalculusLanguageDef

/-! ## Congruence Rules

For each WM constructor, one rule per argument position.
The convention: variable `X` reduces to `X'` via congruence. -/

-- Revise(W₁, W₂): two positions

/-- If W₁ reduces to W₁', then Revise(W₁, W₂) reduces to Revise(W₁', W₂). -/
def ruleReviseCongLeft : RewriteRule := {
  name := "WM_ReviseCongLeft"
  typeContext := [("W1", .base "State"), ("W1p", .base "State"), ("W2", .base "State")]
  premises := [.congruence (.fvar "W1") (.fvar "W1p")]
  left := pRevise (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1p") (.fvar "W2")
}

/-- If W₂ reduces to W₂', then Revise(W₁, W₂) reduces to Revise(W₁, W₂'). -/
def ruleReviseCongRight : RewriteRule := {
  name := "WM_ReviseCongRight"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("W2p", .base "State")]
  premises := [.congruence (.fvar "W2") (.fvar "W2p")]
  left := pRevise (.fvar "W1") (.fvar "W2")
  right := pRevise (.fvar "W1") (.fvar "W2p")
}

-- Extract(W, q): two positions

/-- If W reduces to W', then Extract(W, q) reduces to Extract(W', q). -/
def ruleExtractCongLeft : RewriteRule := {
  name := "WM_ExtractCongLeft"
  typeContext := [("W", .base "State"), ("Wp", .base "State"), ("q", .base "Query")]
  premises := [.congruence (.fvar "W") (.fvar "Wp")]
  left := pExtract (.fvar "W") (.fvar "q")
  right := pExtract (.fvar "Wp") (.fvar "q")
}

/-- If q reduces to q', then Extract(W, q) reduces to Extract(W, q'). -/
def ruleExtractCongRight : RewriteRule := {
  name := "WM_ExtractCongRight"
  typeContext := [("W", .base "State"), ("q", .base "Query"), ("qp", .base "Query")]
  premises := [.congruence (.fvar "q") (.fvar "qp")]
  left := pExtract (.fvar "W") (.fvar "q")
  right := pExtract (.fvar "W") (.fvar "qp")
}

-- Combine(e₁, e₂): two positions

/-- If e₁ reduces to e₁', then Combine(e₁, e₂) reduces to Combine(e₁', e₂). -/
def ruleCombineCongLeft : RewriteRule := {
  name := "WM_CombineCongLeft"
  typeContext := [("e1", .base "Evidence"), ("e1p", .base "Evidence"), ("e2", .base "Evidence")]
  premises := [.congruence (.fvar "e1") (.fvar "e1p")]
  left := pCombine (.fvar "e1") (.fvar "e2")
  right := pCombine (.fvar "e1p") (.fvar "e2")
}

/-- If e₂ reduces to e₂', then Combine(e₁, e₂) reduces to Combine(e₁, e₂'). -/
def ruleCombineCongRight : RewriteRule := {
  name := "WM_CombineCongRight"
  typeContext := [("e1", .base "Evidence"), ("e2", .base "Evidence"), ("e2p", .base "Evidence")]
  premises := [.congruence (.fvar "e2") (.fvar "e2p")]
  left := pCombine (.fvar "e1") (.fvar "e2")
  right := pCombine (.fvar "e1") (.fvar "e2p")
}

-- Forget(S, W): one reducible position (scope S is a name, not reducible)

/-- If W reduces to W', then Forget(S, W) reduces to Forget(S, W'). -/
def ruleForgetCongRight : RewriteRule := {
  name := "WM_ForgetCongRight"
  typeContext := [("S", .base "Scope"), ("W", .base "State"), ("Wp", .base "State")]
  premises := [.congruence (.fvar "W") (.fvar "Wp")]
  left := pForget (.fvar "S") (.fvar "W")
  right := pForget (.fvar "S") (.fvar "Wp")
}

-- OverlapMerge(W₁, W₂): two positions

/-- If W₁ reduces to W₁', then OverlapMerge(W₁, W₂) reduces to OverlapMerge(W₁', W₂). -/
def ruleOverlapMergeCongLeft : RewriteRule := {
  name := "WM_OverlapMergeCongLeft"
  typeContext := [("W1", .base "State"), ("W1p", .base "State"), ("W2", .base "State")]
  premises := [.congruence (.fvar "W1") (.fvar "W1p")]
  left := pOverlapMerge (.fvar "W1") (.fvar "W2")
  right := pOverlapMerge (.fvar "W1p") (.fvar "W2")
}

/-- If W₂ reduces to W₂', then OverlapMerge(W₁, W₂) reduces to OverlapMerge(W₁, W₂'). -/
def ruleOverlapMergeCongRight : RewriteRule := {
  name := "WM_OverlapMergeCongRight"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("W2p", .base "State")]
  premises := [.congruence (.fvar "W2") (.fvar "W2p")]
  left := pOverlapMerge (.fvar "W1") (.fvar "W2")
  right := pOverlapMerge (.fvar "W1") (.fvar "W2p")
}

-- FallbackRevision(W₁, W₂): two positions

/-- If W₁ reduces to W₁', then FallbackRevision(W₁, W₂) reduces to FallbackRevision(W₁', W₂). -/
def ruleFallbackRevisionCongLeft : RewriteRule := {
  name := "WM_FallbackRevisionCongLeft"
  typeContext := [("W1", .base "State"), ("W1p", .base "State"), ("W2", .base "State")]
  premises := [.congruence (.fvar "W1") (.fvar "W1p")]
  left := pFallbackRevision (.fvar "W1") (.fvar "W2")
  right := pFallbackRevision (.fvar "W1p") (.fvar "W2")
}

/-- If W₂ reduces to W₂', then FallbackRevision(W₁, W₂) reduces to FallbackRevision(W₁, W₂'). -/
def ruleFallbackRevisionCongRight : RewriteRule := {
  name := "WM_FallbackRevisionCongRight"
  typeContext := [("W1", .base "State"), ("W2", .base "State"), ("W2p", .base "State")]
  premises := [.congruence (.fvar "W2") (.fvar "W2p")]
  left := pFallbackRevision (.fvar "W1") (.fvar "W2")
  right := pFallbackRevision (.fvar "W1") (.fvar "W2p")
}

-- ExperimentEvidence(W, q): two positions

/-- If W reduces to W', then ExperimentEvidence(W, q) reduces to ExperimentEvidence(W', q). -/
def ruleExperimentEvidenceCongLeft : RewriteRule := {
  name := "WM_ExperimentEvidenceCongLeft"
  typeContext := [("W", .base "State"), ("Wp", .base "State"), ("q", .base "Query")]
  premises := [.congruence (.fvar "W") (.fvar "Wp")]
  left := pExperimentEvidence (.fvar "W") (.fvar "q")
  right := pExperimentEvidence (.fvar "Wp") (.fvar "q")
}

-- KripkeEvidence(W, φ): one reducible position

/-- If W reduces to W', then KripkeEvidence(W, φ) reduces to KripkeEvidence(W', φ). -/
def ruleKripkeEvidenceCongLeft : RewriteRule := {
  name := "WM_KripkeEvidenceCongLeft"
  typeContext := [("W", .base "State"), ("Wp", .base "State"), ("phi", .base "ModalQuery")]
  premises := [.congruence (.fvar "W") (.fvar "Wp")]
  left := pKripkeEvidence (.fvar "W") (.fvar "phi")
  right := pKripkeEvidence (.fvar "Wp") (.fvar "phi")
}

-- GenericEvidence(W, q): two positions

/-- If W reduces to W', then GenericEvidence(W, q) reduces to GenericEvidence(W', q). -/
def ruleGenericEvidenceCongLeft : RewriteRule := {
  name := "WM_GenericEvidenceCongLeft"
  typeContext := [("W", .base "State"), ("Wp", .base "State"), ("q", .base "Query")]
  premises := [.congruence (.fvar "W") (.fvar "Wp")]
  left := pGenericEvidence (.fvar "W") (.fvar "q")
  right := pGenericEvidence (.fvar "Wp") (.fvar "q")
}

/-! ## Congruence Rule Lists -/

/-- Core congruence rules (for Revise, Extract, Combine). -/
def coreCongruenceRules : List RewriteRule :=
  [ruleReviseCongLeft, ruleReviseCongRight,
   ruleExtractCongLeft, ruleExtractCongRight,
   ruleCombineCongLeft, ruleCombineCongRight]

/-- All congruence rules including extension constructors. -/
def allCongruenceRules : List RewriteRule :=
  coreCongruenceRules ++
  [ruleForgetCongRight,
   ruleOverlapMergeCongLeft, ruleOverlapMergeCongRight,
   ruleFallbackRevisionCongLeft, ruleFallbackRevisionCongRight,
   ruleExperimentEvidenceCongLeft,
   ruleKripkeEvidenceCongLeft,
   ruleGenericEvidenceCongLeft]

/-! ## LanguageDefs with Congruence -/

/-- Extended 6-axis WM LanguageDef with core congruence rules. -/
def wmExtVertexLanguageDefWithCong (v : WMExtVertex) : LanguageDef := {
  name := s!"WMCalculusCong"
  types := wmTypes v
  terms := []
  equations := []
  rewrites := (wmExtVertexLanguageDef v).rewrites ++ coreCongruenceRules
}

/-- Extended full WM LanguageDef with all congruence rules. -/
def wmFullVertexLanguageDefWithCong (v : WMFullVertex) : LanguageDef := {
  name := "WMCalculusFullCong"
  types := wmFullTypes v
  terms := []
  equations := []
  rewrites := (wmFullVertexLanguageDef v).rewrites ++ allCongruenceRules
}

/-! ## Subset Theorems -/

/-- Raw rules are a subset of the congruence-extended rules (6-axis). -/
theorem rawRules_subset_congRules_ext (v : WMExtVertex) :
    ∀ r ∈ (wmExtVertexLanguageDef v).rewrites,
      r ∈ (wmExtVertexLanguageDefWithCong v).rewrites := by
  intro r hr
  simp only [wmExtVertexLanguageDefWithCong, List.mem_append]
  exact Or.inl hr

/-- Raw rules are a subset of the congruence-extended rules (full). -/
theorem rawRules_subset_congRules_full (v : WMFullVertex) :
    ∀ r ∈ (wmFullVertexLanguageDef v).rewrites,
      r ∈ (wmFullVertexLanguageDefWithCong v).rewrites := by
  intro r hr
  simp only [wmFullVertexLanguageDefWithCong, List.mem_append]
  exact Or.inl hr

/-- Core rules are a subset of the congruence-extended rules. -/
theorem coreRules_subset_congRules_ext (v : WMExtVertex) :
    ∀ r ∈ coreRules, r ∈ (wmExtVertexLanguageDefWithCong v).rewrites :=
  fun r hr => rawRules_subset_congRules_ext v r (coreRules_subset_wmExtVertex v r hr)

/-- Core rules are a subset of the congruence-extended full rules. -/
theorem coreRules_subset_congRules_full (v : WMFullVertex) :
    ∀ r ∈ coreRules, r ∈ (wmFullVertexLanguageDefWithCong v).rewrites :=
  fun r hr => rawRules_subset_congRules_full v r (coreRules_subset_wmFullVertex v r hr)

/-- The congruenceCollections field is the same for raw and cong-extended LanguageDefs,
    since both use the default value. -/
theorem congCollections_eq_ext (v : WMExtVertex) :
    (wmExtVertexLanguageDefWithCong v).congruenceCollections =
    (wmExtVertexLanguageDef v).congruenceCollections := by
  rfl

/-- Any raw reduction is also a congruence-extended reduction (6-axis).

    This follows from the fact that the raw rules are a subset of the
    cong-extended rules, and both share the same congruenceCollections. -/
theorem congReduces_of_rawReduces_ext (v : WMExtVertex) (p q : Pattern) :
    langReduces (wmExtVertexLanguageDef v) p q →
    langReduces (wmExtVertexLanguageDefWithCong v) p q := by
  intro h
  unfold langReduces langReducesUsing at h ⊢
  open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises in
  open Mettapedia.OSLF.MeTTaIL.Engine in
  have hrules := rawRules_subset_congRules_ext v
  have hcong : (wmExtVertexLanguageDefWithCong v).congruenceCollections =
      (wmExtVertexLanguageDef v).congruenceCollections := rfl
  induction h with
  | topRule r hr bs hmatch bs' hprem happly =>
    exact .topRule r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        RelationEnv.empty r.premises bs bs' hprem)
      happly
  | congElem hallow i hi r hr bs hmatch bs' hprem happly =>
    refine .congElem ?_ i hi r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        RelationEnv.empty r.premises bs bs' hprem)
      happly
    simp only [LanguageDef.allowsCongruenceIn] at hallow ⊢
    rw [hcong]; exact hallow

/-- Any raw reduction is also a congruence-extended reduction (full vertex). -/
theorem congReduces_of_rawReduces_full (v : WMFullVertex) (p q : Pattern) :
    langReduces (wmFullVertexLanguageDef v) p q →
    langReduces (wmFullVertexLanguageDefWithCong v) p q := by
  intro h
  unfold langReduces langReducesUsing at h ⊢
  open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises in
  open Mettapedia.OSLF.MeTTaIL.Engine in
  have hrules := rawRules_subset_congRules_full v
  have hcong : (wmFullVertexLanguageDefWithCong v).congruenceCollections =
      (wmFullVertexLanguageDef v).congruenceCollections := rfl
  induction h with
  | topRule r hr bs hmatch bs' hprem happly =>
    exact .topRule r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        RelationEnv.empty r.premises bs bs' hprem)
      happly
  | congElem hallow i hi r hr bs hmatch bs' hprem happly =>
    refine .congElem ?_ i hi r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        RelationEnv.empty r.premises bs bs' hprem)
      happly
    simp only [LanguageDef.allowsCongruenceIn] at hallow ⊢
    rw [hcong]; exact hallow

/-! ## Guarded LanguageDefs with Congruence (completing the 2×2 square) -/

/-- Guarded 6-axis WM LanguageDef with core congruence rules.
    Completes the 2×2 square: {Raw, Guarded} × {Plain, +Cong}. -/
def wmExtVertexLanguageDefGuardedWithCong (v : WMExtVertex) : LanguageDef := {
  name := s!"WMCalculusGuardedCong"
  types := wmTypes v
  terms := []
  equations := []
  rewrites := (wmExtVertexLanguageDefGuarded v).rewrites ++ coreCongruenceRules
}

/-- Guarded full WM LanguageDef with all congruence rules. -/
def wmFullVertexLanguageDefGuardedWithCong (v : WMFullVertex) : LanguageDef := {
  name := "WMCalculusFullGuardedCong"
  types := wmFullTypes v
  terms := []
  equations := []
  rewrites := (wmFullVertexLanguageDefGuarded v).rewrites ++ allCongruenceRules
}

/-! ### Guarded ⊆ Guarded+Cong (horizontal arrows) -/

/-- Guarded rules are a subset of guarded+cong rules (6-axis). -/
theorem guardedRules_subset_guardedCongRules_ext (v : WMExtVertex) :
    ∀ r ∈ (wmExtVertexLanguageDefGuarded v).rewrites,
      r ∈ (wmExtVertexLanguageDefGuardedWithCong v).rewrites := by
  intro r hr
  simp only [wmExtVertexLanguageDefGuardedWithCong, List.mem_append]
  exact Or.inl hr

/-- Guarded rules are a subset of guarded+cong rules (full). -/
theorem guardedRules_subset_guardedCongRules_full (v : WMFullVertex) :
    ∀ r ∈ (wmFullVertexLanguageDefGuarded v).rewrites,
      r ∈ (wmFullVertexLanguageDefGuardedWithCong v).rewrites := by
  intro r hr
  simp only [wmFullVertexLanguageDefGuardedWithCong, List.mem_append]
  exact Or.inl hr

/-- CongruenceCollections match between guarded and guarded+cong (6-axis). -/
theorem congCollections_eq_guardedCong_ext (v : WMExtVertex) :
    (wmExtVertexLanguageDefGuardedWithCong v).congruenceCollections =
    (wmExtVertexLanguageDefGuarded v).congruenceCollections := rfl

/-- CongruenceCollections match between guarded and guarded+cong (full). -/
theorem congCollections_eq_guardedCong_full (v : WMFullVertex) :
    (wmFullVertexLanguageDefGuardedWithCong v).congruenceCollections =
    (wmFullVertexLanguageDefGuarded v).congruenceCollections := rfl

/-- Any guarded reduction is also a guarded+cong reduction (6-axis).
    Horizontal arrow in the 2×2 square. -/
theorem guardedCongReduces_of_guardedReduces_ext (v : WMExtVertex) (p q : Pattern) :
    langReducesUsing relEnv (wmExtVertexLanguageDefGuarded v) p q →
    langReducesUsing relEnv (wmExtVertexLanguageDefGuardedWithCong v) p q := by
  intro h
  unfold langReducesUsing at h ⊢
  open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises in
  open Mettapedia.OSLF.MeTTaIL.Engine in
  have hrules := guardedRules_subset_guardedCongRules_ext v
  have hcong : (wmExtVertexLanguageDefGuardedWithCong v).congruenceCollections =
      (wmExtVertexLanguageDefGuarded v).congruenceCollections := rfl
  induction h with
  | topRule r hr bs hmatch bs' hprem happly =>
    exact .topRule r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        relEnv r.premises bs bs' hprem)
      happly
  | congElem hallow i hi r hr bs hmatch bs' hprem happly =>
    refine .congElem ?_ i hi r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        relEnv r.premises bs bs' hprem)
      happly
    simp only [LanguageDef.allowsCongruenceIn] at hallow ⊢
    rw [hcong]; exact hallow

/-- Any guarded reduction is also a guarded+cong reduction (full).
    Horizontal arrow in the 2×2 square. -/
theorem guardedCongReduces_of_guardedReduces_full (v : WMFullVertex) (p q : Pattern) :
    langReducesUsing relEnv (wmFullVertexLanguageDefGuarded v) p q →
    langReducesUsing relEnv (wmFullVertexLanguageDefGuardedWithCong v) p q := by
  intro h
  unfold langReducesUsing at h ⊢
  open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises in
  open Mettapedia.OSLF.MeTTaIL.Engine in
  have hrules := guardedRules_subset_guardedCongRules_full v
  have hcong : (wmFullVertexLanguageDefGuardedWithCong v).congruenceCollections =
      (wmFullVertexLanguageDefGuarded v).congruenceCollections := rfl
  induction h with
  | topRule r hr bs hmatch bs' hprem happly =>
    exact .topRule r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        relEnv r.premises bs bs' hprem)
      happly
  | congElem hallow i hi r hr bs hmatch bs' hprem happly =>
    refine .congElem ?_ i hi r (hrules r hr) bs hmatch bs'
      (applyPremisesWithEnv_mono hrules hcong
        relEnv r.premises bs bs' hprem)
      happly
    simp only [LanguageDef.allowsCongruenceIn] at hallow ⊢
    rw [hcong]; exact hallow

/-! ## OSLF Per Vertex (With Congruence) -/

/-- OSLF type system for congruence-extended 6-axis WM vertex. -/
noncomputable def wmExtVertexOSLFWithCong (v : WMExtVertex) :=
  langOSLF (wmExtVertexLanguageDefWithCong v)

/-- OSLF type system for congruence-extended full WM vertex. -/
noncomputable def wmFullVertexOSLFWithCong (v : WMFullVertex) :=
  langOSLF (wmFullVertexLanguageDefWithCong v)

/-- Galois connection for congruence-extended 6-axis vertex. -/
theorem wmCongCalc_galois (v : WMExtVertex) :
    GaloisConnection
      (langDiamond (wmExtVertexLanguageDefWithCong v))
      (langBox (wmExtVertexLanguageDefWithCong v)) :=
  langGalois (wmExtVertexLanguageDefWithCong v)

/-- Galois connection for congruence-extended full vertex. -/
theorem wmCongFullCalc_galois (v : WMFullVertex) :
    GaloisConnection
      (langDiamond (wmFullVertexLanguageDefWithCong v))
      (langBox (wmFullVertexLanguageDefWithCong v)) :=
  langGalois (wmFullVertexLanguageDefWithCong v)

/-! ## OSLF Per Vertex (Guarded+Cong) -/

open Mettapedia.OSLF.MeTTaIL.Engine
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.DeclReducesPremises

/-- OSLF type system for guarded+cong 6-axis WM vertex. -/
noncomputable def wmExtVertexOSLFGuardedWithCong (ρ : RelationEnv) (v : WMExtVertex) :=
  langOSLFUsing ρ (wmExtVertexLanguageDefGuardedWithCong v)

/-- OSLF type system for guarded+cong full WM vertex. -/
noncomputable def wmFullVertexOSLFGuardedWithCong (ρ : RelationEnv) (v : WMFullVertex) :=
  langOSLFUsing ρ (wmFullVertexLanguageDefGuardedWithCong v)

/-- Galois connection for guarded+cong 6-axis vertex. -/
theorem wmGuardedCongCalc_galois (relEnv : RelationEnv) (v : WMExtVertex) :
    GaloisConnection
      (langDiamondUsing relEnv (wmExtVertexLanguageDefGuardedWithCong v))
      (langBoxUsing relEnv (wmExtVertexLanguageDefGuardedWithCong v)) :=
  langGaloisUsing relEnv (wmExtVertexLanguageDefGuardedWithCong v)

/-- Galois connection for guarded+cong full vertex. -/
theorem wmGuardedCongFullCalc_galois (relEnv : RelationEnv) (v : WMFullVertex) :
    GaloisConnection
      (langDiamondUsing relEnv (wmFullVertexLanguageDefGuardedWithCong v))
      (langBoxUsing relEnv (wmFullVertexLanguageDefGuardedWithCong v)) :=
  langGaloisUsing relEnv (wmFullVertexLanguageDefGuardedWithCong v)

end Mettapedia.OSLF.Framework.WMCalculusContextClosure
